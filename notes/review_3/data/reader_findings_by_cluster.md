# Line-by-line review: findings by theory cluster (2026-10-07)

Produced by 17 independent readers, one per cluster, each reading every line of its theories. These are CLAIMS: the ones the plan relies on were re-checked against the semantic dependency closure (`dead_code_by_theory.txt`), the higher-order clone matcher, or in PIDE (`verification_results.md`). Severity/confidence are the readers' own. Line numbers refer to commit 3bc3803.


## SMS

I read all 7 593 lines of the session. The theories build in one chain, Matrix_Algebra -> Outer_Products -> Orthonormal_Families -> Symmetric_Spectral -> Ky_Fan -> Eigenvalue_Continuity -> Poincare_Separation. Householder_Rotation is the only branch, and it depends only on Outer_Products.

What the session proves:
- the spectral theorem (`symmetric_eigenbasis`), via Rayleigh maximisers on invariant subspaces;
- the definition `psd` and the fact that trace(ab) >= 0 for psd a and b;
- Ky Fan sums defined basis-free, as a Sup over projections of given trace, and shown to be attained at an eigenbasis subset (`kyfan_attained`);
- the ordered eigenvalues `eigval` (differences of Ky Fan sums), shown to decrease;
- the positive-part sums `possum` and the paper-shaped `bracket` quantity;
- a box/simplex linear-programming bound (`lp_upper_bound`);
- Lipschitz continuity of `kyfan`, `eigval`, `possum` and `bracket` in the matrix;
- Courant-Fischer scaffolding;
- Householder reflections and two rotation constructions with their continuity.

**Poincare separation is missing.** The ROOT, the root.tex abstract and the header of Poincare_Separation all advertise it, but no statement in the session proves it. The general form, `eigval_ge_of_subspace`, and the only interlacing theorem, `poincare_separation` (specialised to the paper's `Mp p M`), are in `Relative_Arbitrage/Operator_Formula`.

**The session is not "done" as §2.11 of the plan says.** In particular:
- about 40 statements re-prove HOL-Analysis lemmas. The §6.2 find_theorems sweep was never run; my grep-level version is below.
- about 25 groups of clones remain inside the session. Some are verbatim (`quad_diff_bound`/`_gen`, `onormal_extension`/`_within`, `possum_full_eq_sum_basis`/`possum_within_threshold`, `exists_min_subset`/`exists_top_subset`), and one is a triple (three copies of the "symmetric matrix swaps the quadratic form" lemma).
- about 30 prose blocks are paper-specific (citing Lemma 2.1, 2.2 and 3.1, Eqs. (1.9), (3.4), (3.5), (3.8), Theorem 4.2(a), Remark 1.1(c), Case 1/2, `ell_op_strict_contradiction`, `eigen_ub`, "feasible set"), or are orphaned, stale or garbled.
- Matrix_Algebra (2 689 lines) is a provenance-ordered grab bag. One subsection spans lines 344-2543, and it holds second-order necessary conditions, "pinch" real analysis and orthogonal/affine maps besides matrix calculus.
- Poincare_Separation is a second grab bag: outer-product norms, Frobenius norm, psd closedness, rank-one projections, and Lipschitz bounds for `possum`/`bracket`.
- Some SMS lemmas are re-proved in higher sessions (`onormal_parseval`, `quadform_sum_outer` in Pair_Path_Laws; `hessian_abs_bound_of_two_sided` in Doubling_Of_Variables). The SMS copy of the latter chain is dead code.

**How this was checked.** I tried to use PIDE MCP as asked, but it was not usable. No HOL-Analysis heap exists yet, and a concurrent `isabelle build` was using all 15 GB of RAM. So library duplicates were checked by grepping the exact statements in /opt/Isabelle2026-RC3/src/HOL/Analysis and /opt/afp/thys, and usage was checked by grepping the repository. Library lemma names below are quoted from their source files.


### SMS-1. The advertised Poincare separation theorem is not in the session; its general form is in the paper session

*faithfulness, impact high, confidence high, ~250 lines.*  
Locations: Symmetric_Matrix_Spectra/ROOT:7 (description: '... and Poincare separation'); Symmetric_Matrix_Spectra/document/root.tex abstract ('interlace with those of any compression to a subspace, which is Poincare separation'); Symmetric_Matrix_Spectra/Poincare_Separation.thy:9-19 (header); Relative_Arbitrage/Operator_Formula.thy:289 eigval_ge_of_subspace; Relative_Arbitrage/Operator_Formula.thy:402 eigval_ge_of_eigen_lb; Relative_Arbitrage/Operator_Formula.thy:1505 poincare_separation; Relative_Arbitrage/Operator_Continuity.thy:41 rank1proj

Poincare_Separation.thy claims 'the ordered eigenvalues of a compression of a symmetric matrix to a subspace interlace those of the matrix itself', but no lemma in the session states any interlacing. The theory contains only scaffolding: subspace_inter_nonzero, dim_inter_ge, quadform_ge_on_span_threshold, onormal_orthogonal_to_span_complement and parseval_onormal.

The Courant-Fischer lower bound `eigval_ge_of_subspace` (paper-free: 'if the Rayleigh quotient of a is >= c on a subspace of dimension >= m then c <= eigval m a') is in Operator_Formula:289. The only interlacing statement, `poincare_separation`, is stated for the paper's `Mp p M`.

That proof (Operator_Formula:1530-1574) uses only two facts about Mp p M: it is symmetric, and its quadratic form agrees with M's on the hyperplane p^perp (Mp_quadform_perp). So the paper-free theorem is:
- transpose N = N, and
- x.(N x) = x.(M x) on a subspace W of dimension n - r,
- imply eigval (i+r) M <= eigval i N.
This is §3.1 of the plan (eigval_ge_of_subspace into SMS), still open.

Evidence: grep -i 'interlac\|poincare' over Symmetric_Matrix_Spectra/*.thy finds only prose (MA:688, PS:3,10,127) and ROOT:7. Operator_Formula:1505: theorem poincare_separation ... shows "eigval (Suc i) M \<le> eigval i (Mp p M)". The proof ends 'by (rule eigval_ge_of_subspace[OF symMp subSW dimSW quad])' with quad from Mp_quadform_perp.

Suggested action: Move eigval_ge_of_subspace and eigval_ge_of_eigen_lb into Poincare_Separation (they mention no paper constant). Add the general one-sided separation 'symmetric N agreeing with M on a codimension-r subspace => eigval (i+r) M <= eigval i N'. Derive Operator_Formula's poincare_separation as a 3-line corollary. Alternatively, rename the theory (e.g. Courant_Fischer) and fix ROOT/root.tex.


### SMS-2. Matrix-vector and matrix-matrix algebra that HOL-Analysis already has

*library_duplicate, impact high, confidence high, ~180 lines.*  
Locations: Matrix_Algebra.thy:68 scaleR_matrix_vector; Matrix_Algebra.thy:88 matvec_add_right; Matrix_Algebra.thy:93 matrix_vector_mult_diff; Matrix_Algebra.thy:244 matrix_vector_mult_diff_gen; Matrix_Algebra.thy:653 matvec_diff_right; Matrix_Algebra.thy:658 matvec_scaleR_right; Matrix_Algebra.thy:691 matrix_vector_mult_add; Matrix_Algebra.thy:60 scaleR_matrix_mult; Matrix_Algebra.thy:1343 matmul_scaleR_right; Matrix_Algebra.thy:192 inner_transpose_matrix; Matrix_Algebra.thy:1323 matvec_blin; Matrix_Algebra.thy:2553 matrix_vec_apply; Matrix_Algebra.thy:607 inner_axis_one; Matrix_Algebra.thy:1237 axis1_inner; Matrix_Algebra.thy:612 matrix_vector_axis_one; Matrix_Algebra.thy:1259 matvec_axis1; Poincare_Separation.thy:23 trace_diff_matrix

Each of these restates a lemma of Finite_Cartesian_Product, Cartesian_Space, Cartesian_Euclidean_Space or Determinants, often with a 10-20 line proof. Plan §2.6 items 3-4 kept matvec_scaleR_right and matvec_diff_right, which are themselves HOL lemmas.

Mapping:
- matvec_add_right = matrix_vector_right_distrib
- matvec_diff_right = matrix_vector_mult_diff_gen = matrix_vector_mult_diff_distrib
- matvec_scaleR_right = matrix_vector_mult_scaleR
- matrix_vector_mult_diff (17-line proof) = matrix_vector_mult_diff_rdistrib
- matrix_vector_mult_add (19 lines) = matrix_vector_mult_add_rdistrib
- scaleR_matrix_vector = scaleR_matrix_vector_assoc[symmetric]
- scaleR_matrix_mult = scalar_matrix_assoc[symmetric]
- matmul_scaleR_right = matrix_scalar_ac + scalar_matrix_assoc
- inner_transpose_matrix = transpose_mv_inner (Cartesian_Euclidean_Space:499) up to inner_commute, or dot_lmul_matrix + transpose_matrix_vector
- matvec_blin = matrix_vector_mul_bounded_linear
- matrix_vec_apply = fun_cong of matrix_vector_mul(2) ('linear f ==> (\<lambda>x. matrix f *v x) = f')
- inner_axis_one / axis1_inner = inner_axis'
- matrix_vector_axis_one / matvec_axis1 = matrix_vector_mult_basis + column_def
- trace_diff_matrix = trace_sub (Determinants:27)

Evidence: Finite_Cartesian_Product.thy:1153 matrix_vector_right_distrib "A *v (x + y) = A *v x + A *v y"; :1157 matrix_vector_mult_diff_distrib "A *v (x - y) = A *v x - A *v y"; :1162 matrix_vector_mult_scaleR "A *v (c *\<^sub>R x) = c *\<^sub>R (A *v x)"; :1173 matrix_vector_mult_add_rdistrib; :1177 matrix_vector_mult_diff_rdistrib; :1033 scalar_matrix_assoc; :1038 matrix_scalar_ac; :670 inner_axis'. Cartesian_Space.thy:371 scaleR_matrix_vector_assoc; :517 matrix_vector_mult_basis; matrix_vector_mul[simp] (Cartesian_Space ~line 160). Cartesian_Euclidean_Space.thy:90 matrix_vector_mul_bounded_linear; :499 transpose_mv_inner. Determinants.thy:27 trace_sub. Rough use counts outside SMS (grep, including notes): matvec_scaleR_right 19, scaleR_matrix_vector 22, matvec_blin 15, inner_transpose_matrix 15, scaleR_matrix_mult 14.

Suggested action: Delete and redirect to the HOL names. Where the orientation matters for simp, keep a one-line 'lemmas scaleR_matrix_vector = scaleR_matrix_vector_assoc[symmetric]'. Record the hits in the §6.2 completion note.


### SMS-3. Orthogonal-matrix and affine-image block re-derives HOL's orthogonal-transformation and interior-of-linear-image theory

*library_duplicate, impact medium, confidence high, ~200 lines.*  
Locations: Matrix_Algebra.thy:718 orth_preserves_inner; Matrix_Algebra.thy:806 norm_orthogonal_matrix_vector; Matrix_Algebra.thy:920-1043 open_orth_image, open_affine_image, affine_interior_sub, affine_inv_shape, affine_inv_left, affine_inv_right, affine_interior_image; Householder_Rotation.thy:97 orthogonal_matrixI; Householder_Rotation.thy:251 rotv_orthogonal; Householder_Rotation.thy:309 rotm_orthogonal; Householder_Rotation.thy:125 hrefl_orthogonal (unused)

About 200 lines re-derive library facts. The library lemmas that cover them:
- HOL's `orthogonal_transformation_matrix`: orthogonal_transformation f <-> linear f /\ orthogonal_matrix (matrix f).
- With `orthogonal_transformation_def` and `orthogonal_transformation_norm`, it gives orth_preserves_inner, norm_orthogonal_matrix_vector and orthogonal_matrixI (27 lines) in two lines each.
- `orthogonal_matrix_mul`: rotv_orthogonal (20 lines) and rotm_orthogonal are `orthogonal_matrix_mul[OF hrefl_orthogonal hrefl_orthogonal]`. hrefl_orthogonal exists, but nothing uses it.
- affine_interior_image (34 lines) plus four helper lemmas and open_orth_image (28 lines) follow from three lemmas, because z |-> c *R (R *v z) is linear and injective:
  - `interior_injective_linear_image` (Topology_Euclidean_Space:2147)
  - `interior_translation` (Elementary_Normed_Spaces:1238)
  - `open_affinity` (Elementary_Normed_Spaces:1223)

Evidence: Cartesian_Space.thy:866 'proposition orthogonal_matrix_mul ... shows "orthogonal_matrix(A ** B)"'; :872 orthogonal_transformation_matrix. Linear_Algebra.thy:253 orthogonal_transformation_def, :301 orthogonal_transformation_norm. Topology_Euclidean_Space.thy:2147 'lemma interior_injective_linear_image: ... assumes "linear f" "inj f" shows "interior(f ` S) = f ` (interior S)"'. hrefl_orthogonal: one occurrence in the whole repository (its definition).

Suggested action: Replace orthogonal_matrixI by orthogonal_transformation_matrix. Derive rotv/rotm orthogonality from orthogonal_matrix_mul + hrefl_orthogonal. Reduce affine_interior_image to interior_translation + interior_injective_linear_image, and drop the helpers (open_orth_image, open_affine_image, affine_interior_sub, affine_inv_*), keeping only those used externally (affine_inv_dist: Comparison_Two_Domain).


### SMS-4. Same-statement clone pairs inside Matrix_Algebra (and with Poincare_Separation)

*clone, impact medium, confidence high, ~150 lines.*  
Locations: Matrix_Algebra.thy:73 neg_matrix_vector / :226 matrix_vector_neg_left; Matrix_Algebra.thy:244 matrix_vector_mult_diff_gen / :653 matvec_diff_right; Matrix_Algebra.thy:113 transpose_diff_matrix / :2070 transpose_matrix_diff; Matrix_Algebra.thy:120 matrix_vector_mult_vsum / :2054 matvec_sum_right; Matrix_Algebra.thy:27 transpose_matrix_sum / Poincare_Separation.thy:411 transpose_sum_matrix; Matrix_Algebra.thy:607 inner_axis_one / :1237 axis1_inner; Matrix_Algebra.thy:612 matrix_vector_axis_one / :1259 matvec_axis1; Matrix_Algebra.thy:1047 diag_eq_inner_axis / :1069 diag_entry_quadform; Matrix_Algebra.thy:744 transpose_shift_add / :2381 transpose_shifted_block; Matrix_Algebra.thy:766 transpose_shift_diff / :1516 transpose_sub_smat; Matrix_Algebra.thy:1116 bounded_linear_cross / :1132 bounded_linear_cross_pair; Matrix_Algebra.thy:1326 matmul_sandwich_blin / :2474 conj_mat_continuous

Twelve pairs with identical statements (up to variable names, sides of an equation, or square versus rectangular types). They survived the first two passes because probe4 only renames short identifiers. Notes on individual pairs:
- transpose_sub_smat (H - s I) and transpose_shift_diff (A - \<delta> I) are the same lemma, and both have external users.
- bounded_linear_cross_pair is bounded_linear_cross with the vector sum written outside the \<chi>; both are outer_prod x v + outer_prod v x.
- conj_mat_continuous re-proves the linearity of N |-> R^T N R that matmul_sandwich_blin proves for S N S^T.
- transpose_sum_matrix (with an unneeded 'finite S') duplicates transpose_matrix_sum, which has no hypothesis.

Evidence: MA:73 'shows "(- A) *v x = - (A *v x)"' and MA:226 'shows "(- B) *v x = - (B *v x)"', with identical proofs. MA:744 and MA:2381 both: assumes "transpose A = A" shows "transpose (A + \<delta> *\<^sub>R mat 1) = A + \<delta> *\<^sub>R mat 1". MA:1069 'axis l 1 \<bullet> (a *v axis l 1) = a $ l $ l' versus MA:1047 'a $ i $ i = axis i (1 :: real) \<bullet> (a *v axis i 1)'. PS:411 assumes "finite S" versus MA:27 unconditional.

Suggested action: Keep one of each pair (prefer the earlier, more general one), redirect the uses, and do not leave aliases. State bounded_linear_cross once as bounded_linear (\<lambda>v. outer_prod x v + outer_prod v x), ideally from a 'bounded_bilinear outer_prod' lemma in Outer_Products.


### SMS-5. Three copies of 'a symmetric matrix swaps the arguments of its bilinear form'

*clone, impact medium, confidence high, ~45 lines.*  
Locations: Matrix_Algebra.thy:249 inner_matrix_sym; Matrix_Algebra.thy:2588 matrix_symmetric_swap; Symmetric_Spectral.thy:23 sym_inner_swap

All three state transpose Z = Z ==> v . (Z *v z) = z . (Z *v v). The proofs differ: a 20-line entrywise one, a dot_lmul_matrix one, and an inner_transpose_matrix one. They are used respectively by Doubling_Of_Variables/Viscosity_Ball, by Theorem_On_Sums, and by Ky_Fan/Poincare_Separation/Operator_Formula/Curvature_Operator.

Evidence: MA:249 'assumes s: "transpose Z = Z" shows "v \<bullet> (Z *v z) = z \<bullet> (Z *v v)"'; MA:2588 'assumes symH: "transpose H = H" shows "z \<bullet> (H *v h) = h \<bullet> (H *v z)"'; SS:23 'assumes "transpose a = a" shows "x \<bullet> (a *v y) = y \<bullet> (a *v x)"'.

Suggested action: Keep one copy (in Matrix_Algebra, near inner_transpose_matrix) and rename the uses (about 15 sites).


### SMS-6. quad_diff_bound is an instance of quad_diff_bound_gen; the 80-line proofs are copies

*clone, impact medium, confidence high, ~80 lines.*  
Locations: Matrix_Algebra.thy:1426-1508 quad_diff_bound; Matrix_Algebra.thy:1609-1687 quad_diff_bound_gen

quad_diff_bound assumes a, b in cball x rb. quad_diff_bound_gen assumes norm (a - x) <= R and norm (b - x) <= R, which follow directly. Apart from the first two `have`s, the proofs are line-for-line identical (t1, t2, tri, fin). The intervening prose (MA:1601-1607) even says it is the same bound 're-stated with the confinement region decoupled'.

Evidence: Both conclusions read '\<bar>q \<bullet> (b - x) + (1/2) * ((b - x) \<bullet> (M *v (b - x))) - (q \<bullet> (a - x) + ...)\<bar> \<le> (norm q + 2 * (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>) * R) * norm (b - a)'.

Suggested action: Delete quad_diff_bound's proof and derive it as 'quad_diff_bound_gen[OF sym] using a b by (simp add: dist_norm norm_minus_commute)'. Its users are Value_Function_Euler_Construction (2 occurrences).


### SMS-7. onormal_extension is onormal_extension_within at W = UNIV; the normalisation proof is copied

*clone, impact medium, confidence high, ~79 lines.*  
Locations: Orthonormal_Families.thy:117-195 onormal_extension; Orthonormal_Families.thy:272-364 onormal_extension_within

Both normalise the output of HOL's orthogonal_extension with the same steps: C_def = (\<lambda>u. u /\<^sub>R norm u) ` ((B \<union> U) - {0}), then C_norm, C_orth, BC, C_sub and sub_C, line for line. onormal_extension is the special case W = UNIV, since subspace UNIV holds and B \<subseteq> UNIV.

Evidence: OF:126 and OF:295 have the identical 'define C where "C = (\<lambda>u. u /\<^sub>R norm u) ` ((B \<union> U) - {0})"', followed by identical C_norm/C_orth/C_sub/sub_C blocks.

Suggested action: Prove onormal_extension by onormal_extension_within[OF B subspace_UNIV subset_UNIV]. That saves about 75 lines.


### SMS-8. possum_full_eq_sum_basis is possum_within_threshold at S = B; 70-line proof duplicated

*clone, impact medium, confidence high, ~68 lines.*  
Locations: Ky_Fan.thy:1274-1342 possum_full_eq_sum_basis; Ky_Fan.thy:1515-1606 possum_within_threshold

Take S = B and m = card B = CARD('n) (onormal_span_card). The threshold hypothesis is then vacuous (B - B = {}), and possum_within_threshold yields exactly 'possum CARD('n) a = (\<Sum>u\<in>B. max (u \<bullet> (a *v u)) 0)'. The two proofs share the same parts:
- the positive-part set T or P;
- the same threshold argument;
- the same split/out/inn computation;
- the same Max_le_iff bound.
Poincare_Separation.kyfan_full_eq_trace (PS:39) already uses this vacuous-threshold trick.

Evidence: KF:1279 'shows "possum CARD('n) a = (\<Sum>u\<in>B. max (u \<bullet> (a *v u)) 0)"'; KF:1522 'shows "possum m a = (\<Sum>u\<in>S. max (u \<bullet> (a *v u)) 0)"' under S \<subseteq> B, card S = m, thresh. PS:39 'have vac: ... if "u \<in> B" "v \<in> B - B"'.

Suggested action: Replace possum_full_eq_sum_basis's proof by possum_within_threshold[OF B sym eig subset_refl onormal_span_card[OF B]] with the vacuous threshold. It has 4 external users.


### SMS-9. SMS lemmas re-proved in higher sessions

*clone, impact medium, confidence high, ~120 lines.*  
Locations: Relative_Arbitrage/Pair_Path_Laws.thy:2014 onormal_parseval = Poincare_Separation.thy:325 parseval_onormal; Relative_Arbitrage/Pair_Path_Laws.thy:1937 quadform_sum_outer = Poincare_Separation.thy:229 quadform_weighted_outer_sum_eq; Relative_Arbitrage/Pair_Path_Laws.thy:1898 matvec_sum_outer (first step of PS:208/234); Relative_Arbitrage/Pair_Path_Laws.thy:2119 onormal_span_parseval (generalises parseval_onormal and is the equality case of Orthonormal_Families.thy:66 onormal_bessel); Second_Order_Viscosity_Analysis/Doubling_Of_Variables.thy:3010 hessian_abs_bound_of_two_sided versus Symmetric_Spectral.thy:530 semiconvex_hessian_abs_bound; Second_Order_Viscosity_Analysis/Sup_Convolution.thy:473 second_order_interior_max versus Matrix_Algebra.thy:387 local_min_hessian_psd; Relative_Arbitrage/Exit_Class.thy:218 and Pair_Path_Space.thy:771 outerp_eq_outer_prod (stated twice)

The re-proofs:
- onormal_parseval: identical statement and proof route to parseval_onormal.
- quadform_sum_outer: identical statement to quadform_weighted_outer_sum_eq.
- onormal_span_parseval: the general form (x in span S) of which parseval_onormal is the UNIV case. It belongs in Orthonormal_Families next to onormal_bessel.
- hessian_abs_bound_of_two_sided: the generic form of semiconvex_hessian_abs_bound, whose SMS copy is unused.
- second_order_interior_max / local_min_hessian_psd: the same second-order necessary condition, under a Peano-Taylor hypothesis in one and a differentiable-gradient hypothesis in the other.
- outerp_eq_outer_prod: proved twice in the paper session (outside this cluster; reported for completeness).

Evidence: Pair_Path_Laws:2014 'lemma onormal_parseval ... assumes B: "onormal B" and sp: "span B = UNIV" shows "(\<Sum>u\<in>B. (u \<bullet> z)\<^sup>2) = z \<bullet> z"'; PS:325 'lemma parseval_onormal ... assumes B: "onormal B" "span B = UNIV" shows "(\<Sum>v\<in>B. (v \<bullet> x)^2) = x \<bullet> x"'. Pair_Path_Laws:1940 'shows "z \<bullet> ((\<Sum>u\<in>S. c u *\<^sub>R outer_prod u u) *v z) = (\<Sum>u\<in>S. c u * (u \<bullet> z)\<^sup>2)"' versus PS:232 the same with g, x.

Suggested action: Delete onormal_parseval and quadform_sum_outer. Move onormal_span_parseval and matvec_sum_outer into Orthonormal_Families/Outer_Products and derive parseval_onormal from the former. Delete the SMS semiconvex chain (see the dead-code finding). Keep a single outerp_eq_outer_prod.


### SMS-10. About 30 paper-specific or proof-plan prose blocks in a session advertised as paper-free

*documentation, impact medium, confidence high, ~250 lines.*  
Locations: Matrix_Algebra.thy:351-357, 572-573, 601-605 ('Lemma 2.2 of [LSS] of the paper ... eigen_ub a L'), 685-689 (Eq. (3.4), (3.5), M_p), 711-716 ('feasible set of p'), 1086-1089, 1123-1125 (Lemma 2.1, 'n - k'), 1315-1318 (outerp, Euler machinery), 1364-1370 (Brownian moments), 1510-1514 ('value bound v(x) < T'), 1557-1576 (Eq. (1.9), Remark 1.1(c), Ambrosio-Soner), 1601-1607, 1689-1695, 1718-1737 ('Case 2', 'The paper only records'), 1774-1790, 1894-1912, 2029-2035, 2140-2142, 2167-2170, 2293-2296, 2313-2317, 2397-2401, 2438-2441, 2488-2489, 2528-2530 ('clause (0)'), 2671-2674; Symmetric_Spectral.thy:488-499 (subsection 'The closing chain of Theorem 4.2(a)', names visc_subsol_scaled_strict, ell_op_strict_contradiction), 567-573, 611-618, 638-646 ('Route (i), threaded'), 663-667; Ky_Fan.thy:538, 1266-1272, 1730-1733 (Eq. (3.5)); Eigenvalue_Continuity.thy:16-18, 156-158 (Lemma 3.1, Eq. (3.8)); Poincare_Separation.thy:124-127 (Eq. (3.5)), 220-222 (clipped matrix c), 445-446 (annihilates p), 987, 1008-1010, 1063-1065 (M_p, c = min(\<lambda>_n) 0); Householder_Rotation.thy:494-495; Symmetric_Matrix_Spectra/document/root.bib (only LaiShkolnikovSoner is cited; EvansGariepy and CrandallIshiiLions are unused)

The plan's rule is that 'each session must be describable in one sentence that does not name this paper'. The prose of this session cites the paper 8 times and explains the paper's proof steps: Theorem 4.2(a), Lemma 2.1, 2.2 and 3.1, Eqs. (1.9), (3.4), (3.5), (3.8), Cases 1/2, the 'horns'. It names ell_op_strict_contradiction and visc_subsol_scaled_strict (Relative_Arbitrage/Comparison_Strictness) and eigen_ub (the paper session).

Most of these blocks were carried along with the lemma moves of phases 3/9. Many no longer sit next to the lemma they describe, e.g.:
- MA:685-689 precedes matrix_vector_mult_add;
- MA:1123-1125 precedes bounded_linear_trace;
- PS:445-446 precedes outer_prod_scaleR_right.

Evidence: MA:601 'text \<open>Lemma 2.2 of \<^cite>\<open>LaiShkolnikovSoner\<close> of the paper assumes the set \<open>S\<close> of admissible covariances is bounded. For the paper's \<open>S\<close> ... \<open>eigen_ub a L\<close>'. SS:494 '(\<open>ell_op_strict_contradiction\<close>). This is Theorem 4.2(a) modulo the hypotheses ...'. MA:1567 'the Ambrosio-Soner flow case of Remark 1.1(c)'.

Suggested action: Move the paper-facing prose to the paper-session theories that consume the lemmas (Curvature_Operator, Comparison_Strictness, Value_Function_*, Operator_Formula). Replace each SMS block with a one-sentence generic description of the lemma that follows, or delete it. Remove the unused root.bib entries, and add proper references (Ky Fan 1949, Horn-Johnson) if the library is to stand alone.


### SMS-11. Stale, false or garbled prose and dangling text blocks

*documentation, impact medium, confidence high, ~90 lines.*  
Locations: Matrix_Algebra.thy:777-779 and 2075-2076 ('inner_matrix_transpose is the square case of inner_transpose_matrix from Symmetric_Spectral'); Matrix_Algebra.thy:2052 ('matvec_scaleR_right lives in Operator_Envelopes'); Matrix_Algebra.thy:2067-2068 ('trace_sum_matrix is trace_matrix_sum from Matrix_Algebra'); Matrix_Algebra.thy:2448-2449 ('matvec_scaleR_right' is matvec_scaleR_right from Operator_Envelopes'); Matrix_Algebra.thy:1086-1089 and Ky_Fan.thy:538 (garbled substitutions); Matrix_Algebra.thy:2419 (two commands on one line: 'by simp    finally show ?thesis'); Ky_Fan.thy:545-547; Ky_Fan.thy:1344-1354; Ky_Fan.thy:1816-1822; Ky_Fan.thy:28 ('Section 1'); Symmetric_Spectral.thy:548-565, 661; Outer_Products.thy:62-63; Poincare_Separation.thy:220-222, 987, 1008-1010, 1063-1065

Problems, by kind:
- **Names that do not exist anywhere** in the repository: inner_matrix_transpose and trace_sum_matrix (MA:777, 2067, 2075), and matvec_scaleR_right' (MA:2448).
- **Wrong locations:** inner_transpose_matrix is in Matrix_Algebra, not Symmetric_Spectral. matvec_scaleR_right is at MA:658, not in Operator_Envelopes.
- **Mechanical-substitution damage:**
  - MA:1087-1088 reads 'Convexity comes from convexity of the constraint set and the an eigenvalue upper bound half-spaces, closedness from the a projection-infimum characterisation infimum characterisation'.
  - KF:538 reads 'Like a projection-infimum characterisation of the paper's own operator, kyfan ...'.
- **Descriptions of things that are not there:** KF:545-547 describes 'the set of m-element subsets of the eigenbasis, and the largest m-fold eigenvalue sum', but no such definitions follow.
- **A false claim:** KF:1344-1354 says the negative-part companion 'is not established here', yet kyfan_minus_possum_threshold (KF:1610) establishes exactly it.
- **Prose that does not match the lemma:** KF:1816-1822 describes a different lemma than exists_min_subset.
- **Empty sections and upward references:** SS:548-565 consists of three subsection headings whose only content is 'X lives in Doubling_Of_Variables'. These point upward into a session that imports this one, and they produce empty sections in the PDF.
- **Dangling text:** OP:62-63 ('The Hessian field of the quartic C|z-x|^4, which is what test_fun_at never had to record') ends the theory with no statement following.
- **Orphaned prose:** the PS blocks describe Operator_Formula's M_p argument, and Operator_Formula:1757-1761 now has empty section stubs where these lemmas came from.

Evidence: grep -rnw inner_matrix_transpose / trace_sum_matrix over all .thy: only these text lines. grep 'lemma matvec_scaleR_right' -> Matrix_Algebra.thy:658.

Suggested action: Delete the stale 'lives in' and 'is X from Y' notes. Rewrite the garbled blocks. Correct KF:1344-1354 to cite kyfan_minus_possum_threshold. Remove the empty SS subsections and the dangling OP text. Split MA:2419 onto two lines.


### SMS-12. Poincare_Separation is a grab bag; most of it belongs in earlier theories of the session

*misplacement, impact medium, confidence high, ~500 lines.*  
Locations: Poincare_Separation.thy:449 outer_prod_scaleR_right, :800 inner_outer_prod_self, :819 norm_outer_prod, :835 outer_prod_diff_left, :841 outer_prod_diff_right; Poincare_Separation.thy:23 trace_diff_matrix, :411 transpose_sum_matrix, :890 inner_transpose_self, :905 matrix_mult_entry_inner, :911 norm_matrix_mult_le, :961 norm_mat_1, :990 conj_diff_expand, :1013 norm_conj_diff_le, :1068 entry_abs_le_norm, :1121 continuous_on_quadform, :1134 closed_symmetric_matrices; Poincare_Separation.thy:1146 closed_psd, :427 psd_weighted_outer_sum; Poincare_Separation.thy:29 kyfan_full_eq_trace, :53 is_proj_rank1, :67 is_proj_compl_rank1, :111 trace_mult_rank1, :130 quadform_le_eigval_1, :148 eigval_min_le_quadform; Poincare_Separation.thy:687 possum_lipschitz, :747 bracket_lipschitz, :1080 entrysum_le_norm, :1096 bracket_lipschitz_norm; Householder_Rotation.thy:497 continuous_on_conj_trace

Of the 44 statements in Poincare_Separation, at most 10 are about separation or Courant-Fischer. The rest should move as follows:
- Outer-product algebra and norms -> Outer_Products. outer_prod_scaleR_right belongs next to outer_prod_scaleR_left (OP:36).
- Frobenius-norm and generic matrix facts -> Matrix_Algebra.
- psd closedness and the weighted psd sums -> Symmetric_Spectral (next to psd_limit).
- Rank-one projections and extreme Rayleigh bounds -> Ky_Fan.
- Lipschitz bounds for possum/bracket -> Eigenvalue_Continuity, which then really is 'Lipschitz dependence'.

continuous_on_conj_trace (Householder_Rotation:497) has nothing to do with reflections.

Evidence: PS header (:16-18) itself lists 'the elementary continuity and Lipschitz estimates that make the eigenvalues, projections and outer products vary continuously'.

Suggested action: Redistribute as above. This also removes Poincare_Separation's need to import Eigenvalue_Continuity, so EC and the Courant-Fischer part can build in parallel after Ky_Fan.


### SMS-13. Matrix_Algebra is a provenance-ordered 2 689-line root theory; import hygiene

*structure, impact medium, confidence high, ~2689 lines.*  
Locations: Matrix_Algebra.thy:344 (subsection 'The calculus the doubling and comparison arguments consume', running to :2543); Orthonormal_Families.thy:4 'imports Outer_Products Matrix_Algebra'; Symmetric_Spectral.thy:4 'imports Orthonormal_Families Matrix_Algebra'; 17 theories outside SMS import Symmetric_Matrix_Spectra.Matrix_Algebra directly

One subsection covers lines 344-2543, mixing:
- trace/transpose calculus;
- second-order conditions;
- orthogonal and affine maps with their open/interior images;
- product-metric facts;
- the quadratic Taylor/Lipschitz toolkit;
- 'pinch' analysis;
- nat-indexed orthonormal families;
- projection lemmas;
- matrix-of-linear-map bridges.
Its section headings reflect where lemmas came from ('arrived with the doubling toolbox', MA:208), not what they are.

Matrix_Algebra is the root of every SMS, SOVA and RA theory that uses matrices, so its length serialises everything downstream. The SMS chain is linear (MA -> OP -> OF -> SS -> KF -> EC -> PS), with Householder_Rotation the only branch. Two imports are redundant (OF and SS re-import Matrix_Algebra).

Evidence: grep 'Symmetric_Matrix_Spectra.Matrix_Algebra' finds direct imports in Doubling_Of_Variables, Theorem_On_Sums, and 15 Relative_Arbitrage theories.

Suggested action: Split Matrix_Algebra into:
1. Matrix_Calculus: sums, trace, transpose, *v, **, the bounded-linear and continuity facts, shifts by \<delta>I, entrysum.
2. Quadratic_Forms: quad_taylor_step, quad_diff_bound_gen, quad_shift, has_derivative_quadratic_form, quadratic_test_*, matrix_of_symmetric, matrix_diff_vec.
3. Orthogonal_Maps: orthogonal and affine maps, their images and dist, slimmed per the library-duplicate finding.
Move the analysis lemmas to SOVA and the paper lemmas to RA as in the other findings. Drop the redundant imports. Expected result: Matrix_Calculus under about 900 lines, and SOVA can start after it.


### SMS-14. Argument-level clones: eigenbasis extension, spectral expansion, Max-over-subsets, closedness of psd

*clone, impact medium, confidence medium, ~180 lines.*  
Locations: Poincare_Separation.thy:463-562 eigenbasis_containing_eigenvector versus Symmetric_Spectral.thy:254-335 (induction step of invariant_subspace_eigenbasis_ex); Ky_Fan.thy:81-129 (Peq in is_proj_decomp) versus Symmetric_Spectral.thy:414-456 spectral_decomposition; Ky_Fan.thy:585-612 (kyfan_attained Subs/Max) versus Ky_Fan.thy:295-313 (exists_top_subset); Symmetric_Spectral.thy:575 psd_limit (with Matrix_Algebra.thy:2340 transpose_limit, :2365 tendsto_quadratic_form) versus Poincare_Separation.thy:1134 closed_symmetric_matrices, :1146 closed_psd; Symmetric_Spectral.thy:365-377 versus Ky_Fan.thy:503-524 trace_mult_eigen_weights

Five arguments are each done twice:
- **Eigenbasis extension.** eigenbasis_containing_eigenvector re-runs the induction step of the spectral theorem for a prescribed eigenvector q: hyperplane H = q^perp, invariance via sym_inner_swap, eigenbasis of H, insert q, prove onormal and span = UNIV. That is about 60 lines that the SS induction step already contains with the Rayleigh maximiser in place of q.
- **Spectral expansion.** is_proj_decomp re-proves 'agree on the basis, expand x with onormal_expand, matrix_eq' verbatim from spectral_decomposition. It could instead instantiate spectral_decomposition and use \<mu>_u \<in> {0,1}. HOL's linear_eq_on_span would shorten all three sites (including onormal_complete).
- **Max over subsets.** kyfan_attained re-builds the finite set of m-subsets and its Max, which exists_top_subset already does. With exists_top_subset + threshold_sum_maximal the maximiser comes for free.
- **Closedness of psd.** psd is shown closed twice: sequentially (psd_limit, transpose_limit, tendsto_quadratic_form) and topologically (closed_symmetric_matrices, closed_psd).
- **Trace against an eigenbasis.** trace_mult_psd_nonneg re-does the computation of trace_mult_eigen_weights.

Evidence: SS:254 'define S' where "S' = {x \<in> S. u \<bullet> x = 0}"' versus PS:471 'define H where "H = {y :: real^'n. q \<bullet> y = 0}"'. Each is followed by an invariance proof with sym_inner_swap, insert u/q, onormal via pairwise_insert, and a span argument via x - (u.x) u. KF:112-127 and SS:436-453 are the same 'also have' chains.

Suggested action: Factor out 'eigenbasis_extend: symmetric a, invariant subspace S, unit eigenvector u \<in> S ==> eigenbasis of S containing u' and use it in both SS and PS. Derive is_proj_decomp from spectral_decomposition. Make psd_limit a corollary of closed_psd + closed_sequential_limits, and move closed_psd/closed_symmetric_matrices into Symmetric_Spectral. Derive trace_mult_psd_nonneg from trace_mult_eigen_weights (it would have to move after Ky_Fan's weight lemma, or the weight lemma down into SS).


### SMS-15. Non-spectral real analysis in the matrix library

*misplacement, impact medium, confidence medium, ~450 lines.*  
Locations: Matrix_Algebra.thy:373-562 local_min_gradient_zero, local_min_hessian_psd; Matrix_Algebra.thy:1739 tilted_minimiser_close; Matrix_Algebra.thy:1792 pinch_segment_bound; Matrix_Algebra.thy:1844 pinch_implies_constant; Matrix_Algebra.thy:1914 quad_form_bounded_below; Matrix_Algebra.thy:1943 quad_minimality_pinch; Matrix_Algebra.thy:1994 singular_matrix_avoids_range; Matrix_Algebra.thy:864 dist_prod_scale_fst; Matrix_Algebra.thy:2298 ball_prod_shift_snd; Matrix_Algebra.thy:589 norm_less_of_ball; Symmetric_Spectral.thy:39 linear_coeff_zero

About 450 lines of Matrix_Algebra are viscosity-solution or real-analysis lemmas: second-order conditions at a local min, the 'tilted minimiser' rate, the 'pinch' argument that a function with O(|\<Delta>|^2) two-sided increments is constant, and product-metric facts. Their own prose says they 'neither mention the value function nor the operator' (MA:1789). Notes:
- Test_Functions:1038 says 'tilted_minimiser_close lives in Matrix_Algebra', so the move was downward to the wrong library.
- local_min_hessian_psd is the matrix counterpart of second_order_interior_max (Sup_Convolution:473).
- pinch_* are used only by Value_Function_Supersolution_Case_2 and Pair_Path_Laws (horn_B_locally_constant).
- dist_prod_scale_fst and ball_prod_shift_snd are stated at (real^'n) \<times> (real^'n^'n) but hold for any normed product.

Evidence: MA:1789-1790 'Both statements below are pure real analysis; neither mentions the value function or the operator.' Test_Functions.thy:1038 'text \<open>\<open>tilted_minimiser_close\<close> lives in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>'.

Suggested action: Move local_min_* next to second_order_interior_max in Second_Order_Viscosity_Analysis/Sup_Convolution, or into a small 'Second_Order_Conditions' theory there. Move tilted_minimiser_close, pinch_*, quad_minimality_pinch, quad_form_bounded_below and singular_matrix_avoids_range into Second_Order_Viscosity_Analysis/Test_Functions. Generalise pinch_* to real_normed_vector and tilted_minimiser_close to real_inner, and restate dist_prod_scale_fst and ball_prod_shift_snd at real_normed_vector products.


### SMS-16. Two near-duplicate rotation constructions (rotv, rotm) and a Householder reflection that ignores rank1proj

*clone, impact medium, confidence medium, ~150 lines.*  
Locations: Householder_Rotation.thy:248 rotv and lemmas :251, :272, :287, :419, :455; Householder_Rotation.thy:302 rotm and lemmas :305, :309, :318, :334, :388, :402, :476; Householder_Rotation.thy:24 hrefl; Relative_Arbitrage/Operator_Continuity.thy:41 rank1proj; Poincare_Separation.thy:53 is_proj_rank1, :67 is_proj_compl_rank1

rotv u v = hrefl (u+v) ** hrefl u for unit vectors, and rotm q w = hrefl (|w| q + |q| w) ** hrefl q. For q, w \<noteq> 0, hrefl_scale_matrix gives rotm q w = rotv (sgn q) (sgn w). Each has its own orthogonality, apply, self and continuity lemmas, proved differently, and the two serve different consumers: rotv in Operator_Envelopes, rotm in Value_Function_Supersolution_Case_1.

hrefl v = mat 1 - (2/(v.v)) outer_prod v v, which is mat 1 - 2 * rank1proj v. Yet rank1proj (outer_prod p p /R (p.p)), a generic notion, lives in the paper session. Its generic lemmas there (rank1proj_eq_outer_unit, norm_rank1proj, norm_rank1proj_diff_le, norm_perp_proj_le) duplicate the unit-vector forms is_proj_rank1 and is_proj_compl_rank1 in PS. Moving these generic lemmas down is part of the open §3.1 item.

Evidence: HR:299 states the relation itself: 'rotm q w = rotv q (\<parallel>q\<parallel>/\<parallel>w\<parallel> \<cdot>\<^sub>R w) up to the normalisation'. Operator_Continuity:41-42 'definition rank1proj ... "rank1proj p = outer_prod p p /\<^sub>R (p \<bullet> p)"'.

Suggested action: Define rotm via rotv (or the reverse) and derive one lemma family from the other. Move rank1proj and its generic lemmas (Operator_Formula:1702-1790) into Outer_Products/Ky_Fan, define hrefl v = mat 1 - 2 *R rank1proj v, and phrase is_proj_rank1/_compl_rank1 with rank1proj.


### SMS-17. matvec_norm_le (43 lines) and its helper sum_sq_le_sq_sum re-prove HOL's onorm bound

*library_duplicate, impact low, confidence high, ~75 lines.*  
Locations: Matrix_Algebra.thy:1271 matvec_norm_le; Matrix_Algebra.thy:314 sum_sq_le_sq_sum; Matrix_Algebra.thy:1211 quadform_abs_le

matvec_norm_le states 'norm (M *v w) <= (\<Sum>i j. |M$i$j|) * norm w'. It is `onorm` applied to `onorm_le_matrix_component_sum`, i.e. two lines. sum_sq_le_sq_sum (29 lines) exists only to support it, plus one use in Value_Function_Euler_Construction. quadform_abs_le then follows from Cauchy-Schwarz and matvec_norm_le.

Evidence: Cartesian_Euclidean_Space.thy:132 'lemma onorm_le_matrix_component_sum: fixes A :: "real^'n^'m" shows "onorm((*v) A) \<le> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar>)"'.

Suggested action: Prove matvec_norm_le by onorm[OF matrix_vector_mul_bounded_linear] + onorm_le_matrix_component_sum. Inline or drop sum_sq_le_sq_sum.


### SMS-18. Small wrappers around Main/HOL-Analysis lemmas

*library_duplicate, impact low, confidence high, ~70 lines.*  
Locations: Matrix_Algebra.thy:2037 invertible_matrix_vector_inj; Ky_Fan.thy:811 finite_arg_min_on; Matrix_Algebra.thy:1354 exists_enum_of_card; Matrix_Algebra.thy:2532 compact_cball_bound; Matrix_Algebra.thy:2078 unit_normalize; Matrix_Algebra.thy:373 local_min_gradient_zero; Matrix_Algebra.thy:271 norm_le_card_Basis_bound; Matrix_Algebra.thy:2334 tendsto_entry

Each is a short wrapper around a library lemma:
- invertible_matrix_vector_inj (14 lines) is `inj_matrix_vector_mult` + injD.
- finite_arg_min_on (14 lines) is `arg_min_if_finite(1)` + `arg_min_least` (Lattices_Big). It is used 9 times, including Operator_Formula.
- exists_enum_of_card is `finite_same_card_bij`.
- compact_cball_bound is compact_imp_bounded + `bounded_subset_cball`/`bounded_pos`. It is fixed at real^'n, and Statement/ uses it.
- unit_normalize is norm_sgn/norm_eq_1.
- local_min_gradient_zero is a 12-line wrapper of `has_derivative_local_min`.
- norm_le_card_Basis_bound is norm_le_l1 + sum_mono.
- tendsto_entry is tendsto_vec_nth applied twice.

Evidence: Finite_Cartesian_Product.thy 'lemma inj_matrix_vector_mult: fixes A::"'a::field^'n^'m" assumes "invertible A" shows "inj ((*v) A)"'. Lattices_Big.thy:1054 arg_min_if_finite; arg_min_least 'f(arg_min_on f S) \<le> f y'. Set_Interval.thy:1521 finite_same_card_bij. Elementary_Metric_Spaces.thy:824 bounded_subset_cball. Derivative.thy:596 has_derivative_local_min.

Suggested action: Delete invertible_matrix_vector_inj, finite_arg_min_on and exists_enum_of_card in favour of the library. Keep compact_cball_bound only if Statement/ needs its exact shape, generalised to real_normed_vector. Record the others as one-liners.


### SMS-19. exists_min_subset is exists_top_subset applied to -w

*clone, impact low, confidence high, ~50 lines.*  
Locations: Ky_Fan.thy:1824-1869 exists_min_subset; Ky_Fan.thy:289-352 exists_top_subset

exists_top_subset gives T \<subseteq> U with card T = m and f j <= f i for i in T, j in U - T. With f = -w this is exactly exists_min_subset's 'w u <= w v'. The second copy is proved by a different induction (46 lines). Its preceding prose (KF:1816-1822, about 'weights c in [0,1] with total mass >= m ... the face argument') does not describe the lemma.

Evidence: KF:1827 'm \<le> card B \<Longrightarrow> \<exists>S. S \<subseteq> B \<and> card S = m \<and> (\<forall>u\<in>S. \<forall>v\<in>B - S. w u \<le> w v)'. Its only user is Relative_Arbitrage/Pair_Path_Laws.thy:2184.

Suggested action: Delete exists_min_subset, or make it a 3-line corollary of exists_top_subset[where f = "\<lambda>u. - w u"]. Fix or delete the prose.


### SMS-20. inner_quadform_bound re-proves quadform_abs_le at norm 1; entrysum duplicates the inline \<Sum>\<Sum>|M_ij| of Matrix_Algebra

*clone, impact low, confidence high, ~45 lines.*  
Locations: Eigenvalue_Continuity.thy:32-66 inner_quadform_bound; Matrix_Algebra.thy:1211 quadform_abs_le; Eigenvalue_Continuity.thy:21 entrysum; Matrix_Algebra.thy:1271 matvec_norm_le, :1426, :1609 (inline \<Sum>i j. \<bar>M$i$j\<bar>)

quadform_abs_le gives |v.(Mv)| <= (\<Sum>\<Sum>|M_ij|) * norm v^2. At norm v = 1 this is inner_quadform_bound, which re-does the same double-sum estimate in 35 lines. The constant \<Sum>i j. |M$i$j| appears inline four times in Matrix_Algebra and as the definition entrysum in Eigenvalue_Continuity, which Matrix_Algebra cannot see.

Evidence: EC:35 'shows "\<bar>u \<bullet> (D *v u)\<bar> \<le> entrysum D"' with assumes "norm u = 1"; MA:1213 'shows "\<bar>v \<bullet> (M *v v)\<bar> \<le> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>) * (norm v)\<^sup>2"'.

Suggested action: Move entrysum (with entrysum_nonneg/_sym, and entrysum_le_norm/entry_abs_le_norm from PS) into Matrix_Algebra. Restate quadform_abs_le/matvec_norm_le/quad_diff_bound_gen with it, and derive inner_quadform_bound in one line.


### SMS-21. subspace_inter_nonzero and dim_inter_ge make the same dim_sums_Int argument

*clone, impact low, confidence high, ~30 lines.*  
Locations: Poincare_Separation.thy:288-318 subspace_inter_nonzero; Poincare_Separation.thy:613-624 dim_inter_ge

Both start from dim_sums_Int[OF S W] and the dim_subset_UNIV bound. subspace_inter_nonzero (31 lines) follows from dim_inter_ge in three lines: dim (S \<inter> W) > 0 gives a nonzero element. Both are fixed at real^'n, although DIM('a) for 'a::euclidean_space works.

Evidence: PS:294 'have key: "dim {x + y |x y. x \<in> S \<and> y \<in> W} + dim (S \<inter> W) = dim S + dim W" by (rule dim_sums_Int[OF S W])'; PS:618 is the identical have.

Suggested action: Derive subspace_inter_nonzero from dim_inter_ge, and generalise both to euclidean_space with DIM('a).


### SMS-22. trace_mult_spectral_proj is trace_mult_outer_sum with three unused hypotheses

*generalisation, impact low, confidence high, ~30 lines.*  
Locations: Ky_Fan.thy:218-240 trace_mult_spectral_proj; Ky_Fan.thy:549 spectral_proj_trace (third conclusion); Outer_Products.thy:42 trace_mult_outer_sum; Poincare_Separation.thy:111 trace_mult_rank1

trace_mult_outer_sum, 'trace (A ** (\<Sum>u\<in>B. outer_prod u u)) = (\<Sum>u\<in>B. u \<bullet> (A *v u))', is unconditional. trace_mult_spectral_proj states the same equation under 'onormal B', 'S \<subseteq> B' and an eigenvector hypothesis, none of which is needed. Its proof re-derives trace_mult_outer_sum, including the finiteness of S, which is also unused. trace_mult_rank1 (PS:111) is the singleton case, re-proved again. spectral_proj_trace's eig hypothesis exists only to call it.

Evidence: OP:42-45 has no assumptions. KF:220-222: assumes B: "onormal B" and S: "S \<subseteq> B" and eig ... shows "trace (a ** (\<Sum>u\<in>S. outer_prod u u)) = (\<Sum>u\<in>S. u \<bullet> (a *v u))". Uses: KF:564, PS:44, and Operator_Formula.

Suggested action: Delete trace_mult_spectral_proj and use trace_mult_outer_sum. Drop eig from spectral_proj_trace.


### SMS-23. Projection lemmas exist twice: raw (transpose P = P, P ** P = P) in Matrix_Algebra and via is_proj in Ky_Fan

*clone, impact low, confidence high, ~70 lines.*  
Locations: Matrix_Algebra.thy:2144 proj_inner_self; Matrix_Algebra.thy:2157 proj_inner_self'; Matrix_Algebra.thy:2198 proj_norm_le; Ky_Fan.thy:431 proj_quadform_self; Ky_Fan.thy:451 proj_quadform_le_self; Ky_Fan.thy:201 trace_proj_psd_nonneg; Symmetric_Spectral.thy:351 trace_mult_psd_nonneg

Since is_proj P \<equiv> transpose P = P \<and> P ** P = P:
- proj_inner_self' and proj_quadform_self are the same statement, 'y \<bullet> (P *v y) = (P *v y) \<bullet> (P *v y)'.
- proj_norm_le (norm (P w) <= norm w, 22 lines) and proj_quadform_le_self (u.Pu <= u.u, 29 lines) are equivalent via that identity.
- trace_proj_psd_nonneg is trace_mult_psd_nonneg once 'is_proj P ==> psd P' is available (proj_quadform_nonneg + symmetry).
The Matrix_Algebra copies serve only Value_Function_Tangential_Field. Their prose (MA:2140-2142, 'The kill condition ...') is paper-specific.

Evidence: MA:2160 'shows "y \<bullet> (P *v y) = (P *v y) \<bullet> (P *v y)"' under Psym, Pidem; KF:433 'shows "u \<bullet> (P *v u) = (P *v u) \<bullet> (P *v u)"' under is_proj P.

Suggested action: Keep the Ky_Fan versions. Add 'is_proj P \<Longrightarrow> psd P' and 'norm (P *v w) \<le> norm w' next to them, and redirect Value_Function_Tangential_Field (one place, unfolding is_proj_def). Make trace_proj_psd_nonneg a one-liner.


### SMS-24. Dead statements: the semiconvex-Hessian chain, psd_shifted_diff, hrefl_orthogonal, bracket_eq_sum

*dead_code, impact low, confidence high, ~70 lines.*  
Locations: Symmetric_Spectral.thy:501 hessian_lower_bound_of_psd; Symmetric_Spectral.thy:514 semiconvex_hessian_two_sided; Symmetric_Spectral.thy:530 semiconvex_hessian_abs_bound; Symmetric_Spectral.thy:648 psd_shifted_diff; Householder_Rotation.thy:125 hrefl_orthogonal; Ky_Fan.thy:1255 bracket_eq_sum

The three semiconvex lemmas use each other only. Outside SMS they are named once, in prose (Doubling_Of_Variables:5177). They are stated over abstract maps at euclidean_space and are not about matrices. They duplicate hessian_abs_bound_of_two_sided (Doubling_Of_Variables:3010), and semiconvex_hessian_two_sided's second conclusion is its own hypothesis `neg`. Plan phase 3 moved them in, so the move transported dead code.

The other three:
- psd_shifted_diff is a 'by simp' fact named only in prose (Doubling_Of_Variables:5133).
- hrefl_orthogonal is never used, although it is exactly what rotv_orthogonal and rotm_orthogonal need.
- bracket_eq_sum is named only in prose (Operator_Formula:1023). It is plausibly API (it states what bracket means), so keep it.

Evidence: grep -rnw over all .thy: hrefl_orthogonal has 1 occurrence (its definition); semiconvex_hessian_abs_bound has 2 (its definition plus Doubling_Of_Variables.thy:5177 inside a text block); psd_shifted_diff has 2 (its definition plus Doubling_Of_Variables.thy:5133 text).

Suggested action: Delete the semiconvex chain and psd_shifted_diff, and fix the two prose references. Use hrefl_orthogonal in rotv/rotm_orthogonal. Keep bracket_eq_sum as API.


### SMS-25. Paper-specific lemmas inside the paper-free library

*misplacement, impact low, confidence high, ~60 lines.*  
Locations: Matrix_Algebra.thy:351-371 neg_half_trace_ball_op (with prose about the ball value function 'v x = max (r^2-|x|^2) 0/(n-k)'); Matrix_Algebra.thy:564 quadratic_gradient; Matrix_Algebra.thy:2172 tanpU_sq_norm_le (prose MA:2167-2170: 'the Euler-limit argument in the application'); Matrix_Algebra.thy:1583 rot_cone_ok, :1578 colmat_matvec; Ky_Fan.thy:1252 bracket (the paper's L-weighted eigenvalue expression)

neg_half_trace_ball_op ('ball_op') and quadratic_gradient compute the operator and gradient of the paper's ball candidate (r^2 - y.y)/c. They are used only in Relative_Arbitrage/Curvature_Operator and Viscosity_Ball. tanpU_sq_norm_le is named after the paper's tangential field tanpU and is used only by Value_Function_Tangential_Field. rot_cone_ok and colmat_matvec are generic but trivial, and are used only by Value_Function_Supersolution_Case_1. The definition bracket m L a = L * possum n a + (kyfan m a - possum m a) is the paper's (n-k)-truncated operator. It is parametric, so arguably library material, but it is the only paper-shaped definition in the session.

Evidence: grep: neg_half_trace_ball_op has 4 uses, all in Relative_Arbitrage/Curvature_Operator.thy; quadratic_gradient appears in Curvature_Operator and Viscosity_Ball; tanpU_sq_norm_le has 2 uses, in Value_Function_Tangential_Field.thy.

Suggested action: Move neg_half_trace_ball_op and quadratic_gradient to Relative_Arbitrage (Viscosity_Ball or Curvature_Operator), and tanpU_sq_norm_le to Value_Function_Tangential_Field (or rename it and state it at real_inner). Leave bracket, but describe it generically in the prose.


### SMS-26. Unused or implied hypotheses

*generalisation, impact low, confidence high, ~40 lines.*  
Locations: Matrix_Algebra.thy:974 affine_inv_shape (orth, c0 unused); Householder_Rotation.thy:287 rotv_self (u0 unused); Poincare_Separation.thy:411 transpose_sum_matrix, :418 transpose_weighted_outer_sum (finite unneeded); Poincare_Separation.thy:229 quadform_weighted_outer_sum_eq (finite B unused); Poincare_Separation.thy:373 quadform_weighted_outer_sum_nonneg, :391 quadform_weighted_outer_mono, :427 psd_weighted_outer_sum (onormal B unneeded); Matrix_Algebra.thy:2221 orthonormal_family_containing (0 < m unneeded); Householder_Rotation.thy:334 rotm_apply (q0, w0 implied by pos), :402 rotm_refl_vec_nonzero (q0 implied by pos); Ky_Fan.thy:218 trace_mult_spectral_proj (see separate finding)

Hypothesis by hypothesis:
- affine_inv_shape is proved by '(rule ext) (simp add: matvec_diff_right scaleR_right_diff_distrib)', which uses neither orthogonality nor c > 0.
- rotv_self only needs 2 \<noteq> 0 for hrefl_scale_matrix; hrefl_sq holds for every v, including 0.
- The sum-transpose identities hold without finiteness (MA:27 proves it unconditionally).
- quadform_weighted_outer_sum_eq's proof never mentions B.
- Nonnegativity and monotonicity of x.((\<Sum> g v outer_prod v v) x) need only g >= 0. onormal B is used only to get finiteness, which is itself unnecessary.
- For m = 0, b = (\<lambda>_. x0) witnesses orthonormal_family_containing.
- 0 < |q||w| + q.w forces both q \<noteq> 0 and w \<noteq> 0 (rotm_refl_vec_nonzero already derives w0 from pos).

Evidence: MA:974-979 'assumes orth: "orthogonal_matrix R" and c0: "0 < c" ... by (rule ext) (simp add: matvec_diff_right scaleR_right_diff_distrib)'. HR:289-294 'assumes u0: "u \<noteq> 0" ... by (rule hrefl_scale_matrix) simp ... by (simp add: hrefl_sq)'. PS:233-241 has no use of B. HR:407-411 derives w0 from pos.

Suggested action: Drop the hypotheses and adjust call sites with the mechanical 'OF' edits. Weaken psd_weighted_outer_sum and its two siblings to 'g \<ge> 0' over any finite index set.


### SMS-27. Long proofs of facts that are one-liners from neighbouring lemmas

*simplification, impact low, confidence high, ~200 lines.*  
Locations: Matrix_Algebra.thy:2403-2423 matrix_shift_apply (20 lines; MA:217-219 proves the same equation by one simp); Matrix_Algebra.thy:93-111 matrix_vector_mult_diff, :691-709 matrix_vector_mult_add; Orthonormal_Families.thy:254-270 onormal_span_card (re-proves independence instead of onormal_independent/onormal_card_dim_span); Matrix_Algebra.thy:1098 continuous_on_trace_mult_right versus :1161 bounded_linear_trace_mult_right; Poincare_Separation.thy:1121 continuous_on_quadform versus Matrix_Algebra.thy:1175 bounded_linear_quadform; Matrix_Algebra.thy:1191, 1196, 1206, 1320 trace_mult_diff/_scaleR/_add/_zero_right (linear_diff/_cmul/_add/_0 of bounded_linear_trace_mult_left); Ky_Fan.thy:746-747 (kyfan_0 re-proves trace_mult_zero_right); Symmetric_Spectral.thy:390-399 (psd_convex_comb re-proves quadform_convex_comb MA:1091); Matrix_Algebra.thy:1058 trace_nonneg_psd versus Relative_Arbitrage/Pair_Path_Space.thy:448 psd_diag_nonneg; Ky_Fan.thy:1394-1454 threshold_chain_aux, :1478-1513 kyfan_within_threshold (exE/'using TP by simp' boilerplate); Ky_Fan.thy:1035-1047 versus :981-988 (eigval_antimono repeats eigval_eq_min_of_threshold's T - {w} setup); Poincare_Separation.thy:709-741 possum_lipschitz (two symmetric halves)

These proofs are long only because they do not cite the lemma next to them:
- matrix_shift_apply's 20-line entrywise proof is 'by (simp add: matrix_vector_mult_add_rdistrib scaleR_matrix_vector_assoc[symmetric])', as MA:218 shows.
- onormal_span_card is 'onormal_card_dim_span + dim_span + dim_UNIV'.
- The continuity lemmas follow from the bounded-linear lemmas via linear_continuous_on.
- psd_diag_nonneg (paper session) is the lemma trace_nonneg_psd proves inline. The plan wanted it in SMS.
- threshold_chain_aux can obtain directly instead of going through exE and three 'using TP by simp' steps.
- possum_lipschitz's two halves can be one auxiliary 'possum m A \<le> possum m B + C' instantiated twice.

Evidence: MA:217-219 'have "(A + \<delta> *\<^sub>R mat 1) *v k = A *v k + \<delta> *\<^sub>R k" by (simp add: matrix_vector_mult_add_rdistrib scaleR_matrix_vector_assoc[symmetric])' versus MA:2405 'shows "(M + c *\<^sub>R mat 1) *v h = M *v h + c *\<^sub>R h"' (20 lines).

Suggested action: Shorten as indicated. The plan's 'no proof is to be improved' rule may defer this, but the trivial cases (matrix_shift_apply, onormal_span_card, the continuity-from-linearity lemmas) are deletions or one-liners.


### SMS-28. AFP has Courant-Fischer and Cauchy interlacing, but for complex Hermitian JNF matrices (not reusable cheaply)

*library_duplicate, impact low, confidence high, ~0 lines.*  
Locations: Poincare_Separation.thy (whole); Ky_Fan.thy (eigval ordering); /opt/afp/thys/Two_Hermitian_Results/Cauchy_Eigenvalue_Interlacing.thy:608 courant_fischer, :752 cauchy_eigval_interlacing; /opt/afp/thys/Perron_Frobenius/HMA_Connect.thy; /opt/afp/thys/Matrices_for_ODEs/MTX_Preliminaries.thy:195 matrix_add_rdistrib, :198 vec_mult_inner

No AFP entry has Ky Fan, Householder, or a spectral theorem for real^'n^'n. Two_Hermitian_Results proves Courant-Fischer and Cauchy interlacing (the principal-submatrix form of Poincare separation) for `complex mat` (Jordan_Normal_Form). Transferring them to real^'n^'n would need HMA_Connect, plus a real-from-complex argument and a heavy dependency stack (Jordan_Normal_Form, Commuting_Hermitian, Complex_Bounded_Operators, ...). MTX_Preliminaries contains matrix_add_rdistrib and vec_mult_inner under the same names as this session's lemmas.

Evidence: Two_Hermitian_Results/ROOT: 'session Two_Hermitian_Results = Jordan_Normal_Form + sessions Commuting_Hermitian Fishers_Inequality BenOr_Kozen_Reif QHLProver Complex_Bounded_Operators Hermite_Lindemann'. grep -rli 'courant\|ky fan' /opt/afp/thys finds only Two_Hermitian_Results.

Suggested action: Do not import. Cite Two_Hermitian_Results in the documentation as related work. Consider contributing transpose_add, matrix_add_rdistrib, trace of sums and Frobenius submultiplicativity (norm_matrix_mult_le; absent from HOL, as Operator_Formula:1761 notes) to HOL-Analysis.


### SMS-29. eigval/kyfan conventions match the paper; out-of-range values are junk but never used

*faithfulness, impact low, confidence high, ~0 lines.*  
Locations: Ky_Fan.thy:542 kyfan, :774 eigval, :1252 bracket

The paper's computation (commented block at EM_final_paper.tex:471-477) orders eigenvalues decreasingly, lambda_1 >= ... >= lambda_n. eigval i = kyfan i - kyfan (i-1) is the i-th largest (eigval_antimono, kyfan_eq_sum_eigval). bracket m L a = L*\<Sum>_{i<=n} lambda_i^+ + \<Sum>_{i<=m} min(lambda_i,0) matches 'L\<Sum> lambda_i 1{lambda_i>0} + \<Sum>_{i<=n-k} lambda_i 1{lambda_i<=0}' with m = n - k. For i > CARD('n), kyfan i a is the real Sup of the empty set, an unspecified value. Every lemma guards with i <= CARD('n), so this is harmless.

Evidence: KF:543 'kyfan m a = Sup {trace (a ** P) | P. is_proj P \<and> trace P = real m}'; KF:1253 'bracket m L a = L * possum CARD('n) a + (kyfan m a - possum m a)'; bracket_eq_sum (KF:1255).

Suggested action: None needed. Optionally note in the prose that kyfan m is only meaningful for m <= CARD('n).


### SMS-30. Types fixed to real^'n where euclidean_space or real_inner would do

*generalisation, impact low, confidence medium, ~120 lines.*  
Locations: Orthonormal_Families.thy:19 onormal and the 15 lemmas not mentioning trace/outer_prod; Poincare_Separation.thy:288 subspace_inter_nonzero, :613 dim_inter_ge; Poincare_Separation.thy:847 norm_unit_diff_le; Householder_Rotation.thy:437 halfspace_not_antipodal; Matrix_Algebra.thy:1583 rot_cone_ok, :2078 unit_normalize, :2172 tanpU_sq_norm_le, :589 norm_less_of_ball, :2532 compact_cball_bound, :736 inner_scaleR_diff_eq, :1081 inner_diff_self_expand; Matrix_Algebra.thy:2091-2138 orthonormal_inj, orthonormal_dim_span; Outer_Products.thy:19 outer_prod (square only); Matrix_Algebra.thy:78-111 matrix_mul_diff_right/left etc. (square only)

Several groups are more specific than their proofs need:
- onormal and its extension, Bessel, expansion, card/dim lemmas are stated for (real^'n) set, but every proof uses only euclidean_space facts (orthogonal_extension, orthonormal_basis_subspace are at euclidean_space in HOL).
- The dimension-count lemmas generalise with DIM('a).
- norm_unit_diff_le and the other vector inequalities hold in any real_normed_vector or real_inner space.
- outer_prod could be rectangular ('a::comm_ring_1^'n => 'a^'m => 'a^'m^'n).
- Several *v/** distributivity lemmas are needlessly square.

Evidence: OF:19 'definition onormal :: "(real^'n) set \<Rightarrow> bool"'. The proofs cite only pairwise_orthogonal_independent, orthogonal_extension, span_* and dim_eq_card_independent (all at euclidean_space). PS:851 norm_unit_diff_le uses only norm_triangle_ineq/norm_triangle_ineq3.

Suggested action: Generalise onormal (and the trace-free part of Orthonormal_Families) to 'a::euclidean_space, the dimension counts to DIM('a), and the elementary inequalities to real_inner or real_normed_vector. Leave outer_prod square unless a consumer needs rectangles.


### SMS-31. Three representations of orthonormal families

*clone, impact low, confidence medium, ~110 lines.*  
Locations: Matrix_Algebra.thy:2091 orthonormal_inj, :2108 orthonormal_dim_span, :2221 orthonormal_family_containing (nat-indexed, 'b i \<bullet> b j = (if i = j then 1 else 0)'); Orthonormal_Families.thy:19 onormal (finite set, pairwise orthogonal, unit); HOL Linear_Algebra.thy:1630 vector_in_orthonormal_basis (pairwise orthogonal + norm 1 + independent)

The nat-indexed variant and its 71-line Gram-Schmidt-style extension (orthonormal_family_containing) serve only Value_Function_Tangential_Field and Value_Function_Uniqueness. They duplicate onormal_extension, and HOL's vector_in_orthonormal_basis extends a unit vector to an orthonormal basis directly.

Evidence: MA:2224 '\<exists>b :: nat \<Rightarrow> real^'n. b 0 = x0 \<and> (\<forall>i < m. \<forall>j < m. b i \<bullet> b j = (if i = j then 1 else 0))'. Linear_Algebra.thy:1630 'lemma vector_in_orthonormal_basis: ... assumes "norm a = 1" obtains S where "a \<in> S" "pairwise orthogonal S" ...'.

Suggested action: Derive orthonormal_family_containing from vector_in_orthonormal_basis (or onormal_extension of {x0}) plus an enumeration, and state orthonormal_inj/_dim_span as corollaries of onormal_independent/onormal_card_dim_span. Better still, move the consumer to onormal.


## SemiC+Wiener

I read all 12 theories line by line (6107 lines) and checked every library claim by grepping the sources of HOL, HOL-Analysis, HOL-Probability and the AFP (Lower_Semicontinuous, Standard_Borel_Spaces, Kolmogorov_Chentsov, Martingales). I did not use PIDE. No PIDE session was running. The only prebuilt heap is HOL. The parent's `isabelle build` was still building HOL-Analysis on 4 cores, and only about 1 GB of the 15 GB of RAM was free, so starting a second prover risked breaking that build. Every finding below is a reading of the sources, not a proof checked in PIDE; a single PIDE pass could confirm the suggested one-line replacements.

Semicontinuous_Analysis (2314 lines) is the epsilon-delta calculus of semicontinuity for real-valued functions on a metric space. It covers attainment on compacta (lsc_attains_inf_gen, usc_attains_sup_gen), bounded extension off a closed set, and the envelopes lsc_env/usc_env. Those envelopes are proved equal to the AFP's lsc_hull (lsc_env_ereal), so their basic properties are inherited. It also has the relative envelope lsc_envK (Definition 3.1 of the paper) and the bridge Kext (usc_env composed with closest_point, with lsc_env (Kext K u) = lsc_envK K u on K). Berge's theorem comes in two forms (type class and compactin), together with the metrizable-topology glue: box_of_sequential, compactin_of_seq_compact, closure_of_sequential_limit and seq_compact_closure_of. Finally there is a Bertsekas-Shreve measurable selection of a usc payoff on a compact metric space, built by greedy nested bisection (usc_measurable_selection), plus countably_valued_approx.

Wiener_Measure (3793 lines) builds gauss_measure with variance 0 allowed, its moments and the convolution law. The finite-dimensional distributions bm_fdd are the pushforward of the Gaussian increment product inc_prod under csum, with projectivity via the nested-integral kernel wr. wiener_pre is the polish_projective limit, with Gaussian increments, start at 0, the 4th moment and independent increments (bm_increments_indep). The Kolmogorov-Chentsov continuous modification gives Brownian_motion_exists. The n-dimensional product bm_paths/bmX has increments independent of the natural filtration, and it is shown that bmX, |bmX|^2 - n t and the coordinate squares are martingales. Continuous_Brownian_Motion moves these properties to cbmX built from Bcont.

Main problems:
(a) The same 100-line arguments are proved two or three times: the increment independence (also a third copy in Exit_Class_Witness), the two Berge versions, the two martingale-square proofs and their continuous transfers, and usc_env_eq_self/usc_env_eq_at.
(b) Several helpers re-prove library facts: `dense` for ennreal, compact_space_imp_separable, closure_of_sequentially, indep_set_sigma_sets, prod_emb_PiE, measurable_Least, finite_filtered_measure_natural_filtration and cond_exp_indep.
(c) Semicontinuous_Analysis is based on HOL-Probability only because of Semicontinuous_Selection. As a result Second_Order_Viscosity_Analysis cannot import it and keeps its own copies of the attainment and usc lemmas.
(d) Both "paper-free" sessions still contain paper prose and stale references (Volatile_Market, Ito_Market, ito_const_horizon_market, Brownian_Market, Equicontinuity.*, Proposition 2.4 / Lemma 2.3 / Definition 3.1 / Eq. (1.10)).
(e) About 540 lines of pure Brownian-motion material still sit in Relative_Arbitrage/Exit_Class_Witness.
(f) Four public statements are dead: usc_sup_over_compact, usc_extension_bounded, bm_increments_indep and gauss_measure_conv. The fragment theory Sorted_Lists exists only to serve bm_increments_indep and one prod_indicator use.

PLAN_RESTRUCTURING_2 §2.11 calls Semicontinuous_Analysis "done"; the duplicates listed here say otherwise. Its §3.4 promise that gauss_measure_mean/snd_moment/shifted_square would move into Gaussian_Increments was not carried out.


### SemiC+Wiener-1. The independence argument 'past-measurable g is independent of a function of the increment' is proved three times

*clone, impact high, confidence high, ~200 lines.*  
Locations: Wiener_Measure/Vector_Brownian_Martingales.thy:80-182 bm_indicator_increment_indep_var; Wiener_Measure/Vector_Brownian_Martingales.thy:349-445 bm_meas_increment_indep_var; Relative_Arbitrage/Exit_Class_Witness.thy:111-195 bm_meas_increment_fun_indep_var

All three proofs have the same structure: interpret stochastic_process, take base = bm_filtration_increment_indep, prove inclusions L and R of sigma_sets into sets F and sets V, then finish with BMP.indep_sets_mono_sets / indep_set_def. bm_indicator_increment_indep_var is the copy with g := indicator A, character for character, including the nth_meas and Dcomp sub-proofs. bm_meas_increment_indep_var is the copy with h := (lambda v. v $ i). The general form (any Borel h of the vector increment) sits in the paper session, and its own comment says it 'generalises verbatim'.

Evidence: VBM:85 shows "BMP.indep_var borel (indicator A ...) borel (\<lambda>\<omega>. \<omega> i t - \<omega> i s)" and VBM:354 shows "BMP.indep_var borel (g ...) borel (\<lambda>\<omega>. \<omega> i t - \<omega> i s)" under g_meas: g \<in> borel_measurable (natural_filtration ...). ECW:107 says "Brownian_Market.bm_meas_increment_indep_var generalises verbatim to any Borel function of the vector increment". borel_measurable_indicator[OF A] supplies g_meas for g = indicator A.

Suggested action: Keep one lemma in Vector_Brownian_Martingales, stated for g past-measurable and h Borel on real^'n (ECW's statement). Derive the coordinate case with h = (lambda v. v$i), using bmX_def to rewrite the increment. Delete bm_indicator_increment_indep_var (use bm_meas_increment_indep_var[OF s st borel_measurable_indicator[OF A]] at VBM:233) and move the general lemma out of Exit_Class_Witness.


### SemiC+Wiener-2. Martingale-square proofs: norm and coordinate versions are parallel 110-line proofs, and so are their continuous transfers

*clone, impact high, confidence high, ~300 lines.*  
Locations: Wiener_Measure/Vector_Brownian_Martingales.thy:806-922 martingale_bm_square; Wiener_Measure/Vector_Brownian_Martingales.thy:936-1045 martingale_bm_coord_square; Wiener_Measure/Vector_Brownian_Martingales.thy:745-802 bm_indicator_sq_sum, bm_indicator_sq_integrable, bm_set_integral_sq_eq; Wiener_Measure/Continuous_Brownian_Motion.thy:149-201 martingale_cbmX_square; Wiener_Measure/Continuous_Brownian_Motion.thy:221-276 martingale_cbm_coord_square; Relative_Arbitrage/Exit_Class_Witness.thy:384,446 martingale_bm_cross, martingale_cbm_cross

martingale_bm_square and martingale_bm_coord_square share the whole skeleton: SP/AP interpretations, fm/sfs/sff/SFF, Zmeas, Zint, ap, martingale_of_set_integral_eq, ind_int/ind_val/ins/cst, and a split for w, u and v. The norm version is the sum over i of the coordinate versions, since |bmX|^2 - n t = sum_i ((bmX_i)^2 - t) and trace_I gives the constant. Three helper lemmas (VBM:745-802) exist only for the norm version. In Continuous_Brownian_Motion, the _square and _coord_square transfers are 53- and 56-line proofs that differ only in the function f u y (y . y - c u versus (y$i)^2 - c u). The cross version in Exit_Class_Witness repeats the same pattern a third time.

Evidence: VBM:822-834 and VBM:953-965 hold identical fm/sfs/sff blocks. CBM:172-200 and CBM:247-275 hold identical adapted_of_natural_filtration plus martingale_of_modification_gen blocks. Martingale_Algebra provides martingale_add:20 and martingale_matI:640.

Suggested action: Prove the coordinate (and cross) martingales once and derive martingale_bm_square by summing with martingale_add (add a martingale_sum by finite induction) and trace_I. Better still, prove the matrix martingale bmX bmX^T - t I directly (martingale_matI) and get the norm form through martingale_bounded_linear_image with trace. Add one transfer lemma 'Borel f, martingale of (lambda t w. f t (bmX x0 t w)) for the bmX filtration implies martingale of (lambda t w. f t (cbmX x0 t w)) for the cbmX filtration', so that martingale_cbmX, _square, _coord_square and _cross become one-liners.


### SemiC+Wiener-3. About 540 lines of pure Brownian-motion theory sit in the paper session (Exit_Class_Witness), and bmpair is sbmpair at S = mat 1

*misplacement, impact high, confidence high, ~870 lines.*  
Locations: Relative_Arbitrage/Exit_Class_Witness.thy:23-543 bm_coordinates_indep, bm_increment_coord_indep, bm_increment_cross, bm_meas_increment_fun_indep_var, bm_cross_set_integral_zero, bm_cross_increment_set_integral_zero, bmX_coord_measurable_F, bmX_cross_integrable, martingale_bm_cross, martingale_cbm_cross, martingale_cbm_outerp; Relative_Arbitrage/Exit_Class_Witness.thy:544-880 bmpair_*; Relative_Arbitrage/Value_Function_Euler_Construction.thy:46-420 sbmpair_*; Relative_Arbitrage/Value_Function_Euler_Construction.thy:933-975 bm_coordinate_pow4

None of the bm_*/martingale_*cross* statements mention a paper constant, except martingale_cbm_outerp, which uses outerp (= outer_prod x x). They are the cross-covariation half of the vector Brownian motion and belong next to martingale_bm_coord_square in Wiener_Measure. bm_coordinates_indep re-proves Kolmogorov_Chentsov_Extras.indep_vars_PiM_coordinate; its comment says that lemma is 'not in scope', but Product_Brownian_Motion, an ancestor, imports Kolmogorov_Chentsov_Extras. bmX_coord_measurable_F (ECW:331) duplicates VBM.bm_coordinate_measurable_F (VBM:492). martingale_cbm_outerp recomputes bm_compensator_coord inline (ECW:506-514). Separately, bmpair T = sbmpair (mat 1) T, and the lemma families match one to one (_apply, continuous_on_*_path, _measurable, prob_space_*_law, _law_start, _law_diffquot, _adapted, _law_X_martingale, _law_comp_martingale, _law_in_paper_pair_class). Because Value_Function_Euler_Construction has Exit_Class_Witness as an ancestor, the general version is proved after the special one.

Evidence: ECW:546: bmpair T \<omega> = restrict (\<lambda>t. (cbmX 0 t \<omega>, t *\<^sub>R mat 1)) {0..T}. VFEC:46-49: sbmpair S T \<omega> = restrict (\<lambda>t. (S *v cbmX 0 t \<omega>, t *\<^sub>R (S ** transpose S))) {0..T}. ECW:27-31 comment: \<open>Kolmogorov_Chentsov_Extras.indep_vars_PiM_coordinate\<close> is not in scope here.

Suggested action: Move ECW:23-543 into Wiener_Measure: the cross independence and moments into Vector_Brownian_Martingales, the continuous cross and outer-product martingales into Continuous_Brownian_Motion, stated with outer_prod. Replace bm_coordinates_indep with BMC.indep_vars_PiM_coordinate. Move sbmpair and its lemmas down into Exit_Class_Witness (or a Brownian pair-law theory) and obtain bmpair as the S = mat 1 instance, or drop bmpair. Move bm_coordinate_pow4 into Product_Brownian_Motion.


### SemiC+Wiener-4. Semicontinuous_Analysis is based on HOL-Probability only because of Semicontinuous_Selection, which forces copies in Second_Order_Viscosity_Analysis

*structure, impact high, confidence high, ~150 lines.*  
Locations: Semicontinuous_Analysis/ROOT; Semicontinuous_Analysis/Semicontinuous_Selection.thy:4; Second_Order_Viscosity_Analysis/Crandall_Ishii_Sums.thy:104-151 usc_open_lt, usc_attains_sup_compact; Second_Order_Viscosity_Analysis/Crandall_Ishii_Sums.thy:1763 usc_form_of_continuous; Second_Order_Viscosity_Analysis/Doubling_Of_Variables.thy:2666 usc_extend_const_below

Semicontinuity, Semicontinuous_Envelopes and Berge import only HOL-Analysis.Analysis and Lower_Semicontinuous, and Lower_Semicontinuous is itself a HOL-Analysis session. Only Semicontinuous_Selection needs HOL-Probability and Standard_Borel_Spaces. Second_Order_Viscosity_Analysis is based on HOL-Analysis and does not depend on Semicontinuous_Analysis, so it re-proves usc attainment (usc_attains_sup_compact, a clone of usc_attains_sup_gen), usc_form_of_continuous (a clone of usc_eps_of_continuous) and the usc extension (usc_extend_const_below, a clone of usc_extension_bounded). It says so explicitly. Doubling_Of_Variables:4800 even names usc_attains_sup_gen, which that session cannot see.

Evidence: CIS:106-108: "The session sits on plain HOL-Analysis, so the two attainment facts below are proved here rather than imported from the Semicontinuous_Analysis session". /opt/afp/thys/Lower_Semicontinuous/ROOT: session Lower_Semicontinuous = "HOL-Analysis". Semicontinuity.thy:4 imports "HOL-Analysis.Analysis".

Suggested action: Rebase Semicontinuous_Analysis on HOL-Analysis with sessions Lower_Semicontinuous, keeping Semicontinuity, Semicontinuous_Envelopes and Berge. Move Semicontinuous_Selection, which only serves Exit_Class_Optimizer and Path_Law_Pasting, into Continuous_Path_Spaces (already based on Continuous_Time_Martingales and Standard_Borel_Spaces) or a small Measurable_Selection session. Then add the edge Semicontinuous_Analysis -> Second_Order_Viscosity_Analysis and delete the CIS and Doubling_Of_Variables copies.


### SemiC+Wiener-5. Two Berge theorems with line-parallel 90-line proofs; the type-class one is unused

*clone, impact high, confidence high, ~110 lines.*  
Locations: Semicontinuous_Analysis/Berge.thy:34-123 usc_sup_over_compact; Semicontinuous_Analysis/Berge.thy:454-544 usc_sup_over_compactin

The two proofs are step for step the same (c', small, ex, ex', exf, WW, UU/VV, cover, D, U, key, final). usc_sup_over_compact is the Y = euclidean instance of usc_sup_over_compactin: compact C gives compactin euclidean C, open V gives openin euclidean V, and the box over V implies the box over V \<inter> C. usc_sup_over_compact is used nowhere; grep finds it only in prose at Berge:128,442 and Exit_Time_Semicontinuity:21. Both proofs could also be cut to about 20 lines with HOL's tube_lemma_right (Abstract_Topological_Spaces.thy:2368): the union W of boxes U_P x V_P is open in prod_topology and {x} x C lies in W.

Evidence: Only consumer: Pair_Path_Space.thy:865 'proof (rule usc_sup_over_compactin)'. HOL: tube_lemma_right: openin (prod_topology X Y) W \<Longrightarrow> compactin Y C \<Longrightarrow> x \<in> topspace X \<Longrightarrow> {x} \<times> C \<subseteq> W \<Longrightarrow> \<exists>U V. openin X U \<and> openin Y V \<and> x \<in> U \<and> C \<subseteq> V \<and> U \<times> V \<subseteq> W.

Suggested action: Delete usc_sup_over_compact, or keep it as a 5-line corollary of the compactin version. Re-prove usc_sup_over_compactin through tube_lemma_right and drop the bchoice-over-pairs workaround (Berge:56-83 and 476-498).


### SemiC+Wiener-6. usc_env_eq_self is a verbatim copy of usc_env_eq_at with a stronger hypothesis

*clone, impact medium, confidence high, ~30 lines.*  
Locations: Semicontinuous_Analysis/Semicontinuous_Envelopes.thy:235-261 usc_env_eq_self; Semicontinuous_Analysis/Semicontinuous_Envelopes.thy:459-485 usc_env_eq_at

The proof bodies are identical (cc, cc2, c1/c2, usc[OF c1], cInf_greatest, cSup_upper, ...). usc_env_eq_self assumes usc at every z (\<And>c z. u z < c \<Longrightarrow> ...), while usc_env_eq_at needs it only at x. lsc_env_eq_self (294-324) is the lower-envelope analogue with a third proof; it could be derived from a pointwise-lsc lsc_env_eq_at, because continuity at x gives lsc at x.

Evidence: Only use of usc_env_eq_self: Comparison_Two_Domain.thy (one occurrence). usc_env_eq_at is used by Kext_eq_on_K:546.

Suggested action: Replace the body of usc_env_eq_self with 'by (rule usc_env_eq_at[OF B usc])', or delete it. Derive lsc_env_eq_self from a pointwise statement too.


### SemiC+Wiener-7. compact_space_dense_seq re-proves Standard_Borel_Spaces' compact_space_imp_separable

*library_duplicate, impact medium, confidence high, ~45 lines.*  
Locations: Semicontinuous_Analysis/Semicontinuous_Selection.thy:40-88 Metric_space.compact_space_dense_seq

Both proofs use the same argument: finite (1/2)^n-nets (1/Suc n in the AFP), their countable union, and enumeration. The session already depends on Standard_Borel_Spaces, but Semicontinuous_Selection imports only Lemmas_StandardBorel.

Evidence: /opt/afp/thys/Standard_Borel_Spaces/Set_Based_Metric_Space.thy:1201 (in context Metric_space) lemma compact_space_imp_separable: compact_space mtopology \<Longrightarrow> separable_space mtopology. Lemmas_StandardBorel:1057 separable_space_def2. Set_Based_Metric_Space:287 mdense_def2: mdense U \<longleftrightarrow> U \<subseteq> M \<and> (\<forall>x\<in>M. \<forall>\<epsilon>>0. \<exists>y\<in>U. d x y < \<epsilon>).

Suggested action: Import Standard_Borel_Spaces.Set_Based_Metric_Space and prove compact_space_dense_seq in about 6 lines (compact_space_imp_separable, separable_space_def2, mdense_def2, from_nat_into). Or state the selection lemmas directly over a countable dense set.


### SemiC+Wiener-8. Sequential-limit glue in Berge and Selection repeats HOL's metric-space lemmas, and one argument is written four times

*library_duplicate, impact medium, confidence high, ~120 lines.*  
Locations: Semicontinuous_Analysis/Berge.thy:312-354 closure_of_sequential_limit; Semicontinuous_Analysis/Berge.thy:187-207 and 208-228 (limy/limQ in box_of_sequential); Semicontinuous_Analysis/Semicontinuous_Selection.thy:729-744 limitin_of_dist_half; Semicontinuous_Analysis/Berge.thy:356-437 seq_compact_closure_of; Semicontinuous_Analysis/Berge.thy:158-167, 288-292, 318-321, 365-369 (metrizable_space_def unpacking)

closure_of_sequential_limit is HOL's Metric_space.closure_of_sequentially transported through metrizable_space_def. The argument 'd (x n) l < r n with r -> 0 implies limitin mtopology x l' is written out four times: twice with 1/Suc n in box_of_sequential, once in closure_of_sequential_limit, and once with (1/2)^m in limitin_of_dist_half. The same 3-5 line unpacking of a metrizable_space into Metric_space MYs dY occurs four times. seq_compact_closure_of's approximate-then-triangle argument is the one inlined in HOL's compact_closure_of_eq_Bolzano_Weierstrass. compactin_of_seq_compact is one direction of Metric_space.compactin_sequentially.

Evidence: HOL-Analysis/Abstract_Metric_Spaces.thy:3701 closure_of_sequentially: mtopology closure_of S = {x \<in> M. \<exists>\<sigma>. range \<sigma> \<subseteq> S \<inter> M \<and> limitin mtopology \<sigma> x sequentially}. Abstract_Metric_Spaces.thy:1041 limitin_metric_dist_null. Abstract_Metric_Spaces.thy:2274 compactin_sequentially. Abstract_Metric_Spaces.thy:2462-2512 (closure argument). Standard_Borel_Spaces Set_Based_Metric_Space:298 mdense_def3 (the 1/(n+1) ball argument again).

Suggested action: Add one lemma Metric_space.limitin_of_dist_bound (d (x n) l \<le> r n, r \<longlonglongrightarrow> 0), proved via limitin_metric_dist_null and tendsto_sandwich, and one lemma 'metrizable_space X obtains M d with Metric_space M d, X = mtopology'. Prove closure_of_sequential_limit from closure_of_sequentially, and use the new lemmas for limy/limQ and limitin_of_dist_half. Move this metrizable-sequential glue into its own small theory, since it is not Berge's theorem.


### SemiC+Wiener-9. Usc extension off a closed set exists twice; the library copy is dead and the used copy sits in SOVA at euclidean_space

*clone, impact medium, confidence high, ~85 lines.*  
Locations: Semicontinuous_Analysis/Semicontinuity.thy:191-244 usc_extension_bounded; Second_Order_Viscosity_Analysis/Doubling_Of_Variables.thy:2661-2698 usc_extend_const_below

usc_extension_bounded (relative usc on K, extension by -B) is never used; grep finds only prose at Doubling_Of_Variables:2662 and Comparison_Two_Domain:763. usc_extend_const_below (global usc of u, extension by a constant C \<le> inf over K, fixed to 'a::euclidean_space) is the copy actually used (Comparison_Two_Domain:321). One lemma, 'u usc relative to closed K and C \<le> u on K implies (if y\<in>K then u y else C) is usc' at 'a::metric_space, covers both.

Evidence: usc_extension_bounded conclusion: \<exists>u'. ... (\<And>c z. u' z < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> u' y < c), with u' = (\<lambda>y. if y \<in> K then u y else - B). usc_extend_const_below: uscu (global) + lo: Bl \<le> u y on K + CB: C \<le> Bl shows the same for (if y \<in> K then u y else C).

Suggested action: State the merged lemma once in Semicontinuity, at metric_space with relative usc. Delete usc_extend_const_below after the SOVA -> Semicontinuous_Analysis edge exists, or delete usc_extension_bounded if the edge is not added. Fix the two prose references.


### SemiC+Wiener-10. Paper-specific and stale prose in sessions advertised as paper-free

*documentation, impact medium, confidence high, ~90 lines.*  
Locations: Semicontinuous_Analysis/Berge.thy:9-22 (section 'Proposition 2.4 of LaiShkolnikovSoner'); Semicontinuous_Analysis/Berge.thy:128-135 ('Exit_Time_Semicontinuity.etime_shift_box', 'the path space'); Semicontinuous_Analysis/Berge.thy:271-278, 306-310 ('Lemmas 2.2 and 2.3 of LaiShkolnikovSoner'); Semicontinuous_Analysis/Semicontinuous_Envelopes.thy:149 ('Theorem 4.3 ... \<iota> \<down> 1 step'); Semicontinuous_Analysis/Semicontinuous_Envelopes.thy:327-331 ('Definition 3.1 ... boundary gate of Eq. (1.10) ... lsc_envK is the paper's envelope'); Semicontinuous_Analysis/Semicontinuous_Selection.thy:11-14; Semicontinuous_Analysis/document/root.bib:1 LaiShkolnikovSoner; Wiener_Measure/Product_Brownian_Motion.thy:14-24 ('discharging the locale sufficiently_volatile_market of Volatile_Market'); Wiener_Measure/Product_Brownian_Motion.thy:418, 549, 618 ('market process', 'Past and increments of the market'); Wiener_Measure/Product_Brownian_Motion.thy:543-546 (orphan text on eigenvalue bound L, no lemma follows); Wiener_Measure/Vector_Brownian_Martingales.thy:290, 327-334 (empty section 'The Brownian market is sufficiently volatile'); Wiener_Measure/Vector_Brownian_Martingales.thy:338-347 ('dynkin_quadratic proved in the next section', 'locales of Ito_Market'); Wiener_Measure/Vector_Brownian_Martingales.thy:924-929 ('Z_martingale of ito_const_horizon_market'); Wiener_Measure/Continuous_Brownian_Motion.thy:17-22 ('bm_paths of Brownian_Market', 'the exit-time market'), 143

Both sessions describe themselves in their ROOT as paper-free, yet they cite the paper's numbered results and name theories and locales of Relative_Arbitrage, which they cannot import. Several of these statements are false: dynkin_quadratic is in Relative_Arbitrage/Volatile_Market.thy, not 'in the next section'. ito_const_horizon_market no longer exists (Ito_Market has ito_volatile_market and ito_stopped_market). bm_paths is defined in Product_Brownian_Motion, not Brownian_Market. PBM:543-546 introduces 'Two-sided pointwise bounds on the trace ... eigenvalue upper bound L', but no lemma follows.

Evidence: grep -rn ito_const_horizon_market finds only VBM:927. grep dynkin_quadratic finds Volatile_Market.thy:26,75. VBM:327 has a section with only a text block.

Suggested action: Rewrite the prose in neutral mathematical terms (Berge's maximum theorem, the relative lower envelope, measurable selection, the n-dimensional Brownian motion). Move the paper's motivation into Relative_Arbitrage/Brownian_Market.thy and the consumers. Delete the empty sections and the orphan text, and remove LaiShkolnikovSoner from Semicontinuous_Analysis/document/root.bib.


### SemiC+Wiener-11. Increment independence of the Wiener measure is proved twice by separate transports through csum; the general one is unused

*clone, impact medium, confidence high, ~200 lines.*  
Locations: Wiener_Measure/Brownian_Motion.thy:257-439 bm_increments_indep; Wiener_Measure/Product_Brownian_Motion.thy:43-198 wiener_pre_past_increment_indep; Wiener_Measure/Brownian_Motion.thy:346-378 (tele); Wiener_Measure/Product_Brownian_Motion.thy:129-149 (inc_eq)

Both start from the independent coordinates of inc_prod 0 J (via distr_PiM_reindex or indep_vars_PiM_coordinate), transport along csum (bm_fdd_def) and wiener_pre_marginal, and re-prove the telescoping identity csum J w t - csum J w s = w t for consecutive s < t. bm_increments_indep (183 lines) is referenced nowhere; its downstream users take the past/increment form. Kolmogorov_Chentsov already defines indep_increments for sorted (not strictly sorted) lists, which bm_increments_indep does not connect to.

Evidence: grep -rnw bm_increments_indep finds only its declaration. Kolmogorov_Chentsov/Stochastic_Processes.thy:162 lift_definition indep_increments ... (\<forall>l. set l \<subseteq> I \<and> sorted l \<and> length l \<ge> 2 \<longrightarrow> prob_space.indep_vars ...).

Suggested action: Factor out one lemma: for finite J \<subseteq> {0..}, distr wiener_pre (Pi\<^sub>M J) (\<lambda>\<omega>. \<lambda>u\<in>J. \<omega> u - \<omega> (prevt 0 J u)) = inc_prod 0 J. Derive wiener_pre_past_increment_indep from it in about 30 lines, and either delete bm_increments_indep or restate it as indep_increments bm_coord (the KC notion) and derive the past/increment form from that.


### SemiC+Wiener-12. Dead public statements, and a fragment theory that only serves one of them

*dead_code, impact medium, confidence high, ~330 lines.*  
Locations: Semicontinuous_Analysis/Berge.thy:34 usc_sup_over_compact; Semicontinuous_Analysis/Semicontinuity.thy:196 usc_extension_bounded; Wiener_Measure/Brownian_Motion.thy:257 bm_increments_indep; Wiener_Measure/Gaussian_Increments.thy:266 gauss_measure_conv; Wiener_Measure/Sorted_Lists.thy:1-93

The first four are referenced only in prose or not at all (grep -rnw). Sorted_Lists has four lemmas. sorted_wrt_less_nth_iff, sorted_wrt_less_set_take and sorted_wrt_less_Max_last are used only by the dead bm_increments_indep, and prod_indicator_conj once (BFDD:397). They are not re-proofs of HOL List lemmas; the nearest are sorted_wrt_nth_less, strict_sorted_iff and sorted_nth_mono. sorted_wrt_less_Max_last also holds for a merely sorted list. Gaussian_Increments imports Sorted_Lists but uses nothing from it, so the import only serialises the chain.

Evidence: grep -rnw gauss_measure_conv: only Gaussian_Increments.thy. grep sorted_wrt_less_*: only Brownian_Motion.thy:284,291 inside bm_increments_indep.

Suggested action: Delete or derive as corollaries, per the clone findings. Fold prod_indicator_conj into BFDD and the list facts into Brownian_Motion if bm_increments_indep is kept, then delete Sorted_Lists and let Gaussian_Increments import HOL-Probability directly.


### SemiC+Wiener-13. Gaussian moment and coordinate-lifting boilerplate repeated, with Gaussian moments placed in the wrong theory

*clone, impact medium, confidence high, ~150 lines.*  
Locations: Wiener_Measure/Gaussian_Increments.thy:98-140 gauss_measure_fourth_moment, _nn; Wiener_Measure/Product_Brownian_Motion.thy:235-344 gauss_measure_mean, gauss_measure_snd_moment, gauss_shifted_square; Wiener_Measure/Product_Brownian_Motion.thy:387-416 bm_coordinate_sq; Wiener_Measure/Vector_Brownian_Martingales.thy:12-40 bm_coordinate_mean; Relative_Arbitrage/Value_Function_Euler_Construction.thy:933-975 bm_coordinate_pow4

Each Gaussian moment re-does the v = 0 versus v > 0 split and the has_bochner_integral to integrable/integral step. bm_coordinate_pow4 recomputes 3h^2 from gauss_measure_moment_even (VFEC:948-957), duplicating gauss_measure_fourth_moment. Lifting a moment to bm_paths is the same 25 lines (bm_coordinate_distr, integrable_distr, integral_distr) three times. The pure Gaussian facts sit in Product_Brownian_Motion, although PLAN §3.4 assigns gauss_measure_mean/snd_moment/shifted_square to Gaussian_Increments.

Evidence: PBM:296-298 rule gauss_measure_moment_even[OF v'] at k=1. VFEC:948-950 rule gauss_measure_moment_even[OF h0] at k=2. GI:109-111 the same at k=2.

Suggested action: In Gaussian_Increments, state gauss_measure_moment_even for 0 \<le> v with integrable and integral conclusions, plus the odd moments, and move mean/snd_moment/shifted_square there. Add one lemma, bm_coordinate_integrable_iff / bm_coordinate_integral: for Borel f, integrability and integral of f (\<omega> i u) under bm_paths equal those of f under gauss_measure u. Then bm_coordinate_sq, bm_coordinate_mean and bm_coordinate_pow4 become 2-line corollaries.


### SemiC+Wiener-14. Hand-made measurability of LEAST in the selection theorem; HOL has measurable_Least

*simplification, impact medium, confidence medium, ~110 lines.*  
Locations: Semicontinuous_Analysis/Semicontinuous_Selection.thy:461-489 Least_nat_eq_iff; Semicontinuous_Analysis/Semicontinuous_Selection.thy:535-615 (Ameas induction in usc_measurable_selection); Semicontinuous_Analysis/Semicontinuous_Selection.thy:699-725 (Nm in countably_valued_approx)

Both proofs compute the fibres {x. (LEAST i. Q x i) = j} by hand as 'Q j minus the union over i<j' through Least_nat_eq_iff. HOL's [measurable] rule measurable_Least does this. With it, (lambda x. usc_sel_code M d z (f x) n) is measurable into count_space UNIV (nat lists are countable) by induction on n, so A n js and the preimages follow from measurable_count_space_eq2_countable. Nx m in countably_valued_approx is directly measurable_Least of the ball predicates.

Evidence: HOL-Analysis/Measurable.thy:270 lemma measurable_Least[measurable]: (\<And>i::nat. (\<lambda>x. P i x) \<in> measurable M (count_space UNIV)) \<Longrightarrow> (\<lambda>x. LEAST i. P i x) \<in> measurable M (count_space UNIV).

Suggested action: Prove a measurability lemma for usc_sel_code by induction with measurable_Least. Replace Ameas/split (80 lines) and Nm/fib (16 lines), and delete Least_nat_eq_iff.


### SemiC+Wiener-15. The attainment lemmas carry a superfluous bound hypothesis and require global semicontinuity

*generalisation, impact medium, confidence medium, ~70 lines.*  
Locations: Semicontinuous_Analysis/Semicontinuity.thy:19 lsc_attains_inf_gen; Semicontinuous_Analysis/Semicontinuity.thy:78 usc_attains_sup_gen; Semicontinuous_Analysis/Semicontinuity.thy:109 lsc_attains_inf_ex

Hypothesis B (B \<le> f y on S) follows from semicontinuity and compactness, as CIS.usc_attains_sup_compact shows: it proves attainment without any bound by a 27-line open-cover argument, against 58 lines here. The proofs evaluate semicontinuity only at points of S and test it only against points of S (zs (r l) \<in> S), so semicontinuity relative to S suffices. That relative form would make the extension lemma unnecessary in consumers.

Evidence: lsc_attains_inf_gen assumes B: \<And>y. y \<in> S \<Longrightarrow> B \<le> f y, used only to define m = INF and get bdd_below. Crandall_Ishii_Sums.thy:125 usc_attains_sup_compact assumes only usc, compact S, S \<noteq> {}. Consumers Pair_Path_Laws:634, Comparison_Two_Domain:41 and Comparison_Localisation:1227 each supply a bound.

Suggested action: Restate with relative semicontinuity on S and no B. Prove by the open-cover argument (or via continuous_attains_inf-style compactness). Keep the B-versions as one-line corollaries during migration.


### SemiC+Wiener-16. Filtration and independence boilerplate that HOL-Probability and the AFP Martingales entry already provide

*library_duplicate, impact medium, confidence medium, ~150 lines.*  
Locations: Wiener_Measure/Vector_Brownian_Martingales.thy:301-313, 822-834, 953-965 (fm/sfs/sff); Wiener_Measure/Product_Brownian_Motion.thy:780-792 (indep_sets_sigma via case_bool); Continuous_Time_Martingales/Integrability_Criteria.thy:231-243 (same pattern); Wiener_Measure/Vector_Brownian_Martingales.thy:184-288 bmX_increment_set_integral_zero, bmX_has_cond_exp

Building sigma_finite_filtered_measure for the natural filtration of a stochastic process on a probability space takes 10 lines, three times. The AFP gives it as finite_filtered_measure_natural_filtration together with sublocale finite_filtered_measure \<subseteq> sigma_finite_filtered_measure. The indep_set to sigma_sets step is HOL's indep_set_sigma_sets. The martingale property of bmX (about 100 lines of set-integral computation plus bm_indicator_increment_indep_var) follows from bm_filtration_increment_indep by the AFP's cond_exp_indep, applied per coordinate (real-valued) and assembled with martingale_vecI.

Evidence: /opt/afp/thys/Martingales/Stochastic_Process.thy:152 lemma finite_filtered_measure_natural_filtration: finite_measure M \<Longrightarrow> finite_filtered_measure M (natural_filtration M t\<^sub>0 X) t\<^sub>0. Filtered_Measure.thy:108 sublocale finite_filtered_measure \<subseteq> sigma_finite_filtered_measure. HOL-Probability/Independent_Family.thy:370 indep_set_sigma_sets. Martingales/Conditional_Expectation_Banach.thy:1027 prob_space.cond_exp_indep: subalgebra M F \<Longrightarrow> indep_set F (vimage_algebra (space M) f borel) \<Longrightarrow> integrable M f \<Longrightarrow> AE x. cond_exp M F f x = expectation f. Continuous_Time_Martingales/Martingale_Algebra.thy:500 martingale_vecI.

Suggested action: Replace the fm/sfs/sff blocks with SP.finite_filtered_measure_natural_filtration[OF BMP.finite_measure_axioms], and PBM:780-792 (and Integrability_Criteria:231-243) with indep_set_sigma_sets. Optionally re-prove martingale_bmX componentwise through cond_exp_indep.


### SemiC+Wiener-17. Compensators stated in the shape of the paper's locale instead of as n t, t and t I

*generalisation, impact medium, confidence medium, ~60 lines.*  
Locations: Wiener_Measure/Product_Brownian_Motion.thy:511-541 bm_compensator_const, bm_compensator_coord; Wiener_Measure/Vector_Brownian_Martingales.thy:806-812, 936-942; Wiener_Measure/Continuous_Brownian_Motion.thy:149-155, 221-227; Relative_Arbitrage/Exit_Class_Witness.thy:495-514 martingale_cbm_outerp

The library theorems say |B_t|^2 - set_lebesgue_integral lborel {0..t} (\<lambda>s. trace (mat 1)) and (B_i)^2 - set_lebesgue_integral ... (mat 1 $ i $ i). That is the shape of Ito_Market's ito_Z X acov with acov = mat 1, not the natural statement |B_t|^2 - n t. bm_compensator_* exist only to evaluate these integrals. The paper session itself restates the result as outerp (cbmX) - t *\<^sub>R mat 1 and recomputes bm_compensator_coord inline.

Evidence: VBM:810-812: bmX x0 t \<omega> \<bullet> bmX x0 t \<omega> - set_lebesgue_integral lborel {0..t} (\<lambda>s. trace (mat 1 :: real^'n^'n)). ECW:498: (\<lambda>t \<omega>. outerp (cbmX x0 t \<omega>) - t *\<^sub>R mat 1).

Suggested action: State the Wiener_Measure theorems as - real CARD('n) * t, - t and (matrix form) outer_prod B B - t *\<^sub>R mat 1. Put the set-integral bridge (bm_compensator_*) in Relative_Arbitrage/Brownian_Market.thy, next to the locale instantiation.


### SemiC+Wiener-18. Real-valued envelopes with global bounds: the paper session re-defines the ereal envelope from scratch, and lsc_env/lsc_envK proofs are tripled

*generalisation, impact medium, confidence medium, ~80 lines.*  
Locations: Semicontinuous_Analysis/Semicontinuous_Envelopes.thy:26-30 lsc_env/usc_env, 343-345 lsc_envK; Semicontinuous_Analysis/Semicontinuous_Envelopes.thy:364-371, 391-398, 624-631 (bdd_above for lsc_envK); Semicontinuous_Analysis/Semicontinuous_Envelopes.thy:352-356, 386-390, 619-623 (ball x e \<inter> K \<noteq> {}); Relative_Arbitrage/Viscosity_Definitions.thy:23-33 ell_op_lsc, ell_op_usc

lsc_env and lsc_envK are fixed to real codomain, so every lemma carries a global bound B and the bdd_above/bdd_below side conditions. The paper session's ell_op_lsc/ell_op_usc are exactly the ereal-valued envelopes SUP e. INF w\<in>ball z e. F w, which is the AFP's lsc_hull by the same lsc_hull_liminf_at/min_Liminf_at argument used in lsc_env_ereal, but they are defined independently. lsc_env u = lsc_envK UNIV u, yet the bdd_above lemma is proved for lsc_env once (lsc_env_bdd_above) and inline three more times for lsc_envK. lsc_env_bdd_below_ball is a misnamed special case of HOL's bdd_belowI2, and bdd_belowI[of _ B] is inlined four more times.

Evidence: Viscosity_Definitions:26-27 "ell_op_lsc k L p M = (SUP e \<in> {0<..}. INF w \<in> ball (p, M) e. ell_op_pair k L w)". HOL/Conditionally_Complete_Lattices.thy:76 bdd_belowI2.

Suggested action: Add an ereal (or complete_linorder) version of the envelope defined as, or proved equal to, lsc_hull, with no bound hypotheses, and express ell_op_lsc/ell_op_usc through it with a bridge lemma (the Statement can keep displaying the unfolded definition). Add lsc_envK_bdd_above and lsc_envK_ne lemmas, or define lsc_env as lsc_envK UNIV. Rename or replace lsc_env_bdd_below_ball with bdd_belowI2.


### SemiC+Wiener-19. ennreal_strict_between is `dense`, and its comment is false

*library_duplicate, impact low, confidence high, ~20 lines.*  
Locations: Semicontinuous_Analysis/Semicontinuous_Selection.thy:16-35 ennreal_strict_between; consumers: Relative_Arbitrage/Exit_Class_Optimizer.thy:390, Relative_Arbitrage/Pair_Path_Space.thy:1416, Relative_Arbitrage/Dynamic_Programming_Delayed_Class.thy:154

The comment says 'ennreal is densely ordered. The instance is declared for ereal but not for ennreal.' In fact ennreal instantiates linear_continuum_topology, and linear_continuum = conditionally_complete_linorder + dense_linorder, so `dense` applies to ennreal directly.

Evidence: HOL/Library/Extended_Nonnegative_Real.thy:1165 instantiation ennreal :: linear_continuum_topology. HOL/Conditionally_Complete_Lattices.thy:685 class linear_continuum = conditionally_complete_linorder + dense_linorder. HOL/Topological_Spaces.thy:3071 class linear_continuum_topology = linorder_topology + linear_continuum.

Suggested action: Delete the lemma and write 'using dense by blast' at its four uses. Fix the prose at Path_Exit_Times.thy:1688 and Exit_Class_Optimizer.thy:267.


### SemiC+Wiener-20. Non-semicontinuity helpers in Semicontinuity, under a stale text block about a missing transfer lemma

*misplacement, impact low, confidence high, ~45 lines.*  
Locations: Semicontinuous_Analysis/Semicontinuity.thy:293-318 pos_image_scale, closed_abs_ge, abs_ge_nonempty; Semicontinuous_Analysis/Semicontinuity.thy:278-291 sup_diff_attained_on_compact; Semicontinuous_Analysis/Semicontinuity.thy:295-297 (text)

pos_image_scale ((lambda e. e/r) ` {0<..} = {0<..}), closed_abs_ge and abs_ge_nonempty say nothing about semicontinuity, and each has exactly one consumer in Relative_Arbitrage (Operator_Envelopes:1363; Exit_Class_Limits:847 twice). sup_diff_attained_on_compact is a 3-line wrapper of continuous_attains_sup with one use (Comparison_Principle:1960). The text before them reads 'The transfer lemma: if \<Psi> leaves F invariant and distorts balls around z ... it leaves the upper envelope at z invariant', but that lemma is not here; it is Operator_Envelopes.ell_op_usc_transfer (Operator_Envelopes:1304). Pointer comments at Operator_Envelopes:1301 and Path_Splicing:1214 confirm these were moved down mechanically.

Evidence: Semicontinuity:295-297 text \<open>The transfer lemma: if \<open>\<Psi>\<close> leaves \<open>F\<close> invariant ...\<close>, followed only by pos_image_scale, closed_abs_ge, abs_ge_nonempty.

Suggested action: Move pos_image_scale back to Operator_Envelopes (next to ell_op_usc_transfer, with the text block) and closed_abs_ge/abs_ge_nonempty to Exit_Class_Limits or Path_Splicing, or inline them. Inline sup_diff_attained_on_compact.


### SemiC+Wiener-21. Stale cross-references to moved lemmas and theories, and leftover 'X lives in Y' pointers

*documentation, impact low, confidence high, ~40 lines.*  
Locations: Relative_Arbitrage/Exit_Time_Semicontinuity.thy:21 'Equicontinuity.usc_sup_over_compact'; Continuous_Path_Spaces/Path_Space.thy:1090 'Equicontinuity.box_of_sequential'; Relative_Arbitrage/Exit_Class_Witness.thy:107 'Brownian_Market.bm_meas_increment_indep_var', :197 'Brownian_Market.bm_set_integral_coord_sq_eq', :27-31; Wiener_Measure/Continuous_Brownian_Motion.thy:205-207; Wiener_Measure/Product_Brownian_Motion.thy:25-33 (section 'Independence toolkit' containing only three pointers), 420-421, 477; Wiener_Measure/Vector_Brownian_Martingales.thy:42-43, 933; Wiener_Measure/Brownian_Motion.thy:251-255; Wiener_Measure/Brownian_Finite_Dimensional_Distributions.thy:166; Wiener_Measure/document/root.tex:21-35

The Berge lemmas live in Semicontinuous_Analysis.Berge, not Continuous_Path_Spaces.Equicontinuity. The bm_* lemmas live in Wiener_Measure.Vector_Brownian_Martingales, not Brownian_Market. CBM:205-207 is a historical note about a deleted duplicate. The pointer-only text blocks are residue from moving lemmas and turn into empty paragraphs and an empty section in the document. The Wiener_Measure abstract mentions only the 1-D construction, although the ROOT description advertises the vector process and its martingales.

Evidence: Berge.thy:34 theorem usc_sup_over_compact and :143 lemma box_of_sequential. Equicontinuity.thy declares only holder_* lemmas. VBM:349 bm_meas_increment_indep_var, VBM:623 bm_set_integral_coord_sq_eq.

Suggested action: Correct the qualified names (or use @{thm [source]} antiquotations so a build catches the next move). Delete the pointer blocks and the empty section. Extend the abstract.


### SemiC+Wiener-22. wiener_pre_coord_zero repeats the proof skeleton of wiener_pre_increment, and a vacuous step is left over

*clone, impact low, confidence high, ~60 lines.*  
Locations: Wiener_Measure/Brownian_Motion.thy:75-145 wiener_pre_increment; Wiener_Measure/Brownian_Motion.thy:147-194 wiener_pre_coord_zero; Wiener_Measure/Brownian_Motion.thy:134-135; Wiener_Measure/Product_Brownian_Motion.thy:348-364 wiener_pre_coord'

Both follow the same route (restrict to finite J, distr_distr, wiener_pre_marginal, bm_fdd_def, csum evaluation, product_prob_space PiM_component, prevt evaluation) for J = {s,t} and J = {0}. The general coordinate law (wiener_pre_coord', u \<ge> 0) is proved separately in Product_Brownian_Motion from start plus increment. BM:134-135 is 'have "distr wiener_pre borel (...) = distr wiener_pre borel (...)" by simp', an unused x = x step. The prime in wiener_pre_coord' has no unprimed counterpart.

Evidence: BM:126-141 and BM:175-190 are the same interpret PPS: product_prob_space ... by (intro product_prob_space.intro ...) block followed by PPS.PiM_component.

Suggested action: Prove a single lemma distr wiener_pre borel (\<lambda>\<omega>. \<omega> u) = gauss_measure u (J = {u}) by the increment skeleton and derive coord_zero and start from it. Rename wiener_pre_coord' and delete the vacuous have.


### SemiC+Wiener-23. bm_fdd_projective re-proves prod_emb_PiE

*simplification, impact low, confidence high, ~35 lines.*  
Locations: Wiener_Measure/Brownian_Finite_Dimensional_Distributions.thy:491-529 (restr_pre in bm_fdd_projective)

restr_pre states (\<lambda>f. restrict f J) -` Pi\<^sub>E J A \<inter> space (bm_fdd H) = Pi\<^sub>E H A' with A' s = (if s\<in>J then A s else UNIV). This is HOL's prod_emb_PiE, since space borel = UNIV, plus prod_emb_def and space_bm_fdd.

Evidence: HOL-Analysis/Finite_Product_Measure.thy:132 lemma prod_emb_PiE: J \<subseteq> I \<Longrightarrow> (\<And>i. i \<in> J \<Longrightarrow> E i \<subseteq> space (M i)) \<Longrightarrow> prod_emb I M J (\<Pi>\<^sub>E i\<in>J. E i) = (\<Pi>\<^sub>E i\<in>I. if i \<in> J then E i else space (M i)).

Suggested action: Replace the 39-line set computation with prod_emb_def, space_bm_fdd, space_PiM and prod_emb_PiE.


### SemiC+Wiener-24. Continuous_Brownian_Motion re-proves the facts about the modification already established inside Brownian_motion_exists

*clone, impact low, confidence high, ~45 lines.*  
Locations: Wiener_Measure/Continuous_Brownian_Motion.thy:44-71 Bcont_source, Bcont_target, Bcont_meas, Bcont_coord; Wiener_Measure/Brownian_Motion_Continuity.thy:148-172 (source_B, target_B, B_meas, ae_coord)

Brownian_motion_exists derives proc_source B = wiener_pre, sets of proc_target, measurability of each process B u and AE B u = coordinate u, but exports only some of them. Continuous_Brownian_Motion then re-derives all four for Bcont with the same modificationD/compatible_source/compatible_target reasoning.

Evidence: CBM:44-46 'using modificationD(1)[OF Bcont_mod] by (auto simp: compatible_source)' and BMC:148-149 'using modificationD(1)[OF mod] by (auto simp: compatible_source)'.

Suggested action: Define Bcont in Brownian_Motion_Continuity, or make Brownian_motion_exists (or a lemma about any modification of bm_coord) export measurability and AE coordinate equality, so the CBM lemmas become instances.


### SemiC+Wiener-25. Document structure: several `section` commands per theory, text before the first section, a double header

*structure, impact low, confidence high, ~40 lines.*  
Locations: Wiener_Measure/Brownian_Finite_Dimensional_Distributions.thy:1,10 (two consecutive sections); Wiener_Measure/Product_Brownian_Motion.thy:1,25,36,200,235,346,418,475,549,580; Wiener_Measure/Vector_Brownian_Martingales.thy:1,10,78,290,327,336,581,804,931; Wiener_Measure/Gaussian_Increments.thy:10-31, Brownian_Motion_Continuity.thy:12-16, Continuous_Brownian_Motion.thy:12-23 (text before the section); Semicontinuous_Analysis/Berge.thy:9,125,269,439

Several theories issue many top-level `section`s, which flattens the generated PDF; Semicontinuity uses `subsection`, so the two sessions are inconsistent. Text blocks placed before a theory's first `section` end up in the previous theory's section in the document. BFDD opens with 'section The finite-dimensional distributions and their projectivity' immediately followed by 'section Finite-dimensional distributions'. Gaussian_Increments' opening text is an overview of the whole Wiener_Measure session and belongs in root.tex.

Evidence: Read of the files listed.

Suggested action: Use one `section` per theory and `subsection` inside. Move the session overview (GI:10-30) into document/root.tex.


### SemiC+Wiener-26. gauss_measure_conv_nn computes the Gaussian convolution by hand

*simplification, impact low, confidence medium, ~80 lines.*  
Locations: Wiener_Measure/Gaussian_Increments.thy:157-262 gauss_measure_conv_nn; Wiener_Measure/Gaussian_Increments.thy:266-308 gauss_measure_conv

The 106-line proof goes through densities, the lborel shift, Fubini and conv_normal_density_zero_mean. For positive variances, HOL-Probability's add_indep_normal / distributed_convolution give the pushforward form, since the coordinates of a product of probability spaces are independent. The iterated-integral form then follows by nn_integral_distr and Fubini (nn_integral_fst), leaving only the degenerate variance-0 cases, which are 10 lines each today. gauss_measure_conv itself is unused.

Evidence: HOL-Probability/Distributions.thy:1252 prob_space.add_indep_normal: indep_var borel X borel Y \<Longrightarrow> 0<\<sigma> \<Longrightarrow> 0<\<tau> \<Longrightarrow> distributed M lborel X (normal_density \<mu> \<sigma>) \<Longrightarrow> ... \<Longrightarrow> distributed M lborel (\<lambda>x. X x + Y x) (normal_density (\<mu>+\<nu>) (sqrt (\<sigma>\<^sup>2+\<tau>\<^sup>2))).

Suggested action: Derive the pushforward form from add_indep_normal on gauss_measure a \<Otimes>\<^sub>M gauss_measure b, then the nn-integral form from it. Alternatively, delete gauss_measure_conv if only the nn form is needed.


### SemiC+Wiener-27. Generic global names exported by a library session

*other, impact low, confidence medium, ~20 lines.*  
Locations: Wiener_Measure/Brownian_Finite_Dimensional_Distributions.thy:18-27,67,99 prevt, inc_prod, csum, wr, ins

The constants ins, wr, csum, prevt and inc_prod are construction internals with very generic names, visible in every downstream theory (csum is used again in Product_Brownian_Motion). A collision or confusion with later developments is likely, especially for ins and csum.

Evidence: fun ins :: real \<Rightarrow> (real \<times> real set) list \<Rightarrow> ...; definition csum :: real set \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real.

Suggested action: Prefix them (bm_prevt, bm_inc_prod, bm_csum, bm_wr, bm_ins) or wrap them in a qualified namespace or private context.


### SemiC+Wiener-28. Kext fixed to euclidean_space; closest_point needs only {real_inner, heine_borel}

*generalisation, impact low, confidence medium, ~10 lines.*  
Locations: Semicontinuous_Analysis/Semicontinuous_Envelopes.thy:487-691 Kext, Kext_proj_bound, Kext_proj_near, Kext_eq_on_K, Kext_bounded, Kext_usc, Kext_ge_proj, lsc_env_Kext

closest_point is defined at 'a::{real_inner,heine_borel}, and the proofs use only closest_point_in_set, closest_point_le, closest_point_self and the triangle inequality. Kext_proj_bound is a 1-line instance of the hypothesis B at closest_point_in_set.

Evidence: HOL-Analysis/Convex_Euclidean_Space.thy:1144 definition closest_point :: 'a::{real_inner,heine_borel} set \<Rightarrow> 'a \<Rightarrow> 'a.

Suggested action: Widen to {real_inner,heine_borel}, or to proper metric spaces with a SOME-based nearest point. Inline Kext_proj_bound.


## SOVA1

This cluster is the bottom of Second_Order_Viscosity_Analysis. It is a self-contained, paper-free development of second-order differentiability of convex and semiconvex functions. It imports only HOL-Analysis and never touches Symmetric_Matrix_Spectra. A grep for paper constants, equation numbers or antiquotations finds nothing. Every statement is at 'a::euclidean_space; none is at real^'n.

The six theories form a linear chain:
- Convex_Subgradients (403 lines): subdifferential `subdiff`, nonemptiness via a supporting hyperplane of the epigraph, the proximal map `prox` (existence, uniqueness, prox_subdiff), Minty surjectivity and nonexpansiveness.
- Rademacher (2,544 lines), after Evans-Gariepy: 1-D Lebesgue differentiation, Borel measurability of the set where directional limits exist, Fubini on basis sections, directional derivatives a.e. (rotated to a basis vector), a.e. additivity of directional derivatives via box integrals and moving-box estimates, linearity on a countable dense set of rational directions, and Frechet differentiability by compactness of the sphere. Results: `rademacher_AE` (real-valued, globally Lipschitz) and `rademacher_vec_AE`.
- Moreau_Envelope (604 lines): the resolvent is differentiable a.e.; firm nonexpansiveness gives a psd derivative; the Moreau envelope is C^1 with gradient x - prox f x; and it has a second-order Taylor expansion wherever prox is differentiable.
- Alexandrov (1,477 lines): symmetry of the envelope Hessian via second differences; transport of the expansion from the envelope to f along the resolvent (local inverse by compactness, f_taylor_limit); baby_Sard plus Rademacher give `convex_alexandrov`, then the corollaries `semiconvex_alexandrov` and `semiconvex_alexandrov_bounded`.
- Jensen_Lemma (580 lines), after Crandall-Ishii-Lions: a determinant-free proof. The selection P x = c x - Q x is Lipschitz on the maximiser set K (localized Baillon-Haddad / co-coercivity) and maps K onto cball 0 d, so K is not negligible.
- Sup_Convolution (601 lines): `supconv`, its bounds, Lipschitz inheritance, semiconvexity, continuity, convergence as eps -> 0, three Jensen+Alexandrov composition corollaries, and the general `second_order_interior_max`.

The mathematics is sound and the statements match the textbook results (Jensen's set is even smaller than CIL's: it requires a maximum over the whole ball). The defects are of four kinds:
1. Duplication: two near-identical semiconvex Alexandrov corollaries; a supconv-specific Jensen/Alexandrov composition next to its general form in Theorem_On_Sums; and the has_derivative epsilon-delta extraction, the squared-norm expansion and an integrability bound each re-derived 3 to 11 times.
2. Library re-proofs: has_derivative_at_alt, linear_inj_bounded_below_pos, linear_injective_isomorphism, Sup_add_eq, inner_sum_left_Basis, lipschitz_on_continuous_on.
3. About 420 lines of statements that nothing uses.
4. Misplacement: generic lemmas sit in the wrong theory, and sup-convolution lemmas are spread over five theories in two sessions.

Structurally, the cluster could be its own HOL-Analysis-based session, and its import chain can be loosened so the theories build in parallel.


### SOVA1-1. Sup-convolution facts are scattered over five theories in two sessions; attainment is proved four times

*misplacement, impact high, confidence medium, ~450 lines.*  
Locations: Crandall_Ishii_Sums.thy:153-242 supconv_attained_usc ('a, usc); Relative_Arbitrage/Comparison_Localisation.thy:902-973 supconv_attained_ball ('a, continuous), :1036-1105 supconv_attained_ball_rad, :1188-1267 supconv_attained_usc_ball (real^'n, usc), plus _in/_family/_rad corollaries, supconv_le_of_local_bound :1317, supconv_sandwich :1336, supconv_uniform_upper :1384-1450; Doubling_Of_Variables.thy:2808 supconv_radius_uniform, :4441 supconv_bound_transfer, :4458/4478 supconv_local_max_transfer(_ball) (real^'n), :4516 supconv_onesided_descent, :4707 supconv_attain_radius, :4744 supconv_le_of_local_bound_usc, :4782 supconv_extend_far_le; Theorem_On_Sums.thy:1003-1071 supconv_dominates_shift, supconv_jet_transfer, supconv_neg_jet_transfer; Sup_Convolution.thy:271-294 supconv_near_optimizer

Sup_Convolution has only the basics. 'supconv of a bounded-above usc u attains its sup at a point within sqrt(2eps(Bu - u x)) (+1)' is proved in CIS:153, CL:902, CL:1036 and CL:1188. Continuity implies usc, and the radius variants differ only in strictness, so one usc lemma with an explicit radius subsumes all four. supconv_attain_radius (Doubling:4707) is the delta = 0 case of the radius conclusion of supconv_near_optimizer, with the same proof lines. The Comparison_Localisation statements name no paper constant, i.e. paper-free content in the paper session. PLAN_RESTRUCTURING_2 §3.3 says Sup_Convolution 'gains 22 statements'; in fact they landed in Doubling_Of_Variables.

Evidence: Statements read at the cited lines. For example, CL:902 `assumes B: "\<And>y. u y \<le> Bu" ... cu: "continuous_on UNIV u" shows "\<exists>ys. dist x ys \<le> sqrt (max 0 (2*\<epsilon>*(Bu - u x))) + 1 \<and> supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"`, and CIS:153 has the same conclusion (without radius) under usc.

Suggested action: Prove a single `supconv_attained_usc_radius` (usc, 'a::euclidean_space, any R > sqrt(max 0 (2eps(Bu - u x)))) in Sup_Convolution and derive the variants as one-liners (or drop them). Move all paper-free supconv_* lemmas listed into Sup_Convolution, widening the real^'n ones to 'a where only norms are used. Fix PLAN §3.3.


### SOVA1-2. semiconvex_alexandrov is a 64-line near-verbatim copy of semiconvex_alexandrov_bounded and is reachable only from dead code

*clone, impact medium, confidence high, ~64 lines.*  
Locations: Second_Order_Viscosity_Analysis/Alexandrov.thy:1327-1390 semiconvex_alexandrov; Second_Order_Viscosity_Analysis/Alexandrov.thy:1398-1472 semiconvex_alexandrov_bounded; Second_Order_Viscosity_Analysis/Sup_Convolution.thy:396 (only use: supconv_alexandrov)

The two corollaries share the same proof skeleton: negligible_subset on convex_alexandrov, the same subsetI/CollectI/notI/erule script, the same blB', symB' and `eq` (sq, i1, i2, num) blocks. The only difference is the extra lowB' clause in the _bounded version. The _bounded conclusion set is a subset of the plain one, since dropping the conjunct (\<forall>k. - (c * (norm k)\<^sup>2) \<le> k \<bullet> B k) weakens the predicate. semiconvex_alexandrov is used only by supconv_alexandrov, which is used only by the dead supconv_jensen_alexandrov_point (next finding).

Evidence: grep -rnw semiconvex_alexandrov: Alexandrov.thy:1327 (decl), Sup_Convolution.thy:396 `by (rule semiconvex_alexandrov[OF supconv_semiconvex'[OF B e]])`. Lines 1358-1381 and 1439-1462 are character-identical (`have eq: "(\<lambda>k. (u (y + k) - u y - (p - c *\<^sub>R y) \<bullet> k ...`). semiconvex_alexandrov_bounded is used by Theorem_On_Sums.thy:592 and in Comparison_Localisation prose.

Suggested action: Delete semiconvex_alexandrov together with the dead supconv_* chain. If it is kept as API, prove it in three lines: negligible_subset[OF semiconvex_alexandrov_bounded] and blast.


### SOVA1-3. supconv_alexandrov/supconv_jensen/supconv_jensen_alexandrov_point duplicate the generic semiconvex_jensen_alexandrov_point and are unused

*clone, impact medium, confidence high, ~75 lines.*  
Locations: Second_Order_Viscosity_Analysis/Sup_Convolution.thy:390-396 supconv_alexandrov; Second_Order_Viscosity_Analysis/Sup_Convolution.thy:403-416 supconv_jensen; Second_Order_Viscosity_Analysis/Sup_Convolution.thy:425-464 supconv_jensen_alexandrov_point; Second_Order_Viscosity_Analysis/Theorem_On_Sums.thy:562-622 semiconvex_jensen_alexandrov_point

supconv_jensen_alexandrov_point is the special case phi = supconv u eps, c = 1/eps of semiconvex_jensen_alexandrov_point. The general proof is the same J/N 'non-negligible set not contained in a negligible one' argument, plus interiority. Theorem_On_Sums' own text says so. None of the three Sup_Convolution corollaries is used anywhere. The generic theorem combines only jensen_lemma, semiconvex_alexandrov_bounded and perturbed_maximiser_deep_interior, all from this cluster, so it belongs in Jensen_Lemma (or a small Jensen_Alexandrov theory), not in Theorem_On_Sums.

Evidence: Theorem_On_Sums.thy:562 text: `\<open>supconv_jensen_alexandrov_point\<close> used only semiconvexity of the sup-convolution, which the doubled functional also has ... So the engine is restated for an arbitrary semiconvex \<phi\>`. grep -rnw supconv_jensen_alexandrov_point gives only Sup_Convolution.thy:425 (decl) and Theorem_On_Sums.thy:562 (prose). supconv_jensen and supconv_alexandrov are used only at Sup_Convolution.thy:444,446.

Suggested action: Delete Sup_Convolution.thy:360-464 except supconv_semiconvex' (or see the semiconvexity finding). Move semiconvex_jensen_alexandrov_point into Jensen_Lemma (or a new theory importing Alexandrov and Jensen_Lemma). Sup_Convolution then no longer needs to import Jensen_Lemma or Alexandrov.


### SOVA1-4. The has_derivative epsilon-delta remainder bound is re-derived three times; HOL has has_derivative_at_alt

*library_duplicate, impact medium, confidence high, ~60 lines.*  
Locations: Second_Order_Viscosity_Analysis/Moreau_Envelope.thy:476-493 (moreau_second_order_taylor, `small`); Second_Order_Viscosity_Analysis/Alexandrov.thy:235-254 (moreau_second_difference_limit, `rem`); Second_Order_Viscosity_Analysis/Alexandrov.thy:773-803 prox_remainder_small

Each block unfolds has_derivative_at, applies tendstoD and eventually_at, and case-splits on u = 0 to get norm (G (x + u) - G x - A u) <= e * norm u for norm u < delta. This is exactly the right-hand side of the library characterisation. prox_remainder_small is the library lemma instantiated at G = id - prox f.

Evidence: HOL/Analysis/Derivative.thy:295 has_derivative_at_alt: "(f has_derivative f') (at x) \<longleftrightarrow> bounded_linear f' \<and> (\<forall>e>0. \<exists>d>0. \<forall>y. norm(y - x) < d \<longrightarrow> norm (f y - f x - f'(y - x)) \<le> e * norm (y - x))". The sibling theory Test_Functions.thy:767,893 already uses `unfolding has_derivative_at_alt`.

Suggested action: Replace all three blocks with `has_derivative_at_alt` (then substitute y = x + u). Delete prox_remainder_small and inline the library call in f_taylor_limit.


### SOVA1-5. Rademacher re-derives the same facts in several places

*clone, impact medium, confidence high, ~75 lines.*  
Locations: Rademacher.thy:1252-1262 (in box_integral_dquot_tendsto) and :1430-1442 (in L1_dquot_tendsto) = AE_dlim_set :1915-1931; Rademacher.thy:423-428, 1252-1257, 1432-1437, 1921-1926 ("- dlim_set f v \<in> sets borel" via sets.compl_sets); Rademacher.thy:604-613 (q inside norm_ddir_le) = norm_dquot_le :1203-1214; Rademacher.thy:895-911 (step1 in differentiable_of_dense_linear_ddir) = q in ddir_lipschitz_in_direction :760-777; Rademacher.thy:57-70 (lipschitz_line_section_diff_ae) = lipphi in ftc_along_line :662-675

AE_dlim_set is declared after two theorems that inline its proof verbatim. norm_dquot_le is declared 600 lines after norm_ddir_le, which re-proves it as a local `q`. The quotient-difference Lipschitz estimate and the line-section Lipschitz estimate also appear twice each. These are pure ordering accidents.

Evidence: The text at 1252-1262 and 1921-1930 is identical up to variable names (`have cB: "- dlim_set f v \<in> sets borel" ... negligible_no_dderiv[OF lip v] ... eventually_ae_filter`). Lines 606-612 and 1208-1213 are identical.

Suggested action: Move norm_dquot_le, AE_dlim_set (plus a lemma `borel_compl_dlim_set`) and a `norm_dquot_diff_le` lemma up to the measurability section and cite them.


### SOVA1-6. 'Bounded Borel function times indicator of a finite-measure set is integrable' is proved five times; the |B| bound is re-normalised four times

*clone, impact medium, confidence high, ~80 lines.*  
Locations: Rademacher.thy:1359-1373 integrable_dquot_indicator; Rademacher.thy:1388-1401 (ishift in box_integral_add_split); Rademacher.thy:1537-1558 integrable_bounded_indicator; Rademacher.thy:1933-1961 integrable_ddir_indicator; Rademacher.thy:2008-2025 (ig in ddir_add_AE); Rademacher.thy:1342-1348, 1470-1483, 1948-1953, 1979-1986 (B * norm v \<le> \<bar>B\<bar> * norm v)

All five are Bochner_Integration.integrable_bound with dominating function \<bar>M\<bar> * indicator S and the same abs_mult/mult_right_mono script. integrable_bounded_indicator is the general form but takes a pointwise bound, so the AE-bounded uses (ddir, g) cannot call it. Separately, the sign of B is handled locally four times, while rademacher_AE (2426-2431) simply replaces B by \<bar>B\<bar> once.

Evidence: Compare 1365-1372, 1391-1400, 1543-1557, 1940-1960, 2010-2024: each has `show "integrable lborel (\<lambda>x. (\<bar>B\<bar> * norm v) * indicator S x :: real)" using S Sfin by (intro integrable_mult_right) simp`.

Suggested action: State integrable_bounded_indicator with an `AE x in lborel. \<bar>h x\<bar> \<le> M` hypothesis and use it everywhere. Assume 0 \<le> B in the internal Rademacher lemmas and normalise B once in the public theorems.


### SOVA1-7. About 420 lines of statements in the cluster are used nowhere

*dead_code, impact medium, confidence high, ~420 lines.*  
Locations: Rademacher.thy:632-695 ddir_line_eq + ftc_along_line; Rademacher.thy:754-789 ddir_lipschitz_in_direction; Rademacher.thy:794-810 negligible_no_dderiv_countable; Rademacher.thy:948-997 ddir_add_of_shifted_limit (abandoned route); Rademacher.thy:1417-1498 L1_dquot_tendsto; Rademacher.thy:1908-1911 ennreal_mult_indicator_eq; Moreau_Envelope.thy:339-367 moreau_twice_differentiable_AE; Moreau_Envelope.thy:570-599 moreau_alexandrov_AE; Alexandrov.thy:18-46 second_difference_symmetric, moreau_second_difference_integral; Alexandrov.thy:403-433 moreau_alexandrov_sym_AE; Jensen_Lemma.thy:19-49 perturbed_maximiser_interior; Jensen_Lemma.thy:152-163 interior_max_subdiff; Sup_Convolution.thy:268-357 supconv_near_optimizer (used only by supconv_tendsto) + supconv_tendsto; Convex_Subgradients.thy:366-370 minty_surjective (API, keep)

`grep -rnw NAME --include=*.thy` over the repository finds no use outside the declaring line. The three Moreau/Alexandrov AE packagings are nested restatements: moreau_alexandrov_sym_AE subsumes moreau_alexandrov_AE, and convex_alexandrov is the real endpoint. ddir_add_of_shifted_limit is a remnant of an abandoned additivity route; dquot_add_split is still needed. Library-API judgement applies to supconv_tendsto and minty_surjective. The rest are development scaffolding.

Evidence: Usage counts (excluding the declaration): ftc_along_line 0, ddir_lipschitz_in_direction 0, negligible_no_dderiv_countable 0, ddir_add_of_shifted_limit 0, L1_dquot_tendsto 0, ennreal_mult_indicator_eq 0, moreau_twice_differentiable_AE 0, moreau_alexandrov_AE 0, second_difference_symmetric 0, moreau_second_difference_integral 0, moreau_alexandrov_sym_AE 0, perturbed_maximiser_interior 0, interior_max_subdiff 0, supconv_tendsto 0, minty_surjective 0; ddir_line_eq is used only by ftc_along_line, supconv_near_optimizer only by supconv_tendsto.

Suggested action: Delete the scaffolding (Rademacher, Moreau, Alexandrov and Jensen items). Keep supconv_tendsto (natural API, but state it for usc u) and minty_surjective. Confirm with the semantic unused_thms run.


### SOVA1-8. The squared-norm expansion |a+b|^2 = |a|^2 + 2a.b + |b|^2 is re-derived at least 11 times in the cluster

*clone, impact medium, confidence high, ~70 lines.*  
Locations: Convex_Subgradients.thy:238-244 midpoint_dist_identity, :299-304 prox_step_expand; Moreau_Envelope.thy:197-200 (moreau_upper), :212-216 (moreau_lower); Alexandrov.thy:453-457 (subdiff_prox), :757-766 (f_increment_exact), :1364-1366, :1445-1447 (semiconvex_alexandrov[_bounded]); Jensen_Lemma.thy:119-131 (interior_max_subdiff_unique), :180-189 (max_semiconcave_bound); Sup_Convolution.thy:199-201 (supconv_square_decomp); Crandall_Ishii_Sums.thy:438 norm_sq_add_expand, :1438 norm_sq_diff_expand; Theorem_On_Sums.thy:506 norm_sq_diff_shift; Doubling_Of_Variables.thy:1636 penalty_difference_identity

Each site unfolds power2_norm_eq_inner, inner_add/diff_left/right and inner_commute, and runs simp/argo. Jensen_Lemma.thy:119-131 needs 13 lines with four auxiliary equations. The lemmas that would remove all of this exist, but higher up in the session (Crandall_Ishii_Sums), so the cluster cannot cite them.

Evidence: Crandall_Ishii_Sums.thy:438 `lemma norm_sq_add_expand: "(norm (a + k))\<^sup>2 = (norm a)\<^sup>2 + 2 * (a \<bullet> k) + (norm k)\<^sup>2"`. HOL/Analysis/Inner_Product.thy:359 dot_norm, :362 dot_norm_neg. AFP Projected_Gradient_Descent/Gradient_Preliminaries.thy:511 norm_sq_add, :525 norm_sq_diff (real_inner).

Suggested action: Move norm_sq_add_expand and norm_sq_diff_expand, generalised to real_inner, into Convex_Subgradients (or a small Inner_Product_Identities theory at the bottom) and cite them at every site above.


### SOVA1-9. Generic lemmas sit in theories they have nothing to do with

*misplacement, impact medium, confidence high, ~330 lines.*  
Locations: Sup_Convolution.thy:473-596 second_order_interior_max (11 uses in Doubling, Theorem_On_Sums, Comparison_Localisation); Sup_Convolution.thy:157-192 convex_on_cSUP, convex_on_affine_inner; Alexandrov.thy:441-548 subdiff_prox, subdiff_norm_le, convex_subdiff; :610-621 prox_lipschitz_on, continuous_on_prox; Theorem_On_Sums.thy:568-622 semiconvex_jensen_alexandrov_point; :630 second_order_form_unique

second_order_interior_max mentions no sup-convolution; it is the general 'gradient zero, Hessian nsd at an interior maximum' for second-order expansions and belongs with second_order_form_unique. convex_on_cSUP and convex_on_affine_inner are generic convexity facts. subdiff_prox, convex_subdiff, subdiff_norm_le and the prox continuity lemmas are basic subdifferential/prox facts used by Alexandrov but natural in Convex_Subgradients.

Evidence: second_order_interior_max statement: `bounded_linear X \<Longrightarrow> 0 < \<delta> \<Longrightarrow> (\<And>k. norm k < \<delta> \<Longrightarrow> f (x + k) \<le> f x) \<Longrightarrow> ((\<lambda>k. (f (x + k) - f x - q \<bullet> k - (k \<bullet> X k)/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0) \<Longrightarrow> q \<bullet> v = 0 \<and> v \<bullet> X v \<le> 0`, with no supconv.

Suggested action: Create Second_Order_Expansions (second_order_interior_max, second_order_form_unique, the expansion definition and bound). Move the subdiff/prox basics into Convex_Subgradients and the two convex_on lemmas there too.


### SOVA1-10. The session abstract claims Rademacher for locally Lipschitz functions; the theorem assumes a global Lipschitz bound

*documentation, impact medium, confidence high, ~3 lines.*  
Locations: Second_Order_Viscosity_Analysis/document/root.tex:24-26; Second_Order_Viscosity_Analysis/Rademacher.thy:2421-2424 rademacher_AE

root.tex says 'We formalize Rademacher's theorem, that a locally Lipschitz function on a Euclidean space is differentiable at almost every point'. rademacher_AE assumes `\<And>y z. norm (f y - f z) \<le> B * norm (y - z)` on all of UNIV, and no local version exists in the repository.

Evidence: rademacher_AE: `assumes lip: "\<And>y z. norm (f y - f z) \<le> B * norm (y - z)" shows "AE x in lborel. f differentiable (at x)"`.

Suggested action: Either fix the prose ('a Lipschitz function') or add the local version: cover by countably many balls and extend Lipschitz-on-ball to global with a McShane extension (real-valued) or componentwise.


### SOVA1-11. Semiconvexity has no definition; two spellings force an adapter, and the calculus is spread over four theories and two sessions

*generalisation, impact medium, confidence medium, ~120 lines.*  
Locations: Sup_Convolution.thy:210-247 supconv_semiconvex ((norm x)\<^sup>2 / (2*\<epsilon>) form); Sup_Convolution.thy:368-383 supconv_semiconvex' ((1/\<epsilon>)/2 * (norm x)\<^sup>2 form, 6 uses); Jensen_Lemma.thy:342-367 semiconvex_continuous, semiconvex_max_exists; Theorem_On_Sums.thy:253-450 convex_on_norm_sq, semiconvex_add, semiconvex_penalty, semiconvex_of_fst/_snd; Doubling_Of_Variables.thy:796 semiconvex_penalty_gen, :882 semiconvex_shift_perturb; Symmetric_Matrix_Spectra/Symmetric_Spectral.thy:501-548 hessian_lower_bound_of_psd, semiconvex_hessian_two_sided, semiconvex_hessian_abs_bound; Alexandrov.thy:1432-1438 (lowB' = hessian_lower_bound_of_psd)

`convex_on UNIV (\<lambda>x. u x + (c/2) * (norm x)\<^sup>2)` is written out in every statement, and supconv_semiconvex uses a second form. supconv_semiconvex' exists only to convert between the two. The semiconvex-Hessian lemmas in Symmetric_Matrix_Spectra involve no matrices or spectra; their key step is re-proved as lowB' in semiconvex_alexandrov_bounded.

Evidence: grep 'definition semiconvex' finds nothing. Symmetric_Spectral.thy:505 `have "k \<bullet> (B k - c *\<^sub>R k) = k \<bullet> B k - c * (norm k)\<^sup>2"` = Alexandrov.thy:1434-1435 and 1450-1451.

Suggested action: Add `definition semiconvex_on c f \<equiv> convex_on UNIV (\<lambda>x. f x + (c/2) * (norm x)\<^sup>2)` in a new theory Semiconvex_Functions right after Convex_Subgradients. Gather the calculus there (continuity, max_exists, add, of_fst/of_snd, penalty, psd lower bound), state supconv_semiconvex as `semiconvex_on (1/\<epsilon>) (supconv u \<epsilon>)` and delete the adapter.


### SOVA1-12. The second-order expansion predicate is spelled out about 86 times; an epsilon-extraction from it is repeated

*structure, impact medium, confidence medium, ~150 lines.*  
Locations: Alexandrov.thy:1226-1229, 1285-1298 (convex_alexandrov restates its set 3 times), 1330-1347, 1401-1427; Sup_Convolution.thy:393-395, 434-442, 478-479; Alexandrov.thy:805-833 moreau_taylor_bound; Theorem_On_Sums.thy:1239 superjet_local_max; Doubling_Of_Variables.thy:535 superjet_local_max_onesided

`((\<lambda>k. (f (y + k) - f y - p \<bullet> k - (k \<bullet> B k)/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)` appears on about 86 lines in Alexandrov, Sup_Convolution, Theorem_On_Sums, Crandall_Ishii_Sums and Doubling_Of_Variables. Big set-builder statements are restated inside their own proofs (convex_alexandrov, semiconvex_alexandrov*). The step 'expansion limit => there is delta with |R k| <= eta |k|^2' is proved in moreau_taylor_bound and again in superjet_local_max and superjet_local_max_onesided.

Evidence: grep -rn '/ (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)\|(norm k)\<^sup>2)$' --include=*.thy gives 86 lines.

Suggested action: Introduce `definition has_second_order_expansion f x q X` (or reuse the superjet machinery of Crandall_Ishii_Sums by moving its definition down). Add one lemma `second_order_expansion_bound` giving the eta-delta form, and use it in moreau_taylor_bound and both superjet_local_max variants.


### SOVA1-13. The cluster should be its own session, independent of Symmetric_Matrix_Spectra

*structure, impact medium, confidence medium, ~20 lines.*  
Locations: Second_Order_Viscosity_Analysis/ROOT (sessions Symmetric_Matrix_Spectra); Second_Order_Viscosity_Analysis/Theorem_On_Sums.thy:5 (first theory to import Matrix_Algebra)

The six theories, about 7.2k lines of convex analysis (Rademacher, Moreau, Alexandrov, Jensen, sup-convolution), need only HOL-Analysis. Because they share a session with the viscosity toolbox, they cannot start building until the Symmetric_Matrix_Spectra heap exists. The session abstract mixes two subjects ('Sup-Convolutions, Alexandrov's Theorem, and Comparison of Viscosity Solutions'). A separate session would be an AFP-ready entry in its own right and would build in parallel with Symmetric_Matrix_Spectra.

Evidence: All six theories import only each other and HOL-Analysis.Analysis. Theorem_On_Sums is the first to import "Symmetric_Matrix_Spectra.Matrix_Algebra".

Suggested action: Create session `Convex_Second_Order` (or `Rademacher_Alexandrov`) = HOL-Analysis + Convex_Subgradients, Semiconvex_Functions (new), Rademacher, Moreau_Envelope, Alexandrov, Jensen_Lemma, Jensen_Alexandrov (new), Sup_Convolution (enlarged as in the scattered-supconv finding), Second_Order_Expansions (new). Second_Order_Viscosity_Analysis then depends on it and on Symmetric_Matrix_Spectra, and keeps Theorem_On_Sums, Doubling_Of_Variables, Crandall_Ishii_Sums, Soft_Penalty, Test_Functions and Viscosity_Solutions. Also move the semiconvex_hessian_* lemmas out of Symmetric_Spectral into Semiconvex_Functions.


### SOVA1-14. inj_linear_bounded_below and linear_inj_two_sided_inverse re-prove HOL-Analysis lemmas

*library_duplicate, impact low, confidence high, ~36 lines.*  
Locations: Second_Order_Viscosity_Analysis/Alexandrov.thy:835-853 inj_linear_bounded_below; Second_Order_Viscosity_Analysis/Alexandrov.thy:1074-1090 linear_inj_two_sided_inverse

inj_linear_bounded_below (\<exists>K>0. \<forall>u. norm u \<le> K * norm (D u)) is linear_inj_bounded_below_pos with K = 1/B. linear_inj_two_sided_inverse (\<exists>D'. linear D' \<and> (\<forall>u. D' (D u) = u) \<and> (\<forall>u. D (D' u) = u)) is linear_injective_isomorphism verbatim.

Evidence: HOL/Analysis/Linear_Algebra.thy:524 linear_inj_bounded_below_pos: "linear f \<Longrightarrow> inj f \<Longrightarrow> obtains B where B > 0 \<And>x. B * norm x \<le> norm(f x)". HOL/Vector_Spaces.thy:1485 linear_injective_isomorphism, used at euclidean_space with just linear+inj at Equivalence_Lebesgue_Henstock_Integration.thy:3038 (`using \<open>linear f\<close> linear_injective_isomorphism by blast`).

Suggested action: Delete both lemmas and call the library lemmas in f_taylor_limit (:903) and f_alexandrov_at (:1151).


### SOVA1-15. cSUP_plus_const re-proves Sup_add_eq

*library_duplicate, impact low, confidence high, ~25 lines.*  
Locations: Second_Order_Viscosity_Analysis/Sup_Convolution.thy:131-155 cSUP_plus_const

`bdd_above (range g) \<Longrightarrow> (SUP y. g y) + c = (SUP y. g y + c)` is the conditionally-complete-lattice library lemma with the summands commuted.

Evidence: HOL/Conditionally_Complete_Lattices.thy:728 Sup_add_eq: "bdd_above (f ` A) \<Longrightarrow> A \<noteq> {} \<Longrightarrow> (SUP x\<in>A. a + f x) = a + (SUP x\<in>A. f x)". Only use: Sup_Convolution.thy:222.

Suggested action: Delete it and use Sup_add_eq (with add.commute) in supconv_semiconvex.


### SOVA1-16. lipschitz_continuous_on_UNIV re-proves lipschitz_on_continuous_on; the cluster has three spellings of 'Lipschitz'

*library_duplicate, impact low, confidence high, ~30 lines.*  
Locations: Second_Order_Viscosity_Analysis/Rademacher.thy:388-415 lipschitz_continuous_on_UNIV (10 uses); Second_Order_Viscosity_Analysis/Alexandrov.thy:610-621 prox_lipschitz_on, continuous_on_prox (uses the library route); Second_Order_Viscosity_Analysis/Sup_Convolution.thy:60,87,104 (\<bar>u p - u q\<bar> \<le> L * norm (p - q)); Second_Order_Viscosity_Analysis/Moreau_Envelope.thy:17-25 prox_lipschitz (\<le> 1 * norm (y - z))

The 28-line epsilon-delta proof is lipschitz_on_continuous_on[OF lipschitz_onI] (with max B 0). Alexandrov already does exactly that for prox. Lipschitz hypotheses appear as `\<And>x y. norm (f x - f y) \<le> B * norm (x - y)` (Rademacher), `\<bar>u p - u q\<bar> \<le> L * norm (p - q)` (Sup_Convolution) and `lipschitz_on 1 UNIV` (Alexandrov).

Evidence: HOL/Analysis/Lipschitz.thy:21 lipschitz_onI, :146 lipschitz_on_continuous_on "continuous_on X f if L-lipschitz_on X f". Alexandrov.thy:620 `lipschitz_on_continuous_on[OF prox_lipschitz_on[OF cvx]]`.

Suggested action: Delete lipschitz_continuous_on_UNIV. Preferably state Rademacher and the supconv Lipschitz lemmas with HOL's `B-lipschitz_on UNIV f`.


### SOVA1-17. inner_sum_scaleR_Basis is HOL's simp lemma inner_sum_left_Basis, and inner_sum_scaleR_subset generalises it in the same file

*library_duplicate, impact low, confidence high, ~12 lines.*  
Locations: Second_Order_Viscosity_Analysis/Rademacher.thy:1005-1016 inner_sum_scaleR_Basis; Second_Order_Viscosity_Analysis/Rademacher.thy:2248-2266 inner_sum_scaleR_subset

`j \<in> Basis \<Longrightarrow> (\<Sum>i\<in>Basis. c i *\<^sub>R i) \<bullet> j = c j` is a library [simp] lemma. The same file then proves the S \<subseteq> Basis generalisation separately.

Evidence: HOL/Analysis/Euclidean_Space.thy:72 `lemma (in euclidean_space) inner_sum_left_Basis[simp]: "b \<in> Basis \<Longrightarrow> inner (\<Sum>i\<in>Basis. f i *\<^sub>R i) b = f b"`.

Suggested action: Delete inner_sum_scaleR_Basis and use inner_sum_left_Basis (4 call sites); keep only the subset version.


### SOVA1-18. perturbed_maximiser_interior is the rho = r instance of perturbed_maximiser_deep_interior

*clone, impact low, confidence high, ~31 lines.*  
Locations: Second_Order_Viscosity_Analysis/Jensen_Lemma.thy:19-49 perturbed_maximiser_interior; Second_Order_Viscosity_Analysis/Jensen_Lemma.thy:212-239 perturbed_maximiser_deep_interior

Both proofs run the same Cauchy-Schwarz contradiction line by line (step, `p \<bullet> (x - \<xi>) \<le> norm p * norm (x - \<xi>)`, `\<phi> \<xi> - m \<le> d * r`). With rho = r, the annulus hypothesis of the deep version is exactly the sphere hypothesis of the shallow one, and the conclusion dist x xi < r is x \<in> ball xi r. The shallow version is unused.

Evidence: Lines 36-48 and 224-238 are line-by-line parallel.

Suggested action: Delete perturbed_maximiser_interior.


### SOVA1-19. Second-difference bounds are re-derived inside moreau_second_difference_limit, and symmetry is re-proved inline

*clone, impact low, confidence high, ~40 lines.*  
Locations: Second_Order_Viscosity_Analysis/Alexandrov.thy:107-121 (b1, b2 in second_difference_integrand_bound); Second_Order_Viscosity_Analysis/Alexandrov.thy:290-304 (nb1, nb2 in moreau_second_difference_limit); Second_Order_Viscosity_Analysis/Alexandrov.thy:166-183 second_difference_integrand_bound_left; Second_Order_Viscosity_Analysis/Alexandrov.thy:382-395 (`same` in moreau_hessian_symmetric) vs :18-22 second_difference_symmetric (unused)

The bounds norm (s *\<^sub>R (t *\<^sub>R u)) \<le> \<bar>t\<bar> * norm u and norm (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u)) \<le> \<bar>t\<bar> * (norm v + norm u) are proved inside the integrand-bound lemma and again verbatim in its only caller. A separate _left lemma exists only to re-associate an addition. The commutation lemma second_difference_symmetric is unused, and the same fact is re-proved inline where it is needed.

Evidence: Text at 108-121 equals 291-304. Alexandrov.thy:162-164 says the _left lemma is "kept separate so simp does not distribute the inner product".

Suggested action: Export the two norm bounds as a lemma (or take them as the integrand-bound hypotheses w1, w2). State the integrand bound in the left-associated form directly. Use second_difference_symmetric or delete it.


### SOVA1-20. Firm nonexpansiveness and the 'cancel one norm' step are proved three times; prox is 1-Lipschitz in three phrasings

*clone, impact low, confidence high, ~35 lines.*  
Locations: Convex_Subgradients.thy:379-397 (key + cancellation in prox_nonexpansive); Moreau_Envelope.thy:43-54 prox_firm_nonexpansive; Moreau_Envelope.thy:304-316 prox_deriv_norm_le; Jensen_Lemma.thy:318-333 (end of subdiff_lipschitz_of_semiconcave); Moreau_Envelope.thy:17-25 prox_lipschitz; Alexandrov.thy:610-614 prox_lipschitz_on

prox_nonexpansive proves `(norm (y1 - y2))^2 \<le> (x1 - x2) \<bullet> (y1 - y2)` (firm nonexpansiveness) as an intermediate fact. Moreau_Envelope then re-proves the same as prox_firm_nonexpansive. 'a^2 <= a*b implies a <= b', via Cauchy-Schwarz and mult_le_cancel_right, appears three times. prox_nonexpansive (dist form), prox_lipschitz (norm form, with a literal `1 *`) and prox_lipschitz_on (lipschitz_on) are three spellings of one fact.

Evidence: Convex_Subgradients.thy:385 `have key: "(norm (y\<^sub>1 - y\<^sub>2))\<^sup>2 \<le> (x\<^sub>1 - x\<^sub>2) \<bullet> (y\<^sub>1 - y\<^sub>2)"` vs Moreau_Envelope.thy:46 same statement for prox.

Suggested action: Prove prox_firm_nonexpansive in Convex_Subgradients and derive prox_nonexpansive from it with a lemma `norm_le_of_sq_le_inner`, which also serves prox_deriv_norm_le and Jensen. Keep a single Lipschitz phrasing (lipschitz_on).


### SOVA1-21. semiconvex_continuous vs supconv_continuous; convex_bdd_above_cball / convex_bdd_below_cball are mirror clones that use only continuity

*clone, impact low, confidence high, ~40 lines.*  
Locations: Jensen_Lemma.thy:342-355 semiconvex_continuous; Sup_Convolution.thy:252-266 supconv_continuous; Alexandrov.thy:495-510 convex_bdd_above_cball, :512-527 convex_bdd_below_cball

supconv_continuous is semiconvex_continuous[OF supconv_semiconvex'], re-proved. The two cball-bound lemmas differ only in Sup/Inf. Each derives continuity from convexity and then bounds a continuous image of a compact set. They do not need convexity, which is a generalisation.

Evidence: Sup_Convolution.thy:257-265 repeats Jensen_Lemma.thy:347-354 (`convex_on_continuous[OF open_UNIV ...]`, `continuous_on_diff`). HOL/Topological_Spaces.thy:2789 continuous_attains_sup/inf gives the bounds directly.

Suggested action: Derive supconv_continuous from semiconvex_continuous (after moving the latter to a semiconvexity theory). Replace the cball-bound pair with one lemma for continuous f, or with continuous_attains_sup/inf.


### SOVA1-22. Stale or inaccurate prose

*documentation, impact low, confidence high, ~30 lines.*  
Locations: Jensen_Lemma.thy:385-387; Rademacher.thy:1417-1420; Rademacher.thy:948-952; Moreau_Envelope.thy:572-575; Rademacher.thy:2073-2075; Alexandrov.thy:157-164; Rademacher.thy:1099-1101; Symmetric_Matrix_Spectra/Symmetric_Spectral.thy:494-499

(1) Jensen_Lemma: the measure estimate is said to need 'Hadamard's inequality or a spectral theorem, neither available in this HOL-Analysis'. This session depends on Symmetric_Matrix_Spectra, which proves symmetric_eigenbasis (Symmetric_Spectral.thy:339).
(2) Rademacher: the 'L1 convergence' text says L1 convergence is what lets the domain wobble. L1_dquot_tendsto is unused; the actual route is integral_domain_shift_bound + box_integral_dquot_tendsto.
(3) The subsection 'Additivity in the direction: reduction to a shifted limit' describes an abandoned route.
(4) 'Transporting the expansion to f itself ... remains' and '... agreement with ddir on a dense set of directions remains' read as TODOs, but both are done.
(5) Two consecutive text blocks; the first describes moreau_second_difference_limit, 55 lines later.
(6) The text speaks of 'vanishing integral over every open box', while the hypothesis is equality of the ennreal integrals of g+ and g-.
(7) A lower session's prose names Rademacher, Alexandrov, Jensen_Lemma and Theorem_On_Sums as suppliers.

Evidence: Jensen_Lemma.thy:385 "The usual proof estimates the measure from below by a Jacobian determinant, needing Hadamard's inequality or a spectral theorem, neither available in this HOL-Analysis." grep -rnw L1_dquot_tendsto finds only the declaration.

Suggested action: Reword (1) as 'avoids determinants altogether'. Delete (2) and (3) together with the dead lemmas. Rephrase (4) in the present tense. Merge (5) into one block before :217. Correct (6). Remove upward references from Symmetric_Spectral.


### SOVA1-23. The import chain is needlessly linear

*structure, impact low, confidence high, ~10 lines.*  
Locations: Rademacher.thy:5 `imports Convex_Subgradients`; Jensen_Lemma.thy:5 `imports Alexandrov`; Sup_Convolution.thy:5 `imports Jensen_Lemma`

A name-level usage analysis shows:
- Rademacher uses nothing from Convex_Subgradients.
- Jensen_Lemma uses only subdiff, subdiffD and subdiff_nonempty (Convex_Subgradients), nothing from Rademacher, Moreau_Envelope or Alexandrov.
- Sup_Convolution uses Jensen_Lemma and Alexandrov only in the dead corollaries supconv_jensen and supconv_alexandrov.
So the 7.2k lines build as a single chain, although Rademacher can run in parallel with Convex_Subgradients, Jensen_Lemma in parallel with Rademacher, Moreau_Envelope and Alexandrov (the longest path), and Sup_Convolution right after Convex_Subgradients.

Evidence: The script output was: `Moreau_Envelope uses from Rademacher: rademacher_vec_AE`, `Jensen_Lemma uses from Convex_Subgradients: subdiff subdiffD subdiff_nonempty`, `Sup_Convolution uses from Alexandrov: semiconvex_alexandrov`, `Sup_Convolution uses from Jensen_Lemma: jensen_lemma`, and no other cross-use.

Suggested action: Set the imports as follows:
- Rademacher: HOL-Analysis.Analysis
- Moreau_Envelope: Convex_Subgradients Rademacher
- Jensen_Lemma: Convex_Subgradients (or Semiconvex_Functions)
- Sup_Convolution: Semiconvex_Functions
- a new Jensen_Alexandrov theory, holding semiconvex_jensen_alexandrov_point: Alexandrov Jensen_Lemma
Theorem_On_Sums then imports Jensen_Alexandrov Sup_Convolution.


### SOVA1-24. Small proofs that one library lemma would replace

*simplification, impact low, confidence high, ~110 lines.*  
Locations: Rademacher.thy:357-358, 616-617, 729-730, 741-742, 781-782, 986-987; Moreau_Envelope.thy:78-79, 93-94; Moreau_Envelope.thy:73-82; Sup_Convolution.thy:495-502; Rademacher.thy:723-733, 1682-1694; Rademacher.thy:1669-1675 (integral_box_cbox_eq); Rademacher.thy:2077-2105 bounded_linear_coord_combination; Rademacher.thy:2497-2508 lipschitz_component; :2529-2538; Rademacher.thy:1711-1723 content_cbox_translate; Rademacher.thy:1166-1195 (pos/neg halves of AE_zero_of_box_integrals_zero); Rademacher.thy:418, 484, 655, 795 sort {euclidean_space,banach}

Each item is a few lines that a single library lemma (or symmetry) would replace:
- `eventually (\<lambda>t. t \<noteq> 0) (at 0)` is proved 8 times by `unfolding eventually_at by (intro exI[of _ 1]) auto`.
- `filterlim (\<lambda>t. t *\<^sub>R h) (at 0) (at 0/at_right 0)` is proved 4 times.
- cbox - box \<in> null_sets lborel is re-derived.
- A finite sum of bounded linear maps is shown bounded linear by hand in 29 lines.
- A coordinate projection is shown Lipschitz in 12 lines.
- The final componentwise step of rademacher_vec_AE is re-done by hand.
- Translation invariance of content is re-proved.
- The negative half of AE_zero_of_box_integrals_zero is a copy of the positive half.
- The sort {euclidean_space,banach} is redundant.

Evidence: Library equivalents for the items above, in order:
- HOL/Topological_Spaces.thy:627 eventually_neq_at_within
- HOL/Analysis/Lebesgue_Measure.thy:1308 null_sets_cbox_Diff_box
- HOL/Real_Vector_Spaces.thy:1698 bounded_linear_sum + bounded_linear_inner_left
- HOL/Analysis/Euclidean_Space.thy:173 Basis_le_norm
- HOL/Analysis/Weierstrass_Theorems.thy:1289 differentiable_componentwise_within
- HOL/Analysis/Henstock_Kurzweil_Integration.thy:3458 content_image_affinity_cbox (m=1)
- HOL/Analysis/Topology_Euclidean_Space.thy:1629 `instance euclidean_space \<subseteq> banach`

Suggested action: Use the library lemmas and add one local `filterlim_scaleR_at_0` lemma. Apply the pos half to -g. Drop `banach` from the sorts.


### SOVA1-25. The library statements match the standard theorems

*faithfulness, impact low, confidence high, ~0 lines.*  
Locations: Rademacher.thy:2421 rademacher_AE; Alexandrov.thy:1223 convex_alexandrov; Jensen_Lemma.thy:396 jensen_lemma

rademacher_AE is Evans-Gariepy Thm 3.2 for globally Lipschitz real f; the 'locally Lipschitz' claim in the abstract is reported separately. convex_alexandrov is Alexandrov's theorem for finite convex f on R^n, with a symmetric psd form and a Peano remainder outside a negligible set. jensen_lemma is CIL User's Guide Lemma A.3, with 'positive measure' as 'not negligible'. Its set requires maximality over the whole ball cball xi r rather than a local maximum, so the formal set is smaller and the statement stronger. The hypothesis 0 < rho is derivable from small and bnd (if rho <= 0 then phi xi <= m), so it is redundant but harmless.

Evidence: Statements read at the cited lines.

Suggested action: None beyond the abstract wording.


### SOVA1-26. Difference quotient along a line tends to the derivative: proved twice (66 + 38 lines), and HOL has it

*library_duplicate, impact low, confidence medium, ~90 lines.*  
Locations: Second_Order_Viscosity_Analysis/Moreau_Envelope.thy:56-121 has_derivative_dir_limit; Second_Order_Viscosity_Analysis/Rademacher.thy:343-380 dquot_tendsto_vector_derivative

Both convert has_derivative into convergence of (F (x + t h) - F x) /\<^sub>R t through has_derivative_at, an eventual-equality rewrite, Lim_transform_eventually, tendsto_norm_zero_iff and Lim_null. has_derivative_dir_limit is the composition of the chain rule (\<lambda>t. x + t *\<^sub>R h) with the 1-D statement. The 1-D statement is in HOL up to the shift y = t + h.

Evidence: HOL/Deriv.thy:972 has_vector_derivative_within_1D: "(f has_vector_derivative f') (at x within S) \<longleftrightarrow> ((\<lambda>y. (f y - f x) /\<^sub>R (y - x)) \<longlongrightarrow> f') (at x within S)". Shift with LIM_offset_zero; chain rule via diff_chain_at / derivative_eq_intros.

Suggested action: Prove dquot_tendsto_vector_derivative from has_vector_derivative_within_1D. Prove has_derivative_dir_limit in about 5 lines as chain rule + that lemma, and put it in Rademacher next to it.


### SOVA1-27. Global hypotheses where the standard results are local

*generalisation, impact low, confidence medium, ~60 lines.*  
Locations: Rademacher.thy:2421 rademacher_AE (global Lipschitz); Alexandrov.thy:1223 convex_alexandrov, :1398 semiconvex_alexandrov_bounded (convex_on UNIV); Jensen_Lemma.thy:396 jensen_lemma (semiconvex on UNIV); Sup_Convolution.thy:300 supconv_tendsto (needs continuous (at x) u; usc at x suffices); Convex_Subgradients.thy:17 subdiff (only real_inner needed for subdiffI/D, subdiff_monotone, convex_subdiff)

The textbook statements are local: Lipschitz on an open set; convex or semiconvex on an open ball. STATUS.md:1108-1125 already discusses localising the Jensen/Alexandrov layer, and the abstract claims the local Rademacher. Jensen and Alexandrov are only consumed after the sup-convolution makes functions globally semiconvex, so this is library polish, not a blocker. supconv_tendsto's proof uses only the upper half of continuity.

Evidence: supconv_tendsto proof: only `rb'` (u y < u x + \<eta>/2) is used from continuity; the lower bound comes from supconv_ge.

Suggested action: Low priority. Do the local Rademacher (cheap; see the abstract finding) and weaken supconv_tendsto to usc. Leave Alexandrov and Jensen global unless a consumer needs the local versions.


### SOVA1-28. PLAN §6.2 'is it already in HOL?' sweep for Convex_Subgradients (still open there): result

*other, impact low, confidence medium, ~0 lines.*  
Locations: Second_Order_Viscosity_Analysis/Convex_Subgradients.thy:17-398 (17 statements)

Checked against HOL-Analysis (Convex, Convex_Euclidean_Space, Starlike, Derivative, Lipschitz) and the AFP; the only AFP hits are listed in the evidence. There is no subdifferential, proximal map, Moreau envelope, Minty or nonexpansiveness development, nor a closed/frontier epigraph lemma (HOL has only mem_epigraph and convex_epigraph[I]). The only redundant items are the norm identities midpoint_dist_identity and prox_step_expand (instances of dot_norm/dot_norm_neg; see the squared-norm finding). This closes the Convex_Subgradients bullet of §6.2. Elsewhere in the cluster the sweep found the duplicates reported above: has_derivative_at_alt, linear_inj_bounded_below_pos, linear_injective_isomorphism, Sup_add_eq, inner_sum_left_Basis, lipschitz_on_continuous_on, has_vector_derivative_within_1D, eventually_neq_at_within, null_sets_cbox_Diff_box.

Evidence: grep in HOL for 'subgradient|subdiff|subdifferential' finds only supporting_hyperplane_* (Starlike.thy:4971ff, used by subdiff_nonempty). The AFP grep for proximal|moreau|subdifferential|subgradient|semiconvex|alexandrov finds no relevant entry. Projected_Gradient_Descent has gradients and projections for differentiable f only. Rademacher_Series is unrelated.

Suggested action: Record this in the completion note of PLAN_RESTRUCTURING_2 §10 ('What is left').


## SOVA2

I read all 9,588 lines of the five theories. Lemma usage was measured with grep over the whole repository, using a script that ignores text blocks (scratchpad/py/strip.py). I did not use PIDE: no session was running, only the HOL and Pure heaps exist, and another agent's full `isabelle build` was compiling HOL-Analysis on the 4-core machine at the time. None of the proposed simplifications has been machine-checked.

What the cluster proves:
- Theorem_On_Sums is the algebraic core of the Crandall-Ishii theorem on sums. It has the semiconvexity calculus for the doubled functional (doubled_functional_semiconvex), the Jensen∩Alexandrov point (semiconvex_jensen_alexandrov_point), block diagonality of the product second-order form via ray limits (product_form_block_diagonal), the matrix inequality at an interior maximum (sums_matrix_inequality), the sup-convolution jet transfer (supconv_dominates_shift) and the jet-to-local-maximum step (superjet_local_max). It also holds an unused "limit half of Lemma 3.1" block, wrongly cited to the paper.
- Doubling_Of_Variables is three former theories joined together (`section` at lines 1, 4052 and 5107). It covers:
  - existence, location and penalty bounds for the doubled maximiser;
  - the slices of the doubled jet and the block-matrix linearity, symmetry and norm bounds;
  - Jensen's tilt, the shifted Jensen families, the jet transfer back through the sup-convolution, and the two-domain and localisation glue;
  - a block of elementary real-number helpers.
  Almost everything exists twice: once for the quadratic penalty (α/2)‖x−y‖² and once for a general penalty Pn (the `_gen` lemmas). By grep, the quadratic copy feeds only paper theorems that are themselves never used, plus Crandall_Ishii_Sums, which is not an ancestor of the main theorem.
- Soft_Penalty defines soft_pen κ d = (κ/2)‖d‖² − κ(√(‖d‖²+1)−1) and quartic_pen. It gives the exact second-order expansion and jet (soft_pen_jet_field), Hessian symmetry and bounds, 3κ-Lipschitz gradient, semiconcavity, coercivity and the doubling instances. It is a two-theory concatenation (`section` at line 646).
- Test_Functions defines test_fun_at and test_fun_C2, their closure lemmas (constant, scale, affine, quadratic and quartic shift) and the quadratic minorant/majorant lemmas. It also holds `expandable` and convex_expandable, which have nothing to do with test functions.
- Viscosity_Solutions defines generic sub- and supersolution predicates for an abstract ereal-valued F, with the level 1 hard-wired. None of its four lemmas is used, and the generic predicates are used only by five unused bridge equations in Relative_Arbitrage/Viscosity_Definitions.

Main structural problems:
1. Massive parallel duplication between the quadratic chain and the general-penalty chain.
2. About 1,500 lines of the quadratic chain are dead for Theorem 1.1.
3. Many library re-proofs, including one lemma (norm_Pair_le) that shadows a HOL-Analysis lemma of the same name.
4. Supconv-only, linear-algebra and paper-proof glue lemmas sit in the wrong theories.
5. Paper-specific prose (Theorem 4.2(a), Definition 3.1, Case 2, display (4.4), ell_op, eq36_rhs) and text blocks left behind by mechanical moves, some about unrelated subjects (the Brownian "Euler kernel", pball_exit).
6. Test_Functions and Viscosity_Solutions sit at the end of a fully serial import chain (… → Theorem_On_Sums → Doubling_Of_Variables → Soft_Penalty → Test_Functions → Viscosity_Solutions), although they need only three small helper lemmas from it.


### SOVA2-1. The whole doubling/theorem-on-sums chain exists twice: quadratic penalty and general penalty (_gen)

*clone, impact high, confidence high, ~1400 lines.*  
Locations: Doubling_Of_Variables.thy:183-251 doubling_diagonal_max/off_diagonal/penalty_bound vs 289-339 *_gen; Doubling_Of_Variables.thy:346 doubling_maximiser_exists vs 396 doubling_maximiser_exists_gen; Theorem_On_Sums.thy:376 semiconvex_penalty vs Doubling_Of_Variables.thy:796 semiconvex_penalty_gen; Theorem_On_Sums.thy:457 doubled_functional_semiconvex vs Doubling_Of_Variables.thy:4054 doubled_functional_semiconvex_gen; Theorem_On_Sums.thy:900 sums_matrix_inequality vs Doubling_Of_Variables.thy:957 sums_matrix_inequality_gen; Doubling_Of_Variables.thy:1222/1262 sums_gives_ordering/sums_ordering_at_interior_max vs 1044/1073 *_gen; Doubling_Of_Variables.thy:1530-1576 linear_block_fst/snd, sym_block_fst/snd vs 1107-1210 *_gen (plus Theorem_On_Sums.thy:1111-1226 linear_slice_*/sym_slice_*); Doubling_Of_Variables.thy:1585/1594 transpose_matrix_block_* vs 3596/3607 *_gen; 2012/2019 block_*_matrix_apply vs 3571/3579 *_gen; Doubling_Of_Variables.thy:1699/1845 doubled_jet_slice_fst/snd vs 1737/1883 *_gen; Doubling_Of_Variables.thy:3022-3093 block_form_bound_*/norm_block_matrices_bounded vs 3102-3174 *_gen; Doubling_Of_Variables.thy:3183/3529 penalty_gradient_nearby_bound/upper vs 3641/3658 *_gen; Doubling_Of_Variables.thy:3231 tilted_doubled_jet_slices vs 3305 _gen; 3421 tilted_doubled_hessian_nonpositive vs 3375 _gen; 5191 tilted_doubled_psd_ordering vs 5251 _gen; Doubling_Of_Variables.thy:4241 sums_psd_at_interior_max vs 4199 _gen; 4310 doubled_supconv_jet_exists_shifted vs 4103 _gen; 4829 shifted_jensen_family vs 4963 _gen; 1377 shifted_annulus_bound_split vs 920 _gen

Every step of the doubling and theorem-on-sums argument is proved once for P(d)=(α/2)‖d‖² and again for a general Pn with jet (G,Z). The proof bodies are near-verbatim: same define P/Pop, WP, g0, scWP, rem, expTheta, blk, pdiag structure. In several pairs the quadratic statement is a literal instance of the general one after beta-reduction, with Pn := λd. (α/2)*(norm d)², κ := α, sc := convex_on of the constant 0, G := α(x−y), Z := α I. Examples: tilted_doubled_hessian_nonpositive is tilted_doubled_hessian_nonpositive_gen at P = λd. (α/2)*(norm d)²; the doubling_*_gen lemmas need only P0 = simp. The duplication is wider than plan section 2.11 assumed.

Evidence: tilted_doubled_hessian_nonpositive_gen (3375): fixes a b :: 'a ⇒ real, P :: 'a ⇒ real; the mx hypothesis "(a (fst y) + b (snd y) - P (fst y - snd y)) + pt • y ≤ …" becomes the quadratic version's "(a (fst y) + b (snd y) - (α/2) * (norm (fst y - snd y))²) + pt • y ≤ …" (3428) at P := λd. (α/2)*(norm d)²; the two 50-line proofs are line-for-line identical. shifted_jensen_family (4829-4956) and _gen (4963-5090) are both 128 lines and differ only in Pn vs (α/2)‖·‖², and in calling shifted_annulus_bound_split vs _gen.

Suggested action: Keep one chain. Either delete the quadratic copy where it is dead (next finding), or state it as one-line corollaries of the _gen lemmas. First lift the _gen chain to 'a::euclidean_space with Z a symmetric linear map rather than a matrix (it is only turned into a matrix in transpose_matrix_*/norm_block_matrices_bounded); then the 'a-typed quadratic lemmas in Theorem_On_Sums are instances too.


### SOVA2-2. Doubling_Of_Variables (5,330 lines) is three concatenated theories plus a junk drawer

*structure, impact high, confidence high, ~5330 lines.*  
Locations: Doubling_Of_Variables.thy:1 section 'Doubling of variables'; Doubling_Of_Variables.thy:4052 section 'Jets of the doubled sup-convolution'; Doubling_Of_Variables.thy:5107 section 'From a bounded family to the contradiction'; Doubling_Of_Variables.thy:3858-4050 subsection 'Elementary bookkeeping'

The file has three `section` commands, 16 self-referential 'X lives in Doubling_Of_Variables' pointer texts, and empty subsections. These are signs of concatenation by mechanical moves (plan phase 3). Its content falls into four groups: (a) maximiser existence/location and penalty bounds (generic in Pn); (b) doubled jets, slices and block matrices (the theorem-on-sums ordering); (c) the Jensen/sup-convolution family; (d) real-arithmetic and topology helpers.

Evidence: grep 'section' gives 1, 4052, 5107; 23 'lives in' texts, 16 pointing to the file itself.

Suggested action: After deduplication, split into Doubling_Maximiser (a), Doubled_Jets (b, merged with the slice and block part of Theorem_On_Sums), and Doubled_Sup_Convolution (c, next to Sup_Convolution). Distribute (d) to Power_Inequalities-style helpers or inline it. Expect about 2,000 lines in total.


### SOVA2-3. The quadratic-penalty route is consumed only by unused paper theorems and by Crandall_Ishii_Sums

*dead_code, impact high, confidence medium, ~1500 lines.*  
Locations: Relative_Arbitrage/Comparison_Principle.thy:13 comparison_supconv_doubling_complete (never used); Relative_Arbitrage/Comparison_Principle.thy:217 comparison_supconv_maximiser_complete (never used); Relative_Arbitrage/Comparison_Localisation.thy comparison_env_complete, comparison_supconv_complete (never used); Doubling_Of_Variables.thy: tilted_doubled_jet_slices 3231, tilted_doubled_hessian_nonpositive 3421, tilted_doubled_psd_ordering 5191, shifted_jensen_family 4829, doubled_supconv_jet_exists 4270, norm_block_matrices_bounded 3071, block_fst/snd_matrix_apply 2012/2019, transpose_matrix_block_fst/snd 1585/1594, penalty_gradient_nearby_bound/upper 3183/3529, block_matrices_from_jet 4586, sums_psd_from_jet 4404, jensen_tilt_threshold_pos/small_enough 2475/2481, choice4 2980

In Relative_Arbitrage, the quadratic-specific lemmas above are cited only inside comparison_supconv_doubling_complete and comparison_supconv_maximiser_complete (Comparison_Principle). block_matrices_from_jet and doubled_jet_slices_at_max are cited only inside comparison_env_complete and comparison_supconv_complete (Comparison_Localisation). Those four theorems are never used. The live route to max_principle_boundary_holds goes through comparison_supconv_maximiser_complete_gen, comparison_from_localised_maximiser_gen/_soft and the soft-penalty lemmas. The only other consumer of the quadratic route is Crandall_Ishii_Sums, which is not an ancestor of Theorem 1.1. So most of the quadratic chain, including the Theorem_On_Sums lemmas it rests on (sums_matrix_inequality, doubled_functional_semiconvex(_shifted), semiconvex_penalty, penalty_exact, linear_slice_*, sym_slice_*), is either a leftover of the superseded quadratic proof of Theorem 4.2(a) or library material for Crandall_Ishii_Sums.

Evidence: Text-stripped grep of Relative_Arbitrage, giving the enclosing lemma of every use. tilted_doubled_jet_slices: [comparison_supconv_doubling_complete, comparison_supconv_maximiser_complete]. shifted_jensen_family: [comparison_supconv_maximiser_complete]. block_matrices_from_jet: [comparison_env_complete, comparison_supconv_complete]. Each of those four theorems has exactly one code occurrence, its own statement.

Suggested action: Decide whether Crandall_Ishii_Sums stays. If it does, keep only what it needs and derive it from the _gen chain. Delete the four dead paper theorems and the quadratic lemmas that only they use. Confirm with the semantic dependency analysis before deleting.


### SOVA2-4. shifted_jensen_family and shifted_jensen_family_gen are two 128-line verbatim copies

*clone, impact medium, confidence high, ~128 lines.*  
Locations: Doubling_Of_Variables.thy:4829 shifted_jensen_family; Doubling_Of_Variables.thy:4963 shifted_jensen_family_gen

Same parameter lemmas (shifted_family_parameters), same bnd/gen/halfgen/small blocks, same 28-line definition of P, same choice4 skolemisation. The only difference is (α/2)‖·‖² vs Pn and the semiconvexity constant 2α vs 2κ. The quadratic version is the _gen version at Pn = (α/2)‖·‖², κ = α (sc holds because (α/2)‖d‖² − (α/2)‖d‖² = 0 is convex).

Evidence: Compare lines 4880-4955 with 5010-5089: identical text up to the penalty term.

Suggested action: Delete shifted_jensen_family (its only consumer, comparison_supconv_maximiser_complete, is dead), or derive it from _gen in about 5 lines.


### SOVA2-5. nearby_of_convergent_shifted and nearby_of_convergent_shifted_neg are identical up to + vs −

*clone, impact medium, confidence high, ~67 lines.*  
Locations: Doubling_Of_Variables.thy:2329 nearby_of_convergent_shifted; Doubling_Of_Variables.thy:2401 nearby_of_convergent_shifted_neg

Two 67-line proofs differ only in Mz i + δ *R mat 1 versus Mz i − δ *R mat 1; the estimate uses only ‖δ·I‖ = δN. One lemma parametrised by a fixed matrix S (with Q (Pz i) (Mz i + δ *R S)), instantiated at S = mat 1 and S = −mat 1, replaces both. The lemma could also be stated in any normed space.

Evidence: Lines 2337-2394 and 2409-2466 are character-identical except for the sign in five places.

Suggested action: Merge into nearby_of_convergent_shift S, and keep the two names as one-line instances if wanted.


### SOVA2-6. Two-sided and one-sided superjet→local-max lemmas proved separately

*clone, impact medium, confidence high, ~130 lines.*  
Locations: Theorem_On_Sums.thy:1239 superjet_local_max; Doubling_Of_Variables.thy:535 superjet_local_max_onesided; Doubling_Of_Variables.thy:614 jet_imp_local_min_test vs 566 jet_imp_local_min_test_onesided; Doubling_Of_Variables.thy:3935 onesided_of_tendsto_gen

superjet_local_max_onesided assumes only ∀c>0. eventually (quotient < c), which onesided_of_tendsto_gen (3935) derives from the tendsto hypothesis. Its 30-line proof is the same as superjet_local_max's, which also contains a no-op line 1257 `have "X 0 = 0 ∨ X 0 ≠ 0" by simp`. jet_imp_local_min_test (46 lines) and jet_imp_local_min_test_onesided (47 lines) are identical except for the lemma called. The same 'quotient < c ⇒ increment < c‖k‖²' step is repeated a fifth time in supconv_onesided_descent (4537-4549) and again in Crandall_Ishii_Sums.superjet_of_transfer (CIS:486).

Evidence: superjet_local_max = superjet_local_max_onesided[OF onesided_of_tendsto_gen[OF lim]] (D := numerator). jet_imp_local_min_test proof lines 625-658 equal 578-611 with superjet_local_max_onesided swapped in.

Suggested action: Keep only the one-sided versions. Derive the tendsto forms in 2 lines, or delete them and call the one-sided lemma at the use sites.


### SOVA2-7. Re-proofs of HOL-Analysis lemmas, one of them shadowing the library name

*library_duplicate, impact medium, confidence high, ~90 lines.*  
Locations: Doubling_Of_Variables.thy:3473 norm_Pair_le = HOL-Analysis Product_Vector.thy:722 norm_Pair_le (same name and statement; shadows it; used by Relative_Arbitrage/Pair_Path_Laws.thy:463); Theorem_On_Sums.thy:162/167 norm_Pair_right_zero/left_zero = Product_Vector norm_Pair2/norm_Pair1 [simp]; Theorem_On_Sums.thy:333 convex_on_scaleR_nonneg = Convex.thy:445 convex_on_cmul (semiconvex_penalty_gen at DoV:830 already uses convex_on_cmul); Doubling_Of_Variables.thy:1518 linear_of_bounded_linear_prod = bounded_linear.linear / Linear_Algebra.thy:489 linear_conv_bounded_linear (used at DoV:1114 itself); Soft_Penalty.thy:345 abs_norm_diff_le = Real_Vector_Spaces.thy:867 norm_triangle_ineq3; Doubling_Of_Variables.thy:2168 bounded_seq_limit_point = heine_borel class axiom bounded_imp_convergent_subsequence (Elementary_Metric_Spaces.thy:1556); Soft_Penalty.thy:152 inner_sq_over_norm_sq_le = Inner_Product.thy:107 Cauchy_Schwarz_ineq + power2_norm_eq_inner (and re-proved again inline at Soft_Penalty.thy:1090-1097); Soft_Penalty.thy:336 norm_le_soft_R = NthRoot.thy:652 real_sqrt_sum_squares_ge1 [of _ 1]

Lemmas that are library lemmas, or direct instances of them. norm_Pair_le is the worst case: the theory-local copy hides Product_Vector.norm_Pair_le for every importer.

Evidence: Product_Vector.thy:722 `lemma norm_Pair_le: shows "norm (x, y) ≤ norm x + norm y"`; DoV:3473 `lemma norm_Pair_le: … shows "norm ((a, b) :: 'a × 'b) ≤ norm a + norm b"`. Product_Vector.thy: `norm_Pair1 [simp]: "norm (0,x) = norm x"` and `norm_Pair2 [simp]: "norm (x,0) = norm x"`.

Suggested action: Delete and cite the library lemmas: norm_Pair_le, norm_Pair1/2 (simp), convex_on_cmul, bounded_linear.linear, norm_triangle_ineq3, bounded_imp_convergent_subsequence, Cauchy_Schwarz_ineq, real_sqrt_sum_squares_ge1.


### SOVA2-8. test_fun_quadratic_minorates and test_fun_quadratic_dominates are mirror images (~120 lines each)

*clone, impact medium, confidence high, ~110 lines.*  
Locations: Test_Functions.thy:751 test_fun_quadratic_minorates; Test_Functions.thy:877 test_fun_quadratic_dominates

Same proof: has_derivative_at_alt bound, r = min e d, f t along the segment, DERIV_nonpos_imp_nonincreasing. Only the signs of f and δ differ. With a two-line test_fun_at_uminus (test_fun_at φ g H x ⟹ test_fun_at (−φ) (−g) (−H) x), dominates follows from minorates applied to −φ.

Evidence: Lines 760-869 vs 885-988: the deriv/small/vv/expand blocks are identical modulo sign.

Suggested action: Add test_fun_at_uminus and derive test_fun_quadratic_dominates from test_fun_quadratic_minorates.


### SOVA2-9. Sup-convolution-only lemmas sit in Theorem_On_Sums / Doubling_Of_Variables instead of Sup_Convolution

*misplacement, impact medium, confidence high, ~250 lines.*  
Locations: Theorem_On_Sums.thy:1003 supconv_dominates_shift, 1026 supconv_jet_transfer, 1054 neg_jet_quotient, 1071 supconv_neg_jet_transfer; Doubling_Of_Variables.thy:4441 supconv_bound_transfer, 4458 supconv_local_max_transfer, 4478 supconv_local_max_transfer_ball, 4516 supconv_onesided_descent, 4707 supconv_attain_radius, 4744 supconv_le_of_local_bound_usc, 2808 supconv_radius_uniform

These lemmas mention only supconv and use only supconv_def, supconv_bdd_above and supconv_ge from Sup_Convolution. Plan II §3.3 sent this material to Sup_Convolution, but it ended up in Theorem_On_Sums and Doubling_Of_Variables. supconv_radius_uniform does not even mention supconv: it is sqrt arithmetic. The A *v h statements could be stated with A :: 'a ⇒ 'a so that they fit Sup_Convolution's 'a::euclidean_space setting.

Evidence: supconv_dominates_shift proof: `unfolding supconv_def by (intro cSUP_upper supconv_bdd_above[OF B e]) simp`.

Suggested action: Move them to Sup_Convolution, a 'Sup_Convolution_Jets' section, generalised to 'a.


### SOVA2-10. Pure linear algebra in Doubling_Of_Variables belongs in Symmetric_Matrix_Spectra; test-function helpers belong in Test_Functions

*misplacement, impact medium, confidence high, ~200 lines.*  
Locations: Doubling_Of_Variables.thy:2075 polarization_symmetric, 2094 parallelogram_norm, 2101 symmetric_form_bound, 2149 symmetric_form_bound_unit, 2985 norm_matrix_le_of_form_bound, 3010 hessian_abs_bound_of_two_sided, 1518 linear_of_bounded_linear_prod; Symmetric_Matrix_Spectra/Symmetric_Spectral.thy:550 (text: 'polarization_symmetric, … symmetric_form_bound_unit live in Doubling_Of_Variables'); Doubling_Of_Variables.thy:102 quadratic_grad_derivative_at, 3862 quartic_coeff_assoc; Soft_Penalty.thy:648 quartic_grad_derivative (used only by Test_Functions)

Polarisation, the parallelogram law and 'quadratic-form bound ⟹ operator/matrix-norm bound' mention no doubling. The lower session even keeps a pointer saying they live in the upper one. quartic_grad_derivative and quartic_coeff_assoc are used only by Test_Functions.test_fun_C2_quartic_shift / test_fun_at_quartic_shift, and quadratic_grad_derivative_at only by jet_test_fun_C2.

Evidence: Code use of quartic_grad_derivative: Test_Functions:557 only. quartic_coeff_assoc: Test_Functions:548, 616 only.

Suggested action: Move the linear-algebra lemmas to Symmetric_Matrix_Spectra (Symmetric_Spectral or Matrix_Algebra), and the three helpers to Test_Functions or Matrix_Algebra.


### SOVA2-11. Test_Functions and Viscosity_Solutions sit at the end of a fully serial chain they do not need

*build_time, impact medium, confidence high, ~30 lines.*  
Locations: Test_Functions.thy:5 `imports Soft_Penalty`; Soft_Penalty.thy:5 `imports Doubling_Of_Variables …`; Doubling_Of_Variables.thy:5 `imports Theorem_On_Sums …`; Relative_Arbitrage/Viscosity_Definitions.thy:6-7

Test_Functions uses from its ancestors only quadratic_grad_derivative_at (DoV), quartic_coeff_assoc (DoV), quartic_grad_derivative (Soft_Penalty), and Matrix_Algebra/Outer_Products facts. Yet the chain Rademacher → Moreau → Alexandrov → Jensen → Sup_Convolution → Theorem_On_Sums → Doubling_Of_Variables (5,330 lines) → Soft_Penalty must finish before Test_Functions, Viscosity_Solutions and the whole paper operator/definition layer (Viscosity_Definitions, Operator_Envelopes, Value_Function_*) can start. Similarly, the core of Soft_Penalty (definition, jet, Hessian, Lipschitz) needs only Matrix_Algebra/Outer_Products and convex_on_norm_lift; only the doubling_*_soft instances need DoV.

Evidence: Name-level usage list: Test_Functions uses from SOVA only the three helpers above. Soft_Penalty uses from DoV doubling_penalty_bound_gen, doubling_maximiser_exists_gen, norm_lt_of_penalty_bound_gen, diagonal_max_increments, onesided_of_dominated, convex_on_norm_lift (all in its doubling-instance part).

Suggested action: Make Test_Functions import Symmetric_Matrix_Spectra.Matrix_Algebra + Outer_Products, after moving the 3 helpers. Split Soft_Penalty into Soft_Penalty (function and its calculus, independent of DoV) and Soft_Penalty_Doubling (lines ~1290-1575, above DoV).


### SOVA2-12. Statements fixed to real^'n although they mention no matrix

*generalisation, impact medium, confidence high, ~600 lines.*  
Locations: Doubling_Of_Variables.thy:4054 doubled_functional_semiconvex_gen, 4103 doubled_supconv_jet_exists_shifted_gen, 4270 doubled_supconv_jet_exists, 4310 doubled_supconv_jet_exists_shifted, 4829/4963 shifted_jensen_family(_gen), 4441 supconv_bound_transfer, 4516 supconv_onesided_descent, 4782 supconv_extend_far_le, 4804/4820 attain_gate_of_positive/atu_of_positive_ball, 4639/4675/5139 *_supconv, 3807 compact_frontier_nonempty; Doubling_Of_Variables.thy:33-34 header claim

The DoV header says 'Everything is at 'a::euclidean_space except the 33 statements that produce a matrix'. In fact 55 statements are at real^'n, and 15 of them mention no matrix at all. Every lemma they depend on (supconv, supconv_semiconvex', semiconvex_jensen_alexandrov_point, semiconvex_penalty_gen, second_order_interior_max) is at 'a. The _gen chain's penalty Hessian Z could be a symmetric linear map, which would put the whole general chain at 'a and make the 'a-typed quadratic lemmas instances. compact_frontier_nonempty needs only a nontrivial euclidean space (DIM('a) > 0), not CARD('n).

Evidence: Script over DoV statements: '55 15 [compact_frontier_nonempty, doubled_functional_semiconvex_gen, doubled_supconv_jet_exists_shifted_gen, …]'.

Suggested action: Re-type the 15 matrix-free statements at 'a::euclidean_space; replace Z :: real^'n^'n by a linear Z :: 'a ⇒ 'a in the _gen chain and convert to a matrix only in the norm/transpose lemmas. Correct the header.


### SOVA2-13. Generic viscosity layer hard-wires level 1 and does not cover Definition 3.1

*generalisation, impact medium, confidence high, ~110 lines.*  
Locations: Viscosity_Solutions.thy:25-26, 29-79; Relative_Arbitrage/Viscosity_Definitions.thy:88-126 visc_subsol_env2, visc_supersol_env2, visc_supersol_lsc, supersol_jet

The 'generic' predicates fix the right-hand side 1 ('the equation this session was written for is F = 1'), which is paper-specific. Level c or F ≤ 0 would be generic. They also use only the test_fun_at class and touch u itself. The paper's Definition 3.1 uses C² test functions, the envelopes u*/u_* and boundary conditions; its formal counterparts (visc_*_env2, visc_supersol_lsc, supersol_jet) still exist only in the paper session with ell_op hard-wired, though plan §3.3 listed _env2 and supersol_jet_gen for this theory. Combined with the dead bridge lemmas, the abstraction serves no consumer.

Evidence: Viscosity_Solutions.thy:35 `F (g x) H ≤ 1`; :43 `1 ≤ F (g x) H`. The bridges visc_subsol_eq_gen etc. are unused.

Suggested action: Parametrise the level (or use F ≤ 0 with F − 1 at the paper). Add the test_fun_C2 (_env2) and envelope variants generically, and route the paper predicates and at least one consumer through them. Otherwise drop the theory.


### SOVA2-14. Paper-specific prose in a session advertised as paper-free

*documentation, impact medium, confidence high, ~200 lines.*  
Locations: Theorem_On_Sums.thy:14, 67, 955, 957 ('Lemma 3.1 of \<^cite>\<open>LaiShkolnikovSoner\<close>'); Doubling_Of_Variables.thy:3889-3896 (eq36_rhs k L M, F*(0,M)), 4226-4239 ('the paper's quartic penalty', strict_contradiction_of_shifts_any_p, Theorem 4.2(a)), 4386-4387, 4630 (subsection 'Theorem 4.2(a), end to end'), 4701-4702 (ell_op_env_strict_contradiction), 4778 ('Definition 3.1's gated set'), 2700-2707 & 2780-2786 (gated on {u>0}); Test_Functions.thy:31-43 (ell_op_lsc, ell_op_usc, ell_op, Operator_Envelopes), 53-62 (Definition 3.1, value function, 'the paper's'), 73-77 (Theorem 1.1), 100-101, 327-333 (Theorem 4.3, display (4.4), ell_op_usc_scale, ell_op_usc_conj_rot), 471, 475, 487-496 (Theorem 4.2, visc_subsol, supersol_jet, ell_op_elliptic_le), 579-580, 738-749 & 1041 (Case 2/Case 1), 1150-1153 ('as in the paper'), 1289; Soft_Penalty.thy:1329-1330 (supersol_no_vanishing_jet_onesided), 1436-1439 (comparison_from_localised_maximiser_soft); Viscosity_Solutions.thy:25-26 ('the equation this session was written for is F = 1')

The ROOT describes the session as general machinery, yet the prose names paper results (Theorem 4.2(a), Theorem 4.3, Definition 3.1, display (4.4), Case 1/2), the paper's operator constants (ell_op, ell_op_lsc/usc, eq36_rhs k L) and lemma names that exist only in Relative_Arbitrage (comparison_env_from_jets, comparison_supconv_sequence_complete, env_strict_contradiction_of_shifted_limits, supersol_no_vanishing_jet, subsol_shifted_bound, …). These are forward references to a later session.

Evidence: grep 'Theorem 4\|Definition 3\|the paper\|ell_op\|display (\|Case 2\|eq36' over the 5 files gives 27 hits; the referenced lemmas are defined in Relative_Arbitrage/Comparison_*.thy and Operator_Envelopes.thy.

Suggested action: Rewrite the prose generically ('a comparison argument', 'the operator F'), or move the paragraphs to the Relative_Arbitrage theories that prove those results.


### SOVA2-15. Text blocks left behind by mechanical moves (unrelated or attached to the wrong lemma)

*documentation, impact medium, confidence high, ~150 lines.*  
Locations: Doubling_Of_Variables.thy:3867-3871 ('The Euler kernel … law (sbmpair S T) … Brownian path') in front of dist_pair_le; Test_Functions.thy:685-696 (section 'The ball exit time along a continuous path', pball_exit, pexit, Ito-side supplier) in front of test_fun_at_shifted_quadratic; Test_Functions.thy:31-43 (collection of viscosity notions and ell_op envelopes; belongs to RA Viscosity_Definitions); Test_Functions.thy:1150-1153 (envelopes of F packaged on the product metric space, ereal; belongs to RA Operator_Envelopes) in front of convex_expandable; Doubling_Of_Variables.thy:4701-4705 (θ-scaling gap) in front of supconv_attain_radius; 4777-4780 (antitonicity of viscosity predicates in Ω) in front of supconv_extend_far_le; 4797-4802 (usc attainment) in front of attain_gate_of_positive; 4770-4773 orphan; Doubling_Of_Variables.thy:4226-4239 (supersol_no_vanishing_jet) in front of sums_psd_at_interior_max; 3979-3984 in front of exists_eps_aux; 4023-4028 in front of theta_exists_aux; 3519-3527 in front of penalty_gradient_nearby_upper; 4091-4094 orphan; Soft_Penalty.thy:1290-1295 (subsection 'Jensen's semiconvexity input, for a general penalty') in front of soft_pen_zero; Test_Functions.thy:467-469, 738-749, 991-994, 1041-1045 (each describes a neighbouring lemma, not the one that follows)

Prose that ended up in the wrong place during the moves of Plan II (phases 3 and 9). Some blocks concern subjects of other sessions (Brownian Euler kernel, path exit times, operator envelopes).

Evidence: Test_Functions.thy:685 `section \<open>The ball exit time along a continuous path\<close>` followed at 698 by `lemma test_fun_at_shifted_quadratic`; DoV:3867 'The Euler kernel varies only through the frozen matrix…' followed by `lemma dist_pair_le`.

Suggested action: Move each block back to the theory and lemma it describes: path exit time to Continuous_Path_Spaces/Path_Exit_Times or RA Pair_Path_*, Euler kernel to RA Value_Function_Euler_Construction, envelopes to RA Operator_Envelopes or Viscosity_Definitions. Delete orphans.


### SOVA2-16. Lemmas with no code use anywhere in the repository

*dead_code, impact medium, confidence medium, ~900 lines.*  
Locations: Theorem_On_Sums.thy:51 doubling_antitone (and therefore doubling_penalty_squeeze:33, doubling_ring_identity:28), 72 doubling_penalty_tendsto_zero, 112 antitone_bdd_below_convergent_at_top, 156 block_diagonal_test, 630 second_order_form_unique, 966 doubling_limit_maximises, 1071 supconv_neg_jet_transfer (and therefore neg_jet_quotient:1054), 1095 sums_ord_of_inequality; Doubling_Of_Variables.thy:156 doubling_partial_max_fst, 166 doubling_partial_min_snd, 217 doubling_grad_nonzero (and therefore doubling_off_diagonal 203, doubling_diagonal_max 183), 257 doubling_dist_bound (and therefore doubling_penalty_bound 236), 308 doubling_off_diagonal_gen (and therefore doubling_diagonal_max_gen 289), 1352 shifted_jensen_smallness, 1970 doubled_jet_slices_at_max, 2307 gradient_sequences_align_of_bound (and therefore gradient_sequences_align 2288), 2529 tilt_sequence_admissible, 2552 positive_separation_of_value_gap, 4639 doubling_grad_lower_bound_supconv (and therefore doubling_grad_norm_lower_bound 2245, doubling_grad_lower_bound 2214, doubling_ge_diagonal ToS:20), 4675 doubling_maximiser_supconv (and therefore doubling_maximiser_exists 346), 5139 doubled_value_gap_supconv; Soft_Penalty.thy:1441 doubling_maximiser_supconv_soft; Test_Functions.thy:209 test_fun_at_affine; Viscosity_Solutions.thy:45 visc_sol_gen, 85 visc_subsol_gen_mono, 90 visc_supersol_gen_mono, 95 visc_subsol_gen_env_imp, 100 visc_supersol_gen_env_imp; Relative_Arbitrage/Viscosity_Definitions.thy:170-190 visc_subsol_eq_gen etc. (the bridges into Viscosity_Solutions are themselves unused)

Count of occurrences outside text blocks, across all .thy files: these names occur only in their own statement, or only inside another dead lemma. The 'limit half of Lemma 3.1' (Theorem_On_Sums.thy:10-143 and 955-991) is entirely unused. The first ~120 lines of Doubling_Of_Variables (partial max, diagonal and penalty bounds for the quadratic penalty) are unused. The generic viscosity layer is purely decorative: nothing is stated or proved through it.

Evidence: strip.py count over .thy files with text blocks removed: e.g. 'doubling_penalty_tendsto_zero 1 S/Theorem_On_Sums:1', 'visc_subsol_eq_gen 1 RA/Viscosity_Definitions:1', 'positive_separation_of_value_gap 1 S/Doubling_Of_Variables:1'.

Suggested action: Delete, or keep only those that are deliberate library API (for example doubling_maximiser_exists_gen consumers). Cross-check with the semantic unused_thms run.


### SOVA2-17. Theorem_On_Sums states no theorem on sums; the assembled statement lives in Crandall_Ishii_Sums, which redoes the per-stage Jensen argument

*structure, impact medium, confidence medium, ~800 lines.*  
Locations: Theorem_On_Sums.thy:1 (contents: doubling algebra, semiconvexity calculus, block diagonality, sums_matrix_inequality); Crandall_Ishii_Sums.thy:613 theorem_on_sums_stage (~520 lines), 1139 theorem_on_sums_quadratic, 2039 theorem_on_sums_quadratic_closed; Crandall_Ishii_Sums.thy:680-705 (re-proves the annulus bound of Doubling_Of_Variables.thy:1377 shifted_annulus_bound_split inline); Doubling_Of_Variables.thy:4829/4963 shifted_jensen_family(_gen) + RA Comparison_Principle assembly

The theorem on sums is spread over Theorem_On_Sums (matrix inequality), Doubling_Of_Variables (orderings and psd at interior maxima, slices, Jensen families) and Crandall_Ishii_Sums (classical statement with semijets). There are two independent assemblies of the same Jensen/sup-convolution stage argument: one in Crandall_Ishii_Sums (not an ancestor of Theorem 1.1) and one through shifted_jensen_family_gen into Relative_Arbitrage/Comparison_Principle. The paper session never uses the classical statement.

Evidence: Crandall_Ishii_Sums.theorem_on_sums_stage calls doubled_supconv_jet_exists_shifted, tilted_doubled_hessian_nonpositive, sums_gives_ordering, norm_matrix_le_of_form_bound from DoV, and redoes pen1-pen3 (= shifted_annulus_bound_split).

Suggested action: Pick one assembly. Ideally state the theorem on sums once, in the semijet vocabulary of Crandall_Ishii_Sums, for a general penalty, and have the paper's comparison principle consume that statement. Otherwise rename Theorem_On_Sums to what it is (e.g. Doubled_Functional_Algebra) and mark Crandall_Ishii_Sums as an optional library extra.


### SOVA2-18. Proof glue of the paper's Theorem 4.2(a) inside the paper-free library

*misplacement, impact medium, confidence medium, ~500 lines.*  
Locations: Doubling_Of_Variables.thy:4639 doubling_grad_lower_bound_supconv, 4675 doubling_maximiser_supconv, 5139 doubled_value_gap_supconv, 4782 supconv_extend_far_le, 4804 attain_gate_of_positive, 4820 atu_of_positive_ball ('gated set {u>0}' of Definition 3.1); Doubling_Of_Variables.thy:2709 doubled_maximiser_over_UNIV_snd, 2763 mxK_of_UNIV_snd, 2956 fary_of_pin, 3837 two_domain_gap; Soft_Penalty.thy:1399 pin_of_penalty_bound, 1441/1534 *_supconv_soft; Doubling_Of_Variables.thy:3862-4049 quartic_coeff_assoc, small_multiple_exists, shift_limit_absurd, shift_limit_absurd2, gap_split_aux, exists_eps_aux, eps_mono_aux, theta_exists_aux; 2475-2542 jensen_tilt_*, tilt_sequence_*; Soft_Penalty.thy:465 exists_small_rho_aux

These statements mention no paper constant, which is why the plan's 'statement names no paper constant' rule moved them. But they are fixed to the paper's proof shapes: θ·u versus −w, the gate {u>0}, the two-domain K ⊆ interior K', and the constants 6ρ, 2σ+τ+τ' and (1−θ)·2B. Several are linarith one-liners (shift_limit_absurd(2), interior_radius_pos) whose only consumers are in Relative_Arbitrage/Comparison_*.

Evidence: atu_of_positive_ball concludes `z ∈ {q. 0 < u q}`; shift_limit_absurd is `using assms by linarith`; theta_exists_aux is used only by Comparison_Principle.max_principle_boundary_holds.

Suggested action: Move the θ/gate/two-domain lemmas and the *_aux arithmetic to the paper's comparison layer (Comparison_Strictness/Comparison_Principle), or inline them. Keep in the library only shape-free statements such as doubling_maximiser_exists_gen.


### SOVA2-19. The paper's path toolkit imports Doubling_Of_Variables apparently only for norm_Pair_le

*structure, impact medium, confidence medium, ~20 lines.*  
Locations: Relative_Arbitrage/Pair_Path_Space.thy:30-31 imports Second_Order_Viscosity_Analysis.Sup_Convolution, Doubling_Of_Variables; Relative_Arbitrage/Pair_Path_Laws.thy:463 (rule norm_Pair_le); Relative_Arbitrage/Value_Function_Euler_Construction.thy (dist_pair_le)

The only cluster names the path layer uses are norm_Pair_le, which is a duplicate of the HOL lemma, and, in Value_Function_Euler_Construction, dist_pair_le. Removing the DoV copy and the two imports would let the 16,500-line path toolkit build without waiting for SOVA's doubling/Jensen chain. Sup_Convolution use not checked.

Evidence: Name-level usage map: RA/Pair_Path_Laws uses only norm_Pair_le from the cluster; Pair_Path_Space uses nothing.

Suggested action: Delete DoV.norm_Pair_le and move dist_pair_le to Continuous_Path_Spaces (or prove it via norm_Pair_le). Then try dropping the SOVA imports from Pair_Path_Space.


### SOVA2-20. Semiconvexity calculus re-proved in several places

*clone, impact low, confidence high, ~120 lines.*  
Locations: Theorem_On_Sums.thy:512 doubled_functional_semiconvex_shifted vs Doubling_Of_Variables.thy:882 semiconvex_shift_perturb; Theorem_On_Sums.thy:506 norm_sq_diff_shift vs the `sq` step at Doubling_Of_Variables.thy:889 and Crandall_Ishii_Sums.thy:1438 norm_sq_diff_expand; Doubling_Of_Variables.thy:903-911 (`aff` in semiconvex_shift_perturb) vs Sup_Convolution.thy:182 convex_on_affine_inner; Theorem_On_Sums.thy:387-394 and Doubling_Of_Variables.thy:809-816 (the identities d, s, proved twice); Doubling_Of_Variables.thy:4139-4155 inline nsplit vs 1319 norm_sq_prod_split; also 932-939 in shifted_annulus_bound_split_gen; and 1330 shifted_annulus_bound re-proved inside 920 shifted_annulus_bound_split_gen

doubled_functional_semiconvex_shifted is doubled_functional_semiconvex followed by semiconvex_shift_perturb; it re-proves the shift identity and the affine convexity inline (48 lines). Both versions of the penalty semiconvexity prove ‖a−b‖² and ‖a+b‖² expansions by hand. The library has dot_norm / dot_norm_neg (Inner_Product.thy:359/362). norm_sq_prod_split exists in the same theory but is re-derived from norm_prod_sq twice.

Evidence: doubled_supconv_jet_exists_shifted_gen (4160-4166) already uses `semiconvex_shift_perturb[OF base dnn]`, so the specialised ToS lemma is unnecessary.

Suggested action: Replace doubled_functional_semiconvex_shifted with semiconvex_shift_perturb applied to doubled_functional_semiconvex. Prove `aff` with convex_on_affine_inner. Cite norm_sq_prod_split, and shifted_annulus_bound inside the _gen split lemma.


### SOVA2-21. Four convex_on-composed-with-a-linear-map lemmas instead of one

*generalisation, impact low, confidence high, ~60 lines.*  
Locations: Theorem_On_Sums.thy:301 convex_on_fst; Theorem_On_Sums.thy:317 convex_on_snd; Theorem_On_Sums.thy:348 convex_on_proj_sum; Doubling_Of_Variables.thy:780 convex_on_prod_diff

Each lemma proves convex_on UNIV h ⟹ convex_on UNIV (h ∘ L) for L = fst, snd, fst+snd and fst−snd, with the same 15-line convex_onI argument. HOL-Analysis (Convex.thy) has no general composition-with-linear lemma, so one `convex_on_linear_compose: linear L ⟹ convex_on UNIV h ⟹ convex_on UNIV (λx. h (L x))` covers all four.

Evidence: grep of HOL-Analysis Convex.thy finds convex_on_add/cmul/dist/... but no composition with linear maps. All four proofs use convex_onI + convex_onD + an algebra_simps identity for L((1−t)x+ty).

Suggested action: Prove convex_on_linear_compose once, in Sup_Convolution or Convex_Subgradients, and make the four lemmas instances or delete them.


### SOVA2-22. positive_separation_of_value_gap proves uniform continuity by hand (74 lines), next to a 3-line use of it

*simplification, impact low, confidence high, ~74 lines.*  
Locations: Doubling_Of_Variables.thy:2552 positive_separation_of_value_gap; Doubling_Of_Variables.thy:2844 uniform_modulus_on_compact

The sequential-compactness/subsequence contradiction proof gives exactly what compact_uniformly_continuous gives directly: take d with dist p q < d ⟹ |v p − v q| < γ. uniform_modulus_on_compact, 290 lines later, already does this in 20 lines. The lemma is also unused (see the dead-code finding).

Evidence: uniform_modulus_on_compact proof: `compact_uniformly_continuous[OF cv cC]` then `uniformly_continuous_onE`.

Suggested action: Delete, or reprove in ~6 lines from compact_uniformly_continuous.


### SOVA2-23. second_order_form_unique repeats the ray argument of expansion_ray_limit

*clone, impact low, confidence high, ~68 lines.*  
Locations: Theorem_On_Sums.thy:630 second_order_form_unique (68 lines, unused); Theorem_On_Sums.thy:704 expansion_ray_limit

Both build the same filterlim (λt. t *R v) (at 0) (at_right 0), the same quotient rescaling and the same eventual equality. Uniqueness follows from expansion_ray_limit applied to both forms plus tendsto_unique.

Evidence: Lines 648-655 and 713-720 are identical.

Suggested action: Delete second_order_form_unique (it is unused), or derive it in 5 lines.


### SOVA2-24. Small repeated arithmetic and preamble patterns

*clone, impact low, confidence high, ~80 lines.*  
Locations: Doubling_Of_Variables.thy:1352 shifted_jensen_smallness vs 2481 jensen_tilt_small_enough (same dd<X/(2r) ⇒ 2·dd·r<X); Soft_Penalty.thy:423-498 soft_R_gt_one, soft_grad_coeff_pos, soft_gap_pos, 1258 soft_grad_norm_eq, 1064 soft_hess_quadform_bounds (the step 1<R ⇒ 0<1−1/R repeated); Soft_Penalty.thy:507 sqrt_shift_diff_bound re-proves sqrt_norm_sq_add_one_ge_one inline (a1, b1); Doubling_Of_Variables.thy:4686-4691, Soft_Penalty.thy:1451-1456 and 1550-1555 (identical supconv continuity preamble, 3 times); Doubling_Of_Variables.thy:354-363, 404-413, 452-461 (compact_Times/cfst/csnd preamble, 3 times)

Copy-pasted multi-line patterns that should each be one lemma.

Evidence: See the cited line ranges; the copies are verbatim.

Suggested action: Introduce soft_R_coeff_pos (0 < 1 − 1/√(‖d‖²+1) for d ≠ 0) and one 'doubled sup-convolution is continuous on K×K' lemma, and remove the copies.


### SOVA2-25. soft_pen and almost all of Soft_Penalty fixed to real^'n (plan G3 still open)

*generalisation, impact low, confidence high, ~700 lines.*  
Locations: Soft_Penalty.thy:41 quartic_pen, 54 soft_pen, 315 soft_grad, 413 soft_shrink and 43 further lemmas

47 of the 55 real^'n statements in Soft_Penalty mention no matrix: soft_pen, soft_grad, soft_shrink, the expansion/jet_form, Lipschitz bounds, coercivity and the doubling instances. Only soft_hess, soft_hess_entry/sym/quadform/bounds and quartic_grad_derivative need matrices. inner_sq_over_norm_sq_le, norm_le_soft_R, sqrt_norm_sq_add_one_ge_one and soft_R_lipschitz hold in any real_inner space.

Evidence: Script count: 'Soft_Penalty 55 47 [quartic_pen, soft_pen, inner_sq_over_norm_sq_le, …]'.

Suggested action: Re-type soft_pen/soft_grad/soft_shrink and their lemmas at 'a::euclidean_space (or real_inner where possible). Keep the matrix Hessian at real^'n, and state soft_pen_jet_field with a linear Hessian map plus a matrix corollary.


### SOVA2-26. expandable / convex_expandable live in Test_Functions

*misplacement, impact low, confidence high, ~140 lines.*  
Locations: Test_Functions.thy:1144 expandable, 1155 convex_expandable; Test_Functions.thy:73-77 (its explanatory text, 1,070 lines earlier, in front of test_fun_C2_imp_test_fun_at)

A purely geometric hypothesis of the paper's uniqueness clause. Its consumers are Relative_Arbitrage/Value_Function_Uniqueness, Comparison_Two_Domain and the Statement session. Plan §3.3 proposed a separate Expandable_Sets.thy; it was put into Test_Functions instead, and its text block was left far from the definition.

Evidence: grep: expandable is used in Statement/Theorem_1_1_Statement, Statement_Auxiliary, RA/Value_Function_Uniqueness, RA/Comparison_Two_Domain.

Suggested action: Create Expandable_Sets.thy on Symmetric_Matrix_Spectra (it needs orthogonal_matrix only), or put it in the paper's lowest layer since the Statement displays it. Move the text block next to the definition.


### SOVA2-27. Stale or false references in prose

*documentation, impact low, confidence high, ~30 lines.*  
Locations: Theorem_On_Sums.thy:14, 67, 955, 957: 'Lemma 3.1 of \<^cite>\<open>LaiShkolnikovSoner\<close>' should be Crandall–Ishii–Lions (root.bib key CrandallIshiiLions); the paper has no such lemma; Doubling_Of_Variables.thy:530 onesided_of_tendsto (actual: onesided_of_tendsto_gen); 2892-2893 doubling_maximiser_value_transfer, norm_lt_of_penalty_bound (actual: *_gen); 2009 matrix_apply_eq (exists nowhere); Doubling_Of_Variables.thy:1581 and 2010: matrix_of_symmetric / matrix_vec_apply said to be in Theorem_On_Sums; they are in Symmetric_Matrix_Spectra.Matrix_Algebra (Theorem_On_Sums.thy:1042 itself says so); Test_Functions.thy:477 'test_fun_C2 lives in Viscosity_Definitions' (it is defined at Test_Functions.thy:64); Test_Functions.thy:739 test_fun_strict_minorate_zero_grad (typo; actual …minorant…); 1281 matvec_add_right' (exists nowhere); Doubling_Of_Variables.thy:33-34 '33 statements … stay at real^'n' (actually 55, 15 without a matrix); Viscosity_Solutions.thy:81-83 'This is the only fact stated here' (four lemmas follow); 13-15 'boundary clauses' (none in this theory); Symmetric_Matrix_Spectra/Symmetric_Spectral.thy:550, 554, 565, 661 and Matrix_Algebra.thy:2317, 2671 (lower session pointing up to Doubling_Of_Variables lemmas)

References to renamed or nonexistent lemmas, a wrong citation, wrong 'lives in' claims and wrong counts.

Evidence: A script listing every \<open>identifier_with_underscore\<close> in the five files that is not defined in the repository found doubling_maximiser_value_transfer, matrix_apply_eq, norm_lt_of_penalty_bound, onesided_of_tendsto, test_fun_strict_minorate_zero_grad, matvec_add_right'. root.bib has @article{CrandallIshiiLions}.

Suggested action: Fix the citation to \<^cite>\<open>CrandallIshiiLions\<close>; update or delete the stale names and the wrong 'lives in' claims.


### SOVA2-28. Pointer-only texts and empty subsections

*documentation, impact low, confidence high, ~120 lines.*  
Locations: Doubling_Of_Variables.thy: 16 self-referential 'X lives in Doubling_Of_Variables' texts (e.g. 4096, 4177, 4187, 4197, 4268, 4308, 4364, 4380, 4395, 4399, 4580, 4621, 5130, 5165, 5183, 5318); empty subsections 4372, 4393, 4397, 4578, 4619, 5121, 5163, 5316, 5320; Soft_Penalty.thy: 13 self-referential pointers (714, 780, 828, 850, 961, 1047, 1062, 1141, 1251, 1288, 1300, 1365, 1391); empty subsections 778, 1573; Test_Functions.thy: 471, 475, 487, 1279 (empty or pointer-only sections); Theorem_On_Sums.thy:1040-1042 (subsection with only a pointer)

Left over from the mechanical moves. In the generated document they read as noise, and the self-references are vacuous.

Evidence: Script count: Doubling_Of_Variables self-pointers 16 of 23; Soft_Penalty 13 of 18.

Suggested action: Delete the self-referential pointers and the empty subsections. Keep cross-theory pointers only where they help a reader.


### SOVA2-29. Near-library helpers: one-line rearrangements and wrappers

*library_duplicate, impact low, confidence medium, ~110 lines.*  
Locations: Doubling_Of_Variables.thy:3873 dist_pair_le (norm_Pair_le on differences; dist_Pair_Pair + sqrt_sum_squares_le_sum); Doubling_Of_Variables.thy:2279 tendsto_of_norm_bound (wrapper of Lim_null_comparison; duplicated by Crandall_Ishii_Sums.thy:547 tendsto_of_dist_bound); Doubling_Of_Variables.thy:2094 parallelogram_norm and Theorem_On_Sums.thy:506 norm_sq_diff_shift (rearrangements of Inner_Product.thy dot_norm/dot_norm_neg); Theorem_On_Sums.thy:367 norm_prod_sq (norm_prod_def/norm_Pair); Doubling_Of_Variables.thy:3714 bounded_on_compact, 446 doubling_upper_bound_exists (compact_imp_bounded ∘ compact_continuous_image); Doubling_Of_Variables.thy:2980 choice4 (generic HOL skolemisation; `metis` one-liner)

Thin restatements of library facts that add names without content.

Evidence: tendsto_of_norm_bound's proof is `rule Lim_null_comparison[OF _ D]` plus `simp`.

Suggested action: Inline at the use sites or cite the library. If choice4 is kept, move it to a generic utility theory.


### SOVA2-30. soft_pen: Lipschitz bound, Hessian symmetry and Hessian quadratic form proved the long way

*simplification, impact low, confidence medium, ~150 lines.*  
Locations: Soft_Penalty.thy:355 soft_R_lipschitz (51 lines); Soft_Penalty.thy:970 soft_hess_sym (22 lines); Soft_Penalty.thy:993 soft_hess_quadform (51 lines, entrywise double sums); Soft_Penalty.thy:1156 soft_shrink_lipschitz (71 lines)

soft_R_lipschitz: √(‖x‖²+1) = norm (x,1) by norm_Pair, which soft_pen_gap (Soft:687) already uses. Since (x,1)−(y,1) = (x−y,0), the bound is norm_triangle_ineq3 with norm_Pair2, a few lines. soft_hess_sym: Test_Functions.thy:529 proves the same kind of fact for a·I + b·outer_prod d d in one line (`simp add: transpose_add transpose_scalar op_transpose`). soft_hess_quadform: Outer_Products has outer_prod_mv [simp] (outer_prod u v *v x = (v•x) *R u) and op_matvec, so h•(soft_hess *v h) is a 2-3 line simp with matrix_vector_mult_add_rdistrib / scaleR_matrix_vector_assoc.

Evidence: Outer_Products.thy:22 outer_prod_mv [simp]; :26 transpose_outer_prod [simp]; :54 op_transpose. Test_Functions.thy:527-529 Qsym.

Suggested action: Reprove with the outer-product library and the norm (d,1) representation. Not machine-checked: verify in PIDE.


### SOVA2-31. quad_bdd_above/below_on_bounded: 88 lines for 'continuous on a bounded set is bounded'

*simplification, impact low, confidence medium, ~80 lines.*  
Locations: Doubling_Of_Variables.thy:44 quad_bdd_above_on_bounded (54 lines); Doubling_Of_Variables.thy:114 quad_bdd_below_on_bounded (34 lines)

The quadratic is continuous, so it is bounded on the compact closure of a bounded K (compact_continuous_image, compact_imp_bounded, bounded_pos), which gives both bounds at once. The current proof does Cauchy-Schwarz and onorm estimates by hand, and the 'below' version re-derives itself from the 'above' one through a matrix-negation lemma.

Evidence: Both lemmas only assume `bounded K`.

Suggested action: Prove one lemma `bounded ((λz. p•(z−yh) + (z−yh)•(M *v (z−yh))/2) ` K)` via continuity and closure, and derive the two obtains from it.


### SOVA2-32. Derivatives of quadratic and quartic test functions computed repeatedly

*clone, impact low, confidence medium, ~200 lines.*  
Locations: Test_Functions.thy:637 test_fun_at_quadratic and 698 test_fun_at_shifted_quadratic (re-derive what Matrix_Algebra.thy:2600 has_derivative_quadratic_form / 2629 quadratic_test_derivative provide); Doubling_Of_Variables.thy:102 quadratic_grad_derivative_at = Matrix_Algebra.thy:2654 quadratic_test_grad_derivative at an arbitrary point (same proof); Test_Functions.thy:538-551 vs 602-618 (d2/d3/d4 of the quartic shift, duplicated between test_fun_C2_quartic_shift and test_fun_at_quartic_shift); Test_Functions.thy:249-275 vs 366-386 and 297-317 vs 400-415 (gradient chain rule and Hessian conjugation duplicated between test_fun_at_affine and test_fun_C2_affine); Test_Functions.thy:136 test_fun_at_scaleR vs 172 test_fun_C2_scaleR

Each closure lemma is proved separately for test_fun_at and for test_fun_C2, copying the derivative calculations. test_fun_at_shifted_quadratic recentres to a normal form so that test_fun_at_quadratic applies. A variant of jet_test_fun_at at an arbitrary point (quadratic_test_derivative already holds at every y), plus test_fun_C2_add_const, would give it directly.

Evidence: quadratic_test_derivative (Matrix_Algebra:2629) states the derivative of p•(z−x)+((z−x)•(H *v (z−x)))/2 at every y. quadratic_grad_derivative_at and quadratic_test_grad_derivative have identical proofs.

Suggested action: Generalise quadratic_test_grad_derivative to an arbitrary point (y instead of x) in Matrix_Algebra and delete the DoV copy. Factor the gradient-chain and Hessian-conjugation identities of the affine lemmas into two helper lemmas. Delete the unused test_fun_at_affine.


### SOVA2-33. Slice restriction of a doubled jet implemented three times

*clone, impact low, confidence medium, ~150 lines.*  
Locations: Theorem_On_Sums.thy:172/208 expansion_restrict_fst/snd (with inline filterlim proof `emb`); Doubling_Of_Variables.thy:1653/1663 filterlim_slice_fst/snd + 1699/1845 doubled_jet_slice_fst/snd; Doubling_Of_Variables.thy:1737/1883 doubled_jet_slice_fst_gen/snd_gen; Theorem_On_Sums.thy:844 penalty_exact vs Doubling_Of_Variables.thy:1634/1803 penalty_difference_identity/_snd

Restricting a product expansion to the slices (h,0) and (0,h) is done generically in Theorem_On_Sums (for any Ψ) and then again twice in Doubling_Of_Variables for the doubled functional with quadratic and general penalty. The filterlim facts are re-proved inline in ToS although DoV has them as lemmas. The penalty's exact expansion is proved twice in different shapes.

Evidence: expansion_restrict_fst concludes the slice expansion for arbitrary Ψ; doubled_jet_slice_fst is that lemma at Ψ = a∘fst + b∘snd − (α/2)‖fst−snd‖² plus penalty_difference_identity.

Suggested action: Keep expansion_restrict_fst/snd (moved after filterlim_slice_*) and derive the doubled slice lemmas from them plus the penalty jet (doubled_penalty_jet already provides the general one).


### SOVA2-34. Cross-session duplicates of semicontinuity and quadratic-form facts

*clone, impact low, confidence medium, ~70 lines.*  
Locations: Doubling_Of_Variables.thy:2666 usc_extend_const_below vs Semicontinuous_Analysis/Semicontinuity.thy:196 usc_extension_bounded; Doubling_Of_Variables.thy:3010 hessian_abs_bound_of_two_sided vs Symmetric_Matrix_Spectra/Symmetric_Spectral.thy:530 semiconvex_hessian_abs_bound (same closing abs_leI/linarith step); Doubling_Of_Variables.thy:4744 supconv_le_of_local_bound_usc vs Relative_Arbitrage/Comparison_Localisation.thy:1317 supconv_le_of_local_bound (same conclusion; DoV text 4741 says so); Doubling_Of_Variables.thy:2279 tendsto_of_norm_bound vs Crandall_Ishii_Sums.thy:547 tendsto_of_dist_bound

usc_extend_const_below re-proves the constant-below extension of an ε-form usc function off a closed set, and the DoV text at 2662 cites usc_extension_bounded. Second_Order_Viscosity_Analysis cannot import Semicontinuous_Analysis: that session is based on HOL-Probability and SOVA's ROOT lists only Symmetric_Matrix_Spectra. As a result SOVA and Crandall_Ishii_Sums (usc_open_lt, usc_attains_sup_compact) each carry their own ad-hoc usc formulas.

Evidence: Both proofs: case z ∈ K uses the usc ε-ball and the bound C < c; case z ∉ K uses an open complement (DoV) or infdist (Semicontinuity).

Suggested action: Either base Semicontinuity on HOL-Analysis (it needs nothing probabilistic for these lemmas) and import it into SOVA, or keep one copy in SOVA and have Semicontinuous_Analysis cite it. Delete the RA supconv_le_of_local_bound in favour of the usc version.


### SOVA2-35. Generic topology and analysis helpers in Doubling_Of_Variables

*misplacement, impact low, confidence medium, ~250 lines.*  
Locations: Doubling_Of_Variables.thy:2788 cont_pos_near, 2844 uniform_modulus_on_compact, 3738 cball_subset_interior_of_far_from_boundary, 3775 cball_prod_subset_of_far_from_boundary, 3837 two_domain_gap, 3688 continuous_extension_bounded (Tietze wrapper), 3714 bounded_on_compact, 3807 compact_frontier_nonempty, 2192 nearby_of_convergent, 3484 bounded_seq_limit_point_triple, 2500-2527 tilt_sequence_*

Statements about sets, continuity and sequences, with no doubled functional in them.

Evidence: None of the statements mentions a penalty or a doubled function.

Suggested action: Collect them in a small 'Topology_Helpers' theory low in SOVA, or replace them by library facts (compact_uniformly_continuous, Tietze, bounded_imp_convergent_subsequence).


### SOVA2-36. doubled_penalty_jet hand-rolls 'o(|h|²) composed with a bounded linear map'

*generalisation, impact low, confidence medium, ~100 lines.*  
Locations: Doubling_Of_Variables.thy:661 doubled_penalty_jet (107 lines)

The proof shows R(fst k − snd k)/‖k‖² → 0 from R(h)/‖h‖² → 0 with an explicit ε/4 argument and the bound ‖fst k − snd k‖ ≤ 2‖k‖. A lemma 'R h/‖h‖² → 0 at 0, L bounded linear ⟹ R (L k)/‖k‖² → 0' (with the case L k = 0 handled by R 0 = 0) would cover it. The same rescaling also appears in the slice lemmas. The lemma is fixed to real^'n only because the conclusion writes Z *v.

Evidence: Lines 693-765 are a generic ε-δ argument; only `R0: R 0 = 0` and norm_fst_le/norm_snd_le are used.

Suggested action: Extract the generic little-o composition lemma (in Sup_Convolution or Alexandrov, where the o(|h|²) expansions live) and state doubled_penalty_jet at 'a with a linear Z.


## CTM

Continuous_Time_Martingales is the paper-free probability session built on top of the AFP Martingales entry. It covers six areas.
(1) Discrete-time theory: quadratic variation `qvar` of a square-integrable nat-indexed martingale with the compensator theorem `qvar_compensates` (Quadratic_Variation), and discrete optional stopping `nat_stopped_martingale` (Optional_Sampling).
(2) Sampling a real-indexed martingale along a monotone grid. Time_Discretisation, Sampled_Martingale and Sampled_Quadratic_Variation each do this, and they overlap.
(3) Doob's weak and L2 maximal inequalities. Through `horizon_sq_int_martingale` they give an integrable, square-integrable running-maximum bound `Dsup` (Doob_Inequality).
(4) Continuous-time optional sampling and stopping by dyadic ceilings plus dominated convergence (Optional_Sampling), with the adaptedness side condition discharged in Stopped_Adaptedness.
(5) A transfer calculus for the martingale property: sums, congruence, time change, bounded-linear images, vector and matrix components, products, infinite products, pushforwards, conditioning on an event, restriction to a full-measure event, and modifications (Martingale_Algebra, Martingale_Transfer, Modification_Transfer, Natural_Filtration).
(6) Assorted measure-theoretic helpers: power inequalities, essential infimum, Vitali's theorem, semidirect kernel products, exit times as stopping times, integrability and independence criteria.

Every theory was read in full. The PIDE MCP was not used: no PIDE session was running, the only built heaps are Pure/HOL, and a concurrent `isabelle build ... Relative_Arbitrage` (4 cores, about 6 GB) was already building HOL-Analysis and the rest. All claims were therefore checked by reading the sources and grepping HOL, HOL-Analysis, HOL-Probability and the AFP.

Main conclusions:
* The session is not "done" in the sense of plan §2.11.
  * The sampling of a martingale along a grid is proved four times.
  * Discrete optional stopping is proved twice; the copy in Quadratic_Variation (about 300 lines) is unused and also duplicates the AFP's Fair_Games_Theorem (2026-06-12).
  * The continuous optional-sampling argument is cloned a third time, in path-free form, in Relative_Arbitrage/Path_Stopping_Times (with `pre_sigma_of`, which duplicates the AFP's Doob_Convergence `pre_sigma`).
  * Five dyadic-grid constructions coexist.
  * G4 (essential infimum) was only half executed.
  * Martingale_Algebra re-proves AFP `martingale.add`/`martingale.diff` and HOL `integral_bounded_linear`, and contains vector and matrix copies of the same lemmas where one euclidean_space version would do.
* Moment_Bounds is dead code. The real Eq. (2.7) is `fourth_moment_bound_bounded` in Continuous_Path_Spaces/Increment_Moments.
* Paper prose ("Eq. (2.7)", "Lemma 2.3", "Proposition 2.4", `ito_volatile_market`, "the market locales") is spread over 12 of the 18 theories.
* Several text blocks are orphans or stale (an empty section, a "Superadditivity" paragraph with no lemma, references to nonexistent `mtrans`), and the root.tex abstract misstates Vitali's theorem.
* Import hygiene serialises a 6-theory chain whose links are partly unused (Optional_Sampling does not use Doob_Inequality; Stopped_Adaptedness does not use Optional_Sampling).

Things that are fine:
* Vitali/uniform integrability, Doob's maximal inequality and the semidirect product exist nowhere in HOL or the AFP. The AFP has only the upcrossing inequality and no uniform integrability, so these are genuine contributions.
* A single CTM session is the right granularity. It needs internal re-layering (proposed in the structure finding), not a split.


### CTM-1. Sampling a martingale along a monotone grid is proved four times; the grid Dynkin identities twice

*clone, impact high, confidence high, ~160 lines.*  
Locations: Continuous_Time_Martingales/Time_Discretisation.thy:32-99 (locale time_grid, locale sampled_martingale, sublocale D: sq_int_martingale); Continuous_Time_Martingales/Optional_Sampling.thy:303-332 (locale sampled_cont_martingale, sublocale D: martingale); Continuous_Time_Martingales/Sampled_Martingale.thy:32-64 (martingale_sampled), :71-80 (nat_filtered_of_sampled); Continuous_Time_Martingales/Sampled_Quadratic_Variation.thy:28-41 (sq_int_martingale_sampled); Time_Discretisation.thy:106 qvar_sampled_fun vs Sampled_Quadratic_Variation.thy:50 qvar_sampled_eq; Time_Discretisation.thy:116 grid_expected_qvar vs Sampled_Quadratic_Variation.thy:83 expectation_sq_sampled; Time_Discretisation.thy:132 grid_qvar_compensates vs Sampled_Quadratic_Variation.thy:60 qvar_compensates_sampled

Four places prove the same fact: given martingale M F (0::real) Y and a monotone t :: nat => real with 0 <= t k, the sampled process is a nat-indexed martingale for F∘t.
* The two sublocale proofs (TD:69-99, OS:307-332) are character-for-character the same: filtered_measure.intro, sigma_finite_filtered_measure.intro, adapted_process.intro, martingale.intro. The TD one only adds square-integrability.
* Sampled_Martingale.martingale_sampled proves it a third time, and Sampled_Quadratic_Variation.sq_int_martingale_sampled is the TD sublocale again.
* The transferred results are also duplicated: grid_expected_qvar ≡ expectation_sq_sampled (rearranged), grid_qvar_compensates ≡ qvar_compensates_sampled (with qvar unfolded), and qvar_sampled_fun ≡ qvar_sampled_eq.
* time_grid's hypotheses (0 <= t 0 and t n <= t (Suc n)) are just a repackaging of Sampled_Martingale's (∀k. 0 <= t k, mono t).
* Martingale_Algebra.martingale_time_change (:189) is the real-to-real version of the same statement.

Plan §2.11 praises the locale layering time_grid -> sampled_martingale -> sq_int_martingale but missed that Sampled_Martingale and Sampled_Quadratic_Variation re-do it in parallel.

Evidence: TD:64 `locale sampled_martingale = martingale M F "0 :: real" Y + time_grid t ... assumes Y_sq_integrable`; OS:303 `locale sampled_cont_martingale = martingale M F "0 :: real" Z + time_grid t`; SM:35-37 `assumes X: "martingale M F (0::real) X" and t0: "⋀k. 0 ≤ t k" and tmono: "mono t" shows "martingale M (λk. F (t k)) (0::nat) (λk. X (t k))"`; the TD:72-98 and OS:310-331 proof texts are identical apart from Y/Z.

Suggested action: Keep one lemma: martingale_sampled, optionally generalised to any linearly ordered index with a monotone map into [0,∞), which also subsumes martingale_time_change. Prove the time_grid-based sublocales by `martingale_sampled[OF ...]` in 3 lines. Delete qvar_sampled_fun, grid_expected_qvar and grid_qvar_compensates in favour of the Sampled_Quadratic_Variation versions, or the reverse. Merge Time_Discretisation, Sampled_Martingale and Sampled_Quadratic_Variation into a single theory, e.g. Sampled_Martingales.


### CTM-2. Discrete optional stopping proved twice: Quadratic_Variation's stopped section is unused, and both copies duplicate AFP Fair_Games_Theorem

*dead_code, impact high, confidence high, ~300 lines.*  
Locations: Continuous_Time_Martingales/Quadratic_Variation.thy:306-602 (stopped, stopped_0, stopped_incr, qvar_stopped, locale stopped_sq_int_martingale with Tgt/Tgt_iff/Tgt_sets_F/Tgt_sets_M/ind_Tgt_measurable_F/stopped_incr_ind, stopped_measurable_F, stopped_measurable, stopped_integrable, stopped_sq_integrable, stopped_incr_integrable, martingale_stopped, sq_int_martingale_stopped, stopped_expectation_sq_qvar, stopped_qvar_expectation_le); Continuous_Time_Martingales/Optional_Sampling.thy:38-299 (locale nat_stopped_martingale: Tgt, Tgt_sets_F, Tgt_sets_M, inc, stopped_eq_sum, stopped_integrable, stopped_expectation, set_stopped_expectation); /opt/afp/thys/Fair_Games_Theorem/Stopped_Value_Integration.thy:108 stopped_process, :115 integrable_stopped_process; Optional_Stopping.thy:37 expected_stopped_value_mono, :210 adapted_stopped_process, :259 stopped_process_submartingale; /opt/afp/thys/Doob_Convergence/Stopping_Time.thy:24 stopping_time, :332 stopped_value

The two locales are the same notion of a nat-time stopping time, `assumes stopping_time_T: "⋀n. {ω ∈ space M. T ω ≤ n} ∈ sets (F n)"` (QV:365, OS:41).
* They define Tgt with the same definition and the same proofs of Tgt_sets_F and Tgt_sets_M (QV:368-387 vs OS:47-64).
* QV.martingale_stopped (:521, the stopped process is a martingale) is the set-integral statement OS.set_stopped_expectation (:235) plus martingale_of_set_integral_eq_Suc. OS's version needs no square integrability, as the OS header itself says (OS:24-27).
* Nothing in QV:306-602 is used outside QV. A grep for stopped_def, martingale_stopped, sq_int_martingale_stopped, stopped_expectation_sq_qvar, qvar_stopped, stopped_qvar_expectation_le and ind_Tgt_measurable_F finds no other .thy. The `stopped_sq_integrable` hits in Ito_Market.thy:110/344/590 and Volatile_Market.thy:115 are locale assumptions that happen to have the same name.
* QV.stopped T Y n ω = Y (min n (T ω)) ω is literally AFP Fair_Games_Theorem's `stopped_process X τ i ω ≡ X (min i (τ ω)) ω`, which comes with adaptedness, integrability and the submartingale property of the stopped process.

Plan §2.6 says the `stopped_integrable` pair is not a duplicate. That holds at the level of names; here I am reporting duplicated content plus dead code.

Evidence: grep -rnw martingale_stopped --include=*.thy: only Quadratic_Variation.thy (2 hits). Fair_Games_Theorem metadata: date = 2026-06-12, session Fair_Games_Theorem = Doob_Convergence + (Martingales).

Suggested action: Delete Quadratic_Variation.thy:306-602, keeping only qvar and sq_int_martingale up to line 304. Optionally re-base nat_stopped_martingale on Doob_Convergence.stopping_time and Fair_Games_Theorem: martingale = sub + super, so E X_{min n T} = E X_0 follows from expected_stopped_value_mono in both directions. This needs `sessions Fair_Games_Theorem` in the ROOT.


### CTM-3. Five dyadic-grid constructions; the dtime lemmas are verbatim instances of the dceil lemmas

*clone, impact high, confidence high, ~280 lines.*  
Locations: Continuous_Time_Martingales/Doob_Inequality.thy:591-607 (dy, dy_nonneg, dy_mono, dy_top, dy_le_u, dy_step), :800-874 (dy_floor, dy_floor_tendsto); Continuous_Time_Martingales/Optional_Sampling.thy:486-542 (dgrid, dgrid_0, dgrid_top, dgrid_nonneg, dgrid_le_iff, dgrid_mono, dgrid_Suc, dgrid_unbounded, Least_dgrid_le_iff), :544-629 (dtime_nonneg, dtime_le_u, dtime_le_iff, dtime_ge, dtime_le, dtime_tendsto), :637-746 (dcidx, dceil, dceil_grid, dtime_eq_dceil, Least_dgrid_le_iff2, dceil_ge, dceil_le, dceil_tendsto); Continuous_Time_Martingales/Stopped_Adaptedness.thy:39-42, 189-262 (dg, idx, N, dg_idx_close, inline); Continuous_Time_Martingales/Time_Discretisation.thy:169-185 (finite_dyceil_range, dyceil_grid_le); Relative_Arbitrage/Path_Stopping_Times.thy:15 (dyceil n U x = min U (⌈2^n x⌉/2^n))

`dy n k = u * real k / 2 ^ n` (Doob:592) and `dgrid n k = u * real k / 2 ^ n` (OS:487) are the same definition, with the same nonneg, mono and top lemmas, in two locales.

Inside Optional_Sampling, `dtime_eq_dceil: dtime n ω = dceil n (tau ω)` (:649) holds definitionally, yet:
* dtime_ge/dtime_le/dtime_tendsto (:556-629, about 75 lines) re-prove dceil_ge/dceil_le/dceil_tendsto (:677-746) line by line;
* Least_dgrid_le_iff (:531) is Least_dgrid_le_iff2 (:652) at x = tau ω;
* dceil_grid (:646) is dceil_def;
* dtime_eq_dceil and dceil_grid are never used.

Stopped_Adaptedness rebuilds the ceiling grid inline as `dg n i = min v (real i / 2 ^ n)` with `idx n ω = min (nat ⌈2^n * rho ω⌉) (N n)`. dg n (idx n ω) is exactly Relative_Arbitrage's dyceil n v (rho ω).

Time_Discretisation's 'Two facts about the dyadic floor grid' are helpers for dyceil, a Relative_Arbitrage constant. They were moved down from Relative_Arbitrage, and Path_Stopping_Times.thy:54 and :77 now carry pointer texts to them.

Evidence: OS:649 `lemma dtime_eq_dceil: "dtime n ω = dceil n (tau ω)" unfolding dtime_def dceil_def didx_def dcidx_def ..`; grep -rnw dtime_eq_dceil --include=*.thy: 1 hit (the definition); grep -rnw dceil_grid --include=*.thy: 1 hit.

Suggested action: Create a CTM theory Dyadic_Grids with one grid (scaled by the horizon u), dfloor/dceil with their ge, le and tendsto lemmas, and dyceil, moving dyceil down from Path_Stopping_Times. Derive dtime_* from dceil_*. Use dceil in Stopped_Adaptedness and Doob_Inequality (dy_floor = the floor analogue). Delete dceil_grid and dtime_eq_dceil.


### CTM-4. Continuous-time optional sampling by dyadic approximation proved twice (CTM and Relative_Arbitrage/Path_Stopping_Times); pre_sigma_of re-implements the AFP pre_sigma

*clone, impact high, confidence medium, ~600 lines.*  
Locations: Continuous_Time_Martingales/Optional_Sampling.thy:460-1047 (locale stopped_cont_martingale, simple_stopped_martingale :339-458, set_optional_sampling :857); Relative_Arbitrage/Path_Stopping_Times.thy:1105-1300 (pre_sigma_of, pre_sigma_ofI, sigma_algebra_pre_sigma_of, pre_sigma_of_mono, ...); Relative_Arbitrage/Path_Stopping_Times.thy:1402 set_martingale_sampling_simple, :1534 set_martingale_sampling, :1648 set_martingale_sampling_two; /opt/afp/thys/Doob_Convergence/Stopping_Time.thy:93 pre_sigma, :98 sigma_algebra_pre_sigma, :195 mono_pre_sigma

Path_Stopping_Times contains a second, more general optional-sampling theorem.
* Its statement is generic: `fixes M :: "'a measure" and F :: "real ⇒ 'a measure" and Y :: "real ⇒ 'a ⇒ real" and σ :: "'a ⇒ real"`, concluding `set_lebesgue_integral M A (λω. Y (σ ω) ω) = set_lebesgue_integral M A (Y U)` for A ∈ pre_sigma_of M F σ.
* Its proof is the same as CTM's: a simple-stopping-time case, approximation from above by the dyadic ceiling (dyceil), then dominated convergence with a dominating D.
* set_martingale_sampling_two is full optional sampling for σ ≤ ρ; CTM's set_optional_sampling is its special case with deterministic σ = v and A ∈ F_v.
* None of it mentions paths, so it belongs in CTM.
* pre_sigma_of (`{A. A ∈ sets M ∧ (∀t≥0. A ∩ {σ ≤ t} ∈ sets (F t))}`) is the sets of AFP Doob_Convergence's `pre_sigma T = sigma (space M) {A ∈ sets M. ∀t≥t0. {ω∈A. T ω ≤ t} ∈ sets (F t)}`, with sigma_algebra_pre_sigma and mono_pre_sigma already proved there.

Evidence: Path_Stopping_Times.thy:1107 `pre_sigma_of M F σ = {A. A ∈ sets M ∧ (∀t. 0 ≤ t ⟶ A ∩ {ω ∈ space M. σ ω ≤ t} ∈ sets (F t))}`; :1534-1546 the set_martingale_sampling hypotheses (mg, mono, sub, A, stop, sig0, sigU, cont, Dbd, Dint); OS:470-481 stopped_cont_martingale assumptions (u_pos, tau_nonneg, tau_stop, paths_cont, Z_dom, D_integrable, stopped_measurable).

Suggested action: Move the path-free block Path_Stopping_Times.thy:1105-1840 (pre_sigma_of, set_martingale_sampling*, integrable_at_bounded_stopping_time, stopped_increment_of_horizon_gen) into CTM.Optional_Sampling, or base it on AFP Doob_Convergence.pre_sigma. Derive OS.set_optional_sampling and optional_sampling from set_martingale_sampling_two (or the reverse) so that one dyadic-approximation argument remains.


### CTM-5. Proposed internal re-layering of CTM (merges and deletions)

*structure, impact high, confidence medium, ~1500 lines.*  
Locations: Continuous_Time_Martingales/ROOT; Time_Discretisation.thy, Sampled_Martingale.thy, Sampled_Quadratic_Variation.thy; Optional_Sampling.thy, Stopped_Adaptedness.thy; Moment_Bounds.thy, Integrability_Criteria.thy

The tiny theories should not all stay:
* Moment_Bounds is dead and should be deleted.
* Sampled_Martingale (153 lines) and Sampled_Quadratic_Variation (167) duplicate Time_Discretisation (189) and should merge with it.
* Stopped_Adaptedness (one lemma) is the adaptedness half of optional stopping and should join Optional_Sampling, or a new Optional_Stopping theory. That theory would also receive stopped_martingale_L2 / stopped_compensated_square from Stopped_Localization and the path-free optional-sampling block from Path_Stopping_Times.
* Integrability_Criteria is a grab bag and should be dissolved.

One CTM session remains the right granularity. Splitting off a 'Probability_Supplement' session (Power_Inequalities, Essential_Infimum, Vitali, Semidirect_Kernels, integrability helpers) would mostly buy build parallelism, which better imports also give.

Evidence: See the clone, dead-code and import findings above.

Suggested action: Target layout, bottom to top:
* L0 (no martingales): Power_Inequalities (+ the integrability helpers of Integrability_Criteria, QV:34 and Doob), Dyadic_Grids, Essential_Infimum, Vitali_Convergence (+ Conditional_UI), Semidirect_Kernels (+ emeasure_ksemi_rect, AE_integrable_ksemi_section).
* L1: Natural_Filtration, Martingale_Algebra, Martingale_Transfer, Modification_Transfer.
* L2: Quadratic_Variation (without lines 306-602), Sampled_Martingales (= TD + SM + SQV).
* L3: Doob_Inequality.
* L4: Stopping_Times (exit times; the metric erosion part could go to L0), Optional_Sampling (+ Stopped_Adaptedness + Stopped_Localization's L2 theorems + Path_Stopping_Times' pre_sigma/set_martingale_sampling block, or the AFP pre_sigma).
* Independence lemmas → Wiener_Measure.

Expected net change: about −1 200 lines in CTM, and about −700 lines in Relative_Arbitrage/Continuous_Path_Spaces after the moves.


### CTM-6. G4 (one essential infimum) only half executed: parallel ess_inf/ess_inf_time lemma copies remain; three pushforward lemmas

*clone, impact medium, confidence high, ~70 lines.*  
Locations: Continuous_Time_Martingales/Essential_Infimum.thy:24 ess_inf, :77 ess_inf_time, :83 ess_inf_ennreal; Essential_Infimum.thy:27 ess_infI vs :87 ess_inf_timeI; Essential_Infimum.thy:44-59 ess_inf_AE vs :92-106 ess_inf_time_AE (verbatim proof); Essential_Infimum.thy:32 ess_inf_mono vs :234 ess_inf_time_mono; Essential_Infimum.thy:288 ess_inf_distr vs :274 ess_inf_time_distr vs :255 ess_inf_time_distr_measurable

ess_inf_time is still a separate definition (`Sup {c. AE ω in M. c ≤ ennreal (tau ω)}`) next to ess_inf, joined by the bridge ess_inf_ennreal. G4's fallback allowed keeping it as a definition, but then each ess_inf_time lemma should be a one-line corollary. Instead:
* ess_inf_time_AE copies ess_inf_AE's 15-line countable-SUP proof with `tau ω` replaced by `ennreal (tau ω)`;
* ess_infI/ess_inf_timeI and ess_inf_mono/ess_inf_time_mono are separate proofs;
* the pushforward identity is stated three times: ess_inf_time_distr_measurable and ess_inf_time_distr have identical conclusions and differ only in how measurability is supplied, and ess_inf_distr is the general form.

On the library side: ess_inf M f equals Liminf (ae_filter M) f. HOL-Probability Essential_Supremum.esssup is the dual (Limsup, defined only for measurable f), and the Liminf lemmas (le_Liminf_iff, Liminf_mono) could shorten ess_infI and ess_inf_mono. ess_inf_AE itself legitimately avoids measurability; the library's esssup_AE needs it.

Evidence: EI:44-59 and :92-106 differ only in `ennreal (tau ω)` vs `tau ω`; :255 `ess_inf_time_distr_measurable: g ∈ M →M N ⟹ tau ∈ borel_measurable N ⟹ ess_inf_time (distr M N g) tau = ess_inf_time M (λω. tau (g ω))` vs :274 the same conclusion under `⋀c. {ω ∈ space N. c ≤ ennreal (tau ω)} ∈ sets N`. Users: ess_inf_time_distr_measurable 1 (Path_Splicing), ess_inf_time_distr 5.

Suggested action: Derive ess_inf_timeI, ess_inf_time_AE, ess_inf_time_mono and ess_inf_time_distr from the ess_inf versions via ess_inf_ennreal (one line each). Delete ess_inf_time_distr_measurable and redirect its one use. Optionally restate ess_inf through Liminf (ae_filter M).


### CTM-7. Martingale_Algebra re-proves AFP martingale.add/diff and HOL integral_bounded_linear (and says the AFP lacks them)

*library_duplicate, impact medium, confidence high, ~110 lines.*  
Locations: Continuous_Time_Martingales/Martingale_Algebra.thy:20-57 martingale_add; Martingale_Algebra.thy:69-97 martingale_diff (text: 'The AFP entry does not record the difference'); Martingale_Algebra.thy:305-312 integral_of_bounded_linear; Martingale_Algebra.thy:633-635 (inline re-proof in set_integral_mat_component); /opt/afp/thys/Martingales/Martingale.thy:156 martingale.add, :171 martingale.diff; /opt/Isabelle2026-RC3/src/HOL/Analysis/Bochner_Integration.thy:1052 integral_bounded_linear

* The AFP has, in context martingale, `lemma add[intro]: assumes "martingale M F t0 Y" shows "martingale M F t0 (λi ξ. X i ξ + Y i ξ)"` and `lemma diff[intro]` with the same shape. The CTM versions are less general: martingale_add is restricted to real time.
* integral_of_bounded_linear is literally HOL's `integral_bounded_linear: bounded_linear T ⟹ integrable M f ⟹ integral M (λx. T (f x)) = T (integral M f)`, which the same theory already uses at line 412.
* integral_of_bounded_linear has 31 uses across CTM and Relative_Arbitrage.
* martingale_add_const is AFP martingale_const + add.

Evidence: AFP Martingale.thy:156-169 and :171-185 (quoted above); Martingale_Algebra.thy:412 `by (rule integral_bounded_linear[OF bounded_linear_vec_nth si])`.

Suggested action: Replace martingale_add/martingale_diff by `martingale.add[OF mX mY]` and `martingale.diff`, or keep them as one-line wrappers if the argument order matters, and delete the false sentence. Replace integral_of_bounded_linear by integral_bounded_linear (sed on 31 uses).


### CTM-8. Vector/matrix duplicates in Martingale_Algebra: one euclidean_space version would cover both; two component lemmas restate the bounded-linear corollaries

*generalisation, impact medium, confidence high, ~230 lines.*  
Locations: Continuous_Time_Martingales/Martingale_Algebra.thy:379-390 martingale_vec_nth, martingale_mat_nth; Martingale_Algebra.thy:417-463 martingale_vec_component (≡ martingale_vec_nth at t0 = 0); Martingale_Algebra.thy:702-745 martingale_mat_component (≡ martingale_mat_nth at t0 = 0); Martingale_Algebra.thy:400-415 set_integral_vec_component, :619-638 set_integral_mat_component (instances of set_integral_of_bounded_linear :319); Martingale_Algebra.thy:465 measurable_vec_components / :580 measurable_mat_entries; :477 integrable_vec_components / :591 integrable_mat_entries; :500-561 martingale_vecI / :640-696 martingale_matI; Martingale_Algebra.thy:563-567, :698-700 (prose)

* martingale_vec_component (47 lines) and martingale_mat_component (44 lines) prove, via set integrals, exactly the statements of martingale_vec_nth and martingale_mat_nth, which are 1-3-line corollaries of martingale_bounded_linear_image placed 40 lines earlier.
* martingale_vecI and martingale_matI have the same proof skeleton, as do the measurable_*/integrable_* pairs. All of them go through Basis and inner products, so a single statement for X :: real ⇒ 'a ⇒ 'b::euclidean_space ('(∀b∈Basis. martingale M F 0 (λt ω. X t ω • b)) ⟹ martingale M F 0 X') covers real^'n and real^'n^'n.
* The prose at 563 cites a nonexistent 'Ito_Market.martingale_vecI'. The prose at 698 claims martingale_vec_component 'does not reach a matrix-valued process', but martingale_mat_nth already does.

Evidence: MA:417-420 `lemma martingale_vec_component: fixes X :: "real ⇒ 'a ⇒ real^'n::finite" assumes mg: "martingale M F 0 X" shows "martingale M F 0 (λt ω. X t ω $ k)"` vs MA:379-383 `corollary martingale_vec_nth: fixes Y :: "real ⇒ 'a ⇒ (real^'n::finite)" assumes mg: "martingale M F t0 Y" shows "martingale M F t0 (λu ω. Y u ω $ i)" by (rule martingale_bounded_linear_image[OF bounded_linear_vec_nth mg])`.

Suggested action: Make martingale_vec_component and martingale_mat_component abbreviation-style `lemmas` of the _nth corollaries, or rename their 14 + 6 uses. Replace the vec/mat pairs by euclidean_space lemmas (martingale_euclideanI, measurable_euclidean_components, integrable_euclidean_components, set_integral_inner) and keep the vec/mat names as instances if convenient. Fix the prose.


### CTM-9. Two Dynkin π-λ arguments for vanishing set integrals; modification-transfer theorems share about 60 lines of boilerplate

*clone, impact medium, confidence high, ~220 lines.*  
Locations: Continuous_Time_Martingales/Natural_Filtration.thy:133-184 set_integral_zero_of_generator; Continuous_Time_Martingales/Modification_Transfer.thy:159-365 set_integral_zero_transfer (induction :207-364); Modification_Transfer.thy:380-516 martingale_of_modification_vec, :527-639 martingale_of_modification_gen; Modification_Transfer.thy:172-180, :437-441, :471-475, :596-600, :624-628 (inline re-proofs of sets_natural_filtration_subset, defined at :671); Modification_Transfer.thy:392-401, :546-555 (sff) vs /opt/afp/thys/Martingales/Stochastic_Process.thy:152 finite_filtered_measure_natural_filtration

* set_integral_zero_transfer contains a full sigma_sets_induct_disjoint induction: basic, empty, compl, and countable disjoint union by dominated convergence. That is the argument of set_integral_zero_of_generator, which in Natural_Filtration uses lebesgue_integral_countable_add. The cylinder family contains space M (take P = {}), so only the basic case is specific. Modification_Transfer imports only Martingales.Martingale, which explains the duplication.
* martingale_of_modification_vec and _gen repeat fm/sfs/sff/int'/split_diff/A_M/si/B_M/sB. _vec handles the vector case componentwise only because set_integral_zero_transfer is stated for real D; the Dynkin argument works verbatim for Banach-valued D with *_R, which would make _vec the instance Y = X of a Banach-valued _gen.
* The finite-measure ⟹ sigma_finite_filtered_measure (natural_filtration) construction is AFP finite_filtered_measure_natural_filtration plus the sublocale finite_filtered_measure ⊆ sigma_finite_filtered_measure.

Evidence: MT:209 `proof (induct rule: sigma_sets_induct_disjoint)` vs NF:152 `proof (induction rule: sigma_sets_induct_disjoint)`; MT:671-680 sets_natural_filtration_subset exists at the end of the same theory while the same fact is re-derived 5 times above it.

Suggested action: Import Natural_Filtration into Modification_Transfer and reduce set_integral_zero_transfer to its basic case (about 50 lines instead of 200). Generalise D/D' and _gen's Y to 'c::{banach,second_countable_topology} and derive _vec from it. Use AFP finite_filtered_measure_natural_filtration and sets_natural_filtration_subset.


### CTM-10. Integrability helpers duplicated across Quadratic_Variation, Doob, Vitali and Integrability_Criteria, and against the library

*clone, impact medium, confidence high, ~150 lines.*  
Locations: Continuous_Time_Martingales/Quadratic_Variation.thy:34-59 integrable_prod_of_squares vs Integrability_Criteria.thy:557-577 integrable_mult_of_sq; Doob_Inequality.thy:332-359 maxabs_prod_integrable (instance); Integrability_Criteria.thy:408-428 integrable_of_sq_integrable vs Doob_Inequality.thy:652-671 gsup_le_one_plus_sq + gsup_integrable; Vitali_Convergence.thy:100-110 integrable_clamp (unused) vs Integrability_Criteria.thy:442-450 clamp_integrable; Vitali_Convergence.thy:90-99 integrable_tail (max 0 (|h|-K)) vs Integrability_Criteria.thy:464-474 tail_integrable (|f|·1{R<|f|}); Integrability_Criteria.thy:435-440 bounded_measurable_integrable (= finite_measure.integrable_const_bound); Integrability_Criteria.thy:582-591 integrable_cmult (= HOL-Analysis Bochner_Integration.thy:998 integrable_mult_right), :593-602 integral_cmult (= :1089 integral_mult_right / :1099 integral_mult_right_zero)

* integrable_prod_of_squares and integrable_mult_of_sq have the same statement: f, g real, Borel, f² and g² integrable ⟹ f·g integrable. maxabs_prod_integrable re-derives the absolute-value instance a third time.
* integrable_of_sq_integrable (finite measure, f² integrable ⟹ f integrable, via |f| ≤ 1 + f²) is exactly the gsup_integrable argument, with its own copy of the elementary inequality.
* clamp_integrable ≡ integrable_clamp; the latter is never used.
* There are two tail-truncation conventions: Vitali's unif_integrable uses max 0 (|f|-K); Integrability_Criteria and the Relative_Arbitrage consumer weak_conv_integral_of_L2_bound use |f|·1{|f|>R}.
* integrable_cmult and integral_cmult are library simp/intro rules (17 and 12 uses).

Evidence: HOL Bochner_Integration.thy:998 `lemma integrable_mult_right[simp, intro]: fixes c :: "_::{real_normed_algebra,second_countable_topology}" shows "(c ≠ 0 ⟹ integrable M f) ⟹ integrable M (λx. c * f x)"`; :1089 `integral_mult_right[simp]`. grep -rnw integrable_clamp --include=*.thy: 1 hit.

Suggested action: Keep one product lemma, placed in Power_Inequalities or an 'Integrability' theory low in the session, and one sq-integrable ⟹ integrable lemma, and use them in Doob_Inequality. Delete Vitali.integrable_clamp, bounded_measurable_integrable, integrable_cmult and integral_cmult, redirecting to the library. Pick one tail truncation, or prove a two-line conversion lemma between the two.


### CTM-11. Special cases proved separately next to their general forms

*generalisation, impact medium, confidence high, ~150 lines.*  
Locations: Continuous_Time_Martingales/Optional_Sampling.thy:809-846 optional_sampling vs :857-1047 set_optional_sampling; Optional_Sampling.thy:183-197 stopped_expectation vs :235-290 set_stopped_expectation; Optional_Sampling.thy:412-422 simple_optional_sampling vs :438-456 set_simple_optional_sampling; Continuous_Time_Martingales/Martingale_Algebra.thy:189-220 martingale_time_change vs :225-263 martingale_time_change_cong; Martingale_Algebra.thy:125-148 martingale_cong_ge vs :152-185 martingale_cong_AE; Continuous_Time_Martingales/Semidirect_Kernels.thy:179-209 integral_kernel_measurable vs :147-162 integral_ksemi_measurable; Optional_Sampling.thy:1049-1065 stopped_integrable vs :1108-1125 (int, the same domination argument)

Each pair is a special case proved separately next to its general form.
* optional_sampling is set_optional_sampling at A = space M, v = 0: Z (min 0 tau) = Z 0 because tau ≥ 0. It re-runs the whole dominated-convergence argument (38 lines).
* stopped_expectation is set_stopped_expectation at A = space M, m = 0, and simple_optional_sampling is the analogous instance of set_simple_optional_sampling.
* martingale_time_change is martingale_time_change_cong with Y = λu. X (s u); the two proofs are the same 35 lines.
* martingale_cong_ge (any t0, pointwise equality) and martingale_cong_AE (t0 = 0, a.e. equality plus adaptedness) should be one t0-general lemma.
* integral_kernel_measurable takes an extra integrability hypothesis `gi` but is integral_ksemi_measurable instantiated with g' = (λp. g (fst p) (snd p)), which needs no integrability.

Evidence: Semidirect_Kernels.thy:149-150 `integral_ksemi_measurable: Kr ∈ M →M prob_algebra N ⟹ g ∈ borel_measurable (M ⊗M N) ⟹ (λω. ∫ω'. g (ω, ω') ∂Kr ω) ∈ borel_measurable M` vs :179-184 the same conclusion for curried g, assuming additionally `gi: ⋀ω. ω ∈ space M ⟹ integrable (Kr ω) (g ω)`.

Suggested action: Derive each special case from its general form in 3-6 lines: optional_sampling from set_optional_sampling, stopped_expectation from set_stopped_expectation, simple_optional_sampling from set_simple_optional_sampling, martingale_time_change from martingale_time_change_cong, integral_kernel_measurable from integral_ksemi_measurable. Generalise martingale_cong_AE to an arbitrary t0.


### CTM-12. Moment_Bounds is entirely unused; the real Eq. (2.7) is elsewhere

*dead_code, impact medium, confidence high, ~94 lines.*  
Locations: Continuous_Time_Martingales/Moment_Bounds.thy:1-94 (integral_square_le_of_bound, fourth_moment_of_compensated); Continuous_Path_Spaces/Increment_Moments.thy:5 (imports Moment_Bounds), :1901 fourth_moment_bound_bounded; notes/PLAN_RESTRUCTURING_2.md §10 'Moment_Bounds does not disappear'

No .thy names fourth_moment_of_compensated or integral_square_le_of_bound; they appear only in notes/STATUS*.md and dispositions.tsv. The fourth-moment bound of Eq. (2.7) is actually proved as Increment_Moments.fourth_moment_bound_bounded (constant 8C², 'free of Ito and BDG'), which does not use Moment_Bounds. Increment_Moments imports Moment_Bounds only transitively, for Power_Inequalities.square_add_le_two.

The plan's justification for keeping the theory ('a named result') is therefore wrong. The theory is also paper-specific in a paper-free session: its title is 'The fourth-moment bound of Eq. (2.7) of LaiShkolnikovSoner', and it mentions Lemma 2.2 and ito_volatile_market. Its content is a two-line generic integral estimate, with the paper's (t - s) hard-wired. The theory and its two lemmas are the deletion candidates.

Evidence: grep -rn 'fourth_moment_of_compensated\|integral_square_le_of_bound' (all files): only Moment_Bounds.thy, notes/STATUS_ARCHIVE_2026-07-29.md, notes/STATUS.md, notes/restructuring_2/dispositions.tsv.

Suggested action: Delete Moment_Bounds and its ROOT entry. Change Increment_Moments' import to Continuous_Time_Martingales.Sampled_Quadratic_Variation plus Power_Inequalities, and fix the plan note.


### CTM-13. Paper-specific prose throughout the paper-free session (12 of 18 theories)

*misplacement, impact medium, confidence high, ~180 lines.*  
Locations: Essential_Infimum.thy:74, 114-120, 138-142, 157-160, 244-253, 268-272, 285-286; Stopping_Times.thy:9-14 ('Example 3.1 of the paper', 'Ito_Market'), :20-22, :51-52; Moment_Bounds.thy:1-26, 49-56; Vitali_Convergence.thy:11-17, 307-312; Sampled_Martingale.thy:89-110 (locale ito_volatile_market, Z_martingale); Sampled_Quadratic_Variation.thy:18-25, 77-81; Quadratic_Variation.thy:28-29, 575-576; Time_Discretisation.thy:27-29 (Volatile_Market); Optional_Sampling.thy:10-35 (cite LaiShkolnikovSoner, 'market locale' :462-468); Integrability_Criteria.thy:318-322, 346-350, 398-406, 519-522, 552-555, 724-729, 739-741; Martingale_Transfer.thy:20-27, 170-174 ('the DPP'), 422-428, 489-492; Modification_Transfer.thy:9-15, 520-525 ('the market locales'); Martingale_Algebra.thy:563

The ROOT advertises a paper-free library, yet the prose cites Eq. (1.6), (1.7), (2.7) and (2.9), Lemmas 2.2/2.3, Proposition 2.4, Example 3.1, P_x, Berge's theorem, and paper-layer locales and theories (ito_volatile_market, sufficiently_volatile_market, Volatile_Market, Ito_Market, path_law, 'the class', 'clause (iv)'). Essential_Infimum has a whole `section` titled 'The class P_x and the value function of Eq. (1.6)'.

There is also a misattribution: 'Larsson--Ruf's Lemma 2.1 of \<^cite>‹LaiShkolnikovSoner›' (Stopping_Times:52) and 'LR, proof of Lemma 2.1 of \<^cite>‹LaiShkolnikovSoner›' (Integrability_Criteria:346). The lemma is Larsson–Ruf's, not from the cited paper.

Evidence: grep -n 'paper\|Eq\. (\|Lemma 2\|Proposition\|LaiShkolnikovSoner\|Ito_Market\|volatile_market\|market\|DPP' Continuous_Time_Martingales/*.thy returns 45 lines (listed in the locations).

Suggested action: Rewrite these blocks in library terms (what the lemma says, not where the paper uses it), or move them as comments to the consuming Relative_Arbitrage theories. Drop the root.bib citation of the paper from the CTM document unless it is used in a neutral way.


### CTM-14. Orphaned, stale and incorrect text blocks

*documentation, impact medium, confidence high, ~120 lines.*  
Locations: Essential_Infimum.thy:244-247 ('Superadditivity...' with no lemma; none exists in the repository), :268 section header over two generic pushforward lemmas, :285-286 and :298 orphans, :80-81 (prose for ess_inf_time_le_nn_integral placed before ess_inf_ennreal), :108-120 (prose for ess_inf_time_ge_iff placed before ess_inf_time_le_nn_integral); Modification_Transfer.thy:367-371 empty section 'The martingale property transfers to the modification' (real-valued case announced, absent), immediately followed by another section at :373; Sampled_Martingale.thy:20-22 (cites nonexistent mtrans/martingale_mtrans), :29-30 ('This text block sits before the theory header' — false), :82-85 orphan ('a uniform partition of mesh dt'); Time_Discretisation.thy:10-29 ('Stochastic integration, layer 2'... 'layer 3'); Optional_Sampling.thy:11 ('layer 3b'); no stochastic integral exists; Time_Discretisation.thy:128-130 ('optional-sampling results of Quadratic_Variation apply verbatim' — that section is dead); Integrability_Criteria.thy:519-522 ('conditioning statement isolated in d ... the rebased future the rebased future'), :552-555 ('ingredients e needs on the way to clause (iv)'), :724-729 and :739-741 (unrelated to the following lemma), :747 orphan; section title :1 'two lattice helpers' does not describe the content; Martingale_Algebra.thy:120-123 ('The processes below differ at negative times' — no such processes), :563, :698-700; Stopping_Times.thy:72-73 (claims a closeness statement that etime_less_of_open_witness does not have; the lemma has no openness hypothesis despite its name); Power_Inequalities.thy:14-15 ('nothing below this theory proves an arithmetic fact of this kind again' — false: Doob_Inequality.thy:519-526, 652-659, 347-352; Integrability_Criteria.thy:421-425, 568-571), :17-21 duplicated verbatim at :91-96; Continuous_Time_Martingales/document/root.tex abstract: 'Vitali's convergence theorem, that a uniformly integrable sequence converging in probability converges in mean' — vitali_convergence assumes AE convergence (Vitali_Convergence.thy:173); notes/PLAN_RESTRUCTURING_2.md §3.5 lists emeasure_ksemi_rect, AE_integrable_ksemi_section, ksemi_weak_conv, etime_shift_*, horizon_sq_int_martingale_stopped as gained by CTM; dispositions.tsv:1215/1295/1340/1358 says STAY and they are still in Relative_Arbitrage

These are text blocks left behind when material moved: prose describing a different lemma, references to deleted lemmas and unbuilt layers, an empty section, and one mathematically wrong claim in the PDF abstract (convergence in probability vs a.e.).

Evidence: Quoted in the locations. vitali_convergence: `assumes ... conv: "AE x in M. (λn. f n x) ⟶ g x"`.

Suggested action: Delete the orphans, move the misplaced paragraphs next to their lemmas, fix the abstract ('converging almost everywhere') and the false claims, and update plan §3.5.


### CTM-15. 'Stop an L2 martingale with continuous paths' (Dsup + stopped_adapted_of_cont + optional_stopping) proved three times outside CTM

*clone, impact medium, confidence medium, ~160 lines.*  
Locations: Continuous_Path_Spaces/Stopped_Localization.thy:22-82 stopped_martingale_L2; Relative_Arbitrage/Pair_Path_Laws.thy:1516-1600 horizon_sq_int_martingale_stopped; Relative_Arbitrage/Exit_Class_Limits.thy:860-925 exit_class_stopped_coord_martingale; Continuous_Time_Martingales/Optional_Sampling.thy:1080 optional_stopping; Stopped_Adaptedness.thy:24; Doob_Inequality.thy:876 Dsup_dominates

All three apply optional_stopping with D := Dsup and stopped_adapted_of_cont, and two of them build the same 'domA' extension of the domination beyond the horizon. stopped_martingale_L2 is pure CTM material: no path space, and it does not need Increment_Moments. Both Relative_Arbitrage proofs could cite it, after a one-line extension of continuity to {0..} for processes capped at T. CTM's optional_stopping carries a domination hypothesis whose standard discharge (L2 plus continuous paths) lives in another session.

Evidence: Pair_Path_Laws.thy:1562 `proof (rule optional_stopping[where D = "λ_. HM.Dsup"])`; Exit_Class_Limits.thy:911 the same line; Stopped_Localization.thy:56 `proof (rule optional_stopping[OF mg tau_nonneg tau_stop])` with D from Dsup.

Suggested action: Move stopped_martingale_L2 and stopped_compensated_square (Stopped_Localization.thy:22-190) into CTM, in a merged Optional_Sampling/Stopped_Adaptedness theory, and state a capped variant. Replace the two Relative_Arbitrage clones by citations.


### CTM-16. Non-martingale content parked in CTM, and CTM content parked in other sessions

*misplacement, impact medium, confidence medium, ~700 lines.*  
Locations: Continuous_Time_Martingales/Integrability_Criteria.thy:61-91 indep_var_distr_iff, :96-306 indep_var_PiM_components, :701-722 indep_vars_cong_sets (only user: Wiener_Measure/Product_Brownian_Motion.thy); Integrability_Criteria.thy:24-56 cInf_mult_pos (only users: Relative_Arbitrage/Operator_Envelopes.thy, Comparison_Strictness.thy), :524-550 cInf_shift_real, :476-517 ennreal_*; Integrability_Criteria.thy:346-396 exp_neg_time_integrable/_integral_lower (only user: Continuous_Path_Spaces/Path_Exit_Times.thy); :731-737 fst_coord_borel stated at (real^'n) × (real^'n^'n); Continuous_Time_Martingales/Stopping_Times.thy:82-198 open_gt_infdist, shift_stays_off, eroded* (metric topology); Continuous_Time_Martingales/Time_Discretisation.thy:169-185 finite_dyceil_range, dyceil_grid_le (helpers for Relative_Arbitrage's dyceil); Continuous_Path_Spaces/Stopped_Localization.thy:22-190 and Continuous_Path_Spaces/Conditional_UI.thy (path-free martingale/UI theory); Relative_Arbitrage/Path_Law_Pasting.thy:1560 emeasure_ksemi_rect, :2038 AE_integrable_ksemi_section, :1799 ksemi_weak_conv; Relative_Arbitrage/Pair_Path_Laws.thy:1516 horizon_sq_int_martingale_stopped

* Three groups of Integrability_Criteria lemmas are used only in other sessions and have nothing to do with martingales: independence of products (about 250 lines, used only by Wiener_Measure, which already sits above CTM), infimum algebra used only by the viscosity layer, and the Laplace-transform bounds used only by Path_Exit_Times (with paper prose).
* fst_coord_borel keeps the pair path type (real^'n) × (real^'n^'n), although it is pair_fst_borel composed with borel_measurable_nth.
* Going the other way, Conditional_UI (UI of conditional expectations) and Stopped_Localization's L2 optional stopping mention no path space and belong next to Vitali_Convergence and Optional_Sampling.
* The ksemi lemmas and horizon_sq_int_martingale_stopped are path-free statements still in Relative_Arbitrage that plan §3.5 meant to move into CTM.

Evidence: Uses per grep: indep_var_PiM_components → Wiener_Measure/Product_Brownian_Motion.thy only; cInf_mult_pos → Operator_Envelopes.thy, Comparison_Strictness.thy; exp_neg_time_integrable → Path_Exit_Times.thy. Path_Law_Pasting.thy:1560 `lemma emeasure_ksemi_rect: assumes K: "Kr ∈ M →M prob_algebra N" ... shows "emeasure (ksemi M N Kr) (A × B) = (∫+ω∈A. emeasure (Kr ω) B ∂M)"`.

Suggested action: Move as follows:
* independence lemmas → Wiener_Measure (or a small Independence theory);
* cInf_* / ennreal_* → Semicontinuous_Analysis or a reals-helper theory at the bottom of CTM;
* exp_neg_time_* → Path_Exit_Times;
* fst_coord_borel: drop, and use measurable_compose of pair_fst_borel and borel_measurable_nth;
* Conditional_UI → next to Vitali_Convergence in CTM;
* Stopped_Localization's first two theorems → Optional_Sampling;
* emeasure_ksemi_rect and AE_integrable_ksemi_section → Semidirect_Kernels;
* horizon_sq_int_martingale_stopped → Optional_Sampling.


### CTM-17. Small re-proofs of HOL/HOL-Probability lemmas

*library_duplicate, impact low, confidence high, ~110 lines.*  
Locations: Continuous_Time_Martingales/Martingale_Transfer.thy:29-37 prob_space_pair_measure = HOL-Probability Giry_Monad.thy:1677 prob_space_pair; Continuous_Time_Martingales/Integrability_Criteria.thy:743-745 bm_prj_measurable = HOL-Analysis Borel_Space.thy:1301 borel_measurable_nth; Continuous_Time_Martingales/Time_Discretisation.thy:38-55 time_grid.t_mono_le = HOL Nat.thy:1990 lift_Suc_mono_le; Integrability_Criteria.thy:476-506 ennreal_Sup_image ≈ HOL-Probability SPMF.thy:32 ennreal_Sup; Integrability_Criteria.thy:508-517 ennreal_min_eq ≈ Extended_Nonnegative_Real.thy:918 min_ennreal; Natural_Filtration.thy:77-124 AE_nonpos_of_set_integral_zero / AE_zero_of_set_integral_zero ≈ HOL-Analysis Set_Integral.thy:825 density_unique_real (on restr_to_subalg M G); Natural_Filtration.thy:192-199 AE_mem_of_emeasure_1 (wrapper of prob_space.AE_prob_1); Doob_Inequality.thy:70-76 sets_F_M (= AFP sets_F_subset); Power_Inequalities.thy:122-126 pow4_nonneg (simp: zero_le_power_eq_numeral)

* prob_space_pair_measure has exactly the statement of the library's prob_space_pair (13 uses).
* bm_prj_measurable has exactly the statement of borel_measurable_nth.
* t_mono_le re-proves lift_Suc_mono_le by induction, although Doob_Inequality.thy:932 already uses lift_Suc_mono_le.
* ennreal_Sup_image is ennreal_Sup with finiteness derived from a bound.
* AE_zero_of_set_integral_zero is density_unique_real transported to a subalgebra; it is a 10-line corollary rather than a 48-line proof.
* The others are trivial wrappers.

Evidence: Giry_Monad.thy:1677 `lemma prob_space_pair: assumes "prob_space M" "prob_space N" shows "prob_space (M ⊗M N)"`; Borel_Space.thy:1301 `lemma borel_measurable_nth[measurable (raw)]: "(λx::real^'n. x $ i) ∈ borel_measurable borel"`; Nat.thy:1990 lift_Suc_mono_le.

Suggested action: Redirect the uses and delete the duplicates. t_mono_le becomes `lift_Suc_mono_le[OF t_step]`.


### CTM-18. integral_pos_of_AE_pos: 91 lines for a corollary of integral_nonneg_eq_0_iff_AE

*simplification, impact low, confidence high, ~85 lines.*  
Locations: Continuous_Time_Martingales/Integrability_Criteria.thy:604-694 integral_pos_of_AE_pos; /opt/Isabelle2026-RC3/src/HOL/Analysis/Bochner_Integration.thy:1875 integral_nonneg_eq_0_iff_AE

0 ≤ ∫f holds by integral_nonneg_AE. If ∫f = 0, then integral_nonneg_eq_0_iff_AE gives AE f = 0, which together with AE f > 0 makes the AE filter trivial, contradicting prob_space. The current proof builds the sets {f > 1/(n+1)}, shows a countable union of null sets is null, and bounds the integral below by an indicator. It has 5 uses, in Value_Function_Subsolution.

Evidence: Bochner_Integration.thy:1875 `lemma integral_nonneg_eq_0_iff_AE: ... integrable M f ⟹ AE x in M. 0 ≤ f x ⟹ integral M f = 0 ⟷ (AE x in M. f x = 0)`.

Suggested action: Re-prove in about 8 lines via integral_nonneg_eq_0_iff_AE and prob_space.AE_False (or ae_filter_eq_bot_iff).


### CTM-19. Sequential-continuity detour repeated where the library's continuous_on_tendsto_compose applies

*simplification, impact low, confidence high, ~45 lines.*  
Locations: Continuous_Time_Martingales/Optional_Sampling.thy:826-837 (optional_sampling), :959-972 (limu), :984-1020 (limmix); Continuous_Time_Martingales/Doob_Inequality.thy:885-906 (Dsup_dominates); Continuous_Time_Martingales/Stopping_Times.thy:612-614 (etime_stays_in_cball); /opt/Isabelle2026-RC3/src/HOL/Topological_Spaces.thy:2405 continuous_on_tendsto_compose

Each site derives `have seq: "⋀x a. a ∈ {0..u} ⟹ (∀n. x n ∈ {0..u}) ⟹ x ⟶ a ⟹ ((λs. Z s ω) ∘ x) ⟶ Z a ω" using cont unfolding continuous_on_sequentially by blast`, then post-processes with comp_def. Stopped_Adaptedness.thy:258 in the same session already uses continuous_on_tendsto_compose for exactly this.

Evidence: Stopped_Adaptedness.thy:258 `proof (rule continuous_on_tendsto_compose[OF cont[OF w] tt rho0])`.

Suggested action: Replace each seq block by continuous_on_tendsto_compose; this saves about 8 lines per site.


### CTM-20. Inconsistent theory headers and mechanically joined lines

*documentation, impact low, confidence high, ~60 lines.*  
Locations: Quadratic_Variation.thy:1-30, Time_Discretisation.thy:1-30, Doob_Inequality.thy:1-26, Optional_Sampling.thy:1-36, Stopped_Adaptedness.thy:1-16, Modification_Transfer.thy:1-16, Stopping_Times.thy:1-18, Natural_Filtration.thy:1-17, Semidirect_Kernels.thy:1-19, Martingale_Algebra.thy:1-18, Martingale_Transfer.thy:1-18; Vitali_Convergence.thy:119, 149, 160, 374; Moment_Bounds.thy:46; Martingale_Algebra.thy:727

* 11 theories have no `section` before `theory`. Their former title survives as the first, oddly indented line of a text block (e.g. QV:11-12 'Quadratic variation of square-integrable discrete-time\n martingales.'), and they use top-level `section` for internal parts. In the generated PDF these internal sections sit at the same level as the other theories' titles, and the opening text precedes any heading.
* Several lines contain two Isar commands joined by spaces, e.g. `by (rule integrable_tail[OF h K])  have "ennreal ...` (Vitali:119), `qed  have` (:149), `fin)    have t:` (:160), `qed    also have` (:374), `by (simp add: prob_space)  finally show ?thesis .` (Moment_Bounds:46), `show ?thesis  proof (rule ...)` (Martingale_Algebra:727). These are artefacts of a line-based rewriter; Relative_Arbitrage/Path_Stopping_Times.thy:44 has the same.

Evidence: Visible in the listed lines.

Suggested action: Give every theory a leading `section` with its title, demote internal `section` to `subsection`, and re-break the joined lines.


### CTM-21. Unused imports serialise a six-theory chain; several imports are only for one lemma

*build_time, impact low, confidence high, ~10 lines.*  
Locations: Continuous_Time_Martingales/Optional_Sampling.thy:5 (imports Doob_Inequality; uses only time_grid/t_ge_0/t_mono_le from Time_Discretisation); Continuous_Time_Martingales/Stopped_Adaptedness.thy:5 (imports Optional_Sampling; uses nothing from it, only AFP adapted_process + continuous_on_tendsto_compose); Continuous_Time_Martingales/Moment_Bounds.thy:5 (imports Quadratic_Variation only for Power_Inequalities.square_add_le_two); Continuous_Time_Martingales/Integrability_Criteria.thy:5 (imports Martingale_Algebra only for integral_of_bounded_linear, itself a library duplicate); Continuous_Time_Martingales/Semidirect_Kernels.thy:4 (imports Martingales.Martingale; pure Giry-monad measure theory); Continuous_Time_Martingales/Modification_Transfer.thy:4 (does not import Natural_Filtration and therefore re-proves its Dynkin lemma)

Power_Inequalities → Quadratic_Variation → Time_Discretisation → Doob_Inequality → Optional_Sampling → Stopped_Adaptedness is a strict chain of about 3 300 lines. Two of its links carry no dependency: Optional_Sampling does not mention maxabs, Dsup, gsup or horizon_sq_int_martingale, and Stopped_Adaptedness does not mention dgrid, dceil, time_grid or optional_stopping. Cutting them lets Doob_Inequality, Optional_Sampling and Stopped_Adaptedness check in parallel. Integrability_Criteria and Semidirect_Kernels could sit at the bottom of the session.

Evidence: grep -n 'maxabs\|Dsup\|horizon_sq\|gsup\|doob\|prob_sq\|esup' Optional_Sampling.thy: no hits; grep -n 'dgrid\|dceil\|time_grid\|optional_stopping\|t_mono_le' Stopped_Adaptedness.thy: only a mention in a text block (line 14).

Suggested action: Change the imports as follows (one build each, since a theory may still need a [measurable] declaration):
* Optional_Sampling: import Time_Discretisation (or the merged sampling theory).
* Stopped_Adaptedness: import Martingales.Martingale.
* Integrability_Criteria and Semidirect_Kernels: import HOL-Probability.Probability only.
* Modification_Transfer: import Natural_Filtration.


### CTM-22. Power_Inequalities still contains duplicate pairs

*clone, impact low, confidence high, ~70 lines.*  
Locations: Continuous_Time_Martingales/Power_Inequalities.thy:128-138 pow4_diff_le ((a-b)^4 ≤ 8a^4+8b^4) vs :215-243 fourth_power_sum_bound ((a+b)^4 ≤ 8(a^4+b^4)); Power_Inequalities.thy:65 sq_mono_abs / :71 sq_abs_mono; :184 fourth_mono_abs / :194 fourth_abs_mono; Power_Inequalities.thy:47-63 abs_prod_le_sq (|ab| ≤ a²+b²) vs :101-106 abs_prod_le_half_squares (|ab| ≤ a²/2+b²/2); Power_Inequalities.thy:208-211 and :226-231 (inline re-derivations of prod_sq_le_half_pow4 :115)

* The two fourth-power sum bounds are the same inequality under b ↦ -b. They have independent proofs, one via square_add_le_two and prod_sq_le_half_pow4, the other via power2_diff identities and argo, about 40 lines in total.
* sq_abs_mono/fourth_abs_mono differ from sq_mono_abs/fourth_mono_abs only by an |·| around an even power.
* abs_prod_le_sq is a weaker form of abs_prod_le_half_squares, proved separately.
* prod_minus_sq_bound and fourth_power_sum_bound re-derive a²b² ≤ a⁴/2 + b⁴/2 inline instead of citing prod_sq_le_half_pow4.

Evidence: PI:128 `lemma pow4_diff_le: "(a - b)^4 ≤ 8*a^4 + 8*b^4"`; PI:215-217 `lemma fourth_power_sum_bound: ... shows "(a + b)^4 ≤ 8 * (a^4 + b^4)"`.

Suggested action: Keep fourth_power_sum_bound and make pow4_diff_le its instance; drop the *_abs_mono variants (simp with power_abs/abs_power2); derive abs_prod_le_sq from abs_prod_le_half_squares; cite prod_sq_le_half_pow4.


### CTM-23. Further statements used nowhere (textual check)

*dead_code, impact low, confidence medium, ~200 lines.*  
Locations: Continuous_Time_Martingales/Time_Discretisation.thy:116 grid_expected_qvar (only used by :151), :132 grid_qvar_compensates, :137 grid_expectation_sq_mono, :151 grid_expected_qvar_indep, :106 qvar_sampled_fun; Continuous_Time_Martingales/Sampled_Martingale.thy:113-148 martingale_of_cond_increment; Continuous_Time_Martingales/Doob_Inequality.thy:262-291 doob_maximal_inequality'; Continuous_Time_Martingales/Optional_Sampling.thy:80-86 indicator_times_integrable, :646 dceil_grid, :649 dtime_eq_dceil; Continuous_Time_Martingales/Vitali_Convergence.thy:100 integrable_clamp, :314-391 tail_le_moment + unif_integrable_of_moment_bound; Continuous_Time_Martingales/Power_Inequalities.thy:178 pow4_binomial; Continuous_Time_Martingales/Quadratic_Variation.thy:306-602 (see the discrete optional stopping finding)

`grep -rnw NAME --include=*.thy` returns only the defining occurrence for: grid_qvar_compensates, grid_expectation_sq_mono, grid_expected_qvar_indep, martingale_of_cond_increment, doob_maximal_inequality', indicator_times_integrable, dceil_grid, dtime_eq_dceil, integrable_clamp, unif_integrable_of_moment_bound and pow4_binomial. tail_le_moment is used only by unif_integrable_of_moment_bound, and grid_expected_qvar only by grid_expected_qvar_indep. Some of these are legitimate library deliverables: doob_maximal_inequality' and the moment criterion for uniform integrability. Most are leftovers of the duplicated sampling layer.

Evidence: Counts from grep (1 = definition only): see the list in the description.

Suggested action: Delete the leftovers: the grid_* trio, martingale_of_cond_increment, indicator_times_integrable, dceil_grid, dtime_eq_dceil, integrable_clamp and pow4_binomial. Keep doob_maximal_inequality' and unif_integrable_of_moment_bound as advertised library results, or remove them. Confirm with the semantic dependency analysis.


### CTM-24. Raw stopping-time hypotheses and real time / t0 = 0 hard-wired

*generalisation, impact low, confidence medium, ~120 lines.*  
Locations: 22 occurrences of `{ω ∈ space M. τ ω ≤ s} ∈ sets (F s)` (+ separate 0 ≤ τ) in 10 theories: Optional_Sampling.thy:41, :476, :1086; Quadratic_Variation.thy:365; Stopped_Adaptedness.thy:29; Continuous_Path_Spaces/Stopped_Localization.thy; Relative_Arbitrage/{Volatile_Market, Ito_Market, Pair_Path_Laws, Value_Function_Market, Pair_Path_Space, Exit_Time_Semicontinuity}.thy; Martingale_Algebra.thy:152, 189, 225, 417, 500, 640, 702, 754, 850, 903, 930 (real time, t0 = 0) vs :72 martingale_diff, :268 martingale_coarser_filtration (generic index, t0); Martingale_Algebra.thy:272 martingale_coarser_filtration assumes finite_filtered_measure (sigma-finite suffices); Martingale_Transfer.thy:95-98, 190-192, 299-301, 507-509, 773-775 (5 copies of the finite_filtered_measure interpretation boilerplate); `measurable_from_subalg[OF _.subalgebras _.adapted]` ≈ AFP stochastic_process.random_variable (MT:99-100, 257-258, 302-305, 788-792; MA:161-164, 947-948)

* AFP Doob_Convergence packages the hypothesis pair as linearly_filtered_measure.stopping_time, with stopping_time_min/max/const/measurable and pre_sigma. The repository restates it by hand everywhere.
* Martingale_Algebra is inconsistent: some lemmas are generic in the index type and t0, while most fix real time and t0 = 0, even though their proofs (via martingale_of_set_integral_eq) do not need it.
* Martingale_Transfer re-derives finite_filtered_measure five times by the same unfold/blast.

Evidence: Doob_Convergence/Stopping_Time.thy:24 `definition stopping_time :: ('a ⇒ 'b) ⇒ bool where "stopping_time T = ((T ∈ space M → {t0..}) ∧ (∀t≥t0. Measurable.pred (F t) (λx. T x ≤ t)))"`.

Suggested action: Introduce a CTM abbreviation, or adopt the AFP's stopping_time (with `sessions Doob_Convergence`), for the hypothesis pair. Generalise the Martingale_Algebra lemmas to an arbitrary t0 (mechanical). Add a one-line lemma finite_filtered_measureI and use AFP random_variable.


## CPS1

The cluster supplies the probabilistic and deterministic halves of the tightness argument behind Lemma 2.2 of the paper. The core is Increment_Moments.thy (2473 lines). For a real-valued martingale whose compensator grows at rate at most C, it proves a fourth-moment bound along partitions without BDG or Ito (fourth_moment_partition_bound), an L2 bound on sum d_k^2 (sum_sq_squared_bound) and convergence of the remainder along uniform partitions (remainder_tendsto_zero). It ends with E(X_T-X_s)^4 <= 8C^2(T-s)^2 for bounded continuous martingales (fourth_moment_bound_bounded). This is stronger than the paper's 66C^2 and consistent with the paper's trace bound coordinatewise, so the cluster has no faithfulness problem. Increment_Tails adds Markov at the fourth power. Dyadic_Chaining is a uniform form of Klenke (21.8), the deterministic chaining over dyadic anchors. Modulus_Tails turns the moment bound into a geometric tail bound on the dyadic bad event (dyadic_bad_event_tail_mom) and gives a modulus on good paths (modulus_of_good_path). Holder_Interpolation converts dyadic moduli into a global Holder bound. Equicontinuity is Arzela-Ascoli for Holder families, used by Path_Space. Conditional_UI proves uniform integrability of families of conditional expectations.
Main problems:
(1) Increment_Moments is a grab-bag. It mixes martingale moment estimates, generic truncation and uniform-integrability lemmas, two text blocks left over from the paper theory Exit_Class_Limits, and deterministic difference-quotient lemmas for paths (consumed almost only by the paper session). It also has a second `section` at line 1977, which files the difference-quotient material under "Uniform integrability".
(2) Clones. diffquot_all_of_rational and diffquot_all_of_rational_ge are copies of each other. Several blocks inside proofs repeat lemmas proved later in the same file. modulus_of_good_path is re-done in metric form as Path_Tightness.dyadic_pair_modulus. "A martingale has constant mean" and "E[cond_exp f] = E f" are re-proved in CTM and in the paper session.
(3) About 320 lines of dead code, plus the whole of CTM.Moment_Bounds, whose only importer, Increment_Moments, uses nothing from it.
(4) Library duplicates: abs_pow4, zero_le_fourth, three proofs of 2 powr(-g) < 1 (HOL has powr_less_one), integrable_pow4_of_bounded, vanishes_of_rational.
(5) Equicontinuity imports HOL-Complex_Analysis.Great_Picard only for Arzela_Ascoli. This makes about 13.4k lines (6 theories) of complex analysis get checked inside the CPS build, although the ~180 lines needed depend only on HOL-Analysis.
(6) Plenty of paper-specific prose (Lemma 2.2/2.3, Eq. (2.7)/(1.7), outerp, h_S(M), Pi_m, Kfr, theta p') in a session meant to be paper-free.
(7) Imports the plan (section 3.6) asked to drop are still there and serialise the build. Holder_Interpolation imports Modulus_Tails and uses nothing from it. Equicontinuity imports Berge and uses nothing from it. Increment_Moments imports Moment_Bounds and uses nothing from it.
Proposed restructuring:
- Continuous_Time_Martingales gains the martingale-moment part of Increment_Moments (replacing the dead Moment_Bounds), Conditional_UI, expectation_cond_exp and martingale_expectation_eq (into Martingale_Algebra), the integrable power lemmas (Integrability_Criteria), the generic real lemmas (Power_Inequalities) and the tail/clamp lemmas (Vitali_Convergence).
- Continuous_Path_Spaces keeps Dyadic_Chaining and Modulus_Tails (absorbing Increment_Tails and dyadic_pair_modulus, and parametrised by a constant K instead of 8*C^2). It keeps Holder_Interpolation (importing only HOL-Analysis) and Equicontinuity (with a local Arzela-Ascoli and no Complex_Analysis, Berge or Holder_Continuous imports). A new deterministic theory, Path_Difference_Quotients, takes the diffquot_* lemmas and vanishes_of_rational.


### CPS1-1. Equicontinuity pulls all of Great_Picard's imports (13.4k lines of complex analysis) into the CPS build for one 100-line theorem

*build_time, impact high, confidence high, ~180 lines.*  
Locations: Continuous_Path_Spaces/Equicontinuity.thy:6 (imports "HOL-Complex_Analysis.Great_Picard"); Continuous_Path_Spaces/ROOT:16 (sessions ... "HOL-Complex_Analysis"); Continuous_Path_Spaces/Equicontinuity.thy:144 (only use: Arzela_Ascoli); /opt/Isabelle2026-RC3/src/HOL/Complex_Analysis/Great_Picard.thy:614 subsequence_diagonalization_lemma, :661 function_convergent_subsequence, :694 Arzela_Ascoli

HOL-Complex_Analysis is not an ancestor of Continuous_Path_Spaces (parent: Continuous_Time_Martingales = HOL-Probability +). Theories imported from a session listed under `sessions` are therefore loaded again inside the CPS build. The import closure of Great_Picard outside HOL-Analysis is 6 theories with 13,371 lines: Contour_Integration, Cauchy_Integral_Theorem, Winding_Numbers, Cauchy_Integral_Formula, Conformal_Mappings and Great_Picard. Contour_Integration, Cauchy_Integral_Theorem and Winding_Numbers are among the slower theories of the distribution. The only thing used is `Arzela_Ascoli` (Equicontinuity.thy:144). Its proof and its two helpers (Great_Picard.thy:614-790, about 180 lines) use only HOL-Analysis facts: compact_uniformly_equicontinuous, uniform_limit_theorem, separable and uniformly_convergent_eq_cauchy. Nothing else in the repository uses complex analysis; grep finds no holomorphic_on, contour_integral or winding_number.

Evidence: grep -rn Complex_Analysis: only Equicontinuity.thy:6,32 and CPS ROOT:16. Great_Picard imports Conformal_Mappings; the closure computed over the import graph is 6 theories and 13371 lines. Arzela_Ascoli is stated at 'a::euclidean_space => 'b::{real_normed_vector,heine_borel}' and its proof cites compact_uniformly_equicontinuous (Analysis/Elementary_Metric_Spaces.thy:2515), uniform_limit_theorem (Analysis/Uniform_Limit.thy:176), separable (Topology_Euclidean_Space.thy:1974) and function_convergent_subsequence (Great_Picard.thy:661, built on subsequence_diagonalization_lemma :614).

Suggested action: Copy subsequence_diagonalization_lemma, function_convergent_subsequence and Arzela_Ascoli (~180 lines, with attribution) into Equicontinuity, or a small Arzela_Ascoli theory under it, and drop "HOL-Complex_Analysis" from the CPS ROOT. Longer term, propose moving them from Great_Picard to HOL-Analysis upstream. Measure with `isabelle build -o timeout=... Continuous_Path_Spaces` before and after.


### CPS1-2. Increment_Moments is four unrelated theories in one file (2473 lines); the second `section` misfiles the deterministic path lemmas

*misplacement, impact high, confidence high, ~500 lines.*  
Locations: Continuous_Path_Spaces/Increment_Moments.thy:1-1975 (martingale moment estimates); Continuous_Path_Spaces/Increment_Moments.thy:1977 `section \<open>Uniform integrability of the squared increments\<close>` and lines 1999-2143 (sq_tail_*, tendsto_real_of_approximants, clamp_*); Continuous_Path_Spaces/Increment_Moments.thy:2146-2175 (text blocks and abs_diff_le_two, zero_le_fourth from Exit_Class_Limits); Continuous_Path_Spaces/Increment_Moments.thy:2177-2469 (diffquot_all_of_rational, diffquot_lipschitz, diffquot_all_of_rational_ge, vanishes_of_rational)

Only lines 1-1975 are about increment moments. Lines 1999-2143 are generic truncation and tail lemmas for real integrands; their consumer is Path_Tightness, and their natural home is CTM.Vitali_Convergence, which already has clamp_diff_abs, integrable_clamp and tail_le_moment. Lines 2177-2469 are deterministic facts about paths 'real => 'b::real_normed_vector', with no probability in them. Their consumers are Holder_Interpolation (prose only), Exit_Class, Dynamic_Programming_*, Pair_Path_Laws, Path_Splicing and Path_Stopping_Times: 15 + 5 + 5 + 5 uses, almost all in the paper session. Because the second `section` sits at line 1977, the document lists 'Difference quotients of a continuous path, tested at rationals' under 'Uniform integrability of the squared increments'.

Evidence: Increment_Moments.thy:1977 `section` (a second section in one theory); :2177 `subsection \<open>Difference quotients of a continuous path, tested at rationals\<close>`; diffquot_all_of_rational has 15 external uses in 10 Relative_Arbitrage theories; vanishes_of_rational is used in Dynamic_Programming_Delayed_Class, Pair_Path_Laws and Path_Stopping_Times.

Suggested action: Split the file. (a) Increment_Moments keeps lines 1-1975, and moves to CTM per the separate finding. (b) Lines 1999-2143 go to CTM.Vitali_Convergence. (c) Lines 2146-2175 go back to Exit_Class_Limits, or to Power_Inequalities and HOL. (d) Lines 2177-2469 go to a new deterministic theory, Continuous_Path_Spaces/Path_Difference_Quotients.thy, that imports only HOL-Analysis and is checked in parallel with everything else.


### CPS1-3. diffquot_all_of_rational is diffquot_all_of_rational_ge with r := 0 (two 85-line copies)

*clone, impact medium, confidence high, ~85 lines.*  
Locations: Continuous_Path_Spaces/Increment_Moments.thy:2185 diffquot_all_of_rational; Continuous_Path_Spaces/Increment_Moments.thy:2325 diffquot_all_of_rational_ge

The two proofs are line-for-line identical: the definitions of d and e, elim, exp/exq, the choice of p and q, pq, pmem/qmem, the tendsto_sandwich squeezes pl/ql, Yp/Yq and closed_sequentially. The only difference is one extra goal `r <= p n` in inS. Instantiating the _ge version at r = 0 gives the plain one: its extra hypothesis `0 <= p` is already in rat, and `0 <= s` is st(1). The accompanying text says so itself: "l is the same argument at r = 0".

Evidence: Increment_Moments.thy:2319 text: "The rational-to-real step with a lower guard.  \<open>l\<close> is the same argument at \<open>r = 0\<close>". Compare lines 2194-2268 with 2334-2411.

Suggested action: Keep diffquot_all_of_rational_ge. Prove diffquot_all_of_rational as `by (rule diffquot_all_of_rational_ge[where r=0]) (use assms in auto)`. Both proofs could also be replaced by a density argument using continuous_constant_on_closure / closure_convex_Int_superset and Rats_closure_real.


### CPS1-4. modulus_of_good_path's chaining computation is repeated in metric form as Path_Tightness.dyadic_pair_modulus, and dyadic_ext_dist_le repeats dyadic_modulus_extension

*clone, impact medium, confidence high, ~110 lines.*  
Locations: Continuous_Path_Spaces/Modulus_Tails.thy:406-455 (block K inside modulus_of_good_path); Continuous_Path_Spaces/Path_Tightness.thy:1337 dyadic_pair_modulus; Continuous_Path_Spaces/Dyadic_Chaining.thy:260 dyadic_modulus_extension; Continuous_Path_Spaces/Path_Tightness.thy:1510 dyadic_ext_dist_le

dyadic_pair_modulus is strictly more general than the inner claim K of modulus_of_good_path: it works for any metric space and has a factor E (E = 1 gives K). Apart from the factor E, the two proofs have the same steps: m' = max m n, w', z', H, the geometric_tail_sum_le bound S1, and the identical e1/e2/le1/rn0/e3 algebra turning r^n + 2 r^(n+1)/(1-r) into 3 r^n/(1-r). dyadic_ext_dist_le (about 54 lines) repeats the anchor-approximation argument of dyadic_modulus_extension: danchor_le/danchor_gt, |danchor u - danchor v| <= |u-v| + 2/2^k, eventually below 2^-n', then tendsto_upperbound. The only difference is that the limits are dyadic_ext f instead of f.

Evidence: Modulus_Tails.thy:430-450 and Path_Tightness.thy:1388-1405 contain the same `e1`, `e2`, `le1`, `rn0`, `e3` facts verbatim (with E factored out). Dyadic_Chaining.thy:284-313 vs Path_Tightness.thy:1532-1562 follow the same approximation steps.

Suggested action: Move dyadic_pair_modulus into Modulus_Tails, next to geometric_tail_sum_le, and derive modulus_of_good_path from it with E = 1 plus dyadic_modulus_extension. Generalise dyadic_modulus_extension to take the two anchor limits as hypotheses ((lambda k. f (danchor k u)) --> g u), so that Path_Tightness.dyadic_ext_dist_le becomes an instance.


### CPS1-5. Inside Increment_Moments, proofs inline lemmas proved later in the same file

*clone, impact medium, confidence high, ~350 lines.*  
Locations: Increment_Moments.thy:342-364 (Ed2 in second_moment_partition_bound) = interval_sq_le :833; Increment_Moments.thy:515-607 (EY2d2 in fourth_moment_partition_bound) = weighted_interval_bound :866 with f := X(t n) - X(t 0); Increment_Moments.thy:1371-1436 (W, Wmeas, Wnn, Wbnd in expectation_max_sq_tendsto_zero) = :1673-1725 (W, Wmeas, Wnn, Wub in remainder_tendsto_zero); Increment_Moments.thy:1576-1605 (preamble of remainder_tendsto_zero) = :1917-1944 (preamble of fourth_moment_bound_bounded); Increment_Moments.thy:1010-1027, 1421-1431, 1710-1720 (|a-b| <= 2R and then (a-b)^2 <= 4R^2) vs abs_diff_le_two :2154; Increment_Moments.thy:306-340 (EYd) and :477-511 (EY3d)

The file was written bottom-up and then extended, so proofs re-derive facts that were later stated as lemmas. Ed2 is interval_sq_le, apart from the conclusion's bound variable. EY2d2 (92 lines) is weighted_interval_bound at f = X(t n) - X(t 0): f^4 is integrable (iY4) and f is F(t n)-measurable (Y2meas), and even the integrability side lemma iY2dA is a copy of if2dA. The max-squared-increment W is defined twice with its measurability, nonnegativity and 4R^2-bound proofs, about 60 lines each. Two theorems share a 30-line preamble that builds upt_nn, upt_mono, upt_le, XmM, q4, dAint, dAbnd and covm. The bound |a-b| <= 2R and then (a-b)^2 <= 4R^2 is derived three times, though abs_diff_le_two is in the same file. EYd and EY3d are the same pull-out argument, E[Z (X t_{n+1} - X t_n)] = 0 for F(t n)-measurable Z, at Z = Y and Z = Y^3. It is also proved in CTM as Quadratic_Variation.cross_cond_exp_zero (discrete) and Martingale_Algebra.martingale_bounded_test, which states E[Z Y_t] = E[Z Y_s].

Evidence: Compare Increment_Moments.thy:345-363 with :847-857, and :545-606 with :928-972. W_def is at :1371 and :1673 with identical text. CTM: Quadratic_Variation.thy:172 cross_cond_exp_zero; Martingale_Algebra.thy:930 martingale_bounded_test.

Suggested action: Reorder: state interval_sq_eq_dA, interval_sq_le and weighted_interval_bound first and use them in Ed2 and EY2d2. Introduce `definition max_sq_incr X s T m w` with lemmas for measurability, nonnegativity and the 4R^2 bound. Put the bounded-package preamble in a locale (see the structure finding). Derive EYd and EY3d from one lemma `E[Z * (X v - X u)] = 0` for F u-measurable Z, or from martingale_bounded_test.


### CPS1-6. About 320 lines in the cluster are referenced nowhere, directly or transitively, and CTM.Moment_Bounds is dead with them

*dead_code, impact medium, confidence high, ~410 lines.*  
Locations: Increment_Moments.thy:78 increment_second_moment_bound (only an @{thm} mention at :269); Increment_Moments.thy:52 expectation_increment_sq (used only by the former); Increment_Tails.thy:99 partition_max_tail_bound; Increment_Tails.thy:62 fourth_moment_bound_subinterval (used only at Modulus_Tails.thy:159,337, inside the dead lemmas below); Modulus_Tails.thy:127 dyadic_level_tail; Modulus_Tails.thy:304 dyadic_bad_event_tail (only a prose mention at :379); Equicontinuity.thy:183 holder_family_subsequence_dist; Equicontinuity.thy:221 holder_onI_bound; Continuous_Time_Martingales/Moment_Bounds.thy:58 fourth_moment_of_compensated (whole theory, 94 lines)

grep -rnw over all .thy files finds no use of these lemmas outside their own definitions and prose. The 'bounded package' corollaries dyadic_level_tail and dyadic_bad_event_tail are never used; every consumer (Path_Tightness x5, Stopped_Localization, Exit_Class_Tightness) calls the _mom versions. Deleting them makes fourth_moment_bound_subinterval dead too. Moment_Bounds is imported only by Increment_Moments, which uses neither of its two lemmas. It is a second, unused derivation of Eq. (2.7), the Ito/BDG-shaped 66C^2 route. The one actually used is Increment_Moments.fourth_moment_bound_bounded with Stopped_Localization. Completion note section 10 of PLAN_RESTRUCTURING_2 kept Moment_Bounds as 'a named result', but nothing names it. expectation_increment_sq also copies the two-point partition set-up (define t, t0, tmono) of CTM.cond_exp_increment_sq (Sampled_Quadratic_Variation.thy:111-126).

Evidence: Uses found by the scratchpad script uses.sh: increment_second_moment_bound int=2 ext=0; partition_max_tail_bound int=1 ext=0; dyadic_level_tail int=1 ext=0; dyadic_bad_event_tail int=2 ext=0; holder_family_subsequence_dist int=1 ext=0; holder_onI_bound int=1 ext=0. grep for integral_square_le_of_bound or fourth_moment_of_compensated finds only Moment_Bounds.thy itself. Moment_Bounds is imported only by Increment_Moments.thy:5.

Suggested action: Delete these lemmas, adjusting the prose at Increment_Moments.thy:268-273 and Modulus_Tails.thy:379. Either delete Moment_Bounds or, preferably, let the moment part of Increment_Moments replace it in CTM. Keep expectation_increment_sq only if it is used in the simplified second_moment_partition_bound.


### CPS1-7. 'A martingale has constant mean' and 'E[cond_exp f] = E f' are proved generically in CPS and again inline in CTM and the paper session

*clone, impact medium, confidence high, ~120 lines.*  
Locations: Continuous_Path_Spaces/Increment_Moments.thy:26 martingale_expectation_eq; Continuous_Path_Spaces/Increment_Moments.thy:249 expectation_cond_exp; Continuous_Time_Martingales/Martingale_Algebra.thy:903 martingale_mean_zero_of_start; :970-985 (e3 inside martingale_bounded_test); Continuous_Time_Martingales/Quadratic_Variation.thy:260-285; Relative_Arbitrage/Ito_Market.thy:615-630, Pair_Path_Laws.thy:4390-4405, Value_Function_Subsolution.thy:320-333 and :1085-1095

martingale_expectation_eq takes martingale.set_integral_eq at the whole space and applies set_integral_space twice. The same three steps appear inline at least six times elsewhere, and martingale_mean_zero_of_start in CTM is the banach-valued special case with start 0. expectation_cond_exp is cond_exp_set_integral at space M; the e3 block of CTM.martingale_bounded_test re-derives it. Both facts are pure martingale and conditional-expectation theory but live in a path-space session, which is why CTM could not use them. Conditional_UI imports all 2473 lines of Increment_Moments just to get expectation_cond_exp.

Evidence: Increment_Moments.thy:33-42 vs Martingale_Algebra.thy:918-922 vs Quadratic_Variation.thy:266-285: the same `set_integral_eq[OF sp] ... set_integral_space[OF ...]` triple.

Suggested action: Move both lemmas to CTM.Martingale_Algebra. State martingale_expectation_eq at 'c::{banach,second_countable_topology}', which the proof supports unchanged, and derive martingale_mean_zero_of_start from it. Replace the inline copies in CTM and Relative_Arbitrage by citations.


### CPS1-8. Conditional_UI and the integrability helpers are martingale and measure theory, not path-space theory

*misplacement, impact medium, confidence high, ~420 lines.*  
Locations: Continuous_Path_Spaces/Conditional_UI.thy (whole, 290 lines); Continuous_Path_Spaces/Increment_Moments.thy:125-245 (integrable_sq_diff', integrable_pow4_diff, integrable_sq_of_pow4, integrable_prod_sq_sq, integrable_cube_prod, integrable_prod_cube); Continuous_Path_Spaces/Increment_Moments.thy:1321 prod_le_K_split, :2154 abs_diff_le_two, :2064 tendsto_real_of_approximants

Conditional_UI states nothing about paths. It extends CTM.Vitali_Convergence (unif_integrable) with absolute continuity of the integral and uniform integrability of cond_exp families, and its consumers are paper theories (Pair_Path_Space, Dynamic_Programming_Pasting, Path_Law_Sampling). The fourth-power integrability lemmas are pure measure theory over Power_Inequalities. prod_le_K_split and abs_diff_le_two are real inequalities; abs_diff_le_two is used only in Relative_Arbitrage/Exit_Class_Limits. tendsto_real_of_approximants is a plain 3-epsilon lemma.

Evidence: Conditional_UI imports "Continuous_Time_Martingales.Vitali_Convergence" and Increment_Moments, using only expectation_cond_exp from the latter. CTM's ROOT description already advertises "Vitali's theorem" and "the elementary power inequalities every moment estimate runs on".

Suggested action: Move Conditional_UI to CTM, after Vitali_Convergence and Martingale_Algebra. Move the integrable_* helpers to CTM.Integrability_Criteria, and prod_le_K_split and abs_diff_le_two to CTM.Power_Inequalities.


### CPS1-9. Paper constant 8*C^2, exponents 4/2 and the real codomain are hard-wired in the tightness layer

*generalisation, impact medium, confidence high, ~150 lines.*  
Locations: Continuous_Path_Spaces/Modulus_Tails.thy:28 dyadic_level_tail_mom (mom: `... <= 8*C\<^sup>2*(v - u)\<^sup>2`), :207 dyadic_bad_event_tail_mom, :385 modulus_of_good_path (f :: real => real); Continuous_Path_Spaces/Holder_Interpolation.thy:68 telescope_grid, :100 holder_of_dyadic_moduli (f :: real => real); Continuous_Path_Spaces/Path_Tightness.thy (67 occurrences of 8*C^2)

`8*C^2` is the constant of this development's version of Eq. (2.7), yet it appears 29 times in Modulus_Tails and 67 times in Path_Tightness. The library proofs use it only as an opaque nonnegative number; dyadic_level_tail_mom does not even assume 0 <= C. modulus_of_good_path, holder_of_dyadic_moduli and telescope_grid are stated for real-valued f, although dyadic_chaining and dyadic_modulus_extension are already metric_space. Path_Tightness therefore had to re-prove the metric version (dyadic_pair_modulus) and does its vector layer coordinatewise.

Evidence: Modulus_Tails.thy:34-35: `mom: ... (∫ω. (X v ω - X u ω)^4 ∂M) ≤ 8*C\<^sup>2*(v - u)\<^sup>2`; Modulus_Tails.thy:386 `fixes f :: "real ⇒ real"`; Dyadic_Chaining.thy:180 `'b::metric_space`.

Suggested action: Replace 8*C^2 by a parameter K with 0 <= K, instantiated as 8*C^2 only where fourth_moment_bound_bounded is applied. State modulus_of_good_path, telescope_grid and holder_of_dyadic_moduli with dist over 'b::metric_space; telescope_grid becomes a dist triangle sum. Optionally generalise to the exponents (a, 1+b).


### CPS1-10. Unneeded imports serialise the build (plan section 3.6 'drop the imports' was not carried out)

*structure, impact medium, confidence high, ~10 lines.*  
Locations: Holder_Interpolation.thy:5 imports Modulus_Tails (nothing used; only a text mention at :11 via @{theory}); Equicontinuity.thy:8 imports Semicontinuous_Analysis.Berge (nothing used; Path_Space uses box_of_sequential); Equicontinuity.thy:7 imports Kolmogorov_Chentsov.Holder_Continuous (used only by the dead holder_onI_bound); Increment_Moments.thy:5 imports Continuous_Time_Martingales.Moment_Bounds (nothing used); Conditional_UI.thy:5 imports Increment_Moments (only expectation_cond_exp used)

Holder_Interpolation is pure real analysis; every fact it cites is in HOL or Complex_Main. Through Modulus_Tails it nevertheless waits for Increment_Tails, Increment_Moments and Dyadic_Chaining. Conditional_UI waits for all 2473 lines of Increment_Moments for one 15-line lemma. Equicontinuity's Berge import belongs to Path_Space, which uses box_of_sequential from it. PLAN_RESTRUCTURING_2 section 3.6 lists 'Equicontinuity, Holder_Interpolation: drop the imports probe6 flags', and the imports are still there.

Evidence: Facts cited in Holder_Interpolation: reals_power_lt_ex, LeastI_ex, not_less_Least, power_increasing, sum_lessThan_telescope, sum_abs, floor_correct, of_int_floor_le, powr_add, powr_le1, powr_mono2, powr_realpow, powr_powr, ... all from HOL. The only Berge lemma used anywhere in CPS is box_of_sequential, in Path_Space.thy.

Suggested action: Holder_Interpolation imports Complex_Main or HOL-Analysis.Analysis only; turn the @{theory} antiquotation at :11 into plain text. Equicontinuity drops Berge and Holder_Continuous after deleting the dead lemmas, and Path_Space imports Semicontinuous_Analysis.Berge itself. Increment_Moments drops Moment_Bounds. Conditional_UI imports the CTM theory that hosts expectation_cond_exp after the move.


### CPS1-11. second_moment_partition_bound (134 lines) follows in ~20 lines from CTM's energy identity

*simplification, impact medium, confidence medium, ~115 lines.*  
Locations: Continuous_Path_Spaces/Increment_Moments.thy:276-409 second_moment_partition_bound; Continuous_Time_Martingales/Sampled_Quadratic_Variation.thy:83 expectation_sq_sampled; Continuous_Path_Spaces/Increment_Moments.thy:52 expectation_increment_sq, :833 interval_sq_le

The proof re-establishes the energy identity along the partition by an induction with orthogonal cross terms (EYd) and an explicit squaring and expansion. CTM already proves this as expectation_sq_sampled: E[X(t n)^2] = E[X(t 0)^2] + E[sum_k d_k^2]. The two-point identity (expectation_increment_sq, or cond_exp_increment_sq) gives E[(X tn - X t0)^2] = E[X tn^2] - E[X t0^2]. Bochner_Integration.integral_sum splits the sum, interval_sq_le bounds each term by C Δt_k, and sum_lessThan_telescope finishes.

Evidence: expectation_sq_sampled: `(∫ω. (X (t n) ω)^2 ∂M) = (∫ω. (X (t 0) ω)^2 ∂M) + (∫ω. (∑k<n. (X (t (Suc k)) ω - X (t k) ω)^2) ∂M)` under exactly the hypotheses X, t0, tmono, sq that second_moment_partition_bound has.

Suggested action: Re-prove second_moment_partition_bound as the composition expectation_increment_sq + expectation_sq_sampled + integral_sum + sum_mono interval_sq_le + sum_lessThan_telescope. Keep expectation_increment_sq, which is otherwise dead, for this purpose.


### CPS1-12. The martingale fourth-moment estimate (Increment_Moments 1-1975) is CTM material

*misplacement, impact medium, confidence medium, ~1975 lines.*  
Locations: Continuous_Path_Spaces/Increment_Moments.thy:1-1975; Continuous_Time_Martingales/Moment_Bounds.thy (dead, also 'Eq. (2.7)'); Continuous_Path_Spaces/ROOT description ('tightness of a family of path laws from increment moments alone')

Everything up to line 1975 is about a real-valued continuous-time martingale with a compensator. It uses only CTM and HOL-Probability: the martingale locale, cond_exp, expectation_sq_sampled and Power_Inequalities. It never uses the path space C([0,T],'b), Prokhorov, Levy_Prokhorov_Metric or Kolmogorov_Chentsov. CPS advertises tightness from increment moments *alone*, which is what Modulus_Tails consumes through its `mom` hypothesis. CTM already hosts the dead Moment_Bounds for the same Eq. (2.7). Once dyadic_level_tail and dyadic_bad_event_tail are deleted, the chaining layer (Modulus_Tails onward) is martingale-free.

Evidence: Increment_Moments imports only CTM theories (Sampled_Quadratic_Variation, Moment_Bounds). Modulus_Tails.dyadic_bad_event_tail_mom needs only Xm, int4 and mom. Downstream uses of fourth_moment_bound_bounded are in Stopped_Localization, Pathwise/Adapted_Quadratic_Variation and Exit_Class_Limits, all of which have CTM as an ancestor.

Suggested action: Move lines 1-1975 to CTM as Martingale_Fourth_Moments.thy, replacing Moment_Bounds. CPS then starts from Dyadic_Chaining and Modulus_Tails, which need only the moment hypothesis.


### CPS1-13. Dyadic_Chaining, Modulus_Tails and Holder_Interpolation re-prove Klenke 21.7-21.9 as in AFP Kolmogorov_Chentsov, in a uniform form

*library_duplicate, impact medium, confidence medium, ~500 lines.*  
Locations: Continuous_Path_Spaces/Dyadic_Chaining.thy:179 dyadic_chaining vs /opt/afp/thys/Kolmogorov_Chentsov/Kolmogorov_Chentsov.thy:433 dist_dyadic_mn, :642 dist_dyadic_fixed; Continuous_Path_Spaces/Modulus_Tails.thy:28 dyadic_level_tail_mom vs Kolmogorov_Chentsov.thy:104 markov, :171 incr, :223 emeasure_A_leq, :289 measure_A_leq; Continuous_Path_Spaces/Modulus_Tails.thy:207 dyadic_bad_event_tail_mom vs Kolmogorov_Chentsov.thy:297 summable_A, :324 lim_B; Continuous_Path_Spaces/Holder_Interpolation.thy:20 exists_dyadic_level and :100 holder_of_dyadic_moduli vs Kolmogorov_Chentsov.thy:690 dist_dyadic (LEAST n with dist t s >= 1/2^n); Continuous_Path_Spaces/Dyadic_Chaining.thy:260 dyadic_modulus_extension vs Kolmogorov_Chentsov.thy:935 L_dist_K

Mathematically this is the AFP's chaining argument: the per-level Markov and union bound, a summable geometric tail over levels, chaining between dyadics, picking the matching level for a gap, and extension by continuity. The repository version is justified and cannot simply cite the AFP. The AFP lemmas live in locale Kolmogorov_Chentsov_finite with an omega-dependent n0 inside a context. They need an AFP stochastic_process with proc_index = {0..}, the moment hypothesis for all s,t >= 0 in nn_integral/powr form, and they conclude existence of a modification rather than a tail bound uniform over laws. The theory text says this (Dyadic_Chaining.thy:15-18, Increment_Tails.thy:12-15). The repository version, however, is welded to a = 4, 1+b = 2 (gamma < 1/4) and a real codomain, so it is not a generalisation of the AFP result either. The proof techniques differ: floor anchors here, dyadic expansions in the AFP.

Evidence: AFP emeasure_A_leq: `emeasure source (A n) <= C * T * 2 powr (- n * (b - a * γ))`. Repository dyadic_level_tail_mom: `... <= 8*C^2*T*(1/2^j) / l^4` with l = 2 powr(-γ j), i.e. the case a=4, b=1, C ↦ 8C^2. Wiener_Measure/Brownian_Motion_Continuity.thy does use the AFP theorem, so the repository now contains both versions.

Suggested action: Keep the repository version. Generalise it to the AFP's parameter shape, E[dist(X v)(X u)^a] <= K (v-u)^(1+b) and gamma < b/a over a metric codomain, so that it strictly contains the AFP level bounds. Consider offering dyadic_chaining and dyadic_bad_event_tail_mom to the AFP entry. Also fix Equicontinuity's prose, which claims the AFP criterion is used.


### CPS1-14. Two hypothesis bundles are repeated on 13 statements; one already exists as a locale in Pathwise_Quadratic_Variation

*structure, impact medium, confidence medium, ~250 lines.*  
Locations: Increment_Moments.thy:276, 428, 800, 833, 866, 978, 1067 (P, X, t0, tmono, dA_int, dA_bounds, cov); Increment_Moments.thy:1559, 1901; Increment_Tails.thy:62, 99; Modulus_Tails.thy:127, 304 (A_int, A_rate, covA, C, R, bnd, cont); Continuous_Path_Spaces/Pathwise_Quadratic_Variation.thy:377 locale bounded_martingale_compensator; :34 compensator_cond_increment; Continuous_Time_Martingales/Time_Discretisation.thy:31 locale time_grid

Seven partition theorems repeat the same 7-8 assumptions, and each proof starts by rebuilding the same XmM, sfs, spF, iY2/iY4 facts. Six 'bounded package' theorems repeat the same 9 assumptions. That bundle already exists downstream as locale bounded_martingale_compensator (P, X, XA, C, R, bnd, Arate, A0, cont). There the compensator relation is the martingale property of X^2 - A, which compensator_cond_increment converts to the covA form these theorems use. The partition bundle extends CTM's time_grid (t 0 >= 0, monotone).

Evidence: Text of Pathwise_Quadratic_Variation.thy:28-31: "fourth_moment_bound_bounded takes the compensator relation in conditional form (its covA hypothesis), while everything here says instead that X^2 - A is a martingale. This bridges the two".

Suggested action: Define a locale covariation_partition = time_grid + (P, X, dA, C, dA_int, dA_bounds, cov) for the partition lemmas, with the shared integrability facts as locale lemmas. Move bounded_martingale_compensator down to wherever fourth_moment_bound_bounded ends up and state remainder_tendsto_zero and fourth_moment_bound_bounded inside it. This removes about 250 lines of hypothesis and preamble repetition.


### CPS1-15. Elementary facts re-proved although HOL, the AFP or Power_Inequalities already has them (checked in PIDE)

*library_duplicate, impact low, confidence high, ~140 lines.*  
Locations: Increment_Tails.thy:20 abs_pow4; Increment_Moments.thy:2168 zero_le_fourth (10 uses in Relative_Arbitrage); Modulus_Tails.thy:187 powr_ratio_lt_1; Modulus_Tails.thy:397-402 (inline r1); Path_Tightness.thy:61 powr_neg_lt_1; Increment_Moments.thy:1522 integrable_pow4_of_bounded; Increment_Moments.thy:2089 clamp_diff_le_tail_pointwise; Increment_Moments.thy:2419 vanishes_of_rational

(a) abs_pow4 `|x|^4 = x^4` is closed by `simp` through HOL's power_even_abs_numeral [simp] (Parity.thy:491). (b) zero_le_fourth `0 <= a^4` is the same statement as Power_Inequalities.pow4_nonneg (Power_Inequalities.thy:122) and is closed by `simp`. (c) There are three separate proofs that 2 powr (negative) < 1, all instances of HOL's powr_less_one (Transcendental.thy:3001): `by (rule powr_less_one) simp_all`. (d) integrable_pow4_of_bounded (25 lines) is finite_measure.integrable_const_bound (Bochner_Integration.thy:2717) plus Power_Inequalities.fourth_abs_mono. (e) clamp_diff_le_tail_pointwise (31 lines) is a one-liner given Vitali_Convergence.clamp_diff_abs, or by `auto simp: indicator_def abs_if max_def min_def`. (f) vanishes_of_rational (51 lines) is continuous_constant_on_closure (Abstract_Topology_2.thy:288) with closure({0..d} ∩ ℚ) = {0..d}, which follows from closure_convex_Int_superset and Rats_closure_real (Cartesian_Euclidean_Space.thy:455), plus the trivial case d = 0.

Evidence: In a scratch theory over Complex_Main in PIDE session cps1_audit_hol, all of these closed without error: `|x::real|^4 = x^4` by simp; `0 ≤ (a::real)^4` by simp; `γ < 1/4 ⟹ 2 powr (-(1-4*γ)) < 1` by (rule powr_less_one) simp_all; `0 < γ ⟹ 2 powr (-γ) < 1` likewise; `0 ≤ R ⟹ ¦z - max (-R) (min R z)¦ ≤ ¦z¦ * (if R < ¦z¦ then 1 else 0)` by (auto simp: abs_if max_def min_def).

Suggested action: Delete abs_pow4, zero_le_fourth, powr_ratio_lt_1 and powr_neg_lt_1, redirecting uses to simp, pow4_nonneg and powr_less_one. Shorten integrable_pow4_of_bounded, clamp_diff_le_tail_pointwise and vanishes_of_rational to cite the library lemmas.


### CPS1-16. holder_of_dyadic_moduli: max 1 (T powr (1-g)) is unnecessary, and dbound clones lipschitz_imp_holder_bound

*simplification, impact low, confidence high, ~30 lines.*  
Locations: Continuous_Path_Spaces/Holder_Interpolation.thy:108 (statement), :202-226 (dbound); Continuous_Path_Spaces/Holder_Interpolation.thy:324 lipschitz_imp_holder_bound; Continuous_Path_Spaces/Path_Tightness.thy holder_const (inherits the max 1)

dbound proves d <= max 1 (T powr (1-g)) * d powr g by splitting on d <= 1. But d <= T always holds there (dT), so d powr (1-g) <= T powr (1-g) follows directly by powr_mono2. This is exactly the argument of lipschitz_imp_holder_bound 100 lines below. The constant max 1 (T powr (1-g)) can therefore become T powr (1-g), which also simplifies Path_Tightness.holder_const.

Evidence: Checked in PIDE (Complex_Main scratch): `0 < d ⟹ d ≤ T ⟹ 0 < g ⟹ g ≤ 1 ⟹ d ≤ T powr (1 - g) * d powr g` proved in 3 lines (powr_add, mult_right_mono, powr_mono2).

Suggested action: Replace dbound by lipschitz_imp_holder_bound, or a lemma it shares. Optionally strengthen the statement to use T powr (1-g), keeping the old form as a corollary if consumers need it.


### CPS1-17. Hypotheses unused by the proofs

*generalisation, impact low, confidence high, ~40 lines.*  
Locations: Increment_Moments.thy:800 interval_sq_eq_dA (P: prob_space M, tmono); Increment_Moments.thy:833 interval_sq_le (tmono; lower half of dA_bounds); Increment_Moments.thy:276 second_moment_partition_bound (lower half `0 ≤ dA k ω` of dA_bounds); Increment_Moments.thy:2018 sq_tail_bound_of_fourth_moment (M: finite_measure M); Increment_Moments.thy:2121 clamp_integral_error (M: finite_measure M); Increment_Tails.thy:28 fourth_moment_tail (P: prob_space M, fm measurability)

interval_sq_eq_dA never interprets P and never uses tmono; its proof uses only X, t0, sq, dA_int and cov. interval_sq_le passes tmono only to it. The bounds Ed2 and interval_sq_le use only `dA k ω ≤ C*Δt`. sq_tail_bound_of_fourth_moment and clamp_integral_error use only integral_mono, integrable_divide_zero, integral_diff and integral_abs_bound, none of which needs finiteness. fourth_moment_tail relies on integral_Markov_inequality_measure (Bochner_Integration.thy:2013), which needs neither a probability space nor measurability of f.

Evidence: Proof bodies at Increment_Moments.thy:811-831, 2026-2039, 2130-2143 and Increment_Tails.thy:35-57 never mention P/M/tmono/fm. integral_Markov_inequality_measure assumes only `integrable M u`, `A ∈ sets M`, `AE x in M. 0 ≤ u x`, `0 < c`.

Suggested action: Drop the unused hypotheses, or weaken dA_bounds to its upper half in the second-moment lemmas, and adjust the few call sites.


### CPS1-18. Text blocks left behind from Exit_Class_Limits, stale or incorrect prose, and formatting glitches

*documentation, impact low, confidence high, ~60 lines.*  
Locations: Increment_Moments.thy:2148-2152 ('Pathwise the localization is eventually inactive ... Fatou turns the uniform bound above into the bound itself'); Increment_Moments.thy:2160-2164 ('This section instantiates the generic chain at F₂ p = (outerp (fst p) - snd p) $ i $ j'); Equicontinuity.thy:13-41 (route via AFP Kolmogorov_Chentsov, Ito/BDG, 66 C^2); Equicontinuity.thy:233-234 (Berge text); Continuous_Path_Spaces/document/root.tex abstract ('iterating Cauchy--Schwarz'); Increment_Moments.thy:1313 and :1390 (two commands on one line)

The two blocks at 2148 and 2160 belong to Relative_Arbitrage/Exit_Class_Limits. Its subsection 'Fatou removes the localization' (:1389) and its 'L2 bound the generic chain asks for' (:1620) are where abs_diff_le_two and zero_le_fourth are used. Here they describe things that are not in this theory and mention the paper constant outerp. Equicontinuity's introduction says the fourth-moment bound comes from Ito and BDG with 66C^2, and that Kolmogorov's criterion is the AFP's Kolmogorov_Chentsov theorem. The formalisation instead proves 8C^2 without BDG and never uses the AFP criterion in CPS (only Dyadic_Interval and Holder_Continuous are imported). The closing text about Berge is unrelated to the theory. The session abstract says the fourth moment is obtained 'by iterating Cauchy--Schwarz and the tower property'. The proof actually uses the binomial expansion, conditional pull-outs and two-square bounds, and Power_Inequalities says 'no Cauchy-Schwarz or Young machinery is needed'.

Evidence: grep 'generic chain': only Increment_Moments.thy:2160 and Exit_Class_Limits.thy:1620. Exit_Class_Limits.thy:1391: 'abs_diff_le_two lives in Continuous_Path_Spaces.Increment_Moments'. grep 'Kolmogorov_Chentsov.' in CPS: only Dyadic_Interval (Dyadic_Chaining.thy:5) and Holder_Continuous (Equicontinuity.thy:7). Increment_Moments.thy:1313: `by (simp add: right_diff_distrib)  also have`.

Suggested action: Move the two text blocks back to Exit_Class_Limits. Rewrite Equicontinuity's introduction to describe what is actually proved, and drop the Berge sentence. Fix the abstract in root.tex. Split the joined command lines.


### CPS1-19. Paper-specific prose in a session advertised as paper-free

*misplacement, impact low, confidence high, ~120 lines.*  
Locations: Increment_Moments.thy:11-18 (Lemma 2.2, trace(acov)), :272, :411-425, :1552-1556 (acov), :1891-1898, :1979-1997 (Lemma 2.3, h_S(M), Π_m(a) ≥ m-k), :2274 (Eq. (1.7)), :2319-2323 (θ p'), :2414 (additive glue's Kfr); Increment_Tails.thy:11-16, :60; Modulus_Tails.thy:11-25; Holder_Interpolation.thy:314-322 (Pair tightness, X-side/Y-side, norm_Pair_le); Equicontinuity.thy:1 (section title 'The Arzela--Ascoli step of Lemma 2.2 of [paper]'), :13-41, :108

The library is meant to be paper-free, but its prose names lemmas and equations of the paper. It also names consumer internals: outerp, the covariation constraint set S with h_S and Π_m, the additive glue's Kfr hypothesis, the random start θ p', and the pair-path X/Y sides. A theory section title names the paper's lemma.

Evidence: grep -n 'LaiShkolnikovSoner\|Eq\. (\|Lemma 2\|outerp\|Kfr\|acov\|admissible' over the seven files: 37 hits.

Suggested action: Rewrite the text blocks in library terms, for example 'a martingale whose compensator grows at rate at most C'. Move paper motivation (Lemma 2.2/2.3, Eq. (2.7), (1.7), h_S, Π_m) to the Relative_Arbitrage theories that instantiate these results. Retitle Equicontinuity as 'Arzela-Ascoli for Holder families'.


### CPS1-20. Increment_Tails is a 211-line fragment whose only live content is Markov at the fourth power

*structure, impact low, confidence high, ~211 lines.*  
Locations: Continuous_Path_Spaces/Increment_Tails.thy (whole)

After removing the dead partition_max_tail_bound and fourth_moment_bound_subinterval and the library duplicate abs_pow4, only fourth_moment_tail (31 lines) remains. Its consumers are Modulus_Tails and Path_Tightness. The theory exists only to sit in the import chain Increment_Moments -> Increment_Tails -> Modulus_Tails.

Evidence: Uses: fourth_moment_tail is used in Modulus_Tails.thy:74 and Path_Tightness.thy:2010; partition_max_tail_bound has no use; fourth_moment_bound_subinterval is used only inside dead lemmas.

Suggested action: Merge fourth_moment_tail into Modulus_Tails, generalised to a Markov inequality at any power, and delete Increment_Tails.thy.


### CPS1-21. Six 20-line integrability proofs follow one template

*simplification, impact low, confidence medium, ~100 lines.*  
Locations: Increment_Moments.thy:125 integrable_sq_diff', :143 integrable_pow4_diff, :164 integrable_sq_of_pow4, :183 integrable_prod_sq_sq, :205 integrable_cube_prod, :226 integrable_prod_cube, :1522 integrable_pow4_of_bounded

Each proof is `rule Bochner_Integration.integrable_bound[of _ g]`, then a `measurable` step, then an `always_eventually` step that proves norm(f) <= norm(g) from a Power_Inequalities bound plus two nonnegativity facts. Only the bound changes.

Evidence: Lines 131-141, 149-161, 170-180, 189-202, 211-223 and 232-244 differ only in the dominating function and the cited Power_Inequalities lemma.

Suggested action: Add one helper `integrable M g ⟹ f ∈ borel_measurable M ⟹ (⋀x. ¦f x¦ ≤ g x) ⟹ integrable M f` (real version of integrable_bound) and make each lemma a 2-line instance. Move them to CTM.Integrability_Criteria.


### CPS1-22. Two tail functionals for uniform integrability: an indicator-tail in Increment_Moments and an excess-tail in Vitali_Convergence

*clone, impact low, confidence medium, ~80 lines.*  
Locations: Increment_Moments.thy:1999 sq_tail_le_fourth_moment_pointwise, :2018 sq_tail_bound_of_fourth_moment, :2121 clamp_integral_error; Continuous_Time_Martingales/Vitali_Convergence.thy:41 clamp_diff_abs, :314 tail_le_moment, :339 unif_integrable_of_moment_bound

Vitali_Convergence measures the tail as max 0 (|y| - K) and derives the moment bound via tail_le_moment. Increment_Moments and its consumer Path_Tightness instead use |y| * indicator {R < |y|} y and prove a parallel moment-tail bound and clamp error. The two are interchangeable for the purpose; having both doubles the truncation infrastructure.

Evidence: tail_le_moment: `max 0 (|y| - K) <= (1 / K powr (p - 1)) * |y| powr p`. sq_tail_le_fourth_moment_pointwise: `z^2 * indicat_real {w. R < w^2} z <= z^4 / R`.

Suggested action: When moving these lemmas to Vitali_Convergence, keep one tail functional and derive the other in one line (|y| * 1{|y|>R} <= 2 max 0 (|y| - R/2)), or restate Path_Tightness's 3-epsilon argument on the excess tail.


### CPS1-23. Small hand-rolled facts available in Set_Interval and Series

*simplification, impact low, confidence medium, ~50 lines.*  
Locations: Modulus_Tails.thy:344 geometric_tail_sum_le; Modulus_Tails.thy:271-287 (s2 in dyadic_bad_event_tail_mom); Increment_Moments.thy:1296 upart_diff_le, :1254 upart vs Continuous_Time_Martingales/Optional_Sampling.thy:486 dgrid

geometric_tail_sum_le (30 lines) follows from sum_gp (Set_Interval.thy:2572), whose closed form is (r^(n+1) - r^(m+1))/(1-r). The set equality s2, (UN j:{n..}. E j) = (UN m. E (n+m)), takes 17 lines but is a one-line `auto` with le_Suc_ex or an analogue of UN_le_add_shift. upart (a uniform partition capped at T) and CTM's dgrid (a uniform dyadic grid) are near-duplicate grid notions.

Evidence: sum_gp: `(∑i=m..n. x^i) = (if n < m then 0 else if x = 1 then ... else (x^m - x^Suc n) / (1 - x))`.

Suggested action: Shorten these with the library lemmas. Leave upart, since it is used only locally once dead code is removed.


## CPS2

Cluster CPS2 is 7 theories of the Continuous_Path_Spaces session, 9,160 lines in all: Path_Space 1287, Path_Exit_Times 2180, Path_Tightness 2940, Path_Space_Infinite 151, Stopped_Localization 644, Pathwise_Quadratic_Variation 1063, Adapted_Quadratic_Variation 896. I read every line. PIDE was not used: no PIDE session was running, and `start_session` with `no_build` for Continuous_Path_Spaces failed because the HOL-Analysis, HOL-Probability, CTM and CPS heaps are not built. Another process was building HOL-Analysis at the time. All claims below therefore come from reading the source and grepping the repository, the distribution and the AFP. Confidence marks reflect that no claim was checked in Isabelle.

What the cluster proves:
(a) Path_Space. C({0..T},'b) is a Polish metric space for 'b::polish_space. It also proves: Hölder balls are compact; the process-to-path map is measurable (pathify_measurable); path_law, restriction, and that restriction is consistent; the continuous-mapping theorem (weak_conv_on_pushforward); a Fatou bound under weak convergence; and closed-set and open-set portmanteau helpers.
(b) Path_Exit_Times. It defines the capped exit time pexit and the uncapped iexit, and proves that pexit is usc and measurable. Its main theorem is ess_inf_pexit_usc, proved by the Laplace route of Larsson–Ruf (step minorant pstep plus open-set portmanteau). It also has the shifted exit time and vshift, iexit_cap, and a set of continuous path test functionals at real^'m.
(c) Path_Tightness. Paths satisfying the 8C² fourth-moment bound are tight (scalar and vector versions), and a sequence of their laws has a weakly convergent subsequence (Prokhorov). The theory then builds a diagonal subsequence, projective consistency, a Daniell–Kolmogorov limit and a continuous modification (dyadic_ext). It ends with general weak-convergence facts: uniform-integrability transfer, and measure equality/order from integrals against bounded continuous functions.
(d) Path_Space_Infinite. The measurable space of continuous paths on {0..}.
(e) Stopped_Localization. Stopping an L² martingale or its compensated square needs no domination hypothesis. With this, Eq. (2.7) (E(ΔX)^4 ≤ 8C²Δt²) is proved for unbounded L² martingales by localisation and Fatou.
(f) Pathwise_Quadratic_Variation and Adapted_Quadratic_Variation. Quadratic variation (QV) as a dyadic-limsup path functional (qvp, qvps, qvmat) identified with the compensator, and an adapted, everywhere-Lipschitz version (qvsa, qvmata).

Main problems found:
- About 2,000 lines of Path_Tightness are dead: the whole C([0,∞)) projective-limit and continuous-modification construction, plus the scalar tightness chain. The modification part also duplicates AFP Kolmogorov_Chentsov.continuous_modification.
- About 1,100 lines of Path_Exit_Times (the Laplace route to ess_inf_pexit_usc) can be replaced by a short proof. That proof would use only lemmas already present: ess_inf_time_less_iff, pexit_sublevel_open and the open-set portmanteau. CTM's own Essential_Infimum text says the Laplace route is unnecessary.
- About 300 lines of portmanteau wrappers duplicate AFP weak_conv_on_eq1/eq2. There are 5 separate `mweak_conv_fin` interpretations, and two lemmas are exact duplicates of each other.
- There are many internal clones: three proofs that the exit-time sublevel sets are open; the QV Lipschitz-supremum argument three times; the compensator identity twice; and stopped-L² facts proved again in the paper session.
- Real^'m and the paper constant 8C² are hard-wired where a type class or a parameter would do.
- The three martingale/QV theories (e, f) depend on nothing in the path-space part and belong lower in the session hierarchy.
- There is a lot of paper prose and many orphan or stale text blocks. Path_Space even ends with a "Kernel pasting" section heading about paper-session lemmas.


### CPS2-1. About 2,000 lines of Path_Tightness are dead: the C([0,∞)) projective limit and continuous-modification chain, and the scalar tightness chain

*dead_code, impact high, confidence high, ~2010 lines.*  
Locations: Continuous_Path_Spaces/Path_Tightness.thy:647-2416 (path_laws_diagonal_subsequence, path_laws_diagonal_consistent, continuous_map_real_diff, continuous_map_path_eval_nth, continuous_map_path_moment, path_law_limit_moment_bound, marginal_map_measurable, projective_limit_of_consistent_path_laws, lim_coordinate_moment_bound, dyadic_pair_modulus, dyadic_ext, modulus_level_choice, dyadic_ext_tendsto, dyadic_ext_dyadic, dyadic_ext_dist_le, dyadic_ext_continuous_on, lim_coordinate_measurable, lim_coordinate_moment_package, lim_dyadic_good_AE, dyadic_ext_continuous_on_all, dyadic_bad_event_sets_strict, lim_good_set, lim_vector_coordinate_measurable, dyadic_ext_measurable, lim_vector_increment_tail, dyadic_ext_modification, lim_continuous_modification, flip_measurable); Continuous_Path_Spaces/Path_Tightness.thy:127-370 (path_law_holder_ball_bound, tight_on_set_path_laws, path_laws_convergent_subsequence)

Grepping all .thy files finds no use outside Path_Tightness of anything in lines 647-2416. The chain ends in four heads, all unused: projective_limit_of_consistent_path_laws, lim_continuous_modification, path_law_limit_moment_bound and flip_measurable. path_laws_diagonal_consistent is used by nothing; path_laws_diagonal_subsequence is used only by it. The scalar chain is dead too: path_laws_convergent_subsequence is unused; tight_on_set_path_laws is used only by it; path_law_holder_ball_bound only by tight_on_set_path_laws. The paper session uses only the _vec versions. notes/UNUSED_THMS.md lists 3 of the heads (lines 139, 143, 144) but not the roughly 30 supporting lemmas, which die with them.

Evidence: Usage counts (grep -rnw over all .thy files), each name occurring only at its own definition: lim_continuous_modification total=1; projective_limit_of_consistent_path_laws total=1; path_law_limit_moment_bound total=1; flip_measurable total=1; path_laws_convergent_subsequence total=1. path_laws_diagonal_consistent occurs only at 788 and in text at 930 and 1026. Every dyadic_ext*/lim_* name is used only inside Path_Tightness.

Suggested action: Delete lines 647-2416 (keep weak_conv_on_integral_unif_integrable and everything after 2416) and lines 127-370. If a C([0,∞)) construction is ever needed, use AFP Kolmogorov_Chentsov.continuous_modification (see the next finding) instead of reviving dyadic_ext.


### CPS2-2. The dyadic_ext continuous modification re-proves AFP Kolmogorov_Chentsov.continuous_modification, which the session already depends on

*library_duplicate, impact high, confidence high, ~1060 lines.*  
Locations: Continuous_Path_Spaces/Path_Tightness.thy:1325-2388 dyadic_ext, dyadic_ext_tendsto, dyadic_ext_modification, lim_continuous_modification; /opt/afp/thys/Kolmogorov_Chentsov/Kolmogorov_Chentsov.thy:1349 continuous_modification, 1355 Kolmogorov_Chentsov

lim_continuous_modification builds a continuous version of a process from the 4th-moment bound by dyadic extension. The AFP theorem Kolmogorov_Chentsov gives a locally γ-Hölder modification on {0..} for any 'b::polish_space process with ∫⁺ dist^a ≤ C·dist^(1+b). With a=4, b=1 and γ<1/4 this is exactly the situation here; the vector bound follows from the coordinate bounds via norm_le_l1_cart. The CPS ROOT already lists `sessions Kolmogorov_Chentsov`. Equicontinuity.thy:25-29 says in its prose that this is the intended route.

Evidence: AFP: `theorem Kolmogorov_Chentsov: ... assumes expectation: ∫⁺ x. dist (X t x) (X s x) powr a ∂proc_source X ≤ C * dist t s powr (1+b) shows ∃X'. modification X X' ∧ (∀ω. local_holder_on γ {0..} (λt. X' t ω))`. Equicontinuity.thy:25: 'Kolmogorov's criterion is Kolmogorov_Chentsov.Kolmogorov_Chentsov, whose hypothesis is literally the moment bound of Eq. (2.7)'.

Suggested action: Delete the chain (it is dead anyway). If the result is needed again, derive it from Kolmogorov_Chentsov.


### CPS2-3. ess_inf_pexit_usc uses the 1,100-line Laplace route; the library already has the tools for a roughly 60-line direct proof

*simplification, impact high, confidence medium, ~1050 lines.*  
Locations: Continuous_Path_Spaces/Path_Exit_Times.thy:193-1316 (ess_inf_time_le_laplace, ess_inf_time_eq_laplace_inf, pstep, pstep_sandwich, pstep_integral, weak_conv_open_liminf, weak_conv_closed_limsup, weak_conv_closed_full_mass, weak_conv_total_mass, pstep_integral_liminf, pstep_integrable, exp_pexit_integral_liminf, ess_inf_pexit_usc); Continuous_Time_Martingales/Essential_Infimum.thy:96-108 (text), 216 ess_inf_time_less_iff; Continuous_Path_Spaces/Path_Space.thy:1026 weak_conv_open_positive_eventually

The claim Limsup_i essinf_{Λi} pexit ≤ essinf_Λ pexit follows directly via Limsup_le_iff: for every y > essinf_Λ, eventually essinf_{Λi} < y. Step 1: ess_inf_time_less_iff (CTM) turns essinf_Λ < y into Λ{pexit<y} > 0. Step 2: {pexit<y} is open (pexit_sublevel_open), so the open-set portmanteau (weak_conv_open_positive_eventually, or AFP weak_conv_on_eq2) makes Λi{pexit<y} > 0 eventually. Step 3: ess_inf_time_less_iff again. pstep, the Laplace representation and exp_pexit_integral_liminf all become unnecessary. CTM's own prose says so: 'This gives a shorter route to Larsson–Ruf's Lemma 2.1 than theirs ... the closed-set form of Portmanteau closes it in one step, with no Laplace transform needed.' Path_Exit_Times.thy:11-19 nevertheless advertises the Laplace route.

Evidence: Essential_Infimum.thy:101-108 (quoted above). ess_inf_time_less_iff: 'ess_inf_time M tau < d ⟷ emeasure M {ω∈space M. ennreal (tau ω) < d} ≠ 0'. weak_conv_open_positive_eventually: '0 < measure N G ⟹ eventually (λi. 0 < measure (Ni i) G)'. Consumers: Exit_Class_Optimizer.thy:75 and Path_Law_Pasting.thy:909 use only the statement of ess_inf_pexit_usc.

Suggested action: Re-prove ess_inf_pexit_usc directly, keeping its statement (the probability hypotheses can probably be weakened). Then delete pstep* and exp_pexit_integral_liminf. Move ess_inf_time_le_laplace and ess_inf_time_eq_laplace_inf to CTM.Essential_Infimum only if wanted as library facts; otherwise delete them.


### CPS2-4. Seven portmanteau wrappers, with 5 separate mweak_conv_fin interpretations, duplicate AFP weak_conv_on_eq1/eq2 and each other

*library_duplicate, impact medium, confidence high, ~300 lines.*  
Locations: Continuous_Path_Spaces/Path_Space.thy:958 weak_conv_closed_full_measure; Continuous_Path_Spaces/Path_Space.thy:1026 weak_conv_open_positive_eventually; Continuous_Path_Spaces/Path_Exit_Times.thy:662 weak_conv_open_liminf; Continuous_Path_Spaces/Path_Exit_Times.thy:739 weak_conv_closed_limsup; Continuous_Path_Spaces/Path_Exit_Times.thy:795 weak_conv_closed_full_mass; Continuous_Path_Spaces/Path_Exit_Times.thy:819 weak_conv_total_mass; Continuous_Path_Spaces/Path_Tightness.thy:2563 (interpretation inside metric_measure_eqI_bounded_cts); /opt/afp/thys/Levy_Prokhorov_Metric/General_Weak_Convergence.thy:883-905 weak_conv_on_eq1, weak_conv_on_eq2; :876 mweak_conv_fin.mweak_conv_imp_limit_space

For metrizable X the AFP gives directly: weak_conv_on Ni N F X ⟷ total mass converges ∧ (∀A closed. Limsup ≤ N A), and the corresponding open-set Liminf form. Each wrapper here instead re-runs the same block: an `interpret mweak_conv_fin`, a uniformly-continuous-to-continuous conversion (cb/cg), and mweak_conv2 or mweak_conv3. This happens in 4 places, plus a 5th at Path_Tightness:2563. weak_conv_open_liminf and weak_conv_closed_limsup are stated at path_metric T, although they hold for any metric. weak_conv_total_mass is the `mass` block of weak_conv_open_liminf (713-730) and also AFP mweak_conv_imp_limit_space. weak_conv_closed_full_mass (PET) is weak_conv_closed_full_measure (PS) at m = path_metric T, with an extra hypothesis `probs` that is never used.

Evidence: PET:795 `weak_conv_closed_full_mass` assumes 'probs: ⋀i. prob_space (Λi i)', and its proof (805-816) never mentions probs. PS:958 `weak_conv_closed_full_measure`: 'weak_conv_on Ni N sequentially (mtopology_of m) ⟹ closedin ... A ⟹ (⋀i. measure (Ni i) A = 1) ⟹ prob_space N ⟹ measure N A = 1'.

Suggested action: Gather the wrappers in one weak-convergence theory, stated for an arbitrary metric m. Prove each in 2-5 lines from weak_conv_on_eq1/eq2 with metrizable_space (mtopology_of m). Delete weak_conv_closed_full_mass and rewrite its 2 uses (Exit_Class.thy:315, 650) to weak_conv_closed_full_measure. Inline or delete weak_conv_total_mass.


### CPS2-5. Three separate proofs that a strict sublevel set of an exit time is open in the path topology

*clone, impact medium, confidence high, ~110 lines.*  
Locations: Continuous_Path_Spaces/Path_Space.thy:750 open_hit_strictly_before (and open_eval_preimage at 784, which repeats its inner step); Continuous_Path_Spaces/Path_Exit_Times.thy:140 pexit_sublevel_open (inner `ev` at 154-167 repeats open_eval_preimage); Continuous_Path_Spaces/Path_Exit_Times.thy:1321 open_etime_shift_less

All three write {f. etime … f < c} as a union over witness times r of evaluation preimages, then apply openin_Union. open_hit_strictly_before is the hit set {f. ∃r≤T. r<c ∧ f r ∈ A}. pexit_sublevel_open is the same set for A = -K, by pexit_less_iff. open_etime_shift_less is the same set for the translated open set {z. y+z∈A}. It goes through etime_less_iff_qtimes_open, which needs path continuity and countability; an open union needs neither. open_hit_strictly_before is used nowhere (only mentioned in prose at Pair_Path_Space.thy:109). Its text at 740-748 claims it lives in Path_Space because etime_less_iff 'lives on a different import branch'; that is no longer true, since Path_Exit_Times imports both.

Evidence: grep: open_hit_strictly_before occurs only in its definition, in dispositions.tsv and in UNUSED_THMS.md:134. The 'brick' text at PS:780: 'The brick the proof above used inline, now stated on its own'.

Suggested action: Prove one lemma in Path_Exit_Times: for open A, if each f ↦ Φ r f is continuous on the path topology, then {f ∈ mspace. etime T A Φ f < c} is openin. Derive pexit_sublevel_open and open_etime_shift_less from it in 2 lines each. Delete open_hit_strictly_before and its text.


### CPS2-6. Path-space facts that Path_Space should provide are re-proved inline or in the paper session at the product type (plan §3.6 items still open)

*clone, impact medium, confidence high, ~170 lines.*  
Locations: Relative_Arbitrage/Pair_Path_Laws.thy:263 restrict_in_mspace (= Path_Space.thy:513 restrict_mspace_path_metric); Relative_Arbitrage/Pair_Path_Laws.thy:1294 measurable_into_path_metric and :1335 mdist_measurable_of_eval (= the ball/sup-over-rationals core of Path_Space.thy:328 pathify_measurable); Relative_Arbitrage/Pair_Path_Space.thy:1253 space_of_path_sets (54 uses), re-derived inline at Path_Exit_Times.thy:605-607, 989-991, 1701-1702, 1778-1779 and Path_Space.thy:1071-1072; Relative_Arbitrage/Pair_Path_Laws.thy:285 standard_borel_path_metric, :291 mspace_path_metric_ne

restrict_in_mspace is restrict_mspace_path_metric specialised to pairs. measurable_into_path_metric + mdist_measurable_of_eval re-run the second-countable-balls-plus-rational-sup argument of pathify_measurable: any map into mspace whose evaluations are measurable is measurable. space_of_path_sets is a one-liner that this cluster re-derives inline at least five times. None of these lemmas is pair-specific.

Evidence: Pair_Path_Laws:263 'restrict ω {0..s} ∈ mspace (path_metric s :: (real ⇒ 'a × 'b) metric)', proved from Lipschitz_restrict_path_metric. PS:513 restrict_mspace_path_metric has the same statement for 'b::polish_space. PLAN §3.6 lists 'space_of_path_sets, mspace_path_metric_ne, restrict_in_mspace' for moving to Path_Space.

Suggested action: In Path_Space, at 'b::polish_space, add space_of_path_sets, mspace_path_metric_ne, standard_borel_path_metric, and a general measurable_into_path_metric_of_eval with pathify_measurable as a 5-line corollary. Delete the paper-session copies and the inline re-derivations.


### CPS2-7. Scalar and vector tightness theorems are near-verbatim copies; one statement at 'b::euclidean_space would cover both

*clone, impact medium, confidence high, ~245 lines.*  
Locations: Continuous_Path_Spaces/Path_Tightness.thy:127 path_law_holder_ball_bound vs :384 path_law_holder_ball_bound_vec; Continuous_Path_Spaces/Path_Tightness.thy:248 tight_on_set_path_laws vs :530 tight_on_set_path_laws_vec; Continuous_Path_Spaces/Path_Tightness.thy:336 path_laws_convergent_subsequence vs :611 path_laws_convergent_subsequence_vec

Each _vec proof repeats its scalar twin line for line, adding a union over coordinates (finite_measure_subadditive_finite) and norm_le_l1_cart. The q^n→0 tail block is repeated a third time in lim_dyadic_good_AE (1691-1701). The scalar versions are dead (see the dead-code finding). Stating the vector version for 'b::euclidean_space with coordinates x•i, i∈Basis, factor card Basis, covers real and real^'m in one theorem.

Evidence: PT:170-171 (Bad) vs 434-436 (Bad i); PT:288-301 vs 570-585 (q, q0, q1, lim, obtain n); PT:353-370 vs 628-645 (rule tight_on_set_imp_convergent_subsequence).

Suggested action: Delete the scalar versions. Optionally restate the _vec versions over Basis of 'b::euclidean_space. Note that the paper session at Pair_Path_Space.thy:438 runs its own copy of this argument at the pair type.


### CPS2-8. The paper's fourth-moment constant 8·C²·(v−u)² is hard-wired into a library tightness theory

*generalisation, impact medium, confidence high, ~60 lines.*  
Locations: Continuous_Path_Spaces/Path_Tightness.thy:138, 260, 347, 396, 542, 622, 669, 799, 979, 1254, 1624, 1658, 1987, 2064, 2287; Continuous_Path_Spaces/Modulus_Tails.thy:207 dyadic_bad_event_tail_mom (outside this cluster, the source of the constant); Continuous_Path_Spaces/Stopped_Localization.thy:371 fourth_moment_L2

Every tightness hypothesis reads (∫(X v − X u)^4) ≤ 8*C²*(v−u)², the constant of the paper's Eq. (2.7). For tightness only a bound B·(v−u)² matters, or in Kolmogorov form B·(v−u)^(1+b). The library would be more reusable with the constant as a parameter. In Stopped_Localization the 8C² is a genuine output (a theorem about martingales), which is fine.

Evidence: PT:137-138: 'mom: ⋀u v. 0 ≤ u ⟹ u ≤ v ⟹ v ≤ T ⟹ (∫ω. (X v ω − X u ω)^4 ∂M) ≤ 8*C²*(v − u)²'.

Suggested action: Replace 8*C² by a parameter B ≥ 0 in dyadic_bad_event_tail_mom and in the Path_Tightness statements. Consumers instantiate B = 8*C².


### CPS2-9. qvps_mono_lip and qvps_continuous are corollaries of the qvsa lemmas; the rational-supremum Lipschitz argument appears three times

*simplification, impact medium, confidence high, ~200 lines.*  
Locations: Continuous_Path_Spaces/Adapted_Quadratic_Variation.thy:155-297 qvps_mono_lip, :299 qvps_continuous; Continuous_Path_Spaces/Adapted_Quadratic_Variation.thy:506 qvsa_mono, :531-622 qvsa_lip, :624 qvsa_continuous, :648 qvsa_eq_qvps; Continuous_Path_Spaces/Pathwise_Quadratic_Variation.thy:736-768 (main block inside qvps_eq_A)

qvsa_eq_qvps gives: qvp_good C w ⟹ qvsa C w t = qvps w t. qvsa_mono, qvsa_lip and qvsa_continuous hold for every path. So qvps_mono_lip (140 lines, same hypothesis qvp_good C w) follows from these in about 3 lines, and qvps_continuous in about 2. qvps_mono_lip is used only by qvps_continuous, and qvps_continuous is used nowhere. The ε/(C+1) rational-approximation argument with of_rat_dense appears three times: PQV 746-767, AQV 258-293 and AQV 569-613. The 'rationals in (0,t) are non-empty' block appears five times: AQV 117-122, 168-173, 219-224, 239-240; PQV 727-732.

Evidence: grep: qvps_continuous total=1 (definition only); qvps_mono_lip is used only in qvps_continuous.

Suggested action: Delete qvps_mono_lip and qvps_continuous, or derive them after qvsa_eq_qvps. Extract a lemma: the supremum over rationals below t of a monotone C-Lipschitz function is C-Lipschitz, and equals it at points of continuity. Use it in qvps_eq_A and qvsa_lip.


### CPS2-10. The compensator identity cond_exp(ΔX²) = cond_exp(ΔA) is proved twice; the hypothesis Aad is derivable

*clone, impact medium, confidence high, ~60 lines.*  
Locations: Continuous_Path_Spaces/Pathwise_Quadratic_Variation.thy:33-74 compensator_cond_increment; Continuous_Path_Spaces/Stopped_Localization.thy:305-329 (tail of stopped_covariation); Continuous_Path_Spaces/Pathwise_Quadratic_Variation.thy:398-408 Ameas vs :48-58 Aadapt; Continuous_Path_Spaces/Stopped_Localization.thy:233, 365, 577, 606 (hypothesis Aad)

stopped_covariation ends with the same five-step cond_exp calculation (cond_exp_increment_sq, cond_exp_diff twice, martingale_property, cond_exp_F_meas) as compensator_cond_increment. It is that lemma applied to the stopped pair (XS, AS), and sqXS and iAS supply its integrability hypotheses. compensator_cond_increment also shows that adaptedness of A follows from X and X²−A being martingales (Aadapt). Hence the hypothesis `Aad: adapted_process M F 0 A` of stopped_covariation, fourth_moment_L2 and its two corollaries is redundant. The same derivation is repeated a third time as Ameas in the locale.

Evidence: PQV:59-73 and SL:310-329 use the same rule chain. PQV:50 'have Aeq: (λω. (X u ω)² − ((X u ω)² − A u ω)) = A u'.

Suggested action: Move compensator_cond_increment below Increment_Moments (Stopped_Localization can import it) and use it in stopped_covariation. Factor out 'A adapted from X and X²−A martingales' as a lemma, then drop Aad from the four Stopped_Localization statements.


### CPS2-11. General weak-convergence and measure theory scattered over three path theories; generic helpers stranded

*misplacement, impact medium, confidence high, ~900 lines.*  
Locations: Continuous_Path_Spaces/Path_Space.thy:614-1009 (weak_conv_on_pushforward, weak_conv_on_nn_integral_le, weak_conv_on_prob_space, weak_conv_closed_full_measure, weak_conv_open_positive_eventually); Continuous_Path_Spaces/Path_Exit_Times.thy:657-842 (portmanteau wrappers); Continuous_Path_Spaces/Path_Tightness.thy:2419-2922 (weak_conv_on_integral_unif_integrable, weak_conv_on_prob_limit, metric_measure_eqI/mono_bounded_cts, unif_integrable_of_L2_bound, weak_conv_integral_of_L2_bound); Continuous_Path_Spaces/Path_Exit_Times.thy:198, 275 ess_inf_time_le_laplace, ess_inf_time_eq_laplace_inf (any probability space) → CTM.Essential_Infimum; Continuous_Path_Spaces/Pathwise_Quadratic_Variation.thy:233 AE_tendsto_zero_of_summable_sq → CTM.Integrability_Criteria; Continuous_Path_Spaces/Pathwise_Quadratic_Variation.thy:795 inner_mv_axis → Symmetric_Matrix_Spectra.Matrix_Algebra (generalises quadform_axis_pair and quadform_axis_pair_minus at :631, 663); Continuous_Path_Spaces/Stopped_Localization.thy:334 etime_eq_T_of_no_hit → CTM.Stopping_Times; Continuous_Path_Spaces/Path_Exit_Times.thy:1913-2008 (rclamp and the test functionals are not about exit times)

None of these statements mentions the path metric, or only as an arbitrary metric m. The weak-convergence results are a coherent 'Weak_Convergence_Extras' theory on top of Levy_Prokhorov_Metric. inner_mv_axis, (e_i + c e_j)•(B(e_i + c e_j)) = B_ii + c(B_ij + B_ji) + c²B_jj, generalises SMS's quadform_axis_pair and quadform_axis_pair_minus (c = ±1 with symmetry). Using it there needs SMS as a CPS dependency, which is cheap because it is HOL-Analysis-based.

Evidence: Matrix_Algebra.thy:631 '(axis i 1 + axis j 1) • (a *v (axis i 1 + axis j 1)) = a$i$i + a$j$j + 2 * a$i$j' (assuming transpose a = a).

Suggested action: Create a Continuous_Path_Spaces theory Weak_Convergence_Extras, imported by Path_Space, and move the weak-convergence lemmas there. Move the Laplace, summability and etime facts to CTM, inner_mv_axis to SMS, and rclamp and the test functionals to Path_Space or a Path_Test_Functionals theory.


### CPS2-12. Stopped-L² facts are re-proved in Stopped_Localization and again in the paper session

*clone, impact medium, confidence medium, ~120 lines.*  
Locations: Continuous_Path_Spaces/Stopped_Localization.thy:290-304 iAS vs :425-439 A_intS; Continuous_Path_Spaces/Stopped_Localization.thy:269-289 sqXS; Continuous_Path_Spaces/Stopped_Localization.thy:22 stopped_martingale_L2; Relative_Arbitrage/Pair_Path_Laws.thy:1516-1600 horizon_sq_int_martingale_stopped; Continuous_Path_Spaces/Stopped_Localization.thy:33-38, 131-136, 252-257 (contXu, three times)

Integrability of the stopped compensator is proved twice in the same file with identical text (iAS and A_intS). Square-integrability of the stopped martingale via Dsup² (sqXS) is re-proved in Pair_Path_Laws.horizon_sq_int_martingale_stopped. That lemma also re-proves stopped_martingale_L2 for a martingale capped at T, using optional_stopping[where D=λ_. Dsup]. The 'continuous on {0..u} a.e.' block and the Dex/SOME D/DP pattern each appear twice or more.

Evidence: SL:291-303 vs SL:426-438: identical apart from ?AS vs ?AS n. Pair_Path_Laws:1561-1572 calls optional_stopping with the same 7 obligations as SL:56-66.

Suggested action: Add lemmas stopped_compensator_integrable and stopped_L2_sq_integrable to Stopped_Localization, and a wrapper of optional_stopping taking ∃D. Have Pair_Path_Laws use stopped_martingale_L2.


### CPS2-13. Stopped_Localization, Pathwise_Quadratic_Variation and Adapted_Quadratic_Variation do not depend on the path space; AQV's import of Stopped_Localization is unused

*misplacement, impact medium, confidence medium, ~2600 lines.*  
Locations: Continuous_Path_Spaces/Stopped_Localization.thy:5-6 imports (CTM theories + Increment_Moments only); Continuous_Path_Spaces/Pathwise_Quadratic_Variation.thy:5-6 imports (Increment_Moments + CTM.Martingale_Algebra only); Continuous_Path_Spaces/Adapted_Quadratic_Variation.thy:5 imports Pathwise_Quadratic_Variation Stopped_Localization

These 2,600 lines are about L² martingales, stopping and quadratic variation of real-valued functions (qvp :: (real ⇒ real) ⇒ real ⇒ real). They use nothing from Path_Space, path_metric, Prokhorov or Levy_Prokhorov. Together with Increment_Moments and Increment_Tails (outside this cluster) they form a martingale-moment and QV layer that fits CTM's described scope ('quadratic variation and its compensator', 'Moment_Bounds'), or a small session between CTM and CPS. Inside CPS they wait for the session-level dependencies HOL-Complex_Analysis, Levy_Prokhorov_Metric, Standard_Borel_Spaces and Kolmogorov_Chentsov, which they do not need. AQV never refers to any lemma of Stopped_Localization (grep finds stopped_*, fourth_moment_L2 and rate_continuous_on only in prose at AQV:27), so the import only serialises the build. Stopped_Localization imports Martingale_Transfer only so that the restrict_full lemmas listed in its final text block are re-exported.

Evidence: grep -n 'stopped_martingale_L2|stopped_compensated_square|stopped_covariation|rate_continuous_on|fourth_moment_L2|etime' Adapted_Quadratic_Variation.thy finds nothing. Exit_Class_Marginals.thy:182 says 'restrict_full package of Stopped_Localization', but the lemmas are at CTM Martingale_Transfer.thy:821ff.

Suggested action: Move Increment_Moments, Increment_Tails, Stopped_Localization, Pathwise_Quadratic_Variation and Adapted_Quadratic_Variation to CTM, or to a new session such as Martingale_Moments = CTM + ..., and update the CPS ROOT description. Remove AQV's import of Stopped_Localization. Have consumers import Martingale_Transfer directly and remove the re-export import.


### CPS2-14. Path_Tightness mixes four unrelated topics and Path_Exit_Times three

*structure, impact medium, confidence medium, ~0 lines.*  
Locations: Continuous_Path_Spaces/Path_Tightness.thy (tightness 1-645; diagonal/projective/modification 647-2416; general weak convergence 2419-2922); Continuous_Path_Spaces/Path_Exit_Times.thy (exit times 1-191, 1394-1802, 2010-2176; Laplace usc 193-1316; test functionals 1913-2008)

Path_Tightness has 2,940 lines, of which only about 645 are tightness. After the dead-code removal and the move of the weak-convergence lemmas it shrinks to about 400. Path_Exit_Times has 2,180 lines and would drop to roughly 1,000 with the direct ess_inf_pexit_usc proof and the test functionals moved out.

Evidence: Section boundaries are quoted in the findings above.

Suggested action: Proposed Continuous_Path_Spaces layout: Weak_Convergence_Extras → Path_Space (with the space_of_path_sets family) → Path_Space_Infinite → Path_Exit_Times (exit times plus usc only) → Path_Tightness (vector tightness only). The QV and stopping theories move to CTM or a Martingale_Moments session.


### CPS2-15. weak_conv_on_prob_space (Path_Space) and weak_conv_on_prob_limit (Path_Tightness) are the same lemma

*clone, impact low, confidence high, ~25 lines.*  
Locations: Continuous_Path_Spaces/Path_Space.thy:918 weak_conv_on_prob_space; Continuous_Path_Spaces/Path_Tightness.thy:2504 weak_conv_on_prob_limit

Both state: if weak_conv_on Ni N sequentially X and every Ni i is a probability space, then prob_space N. The proofs are the same (test against the constant 1). Each has one consumer: Exit_Class_Optimizer.thy:170 and Exit_Time_Semicontinuity.thy:239 respectively.

Evidence: PS:918-922 'fixes Ni :: nat ⇒ 'b measure assumes wc: weak_conv_on Ni N sequentially X and P: ⋀i. prob_space (Ni i) shows prob_space N'. PT:2504-2508 has the same text, with only an extra `fixes X :: 'b topology`.

Suggested action: Delete weak_conv_on_prob_limit and rename its single use.


### CPS2-16. mspace_path_metricD and mspace_path_metric_continuous are the same lemma

*clone, impact low, confidence high, ~15 lines.*  
Locations: Continuous_Path_Spaces/Path_Space.thy:113 mspace_path_metricD; Continuous_Path_Spaces/Path_Space.thy:289 mspace_path_metric_continuous

Both state: f ∈ mspace (path_metric T) ⟹ continuous_on {0..T} f. The second has a one-line proof; the first takes 10 lines. Both have several consumers in Relative_Arbitrage.

Evidence: PS:113-116 'assumes f: f ∈ mspace (path_metric T) shows continuous_on {0..T} f'. PS:289-292 'assumes g ∈ mspace (path_metric T) shows continuous_on {0..T} g'.

Suggested action: Keep one; make the other a `lemmas` alias or rename its uses (8 uses in total).


### CPS2-17. dyadic_pair_modulus duplicates the core of Modulus_Tails.modulus_of_good_path, and powr_neg_lt_1 duplicates an inline block

*clone, impact low, confidence high, ~110 lines.*  
Locations: Continuous_Path_Spaces/Path_Tightness.thy:1337-1410 dyadic_pair_modulus; Continuous_Path_Spaces/Modulus_Tails.thy:409-457 (block K inside modulus_of_good_path); Continuous_Path_Spaces/Path_Tightness.thy:61 powr_neg_lt_1 vs Modulus_Tails.thy:415-419 and :187 powr_ratio_lt_1; Continuous_Path_Spaces/Path_Tightness.thy:1510 dyadic_ext_dist_le vs Dyadic_Chaining.thy:260 dyadic_modulus_extension

dyadic_pair_modulus repeats the geometric-tail calculation (S1, e1, e2, le1, rn0, e3) of modulus_of_good_path line for line, with an extra factor E and a metric codomain. modulus_of_good_path is the case E=1, real codomain, composed with dyadic_modulus_extension. dyadic_ext_dist_le repeats the anchor-approximation argument of dyadic_modulus_extension (2/2^k gap, tendsto_upperbound).

Evidence: Same proof text: PT:1384-1405 vs Modulus_Tails:425-450 (e1/e2/e3, 'nonzero_mult_div_cancel_right[OF ne]').

Suggested action: If dyadic_pair_modulus survives the dead-code removal, move it to Modulus_Tails and derive modulus_of_good_path from it plus dyadic_modulus_extension. Otherwise derive powr_neg_lt_1 once and reuse it inside modulus_of_good_path.


### CPS2-18. 'Monotone C-rate on {0..} implies continuous' is proved four times

*clone, impact low, confidence high, ~60 lines.*  
Locations: Continuous_Path_Spaces/Stopped_Localization.thy:104-122 (contA inside stopped_compensated_square); Continuous_Path_Spaces/Stopped_Localization.thy:193 rate_continuous_on; Continuous_Path_Spaces/Adapted_Quadratic_Variation.thy:299-319 qvps_continuous; Continuous_Path_Spaces/Adapted_Quadratic_Variation.thy:624-643 qvsa_continuous

Each runs the same lipschitz_onI proof with a 'cases a ≤ b' split and dist_real_def abs_diff_le_iff. stopped_compensated_square inlines rate_continuous_on, which is stated 70 lines later in the same file. The AQV copies are rate_continuous_on applied to qvsa_mono and qvsa_lip.

Evidence: SL:106-121 vs SL:199-214 (identical apart from `linarith?`). AQV:303-318 and AQV:628-642 use the same pattern.

Suggested action: Move rate_continuous_on to the top of Stopped_Localization, or lower (CTM or Power_Inequalities). Use it in stopped_compensated_square and in qvsa_continuous.


### CPS2-19. dyadic_qsum_eq_qvar and dyadic_qsum_eq_grid are the same lemma; the 'rat' identification block is copied

*clone, impact low, confidence high, ~30 lines.*  
Locations: Continuous_Path_Spaces/Pathwise_Quadratic_Variation.thy:276 dyadic_qsum_eq_qvar; Continuous_Path_Spaces/Pathwise_Quadratic_Variation.thy:630 dyadic_qsum_eq_grid; Continuous_Path_Spaces/Adapted_Quadratic_Variation.thy:332-343 vs Pathwise_Quadratic_Variation.thy:699-708; Continuous_Path_Spaces/Pathwise_Quadratic_Variation.thy:608-611 vs 640-643 (grid setup)

The two dyadic_qsum lemmas are eta-equivalent, both proved by `simp add: dyadic_qsum_def qvar_def`, and dyadic_qsum_eq_qvar is unused. The AE-over-rationals identification `rat` in qvp_good_ae copies the one in qvps_eq_A word for word. qv_dyadic_L2 and qvp_tendsto rebuild the same grid t with t0 and tmono.

Evidence: PQV:277 'dyadic_qsum (λs. Y s ω) T n = qvar (λk ω. Y (T * real k / 2^n) ω) (2^n) ω'; PQV:631 'dyadic_qsum (λs. X s ω) T n = qvar (λk. X (T * real k / 2^n)) (2^n) ω'.

Suggested action: Delete dyadic_qsum_eq_qvar. State the rational identification as a locale lemma of bounded_martingale_compensator and use it in qvps_eq_A and qvp_good_ae.


### CPS2-20. continuous_map_real_diff re-proves HOL-Analysis continuous_map_diff, and the prose wrongly says it is missing

*library_duplicate, impact low, confidence high, ~8 lines.*  
Locations: Continuous_Path_Spaces/Path_Tightness.thy:934 continuous_map_real_diff and text at 924-927; /opt/Isabelle2026-RC3/src/HOL/Analysis/Abstract_Limits.thy:346 continuous_map_diff

continuous_map_diff [continuous_intros] states 'continuous_map X euclidean f ⟹ continuous_map X euclidean g ⟹ continuous_map X euclidean (λx. f x − g x)' for any real_normed_vector, real included (euclideanreal = euclidean). The text calls continuous_map_real_diff 'missing-in-library'. The lemma is dead anyway.

Evidence: Abstract_Limits.thy:346-349; the proof is identical (continuous_map_atin, tendsto_diff).

Suggested action: Delete it, using continuous_map_diff or continuous_intros.


### CPS2-21. Paper-specific prose (Lemma 2.2/2.3, Eq. (1.6)-(1.8), (2.7), (2.9), Theorem 1.1, P_x, 'the class') inside the advertised paper-free library

*misplacement, impact low, confidence high, ~150 lines.*  
Locations: Continuous_Path_Spaces/Path_Space.thy:13-21, 459-462, 699-702, 952-956, 1268-1277; Continuous_Path_Spaces/Path_Exit_Times.thy:25-29, 45-52, 130-133, 1634-1647, 1804-1809; Continuous_Path_Spaces/Path_Tightness.thy:11-12, 325-333, 374-381, 928, 1238, 1594, 2390-2396, 2419-2435, 2830-2836, 2896-2901, 2925-2936; Continuous_Path_Spaces/Stopped_Localization.thy:332, 346-355; Continuous_Path_Spaces/Pathwise_Quadratic_Variation.thy:15-16, 154-156; Continuous_Path_Spaces/Adapted_Quadratic_Variation.thy:17-18, 24-26, 72-74, 378-381

Examples: PS:13 'The space the martingale laws of Lemma 2.2 of LaiShkolnikovSoner live on'. PET:1804 'Granted Lemma 2.3, this gives clause (1) of Theorem 1.1'. PET:1634 'the ≤ half of (2.9) reduces to ...'. PT:2424 'The lower bounds Π_m(a) ≥ m−k' (sconstraint). PT:2934 'the formal content of the paper's admissibility conditions Eqs. (1.7)-(1.8)'. SL:332 has a section title 'Eq. (2.7) of LaiShkolnikovSoner for unbounded L² martingales'. PQV:16 'what Exit_Class_Marginals consumes'. AQV:378 'fatal for the bridge — both pushforwards go through martingale_distr'.

Evidence: See the quoted lines. The CPS ROOT describes the session as general weak convergence of processes.

Suggested action: Rewrite these blocks in paper-free terms, or move them into the Relative_Arbitrage theories that consume the results, for instance as bridge comments in Path_Tightness_Market and Exit_Class_Marginals.


### CPS2-22. Orphan text blocks and section headings that no longer describe what follows (Path_Space, Path_Exit_Times, Path_Tightness)

*documentation, impact low, confidence high, ~120 lines.*  
Locations: Continuous_Path_Spaces/Path_Space.thy:1110 (subsection 'The path space is Polish, and restriction is measurable' over mspace_path_restrict_self and open_stay_inside); Continuous_Path_Spaces/Path_Space.thy:1206-1214 (transfer principle via exit_class_compact_metric_space, no lemma follows); Continuous_Path_Spaces/Path_Space.thy:1216-1228 (Larsson–Ruf erosion text; eroded and positive_mass_at_some_erosion live in CTM.Stopping_Times); Continuous_Path_Spaces/Path_Space.thy:1257-1258 ('The margin itself', nothing follows); Continuous_Path_Spaces/Path_Space.thy:1268-1277 (section 'Kernel pasting: the semidirect product' and subsection 'two almost-sure clauses of (1.7)', naming exit_class_kglue_law and ksemi; only second_countable_path_metric follows); Continuous_Path_Spaces/Path_Exit_Times.thy:21-23 ('crowning theorem ... at the end': 860 lines follow it); Continuous_Path_Spaces/Path_Exit_Times.thy:130-133, 1405-1406, 1600-1602, 1686-1689, 1744-1747 (orphan texts); Continuous_Path_Spaces/Path_Exit_Times.thy:1357-1370 (subsection 'Berge's box hypothesis' over past_test_functional_cont), :1408 (subsection 'essential infimum of an unbounded time' over pexit_cong lemmas), :1572-1578 (pfut text; pfut is in Relative_Arbitrage.Path_Splicing); Continuous_Path_Spaces/Path_Tightness.thy:1938-1940 (dyadic_ext measurability text placed before lim_vector_coordinate_measurable); Continuous_Path_Spaces/Path_Tightness.thy:2925-2936 (final subsection with no content; the adapter is in Relative_Arbitrage.Path_Tightness_Market); Continuous_Path_Spaces/Pathwise_Quadratic_Variation.thy:158-171 (four orphan texts and blank lines); Continuous_Path_Spaces/Stopped_Localization.thy:628-640 (restrict_full listing)

These are leftovers of moved lemmas. The generated document shows wrong section titles, most visibly a 'Kernel pasting' section inside Path_Space.

Evidence: PS:1268 "section ‹Kernel pasting: the semidirect product›" followed only by second_countable_path_metric. PQV:164-171: a text block, then six blank lines, then the next lemma.

Suggested action: Delete the orphan blocks and retitle or move the subsections. Path_Space should end with the Polish and second-countable lemmas, without the section heading.


### CPS2-23. Stale or incorrect references to lemmas and theories

*documentation, impact low, confidence high, ~40 lines.*  
Locations: Continuous_Path_Spaces/Path_Space.thy:955 'Value_Function_Market.ess_inf_time_ge_iff_measure' (it is CTM Essential_Infimum.thy:193); Continuous_Path_Spaces/Path_Exit_Times.thy:1682-1684 'ess_inf_time_mono lives in Value_Function_Market' (it is CTM Essential_Infimum.thy:234); Continuous_Path_Spaces/Path_Space.thy:1090 'Equicontinuity.box_of_sequential' (it is Semicontinuous_Analysis.Berge.thy:143); Continuous_Path_Spaces/Path_Space.thy:740-748 (says etime_less_iff is on another import branch; false since Path_Exit_Times); Continuous_Path_Spaces/Path_Space.thy:1019-1024 (incorrect claim that the sets equation is needed at every index); Continuous_Path_Spaces/Path_Exit_Times.thy:11-19 (Laplace route advertised; CTM Essential_Infimum.thy:101-108 says it is unnecessary); Continuous_Path_Spaces/Path_Exit_Times.thy:1727-1728 (refers to etime_shift_uniform_margin in downstream Relative_Arbitrage.Pair_Path_Space); Continuous_Path_Spaces/Path_Tightness.thy:924-927 ('missing-in-library continuous_map_real_diff'); Continuous_Path_Spaces/Path_Tightness.thy:2830-2834 (Path_Tightness refers to 'Path_Tightness's weak_conv_on_integral_unif_integrable', i.e. to itself); Continuous_Path_Spaces/Pathwise_Quadratic_Variation.thy:158-159 (sq_diff_le_two does not exist; sq_diff_le is in Power_Inequalities, not Quadratic_Variation); Continuous_Path_Spaces/Adapted_Quadratic_Variation.thy:24-29 (says Stopped_Localization is used; AQV uses nothing from it); Relative_Arbitrage/Exit_Class_Marginals.thy:182 ('restrict_full package of Stopped_Localization'; it is in CTM.Martingale_Transfer)

These prose references name theories or lemmas that have moved or never existed, and a library session refers to the paper session (Value_Function_Market).

Evidence: grep: ess_inf_time_ge_iff_measure and ess_inf_time_mono are defined only in Continuous_Time_Martingales/Essential_Infimum.thy. sq_diff_le_two occurs only in PQV:158. box_of_sequential is defined in Berge.thy:143.

Suggested action: Fix or delete each reference.


### CPS2-24. Path_Exit_Times: pexit lemma family with special cases, out-of-order helpers and inline re-derivations

*clone, impact low, confidence medium, ~120 lines.*  
Locations: Continuous_Path_Spaces/Path_Exit_Times.thy:1410 pexit_cong_nonneg, :1424 pexit_restrict (special cases of :1604 pexit_cong_on); Continuous_Path_Spaces/Path_Exit_Times.thy:54 pexit_mono_T and :88 pexit_stable_above_T (both follow from :1649 pexit_min_horizon); Continuous_Path_Spaces/Path_Exit_Times.thy:2010 pexit_le_of_mem, inlined earlier at 1515, 1590, 1628, 1667; Continuous_Path_Spaces/Path_Exit_Times.thy:2101 pexit_eq_of_stays vs Stopped_Localization.thy:334 etime_eq_T_of_no_hit vs Path_Exit_Times.thy:1594-1595; Continuous_Path_Spaces/Path_Exit_Times.thy:213-224 and 288-302 (ess_inf_time ≤ T, re-derived twice)

pexit_cong_on (agreement on [0,U]) implies pexit_cong_nonneg and pexit_restrict. pexit_min_horizon (pexit S = min (pexit T) S) can be proved directly from etime_le_of_mem and cInf, and then gives pexit_mono_T (33 lines) and pexit_stable_above_T (40 lines) as corollaries; today the dependency runs the other way. pexit_le_of_mem is defined after four lemmas that inline 'unfolding pexit_def ... etime_le_of_mem'. etime_eq_T_of_no_hit (Stopped_Localization) is the etime form of pexit_eq_of_stays and belongs in CTM.Stopping_Times. The bound ess_inf_time ≤ T is CTM ess_inf_time_le_const; that lemma needs only its hypothesis restricted to space M to apply here.

Evidence: PET:1424 'pexit T K (restrict f {0..T}) = pexit T K f' is pexit_cong_on with g = restrict f. CTM Essential_Infimum.thy:144 ess_inf_time_le_const 'assumes bnd: ⋀ω. tau ω ≤ T'.

Suggested action: Reorder: pexit_le_of_mem and pexit_cong_on first, pexit_min_horizon proved directly, the rest as corollaries. Move etime_eq_T_of_no_hit to Stopping_Times. Weaken ess_inf_time_le_const to `ω ∈ space M ⟹ tau ω ≤ T` and use it.


### CPS2-25. metric_measure_eqI_bounded_cts (100 lines) follows from metric_measure_mono_bounded_cts

*simplification, impact low, confidence medium, ~90 lines.*  
Locations: Continuous_Path_Spaces/Path_Tightness.thy:2537-2639 metric_measure_eqI_bounded_cts; Continuous_Path_Spaces/Path_Tightness.thy:2650-2828 metric_measure_mono_bounded_cts; /opt/afp/thys/Levy_Prokhorov_Metric/Levy_Prokhorov_Distance.thy:842 mweak_conv_imp_converge, :511 sublocale LPm: Metric_space

Equal integrals for all bounded continuous g imply equal integrals for [0,1]-valued continuous g, hence measure ≤ in both directions on every Borel set (mono lemma), hence M1 = M2 by measure_eqI. That is about 10 lines and removes the fifth mweak_conv_fin interpretation. For separable metrics, which covers every consumer (all at path_metric), the AFP gives it too: a constant sequence converges weakly, hence in the LP metric, and LP limits are unique. The mono lemma's closed-set part re-does the Urysohn/Um_def argument of AFP mweak_conv2 (General_Weak_Convergence.thy:279-303).

Evidence: Consumers: Pair_Path_Laws.thy:2893, Exit_Time_Semicontinuity.thy:2123, Exit_Class_Limits.thy:452, all with m = path_metric _ (Polish).

Suggested action: Prove the eqI lemma as a corollary of the mono lemma, after the mono lemma.


### CPS2-26. real^'m is fixed where 'b::polish_space or 'b::euclidean_space would do

*generalisation, impact low, confidence medium, ~110 lines.*  
Locations: Continuous_Path_Spaces/Path_Exit_Times.thy:1372 past_test_functional_cont (proof uses only Lipschitz_restrict_path_metric, which is generic); Continuous_Path_Spaces/Path_Exit_Times.thy:1875 confined_paths, :1882 closedin_confined_paths (only closedness of K and continuous_map_path_eval); Continuous_Path_Spaces/Path_Exit_Times.thy:1934 martingale_test_functional_cont, :1974 covariation_test_functional_cont (could use x•i for i∈Basis); Continuous_Path_Spaces/Path_Exit_Times.thy:662, 739, 795, 819 (stated at path_metric T, valid for any metric m); Continuous_Path_Spaces/Path_Space.thy:1138 open_stay_inside ('b::{polish_space,heine_borel}, heine_borel only via separate_compact_closed); Continuous_Path_Spaces/Path_Tightness.thy:1037 marginal_map_measurable, :1052 projective_limit_of_consistent_path_laws (polish_projective needs only 'b::polish_space)

These statements fix real^'m, or a specific metric, without needing it. The two test-functional lemmas also share a cloned 20-line prefix (evdiff, cmp_i, part1', part1). martingale_test_functional_cont inlines past_test_functional_cont (part2', part2) instead of citing it.

Evidence: PET:1946-1958 vs 1986-1998 (identical prefix); PET:1959-1969 repeats the proof of past_test_functional_cont.

Suggested action: Generalise past_test_functional_cont and confined_paths to 'b::polish_space. Prove one lemma: continuity of f ↦ g (f t − f s) for continuous g. Derive both test functionals from it plus past_test_functional_cont. In open_stay_inside, use compact_attains_inf on infdist to drop heine_borel.


### CPS2-27. Hypotheses that are unused or derivable

*generalisation, impact low, confidence medium, ~40 lines.*  
Locations: Continuous_Path_Spaces/Path_Exit_Times.thy:802 weak_conv_closed_full_mass `probs`; Continuous_Path_Spaces/Path_Space.thy:1031-1032 weak_conv_open_positive_eventually `si`, `pi`, `pN`; Continuous_Path_Spaces/Path_Tightness.thy:2443-2448 weak_conv_on_integral_unif_integrable `iCi`, `iCN`, `iTi`, `iTN` (also weak_conv_integral_of_L2_bound 2909-2913); Continuous_Path_Spaces/Pathwise_Quadratic_Variation.thy:184-186 compensated_increment_second_moment `fourth`, `dAsq`, `sqint`; Continuous_Path_Spaces/Stopped_Localization.thy:233 etc. `Aad`

probs is never used. The open-set portmanteau needs neither per-index sets equations nor probability spaces: the AFP gives the total-mass limit from weak convergence alone. Integrability of the clamp and tail follows from measurability, finiteness and iNi/iN (the integrand is bounded by |f|). compensated_increment_second_moment is used only inside the locale, where those three integrability facts are lemmas. On Aad, see the compensator finding above.

Evidence: PET:805-816 never uses probs. PS:1022-1024 claims 'the total-mass step needs space (Ni i) = mspace m with no exceptions', but mweak_conv_fin.space_Ni and mweak_conv_imp_limit_space need only 'eventually'.

Suggested action: Drop the hypotheses and adjust the call sites; there are few: 2 for weak_conv_closed_full_mass, 1 for weak_conv_open_positive_eventually, 2 for weak_conv_integral_of_L2_bound.


## RA-path1

Method: I read all 8360 lines and checked every claim below by grepping the repository, the Isabelle distribution and the AFP. No PIDE session was running (list_sessions returned nothing), so none of the suggested proof replacements has been machine-checked. "Used" counts are textual.

What the cluster is supposed to be: the bottom of the paper session's path toolkit. Pair_Path_Space fixes `'n pairpath = real => (real^'n) x (real^'n^'n)`; Pair_Path_Laws handles families of laws and their weak limits; Path_Splicing defines pcut, pfut, pshift, padd, pglue, iglue, pfst, pcoord, ploc, pembed, pdel and prebase.

What it actually contains is a mix of six kinds of material, and many section headers and text blocks no longer sit next to the lemmas they describe:
(a) Generic path-space measure theory. About 70 statements are typed at `real => 'a x 'b` but never look at a component.
(b) Genuinely pair-specific surgery: pshift, pfst, pcoord/ploc, pexit-of-fst lemmas, coordinate measurability.
(c) A generic "martingale property passes to weak limits" chain: martingale_test_F, martingale_test_F_limit, martingale_event_F_limit, martingale_F_limit, plus the rational-time lemmas integrable_and_set_integral_eq_of_rational_times and martingale_of_rational_set_integral_eq.
(d) Generic stochastic analysis: localised pathwise quadratic variation (qvps/qvmat_eq_A_localised); exit-time upper semicontinuity (etime_shift_box, vshift_sup_usc); horizon_sq_int_martingale_stopped.
(e) About 30 pure matrix lemmas: outerp and its family, psd lemmas, onormal Parseval, weighted_min_value, rot_col_cont.
(f) Paper-specific helpers for the Euler construction and the supersolution proof: euOrth_*, euXi_term_cont, quad_*, open_quad_bad_event*, radial_sq_upto*, tilted_local_touching, horn_B_locally_constant, nonbinding_horizon_ex. Also the parametric class covariation_class/covariation_val, which contradicts the ROOT's claim that the toolkit "knows nothing of the constraint set or the value function".

Main problems:
- A large clone. The coordinate version of the test-functional / weak-limit martingale chain (Pair_Path_Space plus Exit_Class_Limits) duplicates the generic F-chain in Pair_Path_Laws, about 750 lines.
- Six copies of one continuity argument ("approach t from below").
- Re-derivations of library facts: pathify_measurable, natural_filtration_eval, sets_natural_filtration_subset, parseval_onormal, quadform_weighted_outer_sum_eq, restrict_mspace_path_metric, stopped_martingale_L2, the polarisation in Pathwise_Quadratic_Variation, and the pexit lemmas of Path_Exit_Times.
- A dead chain of 11 definitions and lemmas.
- Unnecessary imports. Pair_Path_Space imports Sup_Convolution and Doubling_Of_Variables only for norm_Pair_le, which HOL-Analysis already has, and one text note. This puts about 12.8k lines of Second_Order_Viscosity_Analysis in front of a strictly linear 17.2k-line toolkit chain. In addition, at least five consumers import the end of the chain (Path_Law_Sampling) although they use only Pair_Path_Space/Pair_Path_Laws.

Proposed restructuring for this cluster:
1. Move generic path measure theory to Continuous_Path_Spaces.Path_Space at `real => 'c::{polish_space,banach}`.
2. Move the exit-time block to Path_Exit_Times and the QV localisation to Adapted_Quadratic_Variation.
3. Put the F-chain and the rational-time lemmas in a new Continuous_Path_Spaces theory (e.g. Weak_Limit_Martingales).
4. Move the outerp/psd/onormal lemmas to Symmetric_Matrix_Spectra and ess_inf_time_min_const to Essential_Infimum.
5. Move the Euler and supersolution helpers to Value_Function_Euler_Construction and Value_Function_Supersolution_Case_1/2.
6. Give covariation_class/val their own theory at the head of the class layer.
7. What then remains is the operations (generic at `'c`) plus a small Pair_Paths theory (pshift, pfst, pcoord, ploc, pexit-of-fst). That is the right content for the Path_Space_Operations session that section 11 unblocks.


### RA-path1-1. Coordinate test-functional / weak-limit martingale chain duplicates the generic F-chain (about 750 lines)

*clone, impact high, confidence high, ~750 lines.*  
Locations: Relative_Arbitrage/Pair_Path_Space.thy:828 pair_eval_coord_cont; Pair_Path_Space.thy:992 pair_eval_coord_sq_cont; Pair_Path_Space.thy:1007 pair_test_functional_cont; Pair_Path_Space.thy:1307 pair_law_coord_measurable; Pair_Path_Space.thy:1381 pair_law_coord_sq_measurable; Pair_Path_Space.thy:1448 pair_law_sq_integrable_of_nn_bound; Pair_Path_Space.thy:1526 pair_law_sq_mean_of_nn_bound; Pair_Path_Space.thy:1545 pair_test_measurable; Pair_Path_Space.thy:1604 pair_test_sq_bound; Pair_Path_Laws.thy:98 pair_test_integrable; Pair_Path_Laws.thy:170 pair_law_limit_sq_nn_bound; vs Pair_Path_Laws.thy:1866-2458 pair_eval_F_cont .. pair_test_F_integrable; Pair_Path_Laws.thy:2462 martingale_test_F, 2515 martingale_test_F_limit, 2777 martingale_event_F_limit, 3126 martingale_F_limit; Exit_Class_Limits.thy:121 exit_class_martingale_test, 207 exit_class_martingale_test_limit, 322 exit_class_limit_increment_integrable, 350 exit_class_martingale_event_limit, 577 exit_class_coord_martingale_limit

Every coordinate lemma is the instance F = (%p. fst p $ i) of an F-lemma that sits next to it.
- `pair_test_sq_bound` (84 lines) and `pair_test_F_sq_bound` (75 lines) are line-for-line the same proof with `fst (\<omega> t) $ i` replaced by `F (\<omega> t)`.
- Exit_Class_Limits then re-runs the generic chain at coordinates: exit_class_martingale_test = martingale_test_F, exit_class_martingale_test_limit = martingale_test_F_limit, exit_class_martingale_event_limit (214 lines, same density/push-forward argument) = martingale_event_F_limit, exit_class_coord_martingale_limit (121 lines) = martingale_F_limit.
- Exit_Class_Limits itself already uses `martingale_F_limit` at line 1770 for the compensated clause.
- The coordinate chain exists only to feed exit_class_coord_martingale_limit. The grep shows that, apart from pair_law_coord_measurable, its lemmas have no other users.

Evidence: Pair_Path_Space.thy:1604 `lemma pair_test_sq_bound ... shows "integrable N (%w. (h (restrict w {0..s}) * (fst (w t) $ i - fst (w s) $ i))^2)"` vs Pair_Path_Laws.thy:2320 `lemma pair_test_F_sq_bound ... shows "integrable N (%w. (h (restrict w {0..s}) * (F (w t) - F (w s)))^2)"`. Same internal steps: iss/itt, fm, fsqm, dom_int, ptwise (e1, sq_le), Bs/Bt. Exit_Class_Limits.thy:1770 `proof (rule martingale_F_limit [where F = "%p. (outerp (fst p) - snd p) $ i $ j" ...])`. The hypotheses of exit_class_coord_martingale_limit are supplied by exit_class_coord_martingale (mgm with F = %p. fst p $ i) and exit_class_sq_nn_bound (nnm). Grep for exit_class_martingale_test, exit_class_martingale_event_limit and pair_test_integrable finds users only inside this chain.

Suggested action: Prove exit_class_coord_martingale_limit as `martingale_F_limit[where F = "%p. fst p $ i"]` plus exit_class_sq_nn_bound, about 15 lines. Then delete exit_class_martingale_test, _test_limit, _limit_increment_integrable, _martingale_event_limit and exit_class_limit_sq_nn, and in this cluster pair_eval_coord_sq_cont, pair_test_functional_cont, pair_law_coord_sq_measurable, pair_law_sq_integrable_of_nn_bound, pair_law_sq_mean_of_nn_bound, pair_test_measurable, pair_test_sq_bound, pair_test_integrable and pair_law_limit_sq_nn_bound. Keep pair_law_coord_measurable and pair_eval_coord_cont as one-line corollaries of the _F_ versions.


### RA-path1-2. qvmat_eq_A_localised re-proves the polarisation of Pathwise_Quadratic_Variation

*clone, impact high, confidence high, ~180 lines.*  
Locations: Relative_Arbitrage/Pair_Path_Space.thy:1035-1241 qvmat_eq_A_localised; Continuous_Path_Spaces/Pathwise_Quadratic_Variation.thy:846-1060 locale bounded_matrix_martingale_compensator (Xpol, Apol, Apol_diff, polarised, qvmat_eq_A)

The `pol` block of qvmat_eq_A_localised repeats the body of `bounded_matrix_martingale_compensator.polarised` verbatim:
- the definitions Y = X_i + c X_j and G = A_ii + c(A_ij + A_ji) + c^2 A_jj (= Xpol/Apol);
- the martingale of Y via martingale.add/scaleR_const;
- the four-martingale decomposition of Y^2 - G;
- the Grate bound with the same add_mono / abs / sq_mono_abs / inner_mv_axis steps.
The final e1/e2/qvmat_def assembly repeats qvmat_eq_A. The only difference is the missing boundedness hypothesis, which is handled by calling qvps_eq_A_localised instead of the locale's qvps_eq_A.

Evidence: Pair_Path_Space.thy:1063 `define Y where "Y = (%v w. X v w $ i + c * (X v w $ j))"`, 1064 `define G ...`, 1076-1092 identical `eq`/m1..m4 to Pathwise_Quadratic_Variation.thy:906-924, 1097-1152 identical to the Apol rate proof at :939-990 (same text `also have "... <= C * (v - u) + 1 * (C * (v - u) + C * (v - u)) + 1 * (C * (v - u))"`).

Suggested action: Factor the boundedness-free part of `polarised` (martingale of Xpol, compensated martingale, Apol rate) into locale-free lemmas in Pathwise_Quadratic_Variation (or Adapted_Quadratic_Variation) and use them in both proofs. Move qvps_eq_A_stopped, qvps_eq_A_localised and qvmat_eq_A_localised to Continuous_Path_Spaces.Adapted_Quadratic_Variation, which already imports Stopped_Localization and Pathwise_Quadratic_Variation.


### RA-path1-3. The continuity argument "approach t from below" is proved six times (about 480 lines); three copies are exact instances of a sibling

*clone, impact high, confidence high, ~480 lines.*  
Locations: Relative_Arbitrage/Pair_Path_Space.thy:138 radial_sq_upto_gen; Pair_Path_Laws.thy:3265 radial_sq_upto; Pair_Path_Laws.thy:3668 quad_good_upto_region; Pair_Path_Laws.thy:3944 quad_good_upto; Pair_Path_Laws.thy:3760 quad_good_rat_to_real_region; Pair_Path_Laws.thy:3852 quad_good_rat_to_real; Pair_Path_Laws.thy:1443 open_quad_bad_event_region vs 3509 open_quad_bad_event; Pair_Path_Laws.thy:3632 quad_eval_cont

All six lemmas show that a continuous g on [0,c] which satisfies an (in)equality at t' in (0,t), or at rational t', satisfies it at t. Each builds the sequence `tj j = t - t/(2*Suc j)` (or a rational sequence via choice and tendsto_sandwich), proves tj -> t, and uses continuous_on_sequentially.
- radial_sq_upto is exactly radial_sq_upto_gen at F = %v. (norm (v - y0))^2, c0 = (norm (x - y0))^2. The text at Pair_Path_Space.thy:132-136 says so, but the proof is re-done.
- quad_good_upto, quad_good_rat_to_real and open_quad_bad_event are the RO = ball x rb instances of the _region versions, re-proved in full (76, 91 and 52 lines).
- quad_eval_cont repeats the continuity block (c0, c1, cq, cin, contf) of open_quad_bad_event(_region) a third time.

Evidence: radial_sq_upto_gen grow: `F (fst (w t)) = c0 + t * cn`; radial_sq_upto grow: `(norm (fst (w t) - y0))^2 = (norm (x - y0))^2 + t * cn`. quad_good_upto inb: `fst (w s) : ball x rb`; quad_good_upto_region inb: `fst (w s) : RO`. HOL-Analysis Elementary_Metric_Spaces.thy:3093/3103 has continuous_le_on_closure / continuous_ge_on_closure, already used for exactly this purpose by Continuous_Path_Spaces/Path_Space.thy:274 le_on_Icc_of_rats.

Suggested action: Prove one real-analysis helper, e.g. `continuous_on {0..c} g ==> 0 < t ==> t <= c ==> (!!s. s : S ==> a s <= g s) ==> t : closure S ==> a t <= g t`, using continuous_ge_on_closure with S = {0<..<t} or ({0<..<t} Int Rats). Derive the _region lemmas in about 10 lines each, make radial_sq_upto, quad_good_upto, quad_good_rat_to_real and open_quad_bad_event one-line instances, and fold quad_eval_cont into open_quad_bad_event_region. Then move all of them to the Euler/supersolution theories (see the misplacement finding).


### RA-path1-4. Measurability into the path space is re-derived instead of using Path_Space.pathify_measurable

*library_duplicate, impact high, confidence high, ~330 lines.*  
Locations: Relative_Arbitrage/Pair_Path_Laws.thy:1294 measurable_into_path_metric; Pair_Path_Laws.thy:1335 mdist_measurable_of_eval; Pair_Path_Laws.thy:1652 mdist_measurable_natural_filtration; Pair_Path_Laws.thy:1712 mball_in_natural_filtration; Pair_Path_Laws.thy:1750 sets_natural_filtration_path; Path_Splicing.thy:227 padd_measurable_left, 324 padd_measurable, 1615 pembed_measurable, 1701 pdel_measurable_pair, 1866 prebase_measurable; Continuous_Path_Spaces/Path_Space.thy:328 pathify_measurable

pathify_measurable already contains the argument: balls generate the Borel algebra, and mdist <= q is a countable intersection over rational times via path_mdist_le_iff.
- measurable_into_path_metric plus mdist_measurable_of_eval re-prove it.
- mdist_measurable_natural_filtration, mball_in_natural_filtration and sets_natural_filtration_path re-prove it a third time for the natural filtration.
- padd, pembed, pdel and prebase are all defined as `restrict (...) {0..T}`, so pathify_measurable applies to them directly. pglue_measurable, iglue_measurable, pfst_measurable and restrict_measurable_natural_filtration in this same cluster already do so.
- The five consumers instead case-split on `t : {0..T}` / `undefined` (about 25 lines each).
- sets_natural_filtration_path's inclusion `sets path_borel <= sets F` follows from pathify_measurable with M = the natural filtration (evaluations are measurable by natural_filtration_eval) and mspace_path_restrict_self.

Evidence: Pair_Path_Laws.thy:1348-1355 `{w : space M. mdist ... (f w) a <= q} = (INT t : {0..T} Int Rats. ...)` using `path_mdist_le_iff`; Path_Space.thy:365-396 the same `leq_set`. Path_Splicing.thy:56 `padd T p' w = restrict (%t. p' t + w t) {0..T}`, :1466 `pembed s T w = restrict (%t. w (max (t - s) 0)) {0..T}`, :1528 prebase also restrict. Path_Splicing.thy:712 `using pathify_measurable[OF T0 Xm cont] unfolding pglue_def` shows the intended pattern. Pair_Path_Space.thy:1292 `by (rule pathify_measurable[OF s evm cont])` for a natural-filtration domain.

Suggested action: Rewrite padd_measurable(_left), pembed_measurable, prebase_measurable and pdel_measurable_pair (and the three uses in Path_Stopping_Times and one in Path_Law_Pasting) with pathify_measurable. Prove sets_natural_filtration_path from pathify_measurable plus sets_natural_filtration_subset. Delete measurable_into_path_metric, mdist_measurable_of_eval, mdist_measurable_natural_filtration and mball_in_natural_filtration.


### RA-path1-5. About 30 pure matrix lemmas (the outerp family, psd, onormal, threshold selection, rotation continuity) belong in Symmetric_Matrix_Spectra

*misplacement, impact high, confidence high, ~600 lines.*  
Locations: Pair_Path_Space.thy:718 definition outerp, 727 outerp_matvec_image, 766 outerp_scale_self, 771 outerp_eq_outer_prod, 776 trace_mult_outerp, 796 trace_mult_outerp_sum, 1539 outerp_diff, 1566 outerp_diff_compensated, 448 psd_diag_nonneg, 691 rot_col_cont; Pair_Path_Laws.thy:33 psd_mat_1, 43 comp_shift_split, 183 cols_mult_transpose, 205 trace_outerp_mult, 210 quadform_outerp, 303 sq_coord_split, 537 outerp_sq, 575 outerp_add, 581 outerp_zero, 815 trace_outerp, 1797 psd_kernel_eq, 1898 matvec_sum_outer, 1937 quadform_sum_outer, 1970 traceM_sum_outer, 2014 onormal_parseval, 2119 onormal_span_parseval, 2174 weighted_min_value, 2396 norm_outerp, 2404 outerp_borel, 3441 comp_entry_eq, 3446 comp_entry_cont

None of these mentions a path, a measure on paths or the paper. outerp is the rank-one projector and is used 714 times. psd_diag_nonneg and psd_kernel_eq are psd facts and belong next to `psd` in Symmetric_Spectral. weighted_min_value is the threshold step next to Ky_Fan.exists_min_subset. rot_col_cont is about Householder_Rotation.rotm.

PLAN section 3.1 scheduled the 29 outerp lemmas for Symmetric_Matrix_Spectra; section 10 only records that outerp could not become an abbreviation, so the move was never done. Several of these lemmas are the only reason Pair_Path_Space imports Ky_Fan, Householder_Rotation, Poincare_Separation and Orthonormal_Families.

Side note: Matrix_Algebra.thy:1044 diag_eq_inner_axis and :1069 diag_entry_quadform (the latter is what psd_diag_nonneg uses) are the same equation, one the symmetric form of the other.

Evidence: Usage: weighted_min_value, psd_kernel_eq, onormal_*, matvec_sum_outer and traceM_sum_outer are used only in Value_Function_Subsolution; rot_col_cont only in Value_Function_Supersolution_Case_1; psd_diag_nonneg in Exit_Time_Semicontinuity and Path_Tightness_Market. Pair_Path_Space.thy:721-725: "outerp ... stays a definition of its own because making it an abbreviation unfolds it in every simp set".

Suggested action: Move outerp and its algebraic lemmas to Symmetric_Matrix_Spectra.Outer_Products (keep it a definition, proving each lemma from the outer_prod one via outerp_eq_outer_prod). Move psd_mat_1, psd_diag_nonneg and psd_kernel_eq to Symmetric_Spectral, onormal_span_parseval to Orthonormal_Families, weighted_min_value to Ky_Fan and rot_col_cont to Householder_Rotation. outerp_borel and comp_entry_cont can go to Outer_Products too (Borel measurability is available via HOL-Analysis). Re-read Statement prose that displays outerp. Merge diag_eq_inner_axis into diag_entry_quadform.


### RA-path1-6. Paper-specific helpers (Euler scheme, supersolution cases, horizon choice) sit in the advertised paper-free toolkit

*misplacement, impact high, confidence high, ~1300 lines.*  
Locations: Pair_Path_Laws.thy:846 euOrth_mset_cond, 2051 euOrth_mset, 1362 euXi_term_cont (used only in Value_Function_Euler_Construction / Supersolution_Case_1); Pair_Path_Laws.thy:1443 open_quad_bad_event_region, 3509 open_quad_bad_event, 3632 quad_eval_cont, 3668/3760/3852/3944 quad_good_*; Pair_Path_Space.thy:138 radial_sq_upto_gen (Value_Function_Assembly), Pair_Path_Laws.thy:3265 radial_sq_upto (Supersolution_Case_1); Pair_Path_Laws.thy:593 tilted_local_touching, 1047 horn_B_locally_constant (only Value_Function_Supersolution_Case_2); Pair_Path_Laws.thy:241 nonbinding_horizon_ex (only Value_Function_Uniqueness; mentions k < CARD('n)); Pair_Path_Space.thy:49 path_laws_convergent_subsequence_market (only Path_Tightness_Market)

The ROOT says the path toolkit "knows nothing of the constraint set or the value function". These lemmas serve exactly one paper theory each:
- the Euler bad-event and orthogonality sets;
- the quadratic test-function growth along the confinement region;
- the radial growth of the tangential field;
- the touching argument of supersolution case 2 (tilted_local_touching and horn_B_locally_constant are pure real analysis on lsc functions and use no path at all);
- the choice of a non-binding horizon (k < CARD('n), the paper's delta = rK^2/(n-k)).
Their text is paper prose ("The second horn dies here", "Case 1 for the lower envelope", "exit_val_ball_lower_plus").

path_laws_convergent_subsequence_market is fully generic, an L2-plus-compensator adapter to path_laws_convergent_subsequence_vec, despite its name.

Keeping these here makes Pair_Path_Space import Semicontinuous_Analysis.Semicontinuity, Ky_Fan and Householder_Rotation, and forces every consumer to wait for the toolkit.

Evidence: Usage grep: tilted_local_touching and horn_B_locally_constant only in Value_Function_Supersolution_Case_2; quad_good_upto_region only in Supersolution_Case_2; quad_good_rat_to_real_region only in Supersolution_Case_1; euOrth_mset only in Value_Function_Euler_Construction; nonbinding_horizon_ex only in Value_Function_Uniqueness (4 uses). Pair_Path_Laws.thy:1156 text "The second horn dies here.  Suppose v_* were constant ...".

Suggested action: Move the euOrth/euXi/quad/open_quad lemmas to Value_Function_Euler_Construction (the first common ancestor of their users). Move radial_sq_upto* to Value_Function_Supersolution_Case_1 (or Euler_Construction if Assembly needs it earlier), tilted_local_touching and horn_B_locally_constant to Value_Function_Supersolution_Case_2 (or, as generic lsc analysis, to Second_Order_Viscosity_Analysis together with Matrix_Algebra's tilted_minimiser_close, pinch_implies_constant and quad_minimality_pinch), and nonbinding_horizon_ex to Value_Function_Uniqueness. Move path_laws_convergent_subsequence_market, renamed, to Continuous_Path_Spaces.Stopped_Localization next to fourth_moment_L2_*.


### RA-path1-7. Generic path-space measure theory and martingale-limit machinery should go to Continuous_Path_Spaces / Continuous_Time_Martingales

*misplacement, impact high, confidence high, ~2200 lines.*  
Locations: Pair_Path_Space.thy:1253 space_of_path_sets (54 uses; re-derived inline 16 more times as sets_eq_imp_space_eq + space_borel_of); Pair_Path_Laws.thy:341 pair_law_eval_measurable (93 uses); Pair_Path_Laws.thy:285 standard_borel_path_metric, 291 mspace_path_metric_ne, 314 standard_borel_ne_path_metric, 371 frozen_set_measurable, 480 natural_filtration_eq_restrict_vimage, 1198 path_eval_at_measurable_time, 3003 countable_Int_stable_generator_path; Pair_Path_Space.thy:1269 restrict_measurable_natural_filtration, 1295 past_test_measurable_natural_filtration; Pair_Path_Laws.thy:1866-3433 F-chain and rational-time lemmas; Pair_Path_Space.thy:1396 ess_inf_time_min_const; Pair_Path_Space.thy:237/483 qvps_eq_A_stopped/_localised

None of these uses a component of the pair; most are stated at `'a::{polish_space,banach} x 'b::{polish_space,banach}` only because they were mechanically widened from 'n pairpath.
- space_of_path_sets and pair_law_eval_measurable are basic Path_Space API. Path_Space, Path_Exit_Times, Path_Tightness and three paper theories re-derive space_of_path_sets inline.
- The F-chain plus integrable_and_set_integral_eq_of_rational_times and martingale_of_rational_set_integral_eq are a library result in their own right: martingale laws with a uniform L2 bound are closed under weak convergence.
- ess_inf_time_min_const belongs in Essential_Infimum. It needs only ennreal_min_eq (Integrability_Criteria) and density of ennreal (dense instead of Semicontinuous_Selection.ennreal_strict_between).

Evidence: grep `sets_eq_imp_space_eq` together with `space_borel_of`: 16 hits (Path_Space 4, Path_Exit_Times 2, Path_Tightness 1, Pair_Path_Space 3, ...). Pair_Path_Laws.thy:3126 martingale_F_limit is stated at `(real => 'a x 'b)` with `F :: "'a x 'b => real"` and never uses fst/snd.

Suggested action: Path_Space gains space_of_path_sets, path_eval_measurable (= pair_law_eval_measurable), standard_borel(_ne)_path_metric, mspace_path_metric_ne, frozen_set_measurable, path_eval_at_measurable_time and countable_Int_stable_generator_path, plus the natural-filtration-of-path-space lemmas. A new Continuous_Path_Spaces theory (e.g. Weak_Limit_Martingales, after Path_Tightness and Conditional_UI) gains the F-chain and the rational-time lemmas. Essential_Infimum gains ess_inf_time_min_const; Adapted_Quadratic_Variation gains the QV localisation. State everything at `real => 'c::{polish_space,banach}` (next finding).


### RA-path1-8. Pair_Path_Space's import of Sup_Convolution and Doubling_Of_Variables serialises about 12.8k lines of Second_Order_Viscosity_Analysis before the 17.2k-line linear toolkit chain

*build_time, impact high, confidence high, ~15 lines.*  
Locations: Relative_Arbitrage/Pair_Path_Space.thy:30-31 imports Second_Order_Viscosity_Analysis.Sup_Convolution, Doubling_Of_Variables; Pair_Path_Laws.thy:463 (norm_Pair_le), 203 (dist_pair_le note); Second_Order_Viscosity_Analysis/Doubling_Of_Variables.thy:3473 norm_Pair_le vs HOL-Analysis Product_Vector.thy:722 norm_Pair_le; Pair_Path_Space.thy:32 Wiener_Measure.Brownian_Finite_Dimensional_Distributions

Relative_Arbitrage's parent is Continuous_Path_Spaces, so Second_Order_Viscosity_Analysis theories are loaded inside this session's build. Doubling_Of_Variables pulls Theorem_On_Sums, Sup_Convolution, Jensen_Lemma, Alexandrov, Moreau_Envelope, Rademacher and Convex_Subgradients: 12,817 lines that must finish before Pair_Path_Space starts.

The toolkit uses nothing from these eight theories except norm_Pair_le, which is in HOL-Analysis Product_Vector.thy:722 with the same statement (Doubling_Of_Variables re-proves it, a library duplicate), and the one text antiquotation at Pair_Path_Laws.thy:203. The rest of the toolkit (Path_Stopping_Times, Path_Law_Pasting, Path_Law_Sampling) uses none of them either.

The theories downstream that need this layer (Comparison_*, Operator_Envelopes, Value_Function_Euler_Construction, Viscosity_Definitions via Test_Functions) import it directly. Brownian_Finite_Dimensional_Distributions is likewise unused by the toolkit; only Value_Function_Euler_Construction uses gauss_measure / gauss_measure_moment_even from Gaussian_Increments. Ky_Fan, Householder_Rotation, Poincare_Separation, Orthonormal_Families, Berge and Semicontinuity are needed only by the misplaced lemmas.

Removing the two imports lets the toolkit chain run concurrently with the viscosity session and the operator layer. Exit_Class needs both branches, so its start moves from (viscosity prefix + toolkit) to max(...).

Evidence: Name-usage scan per imported theory (cluster / rest of toolkit): Sup_Convolution 0/0, Theorem_On_Sums 0/0, Jensen_Lemma 0/0, Alexandrov 0/0, Moreau_Envelope 0/0, Rademacher 0/0, Convex_Subgradients 0/0, Doubling_Of_Variables 2/0 (dist_pair_le in text, norm_Pair_le), Brownian_Finite_Dimensional_Distributions 0/0 (only the variable name csum). wc -l of the eight theories = 12817. Product_Vector.thy:722 `lemma norm_Pair_le: shows "norm (x, y) <= norm x + norm y"`.

Suggested action: Drop both Second_Order_Viscosity_Analysis imports and the Wiener_Measure import from Pair_Path_Space, delete the note at Pair_Path_Laws.thy:203, and let Value_Function_Euler_Construction import Wiener_Measure.Gaussian_Increments. Delete Doubling_Of_Variables.norm_Pair_le in favour of HOL's. After the misplacement moves, trim the Symmetric_Matrix_Spectra and Semicontinuous_Analysis imports as well, one build each.


### RA-path1-9. About 70 statements are typed at a product codomain they never inspect; section 11's "pair-free" count measures only absence of 'n pairpath

*generalisation, impact high, confidence medium, ~900 lines.*  
Locations: Pair_Path_Space.thy:1253,1269,1295,1322; Pair_Path_Laws.thy:51,161,263,277,285,291,314,330,341,371,480,1017,1198,1294,1335,1615,1624,1652,1712,1750,1866-3348 (F-chain, 19 statements); Path_Splicing.thy:71,98,116,145,169,227,273,324,385,393,578,593,670,680,721,767,1073,1131,1484,1499,1520,1615,1673,1694,1701,1757,1794,1851,1866,2086

My statement scan finds 67 statements whose types mention `'a x 'b` (as `real => 'a::{polish_space,banach} x 'b::{polish_space,banach}`) but whose statements use no fst, snd, Pair, pshift, pfst or pexit. Another six (padd_measurable, padd_measurable_ksemi, pglue_measurable, iglue_measurable, Lipschitz_pglue, mdist_pglue_le) use fst/snd only of the product of two path spaces.

The definitions pcut, pfut, padd, pglue, iglue, pembed, pdel and prebase are already at `real => 'b`, but their lemmas were widened only to `'a x 'b`. Since Path_Space.thy:30 instantiates `prod :: (polish_space, polish_space) polish_space` and HOL has `prod :: (banach, banach) banach`, a single `'c::{polish_space,banach}` unifies with every current use.

PLAN section 11 reports "Path_Splicing 90/94 pair-free", but by that measure these lemmas still are not stated for C([0,T],E). The remaining genuinely pair-specific statements are pshift*, pfst*, pcoord/ploc*, the pexit-of-fst lemmas, the coordinate measurability lemmas and pair_holder_*.

The pexit-of-fst lemmas (pexit_pglue_ge, pexit_pglue_dpp, pexit_pcut_ge, pexit_delayed_rebase, pexit_padd_dpp, pexit_path_measurable) could in turn be stated for a 'c-valued path and recovered through `fst (pglue r T w w' t) = pglue r T (pfst..) .. t` (G1 wave 3).

Evidence: Script over the three files: prod=1 & fstsnd=0 -> 67 statements (list in locations). Example Path_Splicing.thy:116 `lemma pfut_in_mspace: fixes w :: "(real => 'a::{polish_space,banach} x 'b::{polish_space,banach})"`; the proof uses only continuous_on_compose2 / continuous_on_diff. PLAN_RESTRUCTURING_2.md section 11: "Normalising the whole path layer to {polish_space,banach} turned six theories from 92 errors to zero".

Suggested action: Do the bottom-up widening of each `(real => 'a x 'b)` statement without fst/snd to `(real => 'c::{polish_space,banach})`, renaming fixes to avoid clashes, with build timeouts as in section 11. Re-measure the gate as "statements whose types mention a product codomain" rather than "mention 'n pairpath".


### RA-path1-10. Strictly linear toolkit chain, with consumers importing its end although they use only its first two theories

*structure, impact high, confidence medium, ~30 lines.*  
Locations: Relative_Arbitrage/ROOT; imports of Pair_Path_Laws (Pair_Path_Space), Path_Splicing (Pair_Path_Laws), Path_Stopping_Times, Path_Law_Pasting, Path_Law_Sampling; Exit_Class.thy, Exit_Time_Semicontinuity.thy, Path_Tightness_Market.thy, Exit_Class_Tightness.thy, Value_Function_Uniqueness.thy (all import Path_Law_Sampling directly or transitively)

Each of the six toolkit theories imports exactly its predecessor, and 25 paper theories import Path_Law_Sampling. Exit_Class, Exit_Time_Semicontinuity, Path_Tightness_Market, Exit_Class_Tightness and Value_Function_Uniqueness use no declaration of Path_Splicing, Path_Stopping_Times, Path_Law_Pasting or Path_Law_Sampling: they need only Pair_Path_Space/Pair_Path_Laws (covariation_class, vshift_*, psd_diag_nonneg, path_laws_convergent_subsequence_market). Exit_Class_Limits uses only Path_Splicing.

As a result the whole class layer waits for 8.9k lines of stopping/pasting/sampling material it does not use. Path_Tightness_Market needs only path_laws_convergent_subsequence_market, a generic lemma that belongs in Continuous_Path_Spaces.

Evidence: Name scan: Exit_Class uses Path_Splicing 0 (the 1 hit was the word 'on' in prose), Path_Stopping_Times 0, Path_Law_Pasting 0, Path_Law_Sampling 0; Exit_Time_Semicontinuity, Path_Tightness_Market, Exit_Class_Tightness and Value_Function_Uniqueness likewise 0/0/0/0; Exit_Class_Limits 7/0/0/0. wc: Path_Stopping_Times 2070 + Path_Law_Pasting 3444 + Path_Law_Sampling 3350.

Suggested action: Make each consumer import the lowest toolkit theory it needs: Exit_Class imports a new Covariation_Class theory (or Pair_Path_Laws), Exit_Time_Semicontinuity imports Path_Exit_Times after the vshift move, and Path_Tightness_Market imports nothing from the toolkit. This turns the class layer's dependence on Path_Law_Sampling into a branch that only the Dynamic_Programming_* and Value_Function_* theories wait for.


### RA-path1-11. Four copies (plus inline re-proofs) of Natural_Filtration.natural_filtration_eval; natural-filtration subset/subalgebra facts duplicated

*library_duplicate, impact medium, confidence high, ~110 lines.*  
Locations: Relative_Arbitrage/Pair_Path_Laws.thy:161 path_eval_measurable_natural_filtration'; Pair_Path_Laws.thy:277 nat_filt_eval; Pair_Path_Laws.thy:330 path_eval_natural_filtration; Pair_Path_Laws.thy:1615 path_eval_measurable_natural_filtration; inline: Path_Splicing.thy:152, Pair_Path_Space.thy:1283, Pair_Path_Laws.thy:3467, 3577, 3175; Pair_Path_Laws.thy:1624 sets_natural_filtration_path_subset; Pair_Path_Laws.thy:2600 subalgebra_natural_filtration_path, 2616 sigma_finite_subalgebra_natural_filtration_path

Continuous_Time_Martingales.Natural_Filtration.natural_filtration_eval states `Y v : borel_measurable (natural_filtration N 0 Y u)` for 0 <= v <= u at any `{second_countable_topology, banach}` codomain. With Y = %v w. w v that is exactly nat_filt_eval and the other three lemmas. All of them re-prove it with `unfolding natural_filtration_def by (rule measurable_family_vimage_algebra)`, a pattern that occurs 30 times in the repository.

sets_natural_filtration_path_subset is `Modification_Transfer.sets_natural_filtration_subset[OF pair_law_eval_measurable]`, which has the same conclusion `sets (natural_filtration M 0 X i) <= sets M`. subalgebra_/sigma_finite_subalgebra_natural_filtration_path follow from the AFP Martingales stochastic_process locale (subalgebra_natural_filtration, finite_filtered_measure_natural_filtration). martingale_F_limit (Pair_Path_Laws.thy:3154) already uses finite_filtered_measure_natural_filtration.

Evidence: Natural_Filtration.thy:49 `lemma natural_filtration_eval: fixes Y :: "real => 'b => 'c :: {second_countable_topology, banach}" assumes "0 <= v" "v <= u" shows "Y v : borel_measurable (natural_filtration N (0::real) Y u)" unfolding natural_filtration_def by (rule measurable_family_vimage_algebra)`. Pair_Path_Laws.thy:277-283 nat_filt_eval: same proof text. Modification_Transfer.thy:671 sets_natural_filtration_subset.

Suggested action: Delete the four evaluation lemmas and point their 14+6+7+4 uses at natural_filtration_eval. Derive sets_natural_filtration_path_subset, subalgebra_natural_filtration_path and sigma_finite_subalgebra_natural_filtration_path in one line each from the library facts, or inline them.


### RA-path1-12. outerp/onormal lemmas re-prove Symmetric_Matrix_Spectra facts

*library_duplicate, impact medium, confidence high, ~140 lines.*  
Locations: Relative_Arbitrage/Pair_Path_Laws.thy:2014 onormal_parseval; Pair_Path_Laws.thy:1937 quadform_sum_outer; Pair_Path_Space.thy:796 trace_mult_outerp_sum; Pair_Path_Laws.thy:815 trace_outerp; Pair_Path_Laws.thy:2396 norm_outerp; Pair_Path_Laws.thy:537 outerp_sq; Pair_Path_Laws.thy:210 quadform_outerp; Pair_Path_Laws.thy:1970 traceM_sum_outer; Pair_Path_Laws.thy:33 psd_mat_1

- onormal_parseval is character-for-character Poincare_Separation.parseval_onormal: same statement `onormal B ==> span B = UNIV ==> (SUM u:B. (u . z)^2) = z . z`, same three-step proof.
- quadform_sum_outer is Poincare_Separation.quadform_weighted_outer_sum_eq up to variable names.
- trace_mult_outerp_sum is Outer_Products.trace_mult_outer_sum after outerp_eq_outer_prod, proved again by induction.
- trace_outerp is the [simp] trace_outer_prod.
- norm_outerp is norm_outer_prod.
- outerp_sq is an instance of outer_prod_mult.
- quadform_outerp follows from outer_prod_mv.
- traceM_sum_outer is the weighted form of trace_mult_outer_sum.
- psd_mat_1 takes 9 lines, while Brownian_Market.thy:43 and Exit_Time_Semicontinuity.thy:344 prove the same statement inline `by (simp add: psd_def)`.

Evidence: Poincare_Separation.thy:325 `lemma parseval_onormal: ... assumes B: "onormal B" "span B = UNIV" shows "(SUM v:B. (v . x)^2) = x . x"`. Poincare_Separation.thy:229 `quadform_weighted_outer_sum_eq ... shows "x . ((SUM v:B. g v *R outer_prod v v) *v x) = (SUM v:B. g v * (v . x)^2)"` vs Pair_Path_Laws.thy:1940 `z . ((SUM u:S. c u *R outer_prod u u) *v z) = (SUM u:S. c u * (u . z)^2)`. Outer_Products.thy:42 trace_mult_outer_sum; :29 trace_outer_prod [simp]; Poincare_Separation.thy:819 norm_outer_prod; Outer_Products.thy:39 outer_prod_mult.

Suggested action: Delete onormal_parseval and quadform_sum_outer and redirect their Value_Function_Subsolution uses. Restate the rest as one-line corollaries via outerp_eq_outer_prod when they move to Symmetric_Matrix_Spectra (see the next finding). Replace psd_mat_1's proof by `by (simp add: psd_def)` and use it in Brownian_Market and Exit_Time_Semicontinuity.


### RA-path1-13. The exit-time semicontinuity block belongs in Continuous_Path_Spaces.Path_Exit_Times, whose own text still points to it

*misplacement, impact medium, confidence high, ~420 lines.*  
Locations: Pair_Path_Space.thy:346 etime_shift_le_of_eroded, 372 etime_shift_uniform_margin, 455 etime_shift_box_half, 615 etime_shift_box, 854 vshift_sup_usc, 1489 vshift_sup_usc_of_seq_compact, 1593 etime_shift_of_restrict, 1689 vshift_path_law; Continuous_Path_Spaces/Path_Exit_Times.thy:1728, 1752-1755, 1749 definition vshift; Semicontinuous_Analysis/Berge.thy:130

All eight statements are at `'b::{polish_space,banach}` with no pair and no paper. vshift is defined in Path_Exit_Times, and the rest of the vshift theory (vshift_le, vshift_less_iff_positive_mass, etime_shift_superlevel_closed, open_etime_shift_less, positive_mass_at_some_qtime) lives there.

Path_Exit_Times.thy:1728 says "exactly as in etime_shift_uniform_margin", which is a reference upwards into the paper session. Its text at 1752-1755 ("Both halves of the x-perturbation in one statement: ... there is an open set of paths of positive P-mass on which the exit time stays below d for every starting point within delta of x") describes etime_shift_box_half but is followed by `definition vshift`: the lemma was left behind when the text moved.

Berge.thy:130 cites `Exit_Time_Semicontinuity.etime_shift_box`, a stale name, and is again a reference from a paper-free session into the paper session. The Continuous_Path_Spaces ROOT already advertises "the exit time ... upper semicontinuous along weak convergence of path laws".

Evidence: Path_Exit_Times.thy:1749 `definition vshift :: "real => 'b::{polish_space,real_normed_vector} set => 'b => (real => 'b) measure => real"`. Pair_Path_Space.thy:455 `theorem etime_shift_box_half: fixes ... A :: "'b::{polish_space,banach} set" and P :: "(real => 'b) measure"`. vshift_sup_usc needs Semicontinuous_Analysis.Berge; Continuous_Path_Spaces already lists Semicontinuous_Analysis under `sessions`.

Suggested action: Move the eight lemmas, in this order, to the end of Path_Exit_Times and add the Berge import there. Delete the orphan text at Path_Exit_Times.thy:1752 or put it back in front of etime_shift_box_half, and fix Berge.thy:130. This removes Pair_Path_Space's need for Semicontinuous_Analysis.Berge.


### RA-path1-14. horizon_sq_int_martingale_stopped re-proves Stopped_Localization.stopped_martingale_L2

*clone, impact medium, confidence high, ~55 lines.*  
Locations: Relative_Arbitrage/Pair_Path_Laws.thy:1516 horizon_sq_int_martingale_stopped; Continuous_Path_Spaces/Stopped_Localization.thy:22 stopped_martingale_L2

Clause (1) builds the Doob envelope `HM.Dsup` from the horizon_sq_int_martingale locale and feeds optional_stopping with stopped_adapted_of_cont, which is exactly the body of stopped_martingale_L2. The locale already provides `Y_sq_integrable` for all s >= 0 and the martingale, and `cont0` (derived inside the proof) supplies the continuity hypothesis. So clause (1) is `stopped_martingale_L2[OF HM.prob_space_M HM.martingale_axioms HM.Y_sq_integrable cont0 tnn tstop]`; only clause (2), square integrability of the stopped process via Dsup_sq_integrable, is new.

Evidence: Stopped_Localization.thy:39-77: hsim, Dex/Dsup_dominates/Dsup_integrable, `rule optional_stopping[OF mg tau_nonneg tau_stop]`, stopped_adapted_of_cont; Pair_Path_Laws.thy:1543-1573 the same chain with HM.Dsup. Doob_Inequality.thy:577 locale assumes `Y_sq_integrable: "!!s. 0 <= s ==> integrable M (%w. (Y s w)^2)"`.

Suggested action: Derive clause (1) from stopped_martingale_L2 and keep only clause (2). Move the lemma to Stopped_Localization; it is generic (Q :: 'a measure, Z real-valued).


### RA-path1-15. Dead definitions and lemmas (three of them listed as open in PLAN section 6.3)

*dead_code, impact medium, confidence high, ~230 lines.*  
Locations: Pair_Path_Space.thy:851 abbreviation pairX, 974 abbreviation pairY; Pair_Path_Laws.thy:229 definition Yint; Pair_Path_Laws.thy:84 definition acont, 121 acont_set_borel_measurable; Pair_Path_Laws.thy:722 pair_holder_charge_split; Pair_Path_Laws.thy:4492 covariation_val_mono_class, 4112 covariation_class_mono, 4095 covariation_classI, 4081 covariation_class_martingale_fst, 4088 covariation_class_martingale_compensated

- pairX and pairY: only their own declarations mention them. Section 11 says they were widened but they are still unused, and section 6.3 asked to "either be used or deleted".
- Yint and acont / acont_set_borel_measurable: occur only in their declarations and in prose. Exit_Class_Limits.thy:29, :57 and :64 still describe a market-witness bridge via `Exit_Class.acont` and `Yint (acont ...)` that no proof uses any more.
- pair_holder_charge_split (68 lines): no proof uses it. Pair_Path_Space.thy:445 even says "so the split lemma is not needed either".
- covariation_val_mono_class: unused. Its only support, covariation_class_mono, is the sole user of covariation_classI, covariation_class_martingale_fst and covariation_class_martingale_compensated.
A proof-term analysis should confirm this; these results are textual.

Evidence: grep -rnw: pairX -> Pair_Path_Space.thy:851,852 only; Yint -> Pair_Path_Laws.thy:156 (text), 229, 230, Exit_Class_Limits.thy:64 (text); acont_set_borel_measurable -> Pair_Path_Laws.thy:121 and Exit_Class_Limits.thy:57 (text); pair_holder_charge_split -> Pair_Path_Laws.thy:238 (text), 722, Pair_Path_Space.thy:445 (text); covariation_val_mono_class -> declaration only.

Suggested action: Delete all eleven, along with the stale prose at Exit_Class_Limits.thy:20-70. If monotonicity in S is wanted as API of a future covariation-class library, keep covariation_class_mono and covariation_val_mono_class but say so.


### RA-path1-16. Section headers and text blocks are systematically detached from the lemmas they describe

*documentation, impact medium, confidence high, ~700 lines.*  
Locations: Pair_Path_Space.thy:105-129 (two empty sections, then radial_sq_upto_gen), 220-228, 337 (scalar QV header -> etime_shift_le_of_eroded), 419, 437, 607 (matrix QV header -> etime_shift_box), 682 (-> rot_col_cont), 784-793 (sconstraint prose -> trace_mult_outerp_sum), 816 (Gaussian member -> pair_eval_coord_cont), 966, 977-990 ((1.7) -> pair_eval_coord_sq_cont), 1243, 1259, 1439, 1516; Pair_Path_Laws.thy:16-31 (Theorem 1.1 clause (1) -> psd_mat_1), 77-96, 149-159, 215-227 (ell_op_s <= ell_op -> Yint), 261 'Clause (0)' -> restrict_in_mspace, 584, 669, 1156-1172, 1496, 1603, 1784, 1861 'Sums of outer products' -> pair_eval_F_cont, 2135 'Selecting a value-minimal index set' -> pair_law_F_sq_mean_of_nn_bound, 2307 -> pair_test_F_sq_bound, 3258, 3493, 3745, 4475 'Pair tightness' -> covariation_val; Path_Splicing.thy:24-37, 45-54, 164, 375-383, 400-409, 502, 661, 715-719 (sconstraint/Lemma 2.1 -> pcut_id_on_mspace), 1057-1062 (two empty subsections), 1194, 1310-1316, 1341, 1386, 1605, 1786, 1826, 1903-1923 (three clause texts -> ploc_eq_T_of_below), 2037

The first declaration after almost every section, subsection or text block in the three theories is unrelated to it. This looks like the result of the "topologically sorted" mechanical moves of phases 6 and 12. Examples:
- 'section The exit time is upper semicontinuous' is immediately followed by another 'section Diagonal entries under the eigenvalue constraints'.
- 'section From the convexified constraint to a feasible witness' (the capped spectral split of Eq. (1.9)) heads pair_test_F_sq_bound.
- 'subsection The averaged covariation stays in the constraint set' heads trace_mult_outerp_sum.
The generated PDF of these three theories is therefore incoherent. The orphans also put most of the paper prose (sconstraint 8 times, exit_class 16, exit_val 11, '(1.x)' 14, 'Lemma 2.x' 8, ell_op 1) into what the ROOT calls the path toolkit.

Evidence: awk pairing of each header with the next declaration (output in this audit); e.g. Pair_Path_Laws.thy:2135-2139 `section <Selecting a value-minimal index set: the threshold argument> ... lemma pair_law_F_sq_mean_of_nn_bound`.

Suggested action: After the moves above, re-section each surviving theory by hand. Delete every text block whose subject lives elsewhere (most refer to Exit_Class*, Dynamic_Programming_*, Value_Function_*); write one short paragraph per remaining lemma group. Add a check, e.g. that every `section` is followed within N lines by a declaration whose name occurs in the section's first text, to the move tooling.


### RA-path1-17. The constrained covariation class (covariation_class/val, 25 statements) is class-layer content inside the path toolkit

*structure, impact medium, confidence high, ~475 lines.*  
Locations: Relative_Arbitrage/Pair_Path_Laws.thy:4022-4497 section 'Laws with a constrained covariation'

The definition and its 24 consequences need outerp and the 'n pairpath type. They are used only by Exit_Class (exit_class_eq_covariation and 15 specialisations). They form the generic martingale-problem class of G11 and are neither path surgery nor law surgery. Inside Pair_Path_Laws they make the toolkit carry "the value of the minimum-exit-time problem", against the ROOT layering. They are also the only reason the new session would need to know about a constraint set.

Evidence: Pair_Path_Laws.thy:4480-4482 text: "The value of the minimum-exit-time problem over such a class ... K and S are both parameters". Usage: covariation_* used only in Exit_Class.thy and Pair_Path_Laws.thy.

Suggested action: Give it its own theory, Covariation_Class.thy, importing only Pair_Path_Laws (Pair_Paths after the split). Put it either at the head of the class layer of Relative_Arbitrage or as the last theory of the new Path_Space_Operations session (it is paper-free and parametric in S). Exit_Class imports it.


### RA-path1-18. pexit lower bounds re-derive Path_Exit_Times lemmas (pexit_min_horizon, pexit_split_at_r, pexit_cong_on)

*library_duplicate, impact medium, confidence medium, ~300 lines.*  
Locations: Path_Splicing.thy:1007 pexit_pcut_ge; Path_Splicing.thy:1216 pexit_pglue_ge; Path_Splicing.thy:612 pexit_pglue_split' and 1402 pexit_pglue_split; Path_Splicing.thy:1261 pexit_pglue_dpp; Path_Splicing.thy:1552 pexit_delayed_rebase; Path_Splicing.thy:1950 pexit_padd_dpp; Continuous_Path_Spaces/Path_Exit_Times.thy:1505 pexit_split_at_r, 1580 pexit_surv_of_less, 1604 pexit_cong_on, 1649 pexit_min_horizon, 2101 pexit_eq_of_stays

All six Path_Splicing lemmas unfold `pexit_def etime_def`, prove `lb` for each z in `{t. 0<=t & t<=T & f t : -K} Un {T}` by a hit/cap case split, and finish with cInf_greatest. That is 36-86 lines each.
- pexit_pcut_ge (`min (pexit T K (fst o w)) S <= pexit S K (fst o pcut S w)`) is `pexit_pcut` plus `pexit_min_horizon`, which even give equality.
- pexit_pglue_ge is pexit_cong_on (via pglue_le) plus pexit_min_horizon.
- pexit_pglue_split is a corollary of pexit_pglue_split'. Its hypothesis `s : {0..c}` implies split''s `0 <= s ==> s < c`, yet it is proved again in 48 lines.
- pexit_pglue_dpp's inner `stay` proof (lines 1278-1286) is verbatim the `stay` of pexit_split_at_r and pexit_surv_of_less.
- pexit_delayed_rebase and pexit_padd_dpp are pexit_split_at_r (with pexit_eq_of_stays for the frozen part) plus pexit_cong_on.

Evidence: Path_Exit_Times.thy:1649 `lemma pexit_min_horizon: assumes "0 <= S" "S <= T" shows "pexit S K f = min (pexit T K f) S"`; Path_Splicing.thy:538 `pexit_pcut: pexit U K (%t. fst (pcut U w t)) = pexit U K (%t. fst (w t))`; Path_Exit_Times.thy:1505 `pexit_split_at_r: ... surv: pexit r K f = r ... endK: f r : K shows pexit T K f = r + pexit (T - r) K (%s. f (r + s))`.

Suggested action: Replace pexit_pcut_ge and pexit_pglue_ge by 2-5 line corollaries, derive pexit_pglue_split from pexit_pglue_split', and rewrite pexit_pglue_dpp, pexit_delayed_rebase and pexit_padd_dpp through pexit_split_at_r / pexit_eq_of_stays. If the lemma "(!!t. 0<=t ==> t<b ==> f t : K) ==> b <= T ==> b <= pexit T K f" is wanted repeatedly, add it to Path_Exit_Times.


### RA-path1-19. Small within-repository duplicates: restrict_in_mspace, pcut_id_on_mspace, continuous_on_pglue/iglue, compensated-martingale projection, coordinate continuity/measurability

*clone, impact low, confidence high, ~150 lines.*  
Locations: Pair_Path_Laws.thy:263 restrict_in_mspace vs Continuous_Path_Spaces/Path_Space.thy:513 restrict_mspace_path_metric; Path_Splicing.thy:721 pcut_id_on_mspace vs Path_Space.thy:1112 mspace_path_restrict_self; Pair_Path_Space.thy:1322 continuous_on_pglue vs Pair_Path_Laws.thy:51 continuous_on_iglue; Pair_Path_Laws.thy:4308 covariation_class_compensated_martingale vs 4088 covariation_class_martingale_compensated; Pair_Path_Laws.thy:836 X_eval_entry_measurable vs Pair_Path_Space.thy:1307 pair_law_coord_measurable; Pair_Path_Space.thy:425 path_coord_cont_on vs Pair_Path_Laws.thy:3478 eval_component_continuous; Pair_Path_Laws.thy:4240 covariation_class_eval_measurable vs 341 pair_law_eval_measurable; Path_Splicing.thy:1484 pembed_mspace vs 1499 pembed_mspace_full

- restrict_in_mspace is restrict_mspace_path_metric at a product codomain; it is even proved through Lipschitz_restrict_path_metric, which is itself proved from restrict_mspace_path_metric.
- pcut_id_on_mspace is `mspace_path_restrict_self` after unfolding pcut_def.
- continuous_on_pglue and continuous_on_iglue have identical proofs on {0..T}/{r..T} and {0..}/{r..}.
- covariation_class_compensated_martingale and covariation_class_martingale_compensated have the same statement (bound variable u vs t).
- X_eval_entry_measurable is pair_law_coord_measurable for all u and the path Borel sets.
- path_coord_cont_on and eval_component_continuous are the same fact up to `min u S = u`.
- covariation_class_eval_measurable is pair_law_eval_measurable[OF covariation_class_sets].
- pembed_mspace and pembed_mspace_full repeat the same continuity proof.

Evidence: Path_Space.thy:513 `lemma restrict_mspace_path_metric: ... f : mspace (path_metric m') shows restrict f {0..m} : mspace (path_metric m)`; Pair_Path_Laws.thy:263 `restrict_in_mspace: ... w : mspace (path_metric T ...) shows restrict w {0..s} : mspace (path_metric s ...)`. Pair_Path_Laws.thy:4088 and 4308: both `martingale Q (natural_filtration Q 0 (%t w. w t)) 0 (%t w. outerp (fst (w (min t T))) - snd (w (min t T)))`.

Suggested action: Delete restrict_in_mspace, pcut_id_on_mspace, covariation_class_compensated_martingale (keep one name), X_eval_entry_measurable or pair_law_coord_measurable (keep one, with the other as a corollary), and covariation_class_eval_measurable. Merge continuous_on_pglue/iglue into one lemma over a closed interval [0, b] with b : ereal or an arbitrary upper set, and prove pembed_mspace_full from a shared continuity lemma.


### RA-path1-20. Duplicated paragraphs, stale "lives in" tombstones and incorrect descriptive prose

*documentation, impact low, confidence high, ~120 lines.*  
Locations: Pair_Path_Laws.thy:4336-4338 and 4340-4342 (identical paragraph twice); Pair_Path_Laws.thy:4370-4373 and 4375-4378 (identical paragraph twice); Pair_Path_Space.thy:1591 'pair_snd_borel lives in Exit_Class_Pasting'; Path_Splicing.thy:409 'pair_fst_borel lives in Exit_Class_Pasting' (both are in Continuous_Time_Martingales/Integrability_Criteria.thy:749/754); Pair_Path_Laws.thy:3260 'prod_minus_sq_bound, fourth_power_sum_bound ... live in Increment_Moments' (two are in Power_Inequalities); 37 'X lives in @{theory Y}' tombstone notes (11/16/10); Pair_Path_Space.thy:42-47 theory description; Relative_Arbitrage/ROOT description: 'the path toolkit (Pair_Path_Space through Path_Law_Sampling) knows nothing of the constraint set or the value function'; Pair_Path_Laws.thy:203 '@{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}' note

- Two paragraphs are duplicated verbatim.
- Three tombstones point to the wrong theory.
- The 37 tombstones carry no information for a reader of the document. Some force imports: the antiquotation at Pair_Path_Laws.thy:203 is one of only two reasons the theory needs Doubling_Of_Variables.
- Pair_Path_Space's header says it "collects what is true of paths, and of laws of paths, before any constraint on the covariation is imposed". It actually holds outerp, rotm continuity, Berge semicontinuity, pathwise QV and a Lemma 2.2 adapter.
- The ROOT claim is false: Pair_Path_Laws defines covariation_class (a constraint set as parameter) and covariation_val (the value function of the exit problem), and contains nonbinding_horizon_ex at k < CARD('n).

Evidence: Pair_Path_Laws.thy:4336-4342 two identical `text <Squaring the coordinate is the diagonal entry of outerp ...>`; 4370-4378 two identical `text <integral_of_bounded_linear ... live in ...Martingale_Algebra>`. grep -c 'lives in' -> Pair_Path_Space 11, Pair_Path_Laws 16, Path_Splicing 10.

Suggested action: Delete the duplicate paragraphs and all tombstones (the move history belongs in git, not in the document). Fix or delete the three stale ones. Rewrite the Pair_Path_Space header and the ROOT layer description after the moves.


### RA-path1-21. Hypotheses stronger than needed

*generalisation, impact low, confidence high, ~10 lines.*  
Locations: Pair_Path_Space.thy:1606 pair_test_sq_bound (P: prob_space N); Pair_Path_Laws.thy:2323 pair_test_F_sq_bound (P: prob_space N); Pair_Path_Space.thy:248 qvps_eq_A_stopped (T0: 0 < T); Pair_Path_Laws.thy:292 mspace_path_metric_ne (U: 0 <= U)

- In pair_test_sq_bound and pair_test_F_sq_bound the assumption `P: prob_space N` is never referenced in the proof. Domination by an integrable function needs no finiteness.
- qvps_eq_A_stopped uses `0 < T` only to obtain `0 <= T`.
- mspace_path_metric_ne holds for every U: for U < 0 the everywhere-undefined function is in the space.

Evidence: grep -nw 'P' over Pair_Path_Space.thy:1619-1687 and Pair_Path_Laws.thy:2335-2394 finds no occurrence; Pair_Path_Space.thy:255 `have Tnn: "0 <= T" using T0 by simp` is the only use of T0.

Suggested action: Drop P from both sq_bound lemmas, or delete the coordinate copy entirely (first finding). Weaken T0. Low priority.


### RA-path1-22. Long proofs of routine measurability and continuity facts

*simplification, impact low, confidence medium, ~330 lines.*  
Locations: Pair_Path_Laws.thy:846-1015 euOrth_mset_cond (170 lines); Pair_Path_Laws.thy:2051-2117 euOrth_mset (67); Pair_Path_Laws.thy:1362-1419 euXi_term_cont (58); Pair_Path_Laws.thy:371-433 frozen_set_measurable (62); Pair_Path_Laws.thy:241-259 nonbinding_horizon_ex (19); Pair_Path_Laws.thy:33-41 psd_mat_1 (9)

- euOrth_mset_cond proves continuity of `%w. transpose (SF w) *v G w` entry by entry, through bounded_linear_vec_nth chains, then measurability of a finite conjunction by hand induction on m. The `measurable` method with pair_law_eval_measurable as a [measurable] rule, borel_measurable_continuous_onI and pred rules for `ALL j<m` (pred_intros_countable_bounded) should do this in a few lines, as should euOrth_mset.
- euXi_term_cont similarly rebuilds continuity of outerp and matrix products entrywise; it is continuous_intros plus continuity of outerp, which could be a [continuous_intros] lemma next to outerp_borel.
- frozen_set_measurable goes through rationals and vanishes_of_rational. The set is closed in the path topology: an intersection of closed evaluation preimages, as closedin_start_point does for one time. borel_of_closed would finish in about 12 lines.
- nonbinding_horizon_ex is `gt_ex` applied to `2*(rK*rK)/real(CARD('n)-k)`, since rK*rK >= 0.
- psd_mat_1 is `by (simp add: psd_def)`.

Evidence: Pair_Path_Laws.thy:870-916 nested `entry`/`tc`/`gc`/`prodc` continuity blocks; :992-1014 manual `induction m` over `sets.Int`. Brownian_Market.thy:43 `have psd1: "psd (mat 1 :: real^'n^'n)" by (simp add: psd_def)`. Pair_Path_Laws.thy:820-834 closedin_start_point shows the closedin_continuous_map_preimage_gen pattern.

Suggested action: Re-prove with the measurable method and continuous_intros, adding `continuous_on S f ==> continuous_on S (%x. outerp (f x))` as a [continuous_intros] rule in Outer_Products. Prove frozen_set_measurable by closedness.


### RA-path1-23. The Lipschitz-on-path-space proof pattern is repeated for every operation

*clone, impact low, confidence medium, ~160 lines.*  
Locations: Path_Splicing.thy:169 Lipschitz_pfut, 281 Lipschitz_pshift, 916 Lipschitz_pfst, 1073 mdist_pglue_le + 1131 Lipschitz_pglue; Continuous_Path_Spaces/Path_Space.thy:525 Lipschitz_restrict_path_metric

Each proof unfolds Lipschitz_continuous_map_def, shows the funcset via the `_mspace` lemma, gets pointwise bounds from path_mdist_le_iff_all on both sides, and closes with `exI[of _ B]`. That is 40-60 lines each; the per-operation content is 5-10 lines of pointwise dist arithmetic. Lipschitz_pglue additionally re-proves `a <= sqrt(a^2+b^2)` for prod_dist twice (c1/c2).

Evidence: Path_Splicing.thy:189-191 / 300-301 / 936-938 / 1093-1096 identical `using path_mdist_le_iff_all[OF T f g] by blast` steps; Path_Space.thy:539-552 the same pattern.

Suggested action: Add to Path_Space a lemma `Lipschitz_path_mapI: (!!f. f : mspace (path_metric T) ==> Phi f : mspace (path_metric T')) ==> 0 <= T' ==> (!!f g t. f,g : mspace .. ==> t : {0..T'} ==> dist (Phi f t) (Phi g t) <= B * mdist (path_metric T) f g) ==> Lipschitz_continuous_map ...`. Use it for the four Path_Splicing lemmas, for Lipschitz_restrict_path_metric, and for the analogous lemmas in Path_Stopping_Times/Path_Law_Pasting. Use HOL's real_sqrt_sum_squares_ge1/2 for the prod_metric step.


### RA-path1-24. Hölder-ball tightness criterion: a pair-only statement of a fact proved inline twice in Path_Tightness

*generalisation, impact low, confidence medium, ~80 lines.*  
Locations: Pair_Path_Laws.thy:677 tight_on_set_pair_holder_charge; Pair_Path_Laws.thy:528 compactin_pair_holder_ball (one-line restatement of Path_Space.compactin_path_holder_ball); Continuous_Path_Spaces/Path_Tightness.thy:248 tight_on_set_path_laws (part2), 530 tight_on_set_path_laws_vec

tight_on_set_pair_holder_charge ("if for each e some Hölder ball started at (x,0) carries all but e of every law's mass, the family is tight") holds verbatim at any `'b::{polish_space, real_normed_vector, heine_borel}` with start point p. That is the codomain of compactin_path_holder_ball, and prod is heine_borel. The same compact-set step is done inline in the part2 blocks of tight_on_set_path_laws and _vec. compactin_pair_holder_ball is `by (rule compactin_path_holder_ball[OF T ga c])`.

Evidence: Path_Space.thy:125 `theorem compactin_path_holder_ball: fixes x :: "'b::{polish_space, real_normed_vector, heine_borel}"`; Pair_Path_Laws.thy:535 `by (rule compactin_path_holder_ball[OF T ga c])`.

Suggested action: State `tight_on_set_of_holder_charge` generically in Path_Tightness, use it in tight_on_set_path_laws(_vec) and Exit_Class_Tightness, and delete compactin_pair_holder_ball.


### RA-path1-25. covariation_class prose overstates its meaning for arbitrary S

*faithfulness, impact low, confidence medium, ~10 lines.*  
Locations: Pair_Path_Laws.thy:4024-4036; Pair_Path_Space.thy:979-990

The text says that with "every difference quotient of Y in a fixed set S of matrices ... Y is the covariation of X and S constrains its density. S itself is arbitrary." Requiring all difference quotients (1/(t-s))(Y t - Y s) to lie in S is equivalent to "d<X>/dt in S a.e." (the paper's (1.7)) only when S is closed and convex. For non-convex S it is strictly stronger: the averages of the density must lie in S. The headline theorem is unaffected, because the bridge exit_class_eq_covariation is used at sconstraint k L, which is closed and convex (Lemma 2.1). But the library-style claim that S is arbitrary and the class reads (1.7) is wrong for general S.

Evidence: Pair_Path_Laws.thy:4046 `(AE w in Q. ALL s t. 0 <= s --> s < t --> t <= T --> (1 / (t - s)) *R (snd (w t) - snd (w s)) : S)`; Path_Splicing.thy:715-719 itself notes that the constraint survives concatenation only because the set was convexified (Lemma 2.1).

Suggested action: State in the covariation_class text that the class equals "density in S a.e." iff S is closed and convex, or add `convex S`/`closed S` where the equivalence is claimed.


## RA-path2

The cluster is the upper half of the path toolkit that the DPP layer of Theorem 1.1 runs on. It holds no paper statement, so faithfulness is not at issue here. Everything it proves is infrastructure, and it is reachable from theorem_1_1 through Dynamic_Programming_* and Value_Function_Supersolution_Case_1/2.

(1) Path_Stopping_Times mixes three unrelated subjects.
  * Abstract optional sampling: the dyadic ceiling dyceil; pre_sigma_of, the sigma-algebra F_sigma (sigma algebra of events up to a stopping time sigma); set_martingale_sampling(_simple/_two), i.e. E[Y_sigma; A] = E[Y_U; A] for A in F_sigma. None of this mentions paths.
  * The pathwise (Galmarino-type) notion path_stopping_time, at a product codomain because its continuity clause reads fst. Also the split pstopped/pafter, their measurability, and the bridge path_stopping_time_event_filtration from the pathwise notion to the filtration notion.
  * stopped_increment_of_horizon_gen (sampling a horizon square-integrable martingale at two path stopping times), plus a large dead tail.

(2) Path_Law_Pasting covers six subjects: laws of processes (pair_law_of, a named distr) and martingale transport (martingale_pair_law, martingale_pshift_law, martingale_of_cuts); the shifted law pshift_law with AE transfer and joint weak continuity; the additive glue aglue_law; the deterministic and kernel glues pglue_law, kglue_law and kglue_law' with their AE transfers; the regular conditional distribution of the future given the past (exit_class_rcd, exit_class_rcd_ksemi via AFP Disintegration); and generic semidirect-product (ksemi) facts.

(3) Path_Law_Sampling is mostly not path toolkit. 16 of its 25 statements are at 'n pairpath. They show that the two martingale clauses of the covariation class (X, and outerp X - Y) survive the additive glue at a stopping time (aglue_*) and the conditioning on the past (pfut_rcd_*). Each result is proved twice, once for X and once for the compensated entry.

Main defects:
  * About 2,000 lines of near-verbatim X-versus-compensated twins.
  * About 850 lines of dead code: the abandoned stopping-time kernel route (rect_vimage_pre_sigma_stopping and its chain, set_integral_increment_times_known and its chain), plus the dead path_rcd and path_rcd_ksemi, which are the general forms of two live clones.
  * Re-proofs of CTM.martingale_distr and CTM.natural_filtration_pull, and of AFP Disintegration's prob_kernel.integral_fst and integrable_kernel_integrable.
  * About 60 text blocks separated from their lemmas by the phase-6 carve-out, many carrying paper prose ((1.7), clause (iv), exit_class, exit_val k L, sconstraint).
  * A linear 6-theory import chain whose tail every consumer imports, including 8 theories that use nothing from it.

PIDE could not be used: no PIDE session was running, and the shared machine (4 cores, 15 GB) was still building the HOL-Analysis heap. All claims come from reading the source and from grep, and are rated accordingly.


### RA-path2-1. X versus compensated-entry twins: 7 pairs of near-verbatim proofs in Path_Law_Sampling (about 2,000 lines)

*clone, impact high, confidence high, ~2000 lines.*  
Locations: Relative_Arbitrage/Path_Law_Sampling.thy:209 aglue_inner_increment vs :832 aglue_inner_increment_comp; Relative_Arbitrage/Path_Law_Sampling.thy:575 aglue_law_X_increment vs :1443 aglue_law_comp_increment; Relative_Arbitrage/Path_Law_Sampling.thy:708 aglue_law_X_martingale vs :1781 aglue_law_comp_martingale; Relative_Arbitrage/Path_Law_Sampling.thy:1929 aglue_law_X_integrable vs :2129 aglue_law_comp_integrable; Relative_Arbitrage/Path_Law_Sampling.thy:1599 pfut_rcd_X_increment_zero vs :2822 pfut_rcd_comp_increment_zero; Relative_Arbitrage/Path_Law_Sampling.thy:2032 pfut_rcd_X_integrable vs :2992 pfut_rcd_comp_integrable; Relative_Arbitrage/Path_Law_Sampling.thy:2582 pfut_rcd_X_martingale vs :3080 pfut_rcd_comp_martingale; Relative_Arbitrage/Path_Law_Sampling.thy:2307 aglue_msec_X vs :2438 aglue_msec_C; :2483 aglue_gint_X vs :2526 aglue_gint_C

Each clause is proved once with integrand fst (w (min u T)) $ c and again with (outerp (fst (w (min u T))) - snd (w (min u T))) $ c $ d, by the same argument.

* The outer part of aglue_inner_increment (379-565) and of aglue_inner_increment_comp (1173-1369) are line-for-line the same, with ?Y renamed to ?Z: si, spint, Esplit, compl, Epart/rew, sti/stj, Cpre, samp via stopped_increment_of_horizon_gen, valE, Ym/Zm, e1, e2.
* In pfut_rcd_X_martingale and pfut_rcd_comp_martingale, the blocks exPi/bchoice/Espec/step/zero_all/rat_int/S_int and the per-p' assembly through martingale_of_rational_set_integral_eq are identical except that martingale_vecI becomes martingale_matI.
* The hypothesis lists (about 25 lines each) are also restated six times.

Evidence: Text at Path_Law_Sampling.thy:2813: 'The clause-(iv) twin of pfut_rcd_X_increment_zero.  Two differences, both bookkeeping'. Text at :1173: '-- the outer split, exactly as in the X clause'. The statement lengths come in pairs: 358/539, 124/156, 108/139, 97/119, 174/170, 78/83 and 229/256 lines.

Suggested action: State each argument once for a real-valued path functional h u w = F (w (min u T)) with F continuous, or for a finite family read out by a bounded linear map, under a horizon_sq_int_martingale or martingale hypothesis on h.

* For aglue, take the pathwise inner facts (the 'after' and 'before' steps) as hypotheses; the comp 'after' step already reduces to X instances through 'expand'.
* Derive the X and comp versions as instances. martingale_vecI and martingale_matI then become the only difference.

Expected saving: about 900 lines.


### RA-path2-2. About 850 lines of dead code: the abandoned stopping-time kernel route and its scaffolding

*dead_code, impact high, confidence high, ~850 lines.*  
Locations: Relative_Arbitrage/Path_Law_Pasting.thy:3400 rect_vimage_pre_sigma_stopping (only cited in text at Path_Stopping_Times.thy:1872); Relative_Arbitrage/Path_Law_Pasting.thy:3313 pafter_vimage_pre_sigma; Relative_Arbitrage/Path_Stopping_Times.thy:1153 pstopped_vimage_pre_sigma, :1228 pre_sigma_of_Int, :1127 pre_sigma_ofI_le, :676 path_stopping_time_max, :818 pstopped_cut_compose, :847 pcut_pafter_cut_compose, :802 path_stopping_time_cut_eq; Relative_Arbitrage/Path_Stopping_Times.thy:1901 set_integral_increment_times_known (only cited in text at :2063), plus :1809 integrable_at_path_stopping_time, :1683 integrable_at_bounded_stopping_time and :1246 sigma_algebra_pre_sigma_of, which only it uses; Relative_Arbitrage/Path_Stopping_Times.thy:966 path_stopping_time_shift_event (text :1002 only) and :703 path_stopping_time_shift; Relative_Arbitrage/Path_Stopping_Times.thy:108 exit_component_dyceil_tendsto (text :1003 only); Relative_Arbitrage/Path_Stopping_Times.thy:584 pstopped_padd, :621 pafter_padd (text Dynamic_Programming_Additive_Glue.thy:179 only), :567 padd_stopping_time; Relative_Arbitrage/Path_Stopping_Times.thy:198 pstopped_add_pafter, :216 pafter_before (text Path_Splicing.thy:45/376/1907 only); Relative_Arbitrage/Path_Law_Pasting.thy:1169 kglue_law'_rcd_eq (text Dynamic_Programming_Kernels.thy:195 only); Relative_Arbitrage/Path_Law_Pasting.thy:2389 path_rcd, :2834 path_rcd_ksemi (see the exit_class_rcd clone finding)

`grep -rnw` over all .thy files finds each of these names only at its own declaration and in text or `@{thm [source]}` antiquotations. The intermediate lemmas are used only by other dead lemmas.

The chain is the F_{u max theta} measurability of rectangles for the conditional law of pafter given pstopped: the 'stopping-time twin' of pfut_rcd_X_increment_zero announced at Path_Stopping_Times.thy:1860-1899 and :2053-2064. That twin was never built; the additive glue reached the result another way.

Two side effects:
* §11 of PLAN_RESTRUCTURING_2 spent widening effort on three of these lemmas (padd_stopping_time, pstopped_padd, pafter_padd).
* The 'pair-specific by mathematics' list in its gate includes the dead exit_component_dyceil_tendsto.

Evidence: grep -rnw output: set_integral_increment_times_known appears only at :1901 and in text at :2063. rect_vimage_pre_sigma_stopping appears only at :3400 and in text at PST:1872. path_rcd_ksemi appears only at :2834 and in text at :2907. pstopped_padd/pafter_padd appear only in the text '(@{thm [source] pstopped_padd}, @{thm [source] pafter_padd})' at DP_Additive_Glue:179. notes/UNUSED_THMS.md already listed several of them under the defunct Exit_Class_DPP.

Suggested action: Delete the chains, together with the orphan sections that narrate them (PST:1860-1899, :2050-2064, PLP:2905-2907).

Keep path_rcd and path_rcd_ksemi, and derive the live exit_class_rcd* from them (see that finding). Keep path_stopping_time_cut_eq if it is used to shorten path_stopping_time_cut.

The antiquotations that cite the deleted lemmas must be rewritten in the same commit.


### RA-path2-3. exit_class_rcd and exit_class_rcd_ksemi re-prove the dead general path_rcd and path_rcd_ksemi in the same file

*clone, impact medium, confidence high, ~160 lines.*  
Locations: Relative_Arbitrage/Path_Law_Pasting.thy:1353 exit_class_rcd; Relative_Arbitrage/Path_Law_Pasting.thy:2389 path_rcd; Relative_Arbitrage/Path_Law_Pasting.thy:1601 exit_class_rcd_ksemi; Relative_Arbitrage/Path_Law_Pasting.thy:2834 path_rcd_ksemi; Relative_Arbitrage/Path_Stopping_Times.thy:417-425 (text)

path_rcd states the disintegration for arbitrary measurable phi1 : P -> path_borel u and phi2 : P -> path_borel v. exit_class_rcd is its instance u = r, v = T - r, phi1 = pcut r, phi2 = pfut r T. The two 85-line proofs (marg, PSF, SB, D.measure_disintegration) are identical up to that substitution.

The same holds for exit_class_rcd_ksemi and path_rcd_ksemi (about 70 lines each: measure_eqI_generator_eq on rectangles).

The live copies are the specialised ones, and they carry a paper name (exit_class) in the paper-free layer. The text at PST:417-425 announces 'here they are with the two maps and the two horizons free', but that general version sits in another theory and is dead.

Evidence: Compare PLP:1369-1437 with :2405-2468. The only difference is ?phi = (pcut r w, pfut r T w) versus (phi1 w, phi2 w), plus mcut/mfut instead of m1/m2.

Suggested action: Keep path_rcd and path_rcd_ksemi. Replace the bodies of exit_class_rcd and exit_class_rcd_ksemi with one-line instances (path_rcd[OF Tr PS pcut_measurable pfut_measurable_law]). Rename them to pfut_rcd / pfut_rcd_ksemi. Move the PST:417-425 text next to path_rcd.


### RA-path2-4. martingale_pair_law and martingale_pshift_law re-prove CTM's martingale_distr; phi_filtration_measurable re-proves natural_filtration_pull

*library_duplicate, impact medium, confidence high, ~200 lines.*  
Locations: Relative_Arbitrage/Path_Law_Pasting.thy:68 martingale_pair_law; Relative_Arbitrage/Path_Law_Pasting.thy:315 martingale_pshift_law; Relative_Arbitrage/Path_Law_Pasting.thy:39 phi_filtration_measurable; Continuous_Time_Martingales/Martingale_Transfer.thy:494 martingale_distr; Continuous_Time_Martingales/Natural_Filtration.thy:25 natural_filtration_pull

martingale_distr already proves 'prob_space M, phi : M -> N, filtered_measure (distr M N phi) GG 0, phi in FF u -> GG u, Z u in GG u, martingale M FF 0 (Z o phi) imply martingale (distr M N phi) GG 0 Z'.

martingale_pair_law (87 lines) and martingale_pshift_law (83 lines) re-run its proof verbatim: the set-integral 'key' step through integral_distr and indicator rewriting, then martingale_of_set_integral_eq. Their pull hypotheses are exactly phi_filtration_measurable and pshift_filtration_measurable (Path_Splicing.thy:425).

phi_filtration_measurable (28 lines) is natural_filtration_pull with N = pair_law_of T phi M and Y = (%v w. w v). The product of Banach spaces is a {banach, second_countable_topology} codomain, so the instance typechecks.

Evidence: Martingale_Transfer.thy:489-491: 'This is the general form of what the corresponding path-space transport in the application does for path spaces'. The 'key' block at PLP:132-148 and :374-391 matches Martingale_Transfer.thy:532-549 line for line.

Suggested action: Re-prove martingale_pair_law and martingale_pshift_law as instances of martingale_distr, with filtered_measure supplied by Stochastic_Process.stochastic_process.finite_filtered_measure_natural_filtration. Replace phi_filtration_measurable by natural_filtration_pull. Expected saving: about 170 lines.


### RA-path2-5. Abstract optional sampling, dyceil and pre_sigma_of are general martingale theory and belong in Continuous_Time_Martingales

*misplacement, impact medium, confidence high, ~750 lines.*  
Locations: Relative_Arbitrage/Path_Stopping_Times.thy:15-167 dyceil, dyceil_le_U, dyceil_ge, dyceil_nonneg, dyceil_range, dyceil_le_iff, dyceil_tendsto, dyceil_stopping; Relative_Arbitrage/Path_Stopping_Times.thy:1105-1391 pre_sigma_of, pre_sigma_ofI, space_in_pre_sigma_of, pre_sigma_of_sets, pre_sigma_of_cut, pre_sigma_of_mono, pre_sigma_of_band, pre_sigma_of_value_slice; Relative_Arbitrage/Path_Stopping_Times.thy:1402 set_martingale_sampling_simple, :1485 borel_measurable_at_simple_time, :1534 set_martingale_sampling, :1648 set_martingale_sampling_two; Continuous_Time_Martingales/Time_Discretisation.thy:171 finite_dyceil_range, :175 dyceil_grid_le

About 20 live statements (roughly 750 lines) mention no path, no path_borel and no pair. They are Doob optional sampling for a real martingale against F_sigma.

The constant dyceil is defined in the paper session, yet two lemmas about its grid named after it (finite_dyceil_range, dyceil_grid_le) already live in CTM.Time_Discretisation. The pointer texts PST:54 and :77 ('finite_dyceil_range lives in ...') show the split.

The text at PST:1480 admits the duplication: 'Continuous_Time_Martingales.Optional_Sampling's dceil is locale-bound, so here is a free-standing one'.

Plan §3.7 put this block in the path toolkit ('optional sampling on path space'), but nothing in it is about path space. The path-specific consumer is stopped_increment_of_horizon_gen.

Evidence: The statements are typed at M :: 'a measure, F :: real => 'a measure, Y :: real => 'a => real. Their only dependencies are martingale, subalgebra and sets.

Suggested action: Move dyceil and its lemmas into CTM/Time_Discretisation. Move pre_sigma_of, set_martingale_sampling* and borel_measurable_at_simple_time into CTM/Optional_Sampling (or a new CTM/Stopping_Sigma_Algebra). Keep only stopped_increment_of_horizon_gen and the path_stopping_time bridge in the path layer. Delete the two pointer texts.


### RA-path2-6. Generic semidirect-product (ksemi) lemmas sit in the path layer; the plan's target for ksemi_weak_conv is wrong

*misplacement, impact medium, confidence high, ~600 lines.*  
Locations: Relative_Arbitrage/Path_Law_Pasting.thy:1560 emeasure_ksemi_rect, :1681 AE_kernel_full, :2038 AE_integrable_ksemi_section, :2135 integral_ksemi_real, :2329 integral_ksemi_rect_real, :2665 AE_kernel_integral_zero, :2921 integrable_ksemi_of_distr_rect, :2951 integrable_kernel_integral, :3006 integral_ksemi_rect_of_set_integral; Relative_Arbitrage/Path_Law_Pasting.thy:1799 ksemi_weak_conv; Continuous_Time_Martingales/Semidirect_Kernels.thy; notes/restructuring_2/dispositions.tsv rows for these names (STAY)

These ten statements are typed at arbitrary M :: 'a measure, N :: 'b measure and Kr. They concern ksemi, which is defined in CTM.Semidirect_Kernels.

PLAN §3.5 says Semidirect_Kernels should 'gain ... emeasure_ksemi_rect, AE_integrable_ksemi_section, ksemi_weak_conv', while dispositions.tsv marks all three STAY in the path toolkit. The two records conflict, and the move never happened.

ksemi_weak_conv uses weak_conv_on from AFP Levy_Prokhorov_Metric (General_Weak_Convergence.thy). CTM does not import that entry (its ROOT lists only Martingales), so the plan's target would not even build. Continuous_Path_Spaces, which imports Levy_Prokhorov_Metric and already has weak_conv_on_pushforward, is the right home.

Evidence: PLAN_RESTRUCTURING_2.md:463 lists 'emeasure_ksemi_rect, AE_integrable_ksemi_section, ksemi_weak_conv' for CTM. dispositions.tsv:1329/1340/1358 say 'STAY ... path toolkit layer (phase 6)'. The CTM ROOT has 'sessions Martingales' only.

Suggested action: Move the nine measure-level lemmas to CTM/Semidirect_Kernels, after the AFP-dedup finding has shrunk two of them. Move ksemi_weak_conv to Continuous_Path_Spaces/Path_Space next to weak_conv_on_pushforward. Correct §3.5 and dispositions.tsv.


### RA-path2-7. Long repeated hypothesis bundles call for two locales (pfut_rcd and aglue)

*structure, impact medium, confidence high, ~500 lines.*  
Locations: Relative_Arbitrage/Path_Law_Pasting.thy:1725 pfut_rcd_start, :1976 ksemi_rect_null_of_AE; Relative_Arbitrage/Path_Law_Sampling.thy:1599, :2032, :2582, :2822, :2992, :3080 (pfut_rcd_*); Relative_Arbitrage/Path_Law_Sampling.thy:209, :575, :708, :832, :1443, :1781 (aglue_*)

* pfut_rcd: about 10 statements repeat the hypotheses (r, rT, setsP, PS, K :: kappa in path_borel r -> prob_algebra (path_borel (T-r)), eq :: distr P (pcut,pfut) = ksemi ...), about 12 lines each. Their proofs repeat the same 15-25-line prologue: mcut, mfut, mphi, PQ, setsQ, neQ, KQ, SQY, eq', mphi'.
* aglue: six statements repeat T0 PQ setsQ Kp st thM Qst QH/QHC Qcont Kfr Kmean Kint Kinc (+C), about 25 lines each.

Evidence: The SQY/eq'/mphi' block appears verbatim at PLS:1646-1655, :2069-2078, :2879-2888 and :3036-3045. The Kfr/Kmean/Kint/Kinc assumption text appears at PLS:221-231, :587-597, :720-730, :844-867, :1455-1478 and :1793-1816.

Suggested action: Introduce 'locale pfut_rcd = fixes P r T kappa assumes ...', with the prologue facts as locale lemmas. Introduce 'locale aglue_setup' similarly; it also prepares the parametric statements suggested in the X/comp twins finding. Follow the CTM locale layering that §2.11 cites as the model.


### RA-path2-8. About 60 text blocks and section headers are separated from the lemmas they describe (phase-6 carve-out artefact)

*documentation, impact medium, confidence high, ~600 lines.*  
Locations: Relative_Arbitrage/Path_Stopping_Times.thy:104, :132, :169, :222, :417, :447, :550, :563, :669, :700, :734, :739, :783, :886, :926, :960, :995-1016, :1042, :1085-1091, :1211, :1242, :1310, :1337, :1478-1483, :1639, :1860-1899, :2050, :2053-2064; Relative_Arbitrage/Path_Law_Pasting.thy:155, :160-167, :269, :401-406, :595, :659, :733-737, :778, :923, :974, :1079-1086, :1101-1105, :1159, :1209, :1351, :1440, :1534-1539, :1541-1558, :1792, :1961-1974, :2026-2036, :2076, :2224, :2266-2271, :2322, :2360-2377, :2647-2663, :2697, :2769, :2905-2919, :3064-3074, :3102, :3204-3209, :3302-3311; Relative_Arbitrage/Path_Law_Sampling.thy:15-23, :83, :198-207, :1371, :1429-1441, :1773, :1920-1927, :2026, :2110-2127, :3075, :3336-3346

Examples:
* PST:169 'Sampling a process at a simple stopping time is measurable ... pre_sigma_of_value_slice' sits before 'definition pstopped'; it belongs to borel_measurable_at_simple_time (:1485).
* PST:417 'subsection The regular conditional distribution, with both maps and horizons free' sits before 'definition path_stopping_time'.
* PST:1478 'subsection Dyadic approximation from above' sits 1,460 lines after dyceil's definition.
* PLP:160 'section The off-diagonal covariation of Brownian motion' (about coord_Z_martingale and bm_paths) heads martingale_future_of_past.
* PLP:401 'subsection Almost-sure statements transport through the shift' heads 'definition aglue_law'.
* PLP:2266 'subsection Auxiliaries for clause (iv)' with 'i min theta is a stopping time' heads pstopped_law_start; the lemma it describes is path_stopping_time_min in another theory.
* PLS:198 'subsection Stopping a horizon-capped square-integrable martingale' heads aglue_inner_increment.
* PLS:3336-3346 and PST:2053-2064 are subsections with no content at the end of their theory.
* Several 'section' commands sit mid-theory (PST:995, :1528, :1639, :1860, :1881, :2053; PLP:160; PLS:1920), so the document outline of the three theories is incoherent.
* Stale names: 'exit_class_kglue_law' (PLP:1552, :2657) is exit_class_kglue_law'.
* Incorrect claims: PST:2061-2064 says set_integral_increment_times_known 'kills' the cross terms, but it is dead. PLS:21-23 says integrability of the sampled process is 'reconstructed here'; that is the dead integrable_at_path_stopping_time.

Evidence: Each location was read in full. The pattern matches the §10 note that moved blocks were 'topologically sorted against their new neighbours'.

Suggested action: Per theory, re-attach every text to the lemma it describes, or delete it when the lemma lives in another theory or no longer exists. Keep one 'section' per theory and use subsections. Do this after the dead-code deletion, since about a third of the orphans narrate dead lemmas.


### RA-path2-9. Paper-specific prose and names in the layer the ROOT advertises as paper-free

*misplacement, impact medium, confidence high, ~120 lines.*  
Locations: Relative_Arbitrage/Path_Law_Pasting.thy:163, :233, :405, :778-782 (sconstraint, sconstraint_convex), :815, :1084 (exit_val k L), :1101 ((1.6)), :1209-1215, :1549-1558, :1676, :2034-2036, :2911-2916 (exit_class k L T 0), :3102-3106 ('depends only on k, L'); Relative_Arbitrage/Path_Law_Sampling.thy:83, :567, :699, :816, :1371 (Clause (iv)), :1920, :2126 ('the paper's class (1.7)'), :3338-3346; Relative_Arbitrage/Path_Stopping_Times.thy:995, :1009, :1877, :2053; Relative_Arbitrage/Path_Law_Pasting.thy:1353 exit_class_rcd, :1601 exit_class_rcd_ksemi (names); Relative_Arbitrage/ROOT description

The ROOT says the path toolkit 'knows nothing of the constraint set or the value function'. At the level of constants that is true.

The prose, however, is written in terms of the paper:
* equation numbers (1.6)/(1.7) and the clause numbering (i)-(iv) of the class;
* sconstraint, exit_val k L, exit_class_* lemma names, and k and L.

Two live theorem names, exit_class_rcd and exit_class_rcd_ksemi, carry the paper constant although their statements are pure disintegration of path laws.

This blocks the planned promotion to a Path_Space_Operations session as much as the codomain did.

Evidence: PLP:778-782: 'which is why sconstraint had to be convex (sconstraint_convex) in the first place'. PLP:1084: 're-basing it attains exit_val k L (T - s) K y'.

Suggested action: Rewrite the surviving texts in terms of the generic objects (covariation_class S, the martingale clauses X and outerp X - Y). Move paper narration to the class layer (Dynamic_Programming_*). Rename exit_class_rcd and exit_class_rcd_ksemi as in the exit_class_rcd clone finding.


### RA-path2-10. Path_Law_Sampling is the covariation-class pasting layer, not path toolkit; its two genuine sampling lemmas belong in Path_Stopping_Times

*structure, impact medium, confidence high, ~3300 lines.*  
Locations: Relative_Arbitrage/Path_Law_Sampling.thy:209-3346 (aglue_*, pfut_rcd_*); Relative_Arbitrage/Path_Law_Sampling.thy:25 pcut_after_in_pre_sigma, :85 pstopped_eval_filtration; Relative_Arbitrage/Pair_Path_Laws.thy:4038 covariation_class; Relative_Arbitrage/Path_Law_Pasting.thy:1725 pfut_rcd_start

16 of the 25 statements are at 'n::finite pairpath and use outerp. They show that the two martingale clauses of covariation_class (Pair_Path_Laws:4038-4053) are preserved by the additive glue and by conditioning on the past. pfut_rcd_start (PLP:1725) is their clause-(i) sibling.

The file name ('Sampling a path law at a stopping time') fits only:
* pcut_after_in_pre_sigma, which is pre_sigma_of material;
* pstopped_eval_filtration, which is pstopped material and whose only consumer is Dynamic_Programming_Delayed_Class.

The §11 gate table already records Path_Law_Sampling at 9 of 25 statements pair-free, and says it is 'the pair layer proper'.

Evidence: PLS statement types: aglue_*/pfut_rcd_* all 'fixes Q :: ('n::finite pairpath) measure' with outerp. pstopped_eval_filtration has no pair content (product codomain).

Suggested action: Move pcut_after_in_pre_sigma and pstopped_eval_filtration to Path_Stopping_Times. Rename what remains to something like Covariation_Class_Pasting, placed next to covariation_class at the bottom of the class layer, after merging the X/comp twins. Do not promote it with the path toolkit.

Path_Stopping_Times (pathwise part) and Path_Law_Pasting are promotable to Path_Space_Operations once three things are done: the dead code is removed, the abstract material has gone to CTM, and the prose is cleaned.


### RA-path2-11. AE_integrable_ksemi_section and integral_ksemi_real duplicate AFP Disintegration (prob_kernel.integrable_kernel_integrable, prob_kernel.integral_fst)

*library_duplicate, impact medium, confidence medium, ~300 lines.*  
Locations: Relative_Arbitrage/Path_Law_Pasting.thy:2038 AE_integrable_ksemi_section; Relative_Arbitrage/Path_Law_Pasting.thy:2135 integral_ksemi_real; Relative_Arbitrage/Path_Law_Pasting.thy:2231 integral_aglue_law (msec hypothesis); Relative_Arbitrage/Path_Law_Sampling.thy:2255 aglue_section_measurable, :2307 aglue_msec_X, :2438 aglue_msec_C; /opt/afp/thys/Disintegration/Disintegration.thy:762 integrable_kernel_integrable, :806 integral_fst

The AFP already has these results for any prob_kernel kappa with 'disintegration nu mu' and sigma-finite mu:
* (in prob_kernel) integrable_kernel_integrable: 'AE x in mu. integrable (kappa x) (%y. f (x,y))';
* integral_fst: 'integral nu f = integral mu (%x. integral (kappa x) (%y. f (x,y)))'.

ksemi M N Kr is such a disintegration of itself. That follows directly from emeasure_ksemi_rect (PLP:1560) and sets_ksemi, and Kr in M -> prob_algebra N gives prob_kernel by prob_kernel_def'.

The local integral_ksemi_real (89 lines, positive and negative parts) also requires an extra measurability hypothesis msec on the section integral that the AFP lemma does not need. That hypothesis is threaded through integral_aglue_law, aglue_law_X/comp_increment, aglue_law_X/comp_martingale and Dynamic_Programming_Assembly, and is discharged by aglue_section_measurable, aglue_msec_X and aglue_msec_C (about 140 lines).

Evidence: Disintegration.thy:806-810: lemma (in prob_kernel) integral_fst: assumes 'integrable nu f' 'disintegration nu mu' 'sigma_finite_measure mu' shows '(integral z. f z d nu) = (integral x. integral y. f (x,y) d(kappa x) d mu)'. The session already imports Disintegration (ROOT and Pair_Path_Space imports).

Suggested action: Add a roughly 10-line bridge lemma, ksemi_disintegration ('prob_kernel M N Kr' and 'measure_kernel.disintegration M N Kr (ksemi M N Kr) M'). Derive AE_integrable_ksemi_section and integral_ksemi_real from the AFP lemmas.

Then drop msec from integral_ksemi_real and integral_aglue_law, and delete aglue_section_measurable and the two aglue_msec lemmas once their consumers no longer pass msec. Check that the sigma-finiteness of M is available at each use; M is always a prob_space there.


### RA-path2-12. The dyadic approximation of a random time is built four times

*clone, impact medium, confidence medium, ~250 lines.*  
Locations: Relative_Arbitrage/Path_Stopping_Times.thy:15 dyceil; Continuous_Time_Martingales/Optional_Sampling.thy:486-750 dgrid/didx/dtime/dcidx/dceil (locale stopped_cont_martingale); Continuous_Time_Martingales/Stopped_Adaptedness.thy:36-43 inline dg/idx in stopped_adapted_of_cont; Relative_Arbitrage/Pair_Path_Laws.thy:1208 inline gn in path_eval_at_measurable_time

There are four constructions of the 'ceiling on the 2^-n grid, capped at the horizon' with convergence and range lemmas:
* dyceil n U x = min U (ceiling(2^n x)/2^n);
* dceil (via LEAST on grid u k/2^n);
* the inline idx = min (nat ceiling(2^n rho)) (N n);
* the inline gn = max 0 (min T (ceiling(2^n g)/2^n)).

Each comes with its own versions of: the value is >= x, the value is <= U, convergence to x, finitely many values, and the stopping property. Examples are dyceil_ge/dyceil_tendsto/dyceil_range versus dceil_ge/dceil_le/dceil_tendsto.

Evidence: PST:1480 text quoted above. Optional_Sampling.thy:677 dceil_ge and :730 dceil_tendsto against PST:21 dyceil_ge and :79 dyceil_tendsto.

Suggested action: Make dyceil (free-standing, in CTM/Time_Discretisation) the single grid. Restate dtime as dyceil n u o tau inside stopped_cont_martingale, and use it in stopped_adapted_of_cont and path_eval_at_measurable_time. This is a cross-cluster change: coordinate with the CTM and RA-path1 audits.


### RA-path2-13. 39 statements are fixed at the product codomain 'a x 'b although they never read a component

*generalisation, impact medium, confidence medium, ~400 lines.*  
Locations: Relative_Arbitrage/Path_Stopping_Times.thy:233 pstopped_mspace, :247 pstopped_const_measurable_filtration, :290 pafter_mspace, :314 pstopped_measurable, :362 pafter_measurable; Relative_Arbitrage/Path_Law_Pasting.thy:24 pair_law_of (+ sets_/space_), :39, :68, :169, :789-875 pglue_law family, :1107, :1163-1600 kglue_law' family and exit_class_rcd*, :2389-2560, :2725, :3042-3300; Relative_Arbitrage/Path_Law_Sampling.thy:1373 pfut_vimage_natural_filtration, :1405 rect_vimage_natural_filtration

Per §11, the phase-7 widening sent everything to the product codomain {polish_space,banach} x {polish_space,banach}. That was forced only where path_stopping_time, padd/pshift or fst/snd appear.

The listed statements (5 in PST, 32 in PLP, 2 in PLS, counted by a script over the statement text) mention none of those. Only path_metric/path_borel (needing polish_space) and, for pglue/pfut/pafter, + and - (banach) are used. Example: pstopped_mspace holds at 'b::polish_space; pafter_measurable at 'b::{polish_space,banach}.

The obstacle is bottom-up: their proofs call Pair_Path_Laws lemmas that are themselves stated at the product type (pair_law_eval_measurable, path_eval_at_measurable_time :1198, measurable_into_path_metric :1294, mdist_measurable_of_eval :1335).

Evidence: Script count: Path_Stopping_Times 13 product-typed statements, 5 of them without fst/snd/path_stopping_time/padd/pshift. Path_Law_Pasting 62 and 32. Path_Law_Sampling 9 and 2.

Suggested action: Run the next G1 wave bottom-up: first widen the four Pair_Path_Laws helpers to a single codomain 'b, then these 39 statements. Keep the uniform-sort lesson of §11 (one sort spelling throughout). Do not touch statements that mention path_stopping_time.


### RA-path2-14. Linear 6-theory chain; all ~25 consumers import its tail, 8 of them using nothing from the cluster

*build_time, impact medium, confidence medium, ~20 lines.*  
Locations: Relative_Arbitrage/Path_Stopping_Times.thy:5 (imports Path_Splicing), Path_Law_Pasting.thy:5, Path_Law_Sampling.thy:5; Relative_Arbitrage/Exit_Class.thy, Exit_Class_Limits.thy, Exit_Class_Marginals.thy, Exit_Class_Tightness.thy, Exit_Time_Semicontinuity.thy, Path_Tightness_Market.thy, Value_Function_Uniqueness.thy, Value_Function_Assembly.thy (each imports Path_Law_Sampling)

Pair_Path_Space -> Pair_Path_Laws -> Path_Splicing -> Path_Stopping_Times -> Path_Law_Pasting -> Path_Law_Sampling is strictly linear. Every downstream theory imports Path_Law_Sampling.

A grep for every name declared in the three theories finds no use at all in the 8 consumers listed above. Exit_Class, the root of the class layer, therefore waits for about 8,900 lines of stopping-time and sampling material it does not need.

Inside the chain, the abstract optional-sampling block and the ksemi block do not depend on paths at all, so moving them down (see the misplacement findings) also shortens the critical path.

Evidence: Per-file grep of the cluster's declared names: Exit_Class 0, Exit_Class_Limits 0, Exit_Class_Marginals 0, Exit_Class_Tightness 0, Exit_Time_Semicontinuity 0, Path_Tightness_Market 0, Value_Function_Uniqueness 0, Value_Function_Assembly 0 (Exit_Class_Shift 5, DP_Stopping_Clauses 6).

Suggested action: Re-point these 8 imports to the lowest theory that supplies what they name (likely Pair_Path_Laws or Path_Splicing). Confirm each with one build, since [simp] or [measurable] declarations such as sets_pair_law_of may be used silently. Make Path_Law_Pasting and Path_Stopping_Times siblings where possible.


### RA-path2-15. Redundant or unused hypotheses

*generalisation, impact low, confidence high, ~60 lines.*  
Locations: Relative_Arbitrage/Path_Stopping_Times.thy:1402 set_martingale_sampling_simple (mono); Relative_Arbitrage/Path_Stopping_Times.thy:1534 set_martingale_sampling (mono, sub); Relative_Arbitrage/Path_Stopping_Times.thy:1648 set_martingale_sampling_two (mono, sub); Relative_Arbitrage/Path_Stopping_Times.thy:1683 integrable_at_bounded_stopping_time (mono, sub); Relative_Arbitrage/Path_Stopping_Times.thy:435 pstopped_eval_min (st unused); Relative_Arbitrage/Path_Stopping_Times.thy:567 padd_stopping_time (idem unused); Relative_Arbitrage/Path_Stopping_Times.thy:465 pstopped_fixed_set_measurable, Path_Law_Pasting.thy:2082 pstopped_law_prob, :2273 pstopped_law_start (path_stopping_time used only for 0 <= theta <= T); Relative_Arbitrage/Path_Law_Pasting.thy:2312 pstopped_law_cont

* The hypotheses 'mono: sets (F s) <= sets (F t)' and 'sub: subalgebra M (F t)' follow from 'mg: martingale M F 0 Y', through the AFP filtered_measure axioms sets_F_mono and subalgebras. set_martingale_sampling_simple already uses Mg.subalgebras at :1423. The caller stopped_increment_of_horizon_gen re-derives both from the martingale (:1763-1766).
* pstopped_eval_min never uses st. Its proof uses only idem, T0, u and pstopped_apply. Its fixed type class {topological_space, ab_group_add} x ab_group_add is also unneeded.
* padd_stopping_time never uses idem: the proof is path_stopping_time_cong plus padd_apply plus w0.
* pstopped_fixed_set_measurable, pstopped_law_prob and pstopped_law_start use path_stopping_time only through path_stopping_time_nonneg/_le. With th0/thT hypotheses they would leave the product-codomain constraint.
* pstopped_law_cont holds for any pair_law_of T phi P.

Evidence: AFP Martingales Filtered_Measure.thy:14-15 assumes subalgebras and sets_F_mono. PST:474-477 is the only use of st in pstopped_fixed_set_measurable. PST:439-444 is the whole proof of pstopped_eval_min.

Suggested action: Drop mono and sub from the four sampling theorems and obtain them from mg (call sites shrink as well). Remove st from pstopped_eval_min; its 5 call sites in Path_Law_Sampling pass [OF st idem ...]. Restate the three pstopped lemmas with explicit bounds. padd_stopping_time is dead anyway. All of this is mechanical; confirm with a build.


### RA-path2-16. AE_pshift_law (70 lines) and the reverse half of AE_pshift_law_iff follow from AE_distrD

*simplification, impact low, confidence high, ~80 lines.*  
Locations: Relative_Arbitrage/Path_Law_Pasting.thy:662 AE_pshift_law; Relative_Arbitrage/Path_Law_Pasting.thy:996 AE_pshift_law_iff; /opt/Isabelle2026-RC3/src/HOL/Analysis/Measure_Space.thy:1488 AE_distrD

* The second direction of AE_pshift_law_iff (from AE w in pshift_law T x Q. P w to AE w in Q. P (pshift T x w)) is AE_distrD[OF pshift measurable] in one line. The proof instead goes through pshift_law_compose, pshift_law_zero and a second use of AE_pshift_law.
* AE_pshift_law itself, which hand-builds a null set B, follows by applying AE_distrD to pshift T (-x) on the law Q' = pshift_law T x Q. pshift_law T (-x) Q' = Q by pshift_law_compose and pshift_law_zero, which already exist at :927 and :978. A pshift-composition identity then closes it.

Evidence: Measure_Space.thy:1488-1491: 'lemma AE_distrD: assumes f: f in measurable M M' and AE: AE x in distr M M' f. P x shows AE x in M. P (f x)'.

Suggested action: Rewrite AE_pshift_law in about 10 lines from AE_distrD, pshift_law_compose and pshift_law_zero. Make AE_pshift_law_iff a 3-line iff. Optionally state a generic 'AE transfer through a measurable bijection with measurable inverse' lemma for Continuous_Path_Spaces.


### RA-path2-17. Coordinate and compensated-entry measurability is re-proved inline about 13 times despite X_eval_entry_measurable and comp_eval_entry_measurable

*clone, impact low, confidence high, ~150 lines.*  
Locations: Relative_Arbitrage/Path_Law_Sampling.thy:275-283, :488-501, :626-634, :933-958, :1285-1305, :1515-1539, :2163-2172, :2324-2335, :2458-2476, :2510-2520, :2556-2574, :2893-2911, :3048-3057; Relative_Arbitrage/Pair_Path_Laws.thy:836 X_eval_entry_measurable, :2414 comp_eval_entry_measurable

The blocks 'fst (w u) . axis c 1 is measurable, hence fst (w u) $ c is' and 'outerp (fst z) - snd z is borel; compose with vec_nth twice' are re-derived inline (hb, fcB, femB, semB, ZmB, Zm, Yfix, Zfix, compm, entm).

The identical facts exist as named lemmas in the lower theory Pair_Path_Laws, which Path_Law_Sampling imports.

Evidence: Pair_Path_Laws.thy:836-844 'lemma X_eval_entry_measurable: (%p'. fst (p' u) $ c) in borel_measurable (path_borel T)'. Pair_Path_Laws.thy:2414 'lemma comp_eval_entry_measurable: (%p'. (outerp (fst (p' u)) - snd (p' u)) $ cc $ dd) in borel_measurable (path_borel T)'.

Suggested action: Replace every inline block with the named lemma, plus measurable_cong_sets where the measure is not literally path_borel T.


### RA-path2-18. Smaller repeated arguments inside the cluster

*clone, impact low, confidence high, ~150 lines.*  
Locations: Relative_Arbitrage/Path_Law_Pasting.thy:209-229 (pfut adaptedness inside martingale_future_of_past) vs :2740-2760 pfut_filtration_measurable; Relative_Arbitrage/Path_Stopping_Times.thy:890 path_stopping_time_cut (forward direction :896-907) vs :802 path_stopping_time_cut_eq; Relative_Arbitrage/Path_Law_Sampling.thy:2276-2301 (inline gi in aglue_section_measurable) vs :2345 aglue_section_int_at; the |cc*h| <= |h| step at :2290-2300, :2370-2380, :2420-2429; Relative_Arbitrage/Path_Law_Pasting.thy:254-260, :751-758, :1760-1765, :2293-2299 (measurability of {fst (w 0) = x and snd (w 0) = 0}); Relative_Arbitrage/Path_Stopping_Times.thy:156-165, :985-991, :1031-1038 ('space in sets (F t)' branch); Relative_Arbitrage/Path_Law_Sampling.thy:2616-2642 vs :3116-3141 (countable pi-system choice via bchoice); Relative_Arbitrage/Path_Stopping_Times.thy:1698-1721 vs :1552-1591; :1820-1853 vs :1754-1801 (setup blocks of dead lemmas)

* martingale_future_of_past re-proves the 20-line adaptedness of pfut that pfut_filtration_measurable states.
* The forward half of path_stopping_time_cut is path_stopping_time_cut_eq.
* aglue_section_measurable re-proves aglue_section_int_at inline.
* The start-clause event is shown measurable four times.
* The exPi/bchoice/Espec block should be a lemma returning the family Eg of countable pi-systems.

Evidence: The cited line ranges are textually identical modulo variable names.

Suggested action: Reuse pfut_filtration_measurable, path_stopping_time_cut_eq and aglue_section_int_at. Add a lemma 'countable_pi_systems_natural_filtration_path' that delivers Eg with its five properties. State the start clause as w 0 = (x, 0), so measurability is one pair_law_eval_measurable use.


### RA-path2-19. measurable_into_path_metric and mdist_measurable_of_eval are always used together; the case split on t in {0..T} repeats

*simplification, impact low, confidence high, ~80 lines.*  
Locations: Relative_Arbitrage/Path_Stopping_Times.thy:247 pstopped_const_measurable_filtration, :314 pstopped_measurable, :362 pafter_measurable; Relative_Arbitrage/Path_Law_Pasting.thy:3153-3182 (section_padd_in_filtration); Relative_Arbitrage/Pair_Path_Laws.thy:1294, :1335

8 of the 9 uses of measurable_into_path_metric in the repository discharge its distance hypothesis with mdist_measurable_of_eval[OF T0 into am ev]. Each site also proves 'ev' by the same case split: inside {0..T} by an apply lemma, outside by '= undefined'.

Evidence: grep: 8 uses of measurable_into_path_metric[ and 9 of mdist_measurable_of_eval[. The pattern appears at PST:265-287, :328-359, :384-415 and PLP:3153-3181.

Suggested action: Add 'measurable_into_path_borel_of_eval' to Pair_Path_Laws: from 'into' and evaluation measurability for t in {0..T} of a restrict-valued f, conclude f in M -> path_borel T. Shorten the 4 cluster sites (and 4 more elsewhere).


### RA-path2-20. Mechanical line-join artefacts

*documentation, impact low, confidence high, ~7 lines.*  
Locations: Relative_Arbitrage/Path_Stopping_Times.thy:50, :161, :1425, :1455, :1505, :1612, :1666

Two commands are fused on one line, for example 'qed  have hi: ...' at :50 and 'by blast  moreover have' at :161. The shows clause at :1666 contains a run of spaces mid-formula. 7 of the 10 such sites in the repository are in this cluster.

Evidence: grep -nE '(qed|blast|\]\))  +(have|moreover|qed)'

Suggested action: Re-break the lines. This is purely cosmetic.


### RA-path2-21. path_stopping_time_max and path_stopping_time_shift repeat one argument

*simplification, impact low, confidence high, ~50 lines.*  
Locations: Relative_Arbitrage/Path_Stopping_Times.thy:676 path_stopping_time_max; Relative_Arbitrage/Path_Stopping_Times.thy:703 path_stopping_time_shift; Relative_Arbitrage/Path_Stopping_Times.thy:745 path_stopping_time_min

Both prove that f o theta is a path stopping time when x <= f x and f maps [0,T] into [0,T], by the same c1/c2 split. Both are dead (see the dead-code finding), so the duplication only matters if either is revived.

Evidence: PST:681-697 and :708-731 have the same structure.

Suggested action: If kept, prove one lemma path_stopping_time_comp_ge (x <= f x) and derive max and shift. Otherwise delete both with the dead chain.


### RA-path2-22. pre_sigma_of and its calculus re-create HOL-Probability's filtration.pre_sigma (Stopping_Time.thy), which is already imported but never used

*library_duplicate, impact low, confidence medium, ~120 lines.*  
Locations: Relative_Arbitrage/Path_Stopping_Times.thy:1105 pre_sigma_of, :1111 pre_sigma_ofI, :1219 pre_sigma_of_cut, :1246 sigma_algebra_pre_sigma_of, :1291 pre_sigma_of_mono; Relative_Arbitrage/Path_Stopping_Times.thy:676 path_stopping_time_max, :745 path_stopping_time_min; /opt/Isabelle2026-RC3/src/HOL/Probability/Stopping_Time.thy:61 pre_sigma, :72 sigma_algebra_pre_sigma, :95 sets_pre_sigma, :98 sets_pre_sigmaI, :106 sets_pre_sigmaD, :124 mono_pre_sigma, :43 stopping_time_min, :47 stopping_time_max

HOL-Probability.Probability imports Stopping_Time, so stopping_time F T and filtration.pre_sigma are in scope throughout the development. Grep finds no use of them in the repository.

pre_sigma_of M F sigma = {A in sets M. for all t >= 0, A inter {sigma <= t} in sets (F t)} is the same set system restricted to t >= 0. Its five lemmas (I, cut, sigma_algebra, mono) restate sets_pre_sigmaI, sets_pre_sigmaD, sigma_algebra_pre_sigma and mono_pre_sigma.

Caveat: the HOL locale 'filtration Omega F' quantifies over all t in the index type and needs space (F t) = Omega for every t. The natural filtrations here are used for t >= 0, so a short interpretation lemma for natural_filtration at negative indices would be needed. That is why this is medium confidence.

Evidence: Stopping_Time.thy:61-63: 'definition pre_sigma :: ... where pre_sigma T = sigma Omega {A. forall t. {w in A. T w <= t} in sets (F t)}'. HOL-Probability/Probability.thy:19 imports Stopping_Time.

Suggested action: When moving the block to CTM, either define pre_sigma_of through filtration.pre_sigma, after proving 'filtration (space M) (natural_filtration M 0 X)' once, or state why the t >= 0 indexing forbids it. At minimum, cite the HOL lemmas in the text.


### RA-path2-23. Five law constructors are distr with different wrappers; pshift_law and aglue_law bypass pair_law_of, which itself duplicates Path_Space.path_law

*simplification, impact low, confidence medium, ~60 lines.*  
Locations: Relative_Arbitrage/Path_Law_Pasting.thy:24 pair_law_of, :273 pshift_law (+ :279 sets_pshift_law, :284 space_pshift_law, :289 prob_space_pshift_law), :408 aglue_law (+ :415 sets_aglue_law, :602 prob_space_aglue_law), :784 pglue_law, :1163 kglue_law', :2383 kglue_law; Continuous_Path_Spaces/Path_Space.thy:464 path_law

pglue_law, kglue_law' and kglue_law are defined through pair_law_of T phi M = distr M (path_borel T) phi. pshift_law T x Q is literally distr Q (path_borel T) (pshift T x), and aglue_law is distr (ksemi ...) (path_borel T) (padd ...); both restate their own sets_/space_/prob_space_ lemmas.

pair_law_of is not pair-specific: it is generic in the codomain, so the name is misleading. Path_Space.path_law M X T = distr M (path_borel T) (%w. restrict (%t. X t w) {0..T}) is the same object for a process given by its time slices.

Evidence: PLP:275-277 'pshift_law T x Q = distr Q (path_borel T) (pshift T x)' against PLP:26-27 'pair_law_of T phi M = distr M (path_borel T) phi'.

Suggested action: * Define pshift_law and aglue_law via pair_law_of, or make them abbreviations, and delete the sets_/space_ duplicates.
* Rename pair_law_of to path_law_of (or similar), relate it to Path_Space.path_law by one lemma, and move it with its three basic lemmas to Continuous_Path_Spaces.
* Beware the §10 lesson that abbreviations can make simp diverge: try the definitional route first.


### RA-path2-24. The same AE-transfer skeleton is written four times for different glues

*clone, impact low, confidence medium, ~200 lines.*  
Locations: Relative_Arbitrage/Path_Law_Pasting.thy:627 AE_aglue_law; Relative_Arbitrage/Path_Law_Pasting.thy:817 AE_pglue_law (+ :797 prob_space_pglue_law); Relative_Arbitrage/Path_Law_Pasting.thy:1466 AE_kglue_law' (+ :1443 prob_space_kglue_law'); Relative_Arbitrage/Path_Law_Pasting.thy:2774 AE_kglue_law (+ :2707 prob_space_kglue_law)

Each proof does the same steps: AE_distr_iff on the glue map, measurability of the pulled-back event, AE_pair_measure or AE_ksemi, and a nested eventually_mono over two AE_space conjunctions.

The text at PLP:1459-1464 says so: 'That is the only difference from AE_kglue_law; the proof is the same, with AE_ksemi in place of the product space's AE_pair_measure'.

pglue_law r T Q R is kglue_law' r T (%_. R) Q as soon as ksemi Q N (%_. R) = Q (x)M R, which is a rectangle computation from emeasure_ksemi_rect. With that lemma, AE_pglue_law and prob_space_pglue_law become instances.

Evidence: PLP:841-874 and :1489-1531 differ only in the measure (Q (x)M R versus ksemi Q ?MR Kr) and in the inner AE.

Suggested action: Prove one generic lemma, 'AE x in distr S B g. Phi x iff AE p in Q. AE w in K p. Phi (g (p,w))' for S = ksemi Q N K, plus ksemi_const_kernel. Derive AE_aglue_law, AE_kglue_law' and AE_pglue_law, and keep AE_kglue_law (Pi-measure index) separate or derive it through kglue_law_eq_kglue_law'.


### RA-path2-25. pshift_law_weak_conv_joint (175 lines) is an instance of a generic extended continuous-mapping lemma

*generalisation, impact low, confidence medium, ~150 lines.*  
Locations: Relative_Arbitrage/Path_Law_Pasting.thy:420 pshift_law_weak_conv_joint; Continuous_Path_Spaces/Path_Space.thy:624 weak_conv_on_pushforward

The proof shows weak convergence of distr R_m (pshift T y_m) to distr R (pshift T y) in two steps:
* lim2 is weak_conv_on_pushforward at the fixed map pshift T y, re-proved inline;
* lim1 is a uniform estimate: sup over w of d(pshift T y_m w, pshift T y w) <= |y_m - y| goes to 0, so |integral f o phi_m - integral f o phi| <= e/2 for uniformly continuous bounded f.

Neither step uses anything about pshift beyond Lipschitz continuity and uniform closeness.

Evidence: PLP:491-504 duplicates weak_conv_on_pushforward. PLP:505-581 uses only mdist_pshift_pshift, pshift_in_mspace and uniform continuity of f.

Suggested action: State in Continuous_Path_Spaces: if phi continuous, R_m converges weakly to R, and sup over the space of d(phi_m w, phi w) goes to 0, then distr R_m phi_m converges weakly to distr R phi (via mweak_conv_eq1). Derive pshift_law_weak_conv_joint in about 10 lines.


## RA-operator

The cluster is the operator layer of the paper session, 7,150 lines in 11 theories. In order:
- Curvature_Operator defines F of Eq. (1.9): eigen_lb and eigen_ub (the Courant-Fischer forms of lambda_(n-k) >= 1 and lambda_(1) <= L), feasible, and ell_op = Inf of -tr(Ma)/2 over the feasible set. It also defines ball_v (Eq. 3.9) and proves elementary bounds plus ell_op_eval (F(p, -(2/(n-k))I) = 1).
- Viscosity_Definitions holds the ereal envelopes ell_op_pair, ell_op_lsc and ell_op_usc, ten viscosity predicates, and five bridge equations to the generic Second_Order_Viscosity_Analysis.Viscosity_Solutions.
- Viscosity_Ball, Viscosity_Comparison_Interface and Ball_Solution are an older strand about Example 3.1 on a ball: ball_v is a viscosity solution and is unique, and there is a comparison_principle locale. That locale's assumption is refuted in Value_Function_Uniqueness.
- Constraint_Set_Convexity and Eigenvalue_Bound_Exact prove Lemma 2.1 as two inclusions (lemma_2_1_easy, lemma_2_1_exact). The second uses a hypersimplex swap induction, not the paper's hyperplane separation.
- Operator_Continuity, Operator_Formula, Operator_Envelopes and Operator_Envelope_Continuity cover Lemma 3.1 (the task's "Lemma 3.2"; the formal numbering is right because lemmas share the theorem counter). They define M_p (Eq. 3.4) and prove Eq. (3.5) (ell_op_eq_half_bracket), the index shift and Poincare separation, Eq. (3.6) (eq36), F_* = F at p = 0 (ell_op_lsc_at_zero), F_* = F^* = F off the origin, the M-Lipschitz gap (mgap), and the invariances (scaling, orthogonal conjugation) that Section 4 uses.

Faithfulness. feasible, ell_op, ell_op_lsc/usc, eq36_rhs, the bracket form of (3.5) and visc_sub/supersol_env2 (Definition 3.1, which the Statement displays) match the paper. Two gaps:
- The Statement's claim that taking envelopes over R^{n x n} instead of S^n is "not a widening" relies on F depending only on the symmetric part of M. That fact is announced in two places but proved nowhere.
- The bridges that justify the readings (eigen_lb_iff_eigval_ge, lemma_2_1_exact, the displayed form of 3.5) are dead or absent and are not surfaced in the Statement.

Main problems.
1. Heavy cloning of the basic F-calculus: the entry bound three times, the bdd_below/trace bound four times, scaling in p four times, dilation in M twice, the witness lemma six times, and F^* = F off the origin by two complete independent arguments.
2. The paper-free spectral facts (Courant-Fischer, Poincare separation, rank-one projections, Pi_proj, the hypersimplex) sit here, while Symmetric_Matrix_Spectra advertises them.
3. The generic viscosity layer is decorative: no proof uses it or its bridges, and it lacks the C^2 test-class variant that the Statement uses.
4. Imports serialise the build: Exit_Class waits on Operator_Formula and Ball_Solution for one 10-line lemma, and Operator_Continuity imports Eigenvalue_Bound_Exact for nothing.
5. About 40 orphan or stale text blocks remain from earlier moves.

PIDE was not used: no heap for these sessions exists, and a full isabelle build by the parent was occupying the 4 cores and most of the 15 GB of memory. All findings come from reading every line plus repository-wide grep. Use counts mean "named in any .thy file", so a lemma used only through a [simp] attribute could be missed.


### RA-operator-1. F^* = F off the origin is proved by two independent full arguments, both live

*clone, impact high, confidence high, ~250 lines.*  
Locations: Relative_Arbitrage/Operator_Envelopes.thy:895 ell_op_usc_le_at_nonzero (rotation transport, 163 lines); Relative_Arbitrage/Operator_Envelopes.thy:1143 ell_op_usc_eq_at_nonzero; Relative_Arbitrage/Operator_Envelope_Continuity.thy:240 ell_op_ball_bound, :402 ell_op_usc_off_zero (Lipschitz route); Relative_Arbitrage/Comparison_Strictness.thy:614, :1269; Relative_Arbitrage/Comparison_Localisation.thy:441 (users of the rotation version); Relative_Arbitrage/Comparison_Strictness.thy:743 (user of the Lipschitz version)

Operator_Envelopes proves F^* ≤ F at p ≠ 0 by rotating a near-optimal witness. That needs feasible_conj, Householder rotations, ell_op_approx, ell_op_le_witness and ell_op_bdd, about 250 lines. Operator_Envelope_Continuity independently proves F_* = F^* = F at p ≠ 0, for symmetric M, from the bracket formula plus mgap (ell_op_lipschitz_in_p, ell_op_ball_bound, ell_op_usc_off_zero). The lsc half exists only on the Lipschitz route. All three call sites of the rotation version already have a symmetric matrix in hand (`symY`, `Ys`; Ym - δI is symmetric).

Evidence: Operator_Envelopes:1147 `ell_op_usc k L p M = ereal (ell_op k L p M)` (p ≠ 0). Operator_Envelope_Continuity:406 `ell_op_usc k L p M = ereal (ell_op k L p M)` (sym M, p ≠ 0). Comparison_Strictness:606-614 has `symY` in scope. Comparison_Strictness:1259 `Ys: "transpose Ym = Ym"`.

Suggested action: Keep the Lipschitz route, since it also gives the lsc half. Delete ell_op_usc_le_at_nonzero, ell_op_usc_eq_at_nonzero, ell_op_approx (unless kept per the witness finding), ell_op_le_witness and ell_op_bdd, and rewrite the three call sites with ell_op_usc_off_zero. Better still, first prove the missing symmetric-part lemma (see the faithfulness finding); then the Lipschitz route needs no symmetry hypothesis. feasible_conj stays, because ell_op_conj_rot and Value_Function_Supersolution_Case_1 need it.


### RA-operator-2. Imports serialise the build: the class layer waits on Operator_Formula and Ball_Solution for one 10-line lemma

*build_time, impact high, confidence high, ~20 lines.*  
Locations: Relative_Arbitrage/Exit_Class.thy:3-10 imports Operator_Formula, Ball_Solution; Relative_Arbitrage/Operator_Formula.thy:2114 closed_eigen_ub; Relative_Arbitrage/Operator_Continuity.thy:4 imports Eigenvalue_Bound_Exact; Relative_Arbitrage/Viscosity_Comparison_Interface.thy:4 imports Constraint_Set_Convexity; Relative_Arbitrage/Operator_Envelopes.thy:4-8 imports Ball_Solution, Integrability_Criteria, Doubling_Of_Variables, Semicontinuous_Envelopes; Relative_Arbitrage/Operator_Envelope_Continuity.thy:4 imports Semicontinuity

Exit_Class, root of the roughly 30,000-line class and DPP layer, imports Operator_Formula and Ball_Solution. Of everything in Operator_Formula, Operator_Continuity, Eigenvalue_Bound_Exact, Ball_Solution, VCI and the Viscosity_* theories it uses only closed_eigen_ub (lemma_2_1_exact is prose). The class layer therefore waits for the serial chain Curvature_Operator, Constraint_Set_Convexity, Eigenvalue_Bound_Exact, Operator_Continuity, Operator_Formula (about 3,900 lines) and the ball chain. Operator_Continuity and Operator_Formula use nothing from Constraint_Set_Convexity or Eigenvalue_Bound_Exact. Viscosity_Comparison_Interface uses nothing from Constraint_Set_Convexity. Operator_Envelopes uses only feasible_offdiag_abs_le from Ball_Solution (a duplicate) and Integrability_Criteria only in prose. Doubling_Of_Variables and Semicontinuous_Envelopes arrive transitively via Viscosity_Definitions and Test_Functions/Soft_Penalty. Operator_Envelope_Continuity imports Semicontinuity only for a prose mention.

Evidence: A script over every lemma, theorem and definition name in Operator_Formula, Operator_Continuity, Eigenvalue_Bound_Exact, Ball_Solution, VCI, Viscosity_Ball and Viscosity_Definitions found only `Exit_Class uses Operator_Formula.closed_eigen_ub` and `Eigenvalue_Bound_Exact.lemma_2_1_exact` (the latter in text). A grep for Pi_proj, suff_volatile, Pi_constraint, lemma_2_1 and related names in Operator_Continuity, Operator_Formula, VCI, Operator_Envelopes, Operator_Envelope_Continuity and Ball_Solution returns nothing.

Suggested action: Move closed_eigen_ub (and convex_eigen_ub, now at Exit_Class:31) next to eigen_ub in Curvature_Operator. Let Exit_Class import Constraint_Set_Convexity only. Let Operator_Continuity/Operator_Formula import Curvature_Operator plus the library. Drop the dead imports listed above. Then Lemma 2.1, the formula chain, the envelope chain and the class layer check in parallel. Each removal needs a build: a descendant may rely on a transitive name, and see also the simp-del finding.


### RA-operator-3. The operator layer is split along historical lines; a five-theory layout is proposed

*structure, impact high, confidence medium, ~1500 lines.*  
Locations: Relative_Arbitrage/ROOT:28-47; Relative_Arbitrage/Viscosity_Comparison_Interface.thy (194 lines); Relative_Arbitrage/Operator_Continuity.thy (266 lines); Relative_Arbitrage/Viscosity_Ball.thy (232 lines); Relative_Arbitrage/Ball_Solution.thy (515 lines)

The basic calculus of F is spread over seven theories: bounds in Curvature_Operator; scaling and dilation in VCI; entry bounds in Ball_Solution; M-gap, scaling and conj_rot in Operator_Envelopes; ellipticity in Operator_Envelope_Continuity; witnesses in Value_Function_Subsolution; more copies in Comparison_Strictness. That is why it is cloned. Operator_Continuity is a 266-line fragment of Operator_Formula with a misleading name. VCI is mostly dead. The ball strand (Viscosity_Ball, VCI, Ball_Solution) is off the theorem_1_1 path, but Operator_Envelopes, Exit_Class and Value_Function_Uniqueness import it.

Evidence: Import graph: Operator_Envelopes imports Ball_Solution, which imports VCI, which imports Viscosity_Ball and Constraint_Set_Convexity. Exit_Class imports Ball_Solution and Operator_Formula. The lemma-use script shows that Ball_Solution's only external non-dead export is feasible_offdiag_abs_le.

Suggested action: Proposed layout, executed by moving text only:
1. Operator (from Curvature_Operator): definitions plus all basic F-calculus. That is bounds, witness and approx, scaling, dilation, ellipticity, M-gap through entrysum, conj_rot and feasible_conj, eval, and the optional trace_inf generalisation.
2. Lemma_2_1 (Constraint_Set_Convexity and Eigenvalue_Bound_Exact merged): the stated equality, with Pi_proj and the hypersimplex moved down.
3. Operator_Formula (absorbing Operator_Continuity): M_p, (3.5), the shift, Lipschitz bounds, with the generic Courant-Fischer and Poincare parts moved to Symmetric_Matrix_Spectra.
4. Operator_Envelopes (absorbing Operator_Envelope_Continuity): envelopes, Lemma 3.1 with one off-zero proof, invariances.
5. Viscosity_Definitions: predicates, collapsed variants, the max-principle consequences, and the imp_env lemmas made generic.

Then Example_3_1_Viscosity (optional, reduced Viscosity_Ball). Delete VCI and Ball_Solution, or keep Ball_Solution's comparison as a separate example theory not imported by Exit_Class. Lemma_2_1, Operator_Formula and Viscosity_Definitions all then depend only on Operator and check in parallel; Exit_Class needs only Operator and Lemma_2_1.


### RA-operator-4. The psd+eigen_ub entry bound is proved three times and the Frobenius-norm bound twice

*clone, impact medium, confidence high, ~150 lines.*  
Locations: Relative_Arbitrage/Curvature_Operator.thy:300 feasible_entry_bound; Relative_Arbitrage/Ball_Solution.thy:422 feasible_diag_bound; Relative_Arbitrage/Ball_Solution.thy:449 feasible_offdiag_abs_le; Relative_Arbitrage/Ball_Solution.thy:478 feasible_bounded; Relative_Arbitrage/Exit_Class.thy:133 psd_eigen_ub_diag; Relative_Arbitrage/Exit_Class.thy:150 psd_eigen_ub_entry_abs_le; Relative_Arbitrage/Exit_Class.thy:171 sconstraint_norm_le

feasible_entry_bound and feasible_offdiag_abs_le have the same statement, "a ∈ feasible k L p ⟹ |a$i$j| ≤ L". Neither uses p or k: only psd and eigen_ub. Exit_Class proves the same fact a third time at the right generality (psd a ∧ eigen_ub a L), and its text is near-verbatim the Ball_Solution text (same local names q, nn, psda, plus, minus). feasible_bounded (Ball_Solution:478-511) and sconstraint_norm_le (Exit_Class:171-203) share the same 30-line computation of a•a ≤ (n L)^2. Operator_Envelopes uses feasible_offdiag_abs_le (line 850) and Value_Function_Subsolution:3139 uses feasible_entry_bound, so both copies are live.

Evidence: Curvature_Operator:302-303 `assumes a: "a ∈ feasible k L p" shows "¦a $ i $ j¦ ≤ L"`. Ball_Solution:451-452 `assumes af: "a ∈ feasible k L p" shows "¦a $ i $ j¦ ≤ L"`. Exit_Class:152-153 `assumes a: "psd a" and ub: "eigen_ub a L" shows "¦a $ i $ j¦ ≤ L"`. feasible_bounded's only users are prose (Operator_Formula:2110).

Suggested action: Move psd_eigen_ub_diag, psd_eigen_ub_entry_abs_le and a norm lemma psd_eigen_ub_norm_le into Curvature_Operator, right after the eigen_ub definition. Derive feasible_entry_bound in one line and sconstraint_norm_le in two. Delete feasible_diag_bound, feasible_offdiag_abs_le and feasible_bounded, and redirect Operator_Envelopes:850.


### RA-operator-5. The bdd_below/trace-pairing bound of the infimum is proved four times; mgap duplicates the library's entrysum

*clone, impact medium, confidence high, ~130 lines.*  
Locations: Relative_Arbitrage/Curvature_Operator.thy:354 ell_op_bdd_below; Relative_Arbitrage/Operator_Envelopes.thy:153 trace_mult_feasible_bound; Relative_Arbitrage/Operator_Envelopes.thy:822 ell_op_bdd; Relative_Arbitrage/Value_Function_Subsolution.thy:502 ell_op_s_bdd_below; Relative_Arbitrage/Operator_Envelopes.thy:150 mgap; Relative_Arbitrage/Operator_Envelopes.thy:236 mgap_le_norm; Symmetric_Matrix_Spectra/Eigenvalue_Continuity.thy:21 entrysum; Symmetric_Matrix_Spectra/Poincare_Separation.thy:1068 entry_abs_le_norm, :1080 entrysum_le_norm

Four proofs show that trace(M**a) ≤ (Σ|M_ij|)·L for feasible a: ell_op_bdd_below, trace_mult_feasible_bound (two-sided), ell_op_bdd and ell_op_s_bdd_below (with the bound nL, for sconstraint). ell_op_bdd has the same statement as ell_op_bdd_below plus an unused hypothesis `0 ≤ L`: its proof uses only feasible_offdiag_abs_le, which needs no L ≥ 0. ell_op_le_witness inherits that hypothesis. mgap L M N is entrysum (M - N) * L / 2. mgap_le_norm re-proves entrysum_le_norm, inlining entry_abs_le_norm (component_le_norm_cart, then norm_nth_le).

Evidence: Operator_Envelopes:151 `mgap L M N = (Σi. Σj. ¦M $ i $ j - N $ i $ j¦) * L / 2`. Eigenvalue_Continuity:22 `entrysum D = (Σi. Σj. ¦D $ i $ j¦)`. Operator_Envelopes:241-250 repeats Poincare_Separation:1068-1077 line for line. Operator_Envelopes:824 `assumes L0: "0 ≤ L"` (unused). ell_op_bdd and ell_op_le_witness are used only inside Operator_Envelopes.

Suggested action: Keep one lemma, trace_mult_feasible_bound stated through entrysum, in Curvature_Operator, and derive ell_op_bdd_below from it. Delete ell_op_bdd and drop L0 from ell_op_le_witness. Redefine mgap as an abbreviation for entrysum (M - N) * L / 2, or replace it by entrysum, and derive mgap_le_norm from entrysum_le_norm. Value_Function_Subsolution.ell_op_s_bdd_below then follows from the same lemma via psd_eigen_ub_entry_abs_le.


### RA-operator-6. Scale invariance of F in p is proved four times, the feasible-set version three times, and dilation in M twice

*clone, impact medium, confidence high, ~170 lines.*  
Locations: Relative_Arbitrage/Viscosity_Comparison_Interface.thy:45 feasible_scale_p; Relative_Arbitrage/Viscosity_Comparison_Interface.thy:66 ell_op_scale_p; Relative_Arbitrage/Viscosity_Comparison_Interface.thy:85 ell_op_dilation; Relative_Arbitrage/Operator_Formula.thy:1083 ell_op_scaleR_dir; Relative_Arbitrage/Operator_Envelopes.thy:808 feasible_scale; Relative_Arbitrage/Operator_Envelopes.thy:1201 ell_op_scale; Relative_Arbitrage/Comparison_Strictness.thy:431 feasible_scaleR_p; Relative_Arbitrage/Comparison_Strictness.thy:454 ell_op_scaleR_matrix; Relative_Arbitrage/Comparison_Strictness.thy:474 ell_op_scaleR_p

Three proofs of "feasible k L (c *R p) = feasible k L p" for c ≠ 0: feasible_scale_p, feasible_scale and feasible_scaleR_p.

Four proofs that ell_op k L (c *R p) M = ell_op k L p M:
- ell_op_scale_p (c ≠ 0);
- ell_op_scale (c > 0);
- ell_op_scaleR_p (c ≠ 0);
- ell_op_scaleR_dir (c > 0), which also assumes transpose M = M, p ≠ 0, 1 ≤ L and 1 ≤ k < n and goes through the 1000-line bracket formula. Every one of those extra hypotheses is unnecessary.

Two proofs of positive homogeneity in M: ell_op_dilation re-proves Inf scaling by hand in 35 lines (inf_scale); ell_op_scaleR_matrix uses cInf_mult_pos.

Evidence: VCI:48 `feasible k L (c *R p) = feasible k L p`. Operator_Envelopes:811 `feasible k L (c *R q) = feasible k L q`. Comparison_Strictness:434 `feasible k L (θ *R p) = feasible k L p`. Operator_Formula:1085 `assumes sym ... and c: "0 < c" and p: "p ≠ 0" and L ... and k ...`. ell_op_scaleR_dir is used at Operator_Formula:1488 and Operator_Envelope_Continuity. ell_op_scale_p and ell_op_dilation are used only by Ball_Solution.

Suggested action: State feasible_scale and ell_op_scale (c ≠ 0) and ell_op_dilation (via cInf_mult_pos) once, in Curvature_Operator. Delete the other six and rewrite their roughly ten call sites.


### RA-operator-7. Mp_eigenbasis_adapted re-proves Symmetric_Matrix_Spectra.eigenbasis_containing_eigenvector

*library_duplicate, impact medium, confidence high, ~130 lines.*  
Locations: Relative_Arbitrage/Operator_Formula.thy:148 Mp_eigenbasis_adapted (127 lines); Relative_Arbitrage/Operator_Formula.thy:130 Mp_invariant_perp; Relative_Arbitrage/Operator_Formula.thy:794 Mp_quadform_unit_p; Symmetric_Matrix_Spectra/Poincare_Separation.thy:463 eigenbasis_containing_eigenvector

Mp_eigenbasis_adapted builds, by hand, an orthonormal eigenbasis of M_p that contains q = p/|p| with the rest orthogonal to p. It splits off p-perp, takes an invariant-subspace eigenbasis there, inserts q and proves completeness. The library lemma says exactly this for any symmetric A and unit eigenvector q, and its hypotheses come from transpose_Mp and Mp_apply_p. Operator_Formula itself already calls the library lemma at line 1146. Mp_quadform_unit_p (lines 794-822) repeats the `pull`/`Mpq` computation of lines 240-256.

Evidence: Poincare_Separation:463-468 `assumes sym: "transpose A = A" and q: "norm q = 1" and eigq: "A *v q = (q • (A *v q)) *R q" shows "∃B. onormal B ∧ span B = UNIV ∧ q ∈ B ∧ (∀u∈B. A *v u = ...) ∧ (∀u ∈ B - {q}. q • u = 0)"`. Operator_Formula:151-154 has the same conclusion for A = Mp p M and q = p /R norm p.

Suggested action: Prove Mp_eigenbasis_adapted in about 10 lines from eigenbasis_containing_eigenvector, using Mp_apply_p for the eigenvector condition and scaling q•u = 0 to p•u = 0. Delete Mp_invariant_perp if nothing else uses it. Derive Mp_quadform_unit_p from Mp_apply_p in 3 lines and use it inside the adapted-basis proof.


### RA-operator-8. The orthonormal outer-product sum Σ_{u∈T} u u^T is shown psd with eigen_lb ≥ |T| three times

*clone, impact medium, confidence high, ~110 lines.*  
Locations: Relative_Arbitrage/Curvature_Operator.thy:100-138 (inside feasible_witness); Relative_Arbitrage/Constraint_Set_Convexity.thy:206 onormal_sum_suff_volatile; Relative_Arbitrage/Operator_Formula.thy:722 eigen_ub_weighted_outer_sum, :747 eigen_lb_weighted_outer_sum; Symmetric_Matrix_Spectra/Poincare_Separation.thy:427 psd_weighted_outer_sum

feasible_witness and onormal_sum_suff_volatile contain character-near-identical proofs (the same `quad`, psd and eigen_lb blocks over span T, using onormal_expand and onormal_inner_sums). eigen_lb_weighted_outer_sum and eigen_ub_weighted_outer_sum are the weighted generalisations, and psd_weighted_outer_sum is the psd part in the library.

Evidence: Curvature_Operator:103-104 `have quad: "x • (a *v x) = (Σu∈T. (u • x)²)"` and Constraint_Set_Convexity:214 `have quad: "x • (b *v x) = (Σu∈T. (u • x)²)"`. Lines 121-138 and 225-243 are the same eigen_lb proof with a renamed to b.

Suggested action: State one lemma onormal_outer_sum_props (psd, eigen_lb (card T), eigen_ub 1, trace = card T) in Curvature_Operator, next to the definitions, or the weighted version there. Prove feasible_witness and onormal_sum_suff_volatile from it.


### RA-operator-9. Viscosity_Comparison_Interface's locale has a refuted assumption, and its whole strand is dead

*dead_code, impact medium, confidence high, ~200 lines.*  
Locations: Relative_Arbitrage/Viscosity_Comparison_Interface.thy:151 locale comparison_principle; Relative_Arbitrage/Viscosity_Comparison_Interface.thy:158 viscosity_solution_unique; Relative_Arbitrage/Viscosity_Comparison_Interface.thy:181 ball_v_unique_solution; Relative_Arbitrage/Value_Function_Uniqueness.thy:75-85 (refutation text); Relative_Arbitrage/Viscosity_Ball.thy:216 ball_v_solves_pde_viscosity

Value_Function_Uniqueness states that comparison_principle "holds for no ball", so ball_v_unique_solution is vacuous. The theory header (10-31, 143-149) still presents the locale as the axiomatised Crandall-Ishii interface. viscosity_solution_unique and ball_v_unique_solution have no users. ball_v_solves_pde_viscosity, and with it Viscosity_Ball's two theorems, is used only by this dead theorem. feasible_scale_p has no users at all.

Evidence: Value_Function_Uniqueness:83-85: "Hence ball_v_unique_solution, which carries comparison_principle as a hypothesis, is vacuous; theorem_1_1_uniqueness_general below replaces it." grep: viscosity_solution_unique and ball_v_unique_solution are named only in prose. ball_v_solves_pde_viscosity is used only at Viscosity_Comparison_Interface:190.

Suggested action: Delete the locale and both theorems. Move ell_op_scale_p and ell_op_dilation to Curvature_Operator (see the scaling clone) and delete the theory. If Example 3.1 as a smooth viscosity solution is worth keeping as a sanity check, keep Viscosity_Ball in reduced form.


### RA-operator-10. The generic viscosity layer and its five bridges are unused, and it lacks the variant the Statement uses

*structure, impact medium, confidence high, ~120 lines.*  
Locations: Second_Order_Viscosity_Analysis/Viscosity_Solutions.thy:29-104; Relative_Arbitrage/Viscosity_Definitions.thy:165-190 visc_subsol_eq_gen, visc_supersol_eq_gen, visc_subsol_env_eq_gen, visc_supersol_env_eq_gen, max_principle_boundary_eq_gen

No proof anywhere uses visc_subsol_gen, visc_supersol_gen, visc_sol_gen, visc_*_gen_env, max_principle_boundary_gen, the four generic lemmas, or any of the five bridge equations. The env_eq_gen bridges are used only by max_principle_boundary_eq_gen, which is unused. Phase 9 (PLAN_RESTRUCTURING_2 §10) therefore produced a decorative layer. The claim at Viscosity_Definitions:165-168 that the bridges are "what lets a reader instantiate the machinery of that session at a different F" is false: none of that session's machinery is stated over these predicates, and the comparison proofs (Comparison_*) are over the paper predicates. The generic layer also has no test_fun_C2 variant, so visc_subsol_env2 and visc_supersol_env2, the predicates in Theorem_1_1_Statement, have no generic counterpart.

Evidence: grep -rnw: visc_subsol_gen_mono, visc_supersol_gen_mono, visc_subsol_gen_env_imp, visc_supersol_gen_env_imp, visc_subsol_eq_gen, visc_supersol_eq_gen and max_principle_boundary_eq_gen each have 0 uses. visc_*_gen are named only in Viscosity_Solutions and in the bridge statements.

Suggested action: Either make the layer real or delete it. To make it real: add a test-class parameter (or a C2 variant), restate visc_subsol_imp_env, visc_subsol_env_local, max_principle_le and uniqueness_from_max_principle generically there, and prove the paper versions through the bridges. If the comparison proofs are not going to be restated, delete the bridges and the generic definitions, or at least correct the prose and the Second_Order_Viscosity_Analysis ROOT description.


### RA-operator-11. "F depends only on the symmetric part of M" justifies the envelopes over R^{n×n} but is proved nowhere

*faithfulness, impact medium, confidence high, ~60 lines.*  
Locations: Statement/Theorem_1_1_Statement.thy:92-95; Relative_Arbitrage/Comparison_Strictness.thy:16-23 (section with no lemma); Relative_Arbitrage/Operator_Formula.thy:1685-1693 (section with no lemma); Relative_Arbitrage/Viscosity_Definitions.thy:23-33 ell_op_lsc, ell_op_usc

Definition 3.1 takes F_* and F^* over R^n × S^n, while ell_op_lsc and ell_op_usc take the infimum and supremum over balls in R^n × R^{n×n}. The Statement argues this is "Not a widening: F factors through M ↦ (M + M^T)/2 ... and that map is a contraction fixing S^n". The same claim heads sections in Comparison_Strictness and Operator_Formula, but neither contains a lemma, and a grep for any lemma about ell_op of a transposed or symmetrised matrix finds none. The claim is true and easy (tr(M^T a) = tr(M a) for symmetric a), but the faithfulness argument currently rests on prose.

Evidence: Statement:94 `Not a widening: F factors through M ↦ (M + M^T)/2, the feasible matrices being symmetric, and that map is a contraction fixing S^n.` Operator_Formula:1685 `section ‹F only sees the symmetric part of M›` is followed only by text. Comparison_Strictness:16 likewise.

Suggested action: Add ell_op_sym_part: ell_op k L p M = ell_op k L p ((1/2) *R (M + transpose M)), plus a lemma that, at symmetric M, ell_op_lsc and ell_op_usc equal the envelopes restricted to R^n × S^n. Display it in Statement/Paper_Readings. It also removes the symmetry hypotheses from the Lipschitz route (see the double-proof finding).


### RA-operator-12. Bridges to the paper's wording exist but are dead or missing: eigen_lb ⟺ λ_(n-k) ≥ 1, Lemma 2.1 as an equality, the displayed form of (3.5), (3.5) at p = 0

*faithfulness, impact medium, confidence high, ~40 lines.*  
Locations: Relative_Arbitrage/Operator_Formula.thy:2028 eigen_lb_iff_eigval_ge, :2085 feasible_iff_eigval; Relative_Arbitrage/Eigenvalue_Bound_Exact.thy:560 lemma_2_1_exact, :673-675 (announced, nothing follows); Relative_Arbitrage/Operator_Formula.thy:1036-1037 ("And in the paper's displayed form", nothing follows); Relative_Arbitrage/Operator_Formula.thy:1027 ell_op_eq_half_bracket (requires p ≠ 0); Statement/Paper_Readings.thy

The Statement asserts in prose that eigen_lb a (n - k) is the paper's λ_(n-k)(a) ≥ 1. The lemma that proves it, eigen_lb_iff_eigval_ge, and its corollary feasible_iff_eigval have no users, and the text blaming "Lemma 2.3's compactness" for them is wrong (closedness goes through Pi_constraint). Lemma 2.1 is an equality in the paper. Here it is two unconnected inclusions, the exact one unused, and the announced statement at 673-675 never comes. Text 1036 promises (3.5) in the paper's displayed form via bracket_eq_sum (Ky_Fan:1255), but no theorem follows. Paper (3.5) is also stated with M_0 = M at p = 0, where it holds by the same proof (the bracket_attained witness without the q direction), while ell_op_eq_half_bracket assumes p ≠ 0. The formalisation itself is faithful in every one of these points; the evidence is simply not surfaced.

Evidence: grep -rnw eigen_lb_iff_eigval_ge: only feasible_iff_eigval, which has 0 uses. lemma_2_1_exact is named only in Exit_Class:21 prose. Paper (Statement/EM_final_paper.tex:445-452) displays F(p,M) as two sums over ordered eigenvalues of M_p, with M_p := M for p = 0. Ky_Fan:1255 bracket_eq_sum gives the regrouping.

Suggested action: Add theorem lemma_2_1: k < CARD('n) ⟹ convex hull (suff_volatile k) = Pi_constraint k (two lines). Add the displayed form of (3.5) as a corollary via bracket_eq_sum. Optionally drop p ≠ 0 from ell_op_eq_half_bracket, which also removes the case split in ell_op_le_eq36:96-116. Reference eigen_lb_iff_eigval_ge, lemma_2_1, eq36 and the (3.5) display from Statement/Paper_Readings so that they serve as faithfulness evidence rather than dead code.


### RA-operator-13. Courant-Fischer and Poincare separation are proved in the paper session while Symmetric_Matrix_Spectra advertises them

*misplacement, impact medium, confidence high, ~180 lines.*  
Locations: Relative_Arbitrage/Operator_Formula.thy:289 eigval_ge_of_subspace (110 lines); Relative_Arbitrage/Operator_Formula.thy:1505 poincare_separation; Symmetric_Matrix_Spectra/Poincare_Separation.thy:9-17 (header); Symmetric_Matrix_Spectra/ROOT:7

Poincare_Separation's header promises "the Poincare separation inequality ... the Courant--Fischer variational lower bound for an ordered eigenvalue", and the session ROOT lists "Poincare separation". Both theorems are instead in Relative_Arbitrage.Operator_Formula. eigval_ge_of_subspace mentions no paper constant. poincare_separation uses only that y•(Mp p M *v y) = y•(M *v y) on p⊥ (Mp_quadform_perp) and that M_p is symmetric. Generically: for symmetric N and M agreeing as quadratic forms on a hyperplane, eigval (Suc i) M ≤ eigval i N. Its scaffolding (subspace_inter_nonzero, quadform_outside_threshold_le_eigval, parseval_onormal, dim_inter_ge, quadform_ge_on_span_threshold) is already in Poincare_Separation.

Evidence: Poincare_Separation:10-15 "The Poincare separation inequality and its Courant--Fischer scaffolding ... the Courant--Fischer variational lower bound for an ordered eigenvalue". grep for poincare_separation in Symmetric_Matrix_Spectra finds nothing. The proof at Operator_Formula:1553-1569 uses Mp_quadform_perp and transpose_Mp only.

Suggested action: Move eigval_ge_of_subspace and a generic hyperplane-compression form of poincare_separation into Symmetric_Matrix_Spectra.Poincare_Separation, and keep a 3-line M_p instance in Operator_Formula. Also move eigen_lb_iff_eigval_ge if eigen_lb moves (see the next finding).


### RA-operator-14. Stale theory headers claim results the theories no longer contain

*documentation, impact medium, confidence high, ~150 lines.*  
Locations: Relative_Arbitrage/Curvature_Operator.thy:10-28; Relative_Arbitrage/Constraint_Set_Convexity.thy:9-23; Relative_Arbitrage/Eigenvalue_Bound_Exact.thy:10-19; Relative_Arbitrage/Operator_Continuity.thy:11-24; Relative_Arbitrage/Operator_Formula.thy:11-22; Relative_Arbitrage/Operator_Envelopes.thy:13-32; Relative_Arbitrage/Viscosity_Comparison_Interface.thy:10-31; Relative_Arbitrage/Ball_Solution.thy:10-28

Each header promises material that has moved or never existed:
- Curvature_Operator promises the spectral theorem, the viscosity sub/supersolutions and that Example 3.1 is a viscosity solution. They are in Symmetric_Spectral and Viscosity_Ball.
- Constraint_Set_Convexity promises both inclusions of Lemma 2.1, the second "on hyperplane separation ... Abel-summation". Only the easy one is here; the hard one is in Eigenvalue_Bound_Exact and uses a hypersimplex argument.
- Eigenvalue_Bound_Exact says it builds "on A_k ⊆ closure (conv B_k) from Constraint_Set_Convexity". No such lemma exists anywhere.
- Operator_Continuity promises Eqs. (3.4)-(3.6) and Lemma 3.1. It contains only M_p and trace_Mp, and no continuity, despite its name.
- Operator_Formula says it "Formalizes ... the Poincare separation inequality together with the Rayleigh bounds". The Rayleigh bounds are in Symmetric_Matrix_Spectra.
- Operator_Envelopes says the envelope-free notions are "of Curvature_Operator" and that "Comparison_Principle restates Definition 3.1 ... as visc_subsol_env2". Both are now in Viscosity_Definitions.
- Viscosity_Comparison_Interface claims orthogonal equivariance (that is in Operator_Envelopes.ell_op_conj_rot), calls gradient scaling "part of Lemma 3.1" (it is not), and calls Crandall-Ishii unformalised and axiomatised.
- Ball_Solution calls Crandall-Ishii unformalised.

Evidence: Curvature_Operator:22-28 "together with the spectral theorem for real symmetric matrices ... It also gives viscosity sub- and supersolutions". Eigenvalue_Bound_Exact:12-13 "Building on A_k ⊆ closure (conv B_k) from Constraint_Set_Convexity". VCI:29-31 "a deep result of viscosity theory with no Isabelle formalization, and is taken here as an interface assumption". Second_Order_Viscosity_Analysis/Crandall_Ishii_Sums and Comparison_Principle.max_principle_boundary_holds exist.

Suggested action: Rewrite the eight headers to describe current content, and rename Operator_Continuity, e.g. to Operator_Mp, or merge it into Operator_Formula.


### RA-operator-15. Twin sub/super proofs in Viscosity_Ball and Ball_Solution; the general smooth-comparison lemma described in the text was deleted

*clone, impact medium, confidence medium, ~330 lines.*  
Locations: Relative_Arbitrage/Viscosity_Ball.thy:17 ball_v_viscosity_subsol (95 lines); Relative_Arbitrage/Viscosity_Ball.thy:113 ball_v_viscosity_supersol (96 lines); Relative_Arbitrage/Ball_Solution.thy:152 visc_subsol_le_ball_v (78 lines); Relative_Arbitrage/Ball_Solution.thy:234 ball_v_le_visc_supersol (80 lines); Relative_Arbitrage/Ball_Solution.thy:399-415 (text describing the vanished general lemma); Relative_Arbitrage/Ball_Solution.thy:50 ball_v_scaled_test_fun

The two Viscosity_Ball proofs are mirror images: the same 30 lines of epsilon bookkeeping, the same ψ, gψ and derivative blocks, and local_min_gradient_zero / local_min_hessian_psd. They even prove symH' two different ways (lines 102 and 198). A paper-free jet-comparison lemma would replace both: if ψ and φ are test_fun_at x with jets (gψ, Hψ) and (gφ, Hφ) and φ - ψ has a local min at x, then gφ x = gψ x and Hφ - Hψ is psd. Ball_Solution.ball_v_scaled_test_fun with c = 1 already supplies the jet of ball_v. The Ball_Solution twins differ only in max/min and c > 1 versus c < 1. Their text (399-415) describes "the general form of visc_subsol_le_ball_v" for any compact K and any smooth strict supersolution, but no such lemma exists any more.

Evidence: Viscosity_Ball:42-48 and :138-144 are identical (`define e where "e = min e1 (min e2 e3)"` ...). Ball_Solution:409 `This is the general form of visc_subsol_le_ball_v with ψ = c · ball_v` is followed by nothing.

Suggested action: If the ball strand is kept: add the jet-comparison lemma to Second_Order_Viscosity_Analysis.Test_Functions, reduce Viscosity_Ball to two 15-line corollaries, and restore one generic "comparison with a smooth strict super/subsolution" lemma from which both Ball_Solution theorems follow. Otherwise see the dead-strand finding.


### RA-operator-16. A global `declare transpose_matrix_vector [simp del]` in a dead theory leaks into everything downstream

*structure, impact medium, confidence medium, ~5 lines.*  
Locations: Relative_Arbitrage/Viscosity_Comparison_Interface.thy:34-38

The declaration's justification is "would obstruct the conjugation rewrites below", but the conjugation lemmas moved to Operator_Envelopes long ago. The simp deletion is inherited by Ball_Solution, Operator_Envelopes, Operator_Envelope_Continuity and every Comparison_* and Value_Function_* theory. It is not inherited by Operator_Formula, so the two operator branches run with different simpsets, and their merge in Operator_Envelope_Continuity depends on Isabelle's simpset-merge semantics. Deleting the theory (see the dead-locale finding) can silently change downstream simp behaviour.

Evidence: VCI:34-38 `text ‹Keep matrix-vector products in *v-form: the default normalization to the vector-matrix form x v* A would obstruct the conjugation rewrites below.› declare transpose_matrix_vector [simp del]`. The only conjugation lemma left in VCI is none: ell_op_conj_rot and feasible_conj are in Operator_Envelopes.

Suggested action: Move the declaration to the theory that needs it, preferably as a local `supply transpose_matrix_vector[simp del]` or a `context begin ... end` around feasible_conj and ell_op_conj_rot, before deleting VCI. Re-run the build.


### RA-operator-17. The ten predicate variants: only six are on the Theorem 1.1 path, and they can collapse to two generic definitions

*simplification, impact medium, confidence medium, ~100 lines.*  
Locations: Relative_Arbitrage/Viscosity_Definitions.thy:35-161

On the path to theorem_1_1:
- visc_subsol: exit_val is first proved a local subsolution, then lifted by visc_subsol_imp_env;
- visc_subsol_env and visc_supersol_env: the comparison layer;
- visc_subsol_env2 and visc_supersol_env2: displayed;
- visc_supersol_lsc (Case 2);
- supersol_jet (35 uses in Comparison_*);
- max_principle_boundary.

Off the path:
- visc_supersol and visc_sol: only the ball strand and the dead locale;
- visc_sol_env: zero uses;
- max_principle_boundary_raw: only for its own refutation (Comparison_Principle:1241).

visc_supersol_lsc k L K Ω u is literally visc_supersol_env k L K Ω (lsc_env u) (compare lines 114-117 with 74-77). supersol_jet is visc_supersol_gen (ell_op_usc k L). The variants differ along four axes: touching (ball versus K), test class (test_fun_at versus test_fun_C2), operator (F, F_*, F^*) and function (u versus lsc_env u).

Evidence: grep counts: visc_sol_env appears only in its definition and a prose pointer (Operator_Envelopes:545). visc_supersol_lsc_def and visc_supersol_env_def differ only in `lsc_env u x`/`lsc_env u y` for `u x`/`u y`. supersol_jet_def is visc_supersol_def with ell_op_usc.

Suggested action: Define visc_supersol_lsc as an abbreviation for visc_supersol_env ... (lsc_env u). Delete visc_sol_env, and delete visc_sol/visc_supersol together with the ball strand. Long term, one generic pair visc_subsol_gen T F N Ω u, with T the test class, N x a filter (`at x` or `principal K`) for the touching and F the operator, covers every variant at 52 unfolding sites (PLAN §2.4 count).


### RA-operator-18. Paper-free statements left in the operator theories

*misplacement, impact medium, confidence medium, ~500 lines.*  
Locations: Relative_Arbitrage/Operator_Continuity.thy:41-121 rank1proj and its lemmas; Relative_Arbitrage/Operator_Formula.thy:45-63, 1045-1067, 1702-1792 (rank1proj_annihilates_perp, perp_proj_fixes_perp, rank1proj_scaleR, rank1proj_eq_outer_unit, norm_rank1proj_diff_le, norm_rank1proj, norm_perp_proj_le); Relative_Arbitrage/Constraint_Set_Convexity.thy:33-57 Pi_proj, Pi_proj_bdd_below, Pi_proj_le, Pi_proj_ge; Relative_Arbitrage/Eigenvalue_Bound_Exact.thy:68-157 shift, sum_shift, shift_convex_combination; :166-406 the hypersimplex induction; Relative_Arbitrage/Curvature_Operator.thy:42-46 eigen_lb, eigen_ub; Relative_Arbitrage/Operator_Formula.thy:2114 closed_eigen_ub; Relative_Arbitrage/Exit_Class.thy:31 convex_eigen_ub

rank1proj p = p p^T/|p|^2, with its symmetry, idempotence-type facts, Lipschitz bound and Frobenius norm, belongs in Symmetric_Matrix_Spectra.Outer_Products, which already has is_proj_rank1 and is_proj_compl_rank1 for unit vectors. Pi_proj is, by its own text, "the dual of kyfan" and belongs in Ky_Fan. The hypersimplex decomposition (c ∈ [0,1]^B with Σc = m is a convex combination of 0/1 points) is pure convex geometry: suff_volatile enters only through the base case and the linear map c ↦ Σ c_u u u^T. eigen_lb and eigen_ub are Courant-Fischer conditions with no paper content, and their closedness and convexity lemmas are scattered over three theories. The global constant `shift` (Eigenvalue_Bound_Exact:68) is a very generic name to export from the paper session.

Evidence: Constraint_Set_Convexity:28-31 "Pi_proj is the dual of kyfan from Ky_Fan: the sum of the m SMALLEST eigenvalues". Eigenvalue_Bound_Exact:68 `definition shift :: "('a ⇒ real) ⇒ 'a ⇒ 'a ⇒ real ⇒ ('a ⇒ real)"`.

Suggested action: Move the rank1proj block to Outer_Products and Pi_proj with its three lemmas to Ky_Fan. State the hypersimplex lemma generically (finite B, c :: 'a ⇒ real) in Symmetric_Matrix_Spectra, or in a small convexity theory, and get diag_in_convex_hull through convex_hull_linear_image. Gather eigen_ub, closed_eigen_ub, convex_eigen_ub and the psd_eigen_ub bounds with eigen_lb in one place, either Curvature_Operator or Symmetric_Matrix_Spectra; the Statement only displays them, so a move is not a rename. Make `shift` local (a `context` or qualified name).


### RA-operator-19. Generic envelope and viscosity facts are stated for the paper operator only

*misplacement, impact medium, confidence medium, ~250 lines.*  
Locations: Relative_Arbitrage/Operator_Envelopes.thy:554 visc_subsol_imp_env, :579 visc_supersol_imp_env; Relative_Arbitrage/Operator_Envelopes.thy:1080 visc_subsol_env_local; Relative_Arbitrage/Operator_Envelopes.thy:47-118 ell_op_lsc_le, ell_op_le_usc, ell_op_usc_ge_one_limit; Relative_Arbitrage/Operator_Envelopes.thy:1304 ell_op_usc_transfer; Relative_Arbitrage/Viscosity_Definitions.thy:15-33 ell_op_pair, ell_op_lsc, ell_op_usc; Semicontinuous_Analysis/Semicontinuous_Envelopes.thy:26 lsc_env (real-valued)

ell_op_lsc and ell_op_usc are the SUP/INF envelope of lsc_env at an ereal-valued function. Every lemma about them proved here is a general envelope fact: the sandwich, that usc_env is usc along sequences (ell_op_usc_ge_one_limit), and transport along a bi-Lipschitz F-preserving map (ell_op_usc_transfer). Likewise, visc_subsol_imp_env (local touching implies global, with F_* ≤ F) and visc_subsol_env_local (global touching recovered from local via a quartic penalty) mention the operator only through ell_op_lsc. Text 1471-1473 even notes that the lsc versions "follow verbatim" but were not stated.

Evidence: Viscosity_Definitions:26-27 `ell_op_lsc k L p M = (SUP e ∈ {0<..}. INF w ∈ ball (p, M) e. ell_op_pair k L w)`. Semicontinuous_Envelopes:27 `lsc_env u x = (SUP e ∈ {0<..}. INF y ∈ ball x e. u y)`. ell_op_usc_transfer's hypotheses mention only ell_op_pair k L as an opaque function.

Suggested action: Add an ereal-valued envelope (or generalise lsc_env's codomain) to Semicontinuous_Envelopes, with sandwich, usc-limit and transfer lemmas, and define ell_op_lsc/usc as instances. Move the predicate-level facts into Viscosity_Solutions over visc_*_gen, which also gives that layer its first real users.


### RA-operator-20. One generic "trace infimum over a set" would absorb about fifteen duplicated F-lemmas and also serve G11

*generalisation, impact medium, confidence medium, ~300 lines.*  
Locations: Relative_Arbitrage/Curvature_Operator.thy:56 ell_op; Relative_Arbitrage/Value_Function_Subsolution.thy:499 ell_op_s; Relative_Arbitrage/Operator_Envelopes.thy:132 ell_op_zero_le, :190 ell_op_M_gap, :316 ell_op_zero_matrix; Relative_Arbitrage/Operator_Envelope_Continuity.thy:487 ell_op_elliptic; Relative_Arbitrage/Operator_Envelopes.thy:1214 ell_op_conj_rot

ell_op k L p M is Inf((λa. -trace(M**a)/2) ` feasible k L p), and ell_op_s k L M is the same infimum over sconstraint k L. The lemmas proved by hand for F only use properties of the set S:
- bdd_below when S is bounded;
- the witness bound and the near-optimal approximation;
- antitone in S (this is ell_op_zero_le, and also ell_op_s ≤ ell_op through feasible_subset_sconstraint);
- the M-gap via entrysum and dilation in M;
- ellipticity when S ⊆ psd;
- conjugation invariance when S is invariant;
- F(0) = 0.

Evidence: Value_Function_Subsolution:499-500 `ell_op_s k L M = Inf ((λa. - trace (M ** a) / 2) ` sconstraint k L)`, with its own bdd_below (502) and witness (530) lemmas, a 5th and 7th copy. ell_op_zero_le's proof is cInf_superset_mono on feasible_zero_mono.

Suggested action: Define trace_inf S M (or a locale for a bounded constraint set) in Curvature_Operator, or lower in a paper-free theory. Prove the about ten lemmas once and make ell_op and ell_op_s abbreviations or one-line instances. This fits PLAN G11 (the class over an abstract constraint set).


### RA-operator-21. Four ε–δ envelope arguments share one skeleton

*simplification, impact medium, confidence medium, ~170 lines.*  
Locations: Relative_Arbitrage/Operator_Envelopes.thy:452 ell_op_lsc_at_zero (80 lines); Relative_Arbitrage/Operator_Envelope_Continuity.thy:126 ell_op_usc_at_zero_le (68); Relative_Arbitrage/Operator_Envelope_Continuity.thy:337 ell_op_lsc_off_zero (64); Relative_Arbitrage/Operator_Envelope_Continuity.thy:402 ell_op_usc_off_zero (61)

Each does the same steps: bound F on ball(z,e) by c ± C·e (via dist_snd_le or dist_fst_le), pick e = d/(2C), then close with ereal_le_epsilon2 and add_right_mono. The four `dN`/`dM` distance blocks (Operator_Envelopes:470-480, OEC:141-151, 264-285) and the two copies of the e and Ce computation (OEC:356-378 and 418-440) are identical. One lemma would serve all four: (∀e>0. ∀w∈ball z e. f w ≤ c + C*e) ⟹ usc envelope at z ≤ c, plus its lsc dual.

Evidence: OEC:356-378 and :418-440 are character-identical (`define e where "e = min (d / (2 * C)) (norm p / 2)"` ... `finally show ?thesis .`). OEC:124 notes "This mirrors ell_op_lsc_at_zero".

Suggested action: Prove the generic envelope-from-ball-bound lemmas once (Semicontinuous_Envelopes, or the ereal envelope theory proposed above), and reduce the four theorems to about 10 lines each.


### RA-operator-22. The "one feasible witness bounds F" step is repeated six times, and the "near-optimal witness" step twice

*clone, impact low, confidence high, ~70 lines.*  
Locations: Relative_Arbitrage/Operator_Envelopes.thy:867 ell_op_le_witness; Relative_Arbitrage/Value_Function_Subsolution.thy:52 ell_op_le_of_witness; Relative_Arbitrage/Curvature_Operator.thy:406-408 (inline); Relative_Arbitrage/Operator_Formula.thy:1006-1008 (inline); Relative_Arbitrage/Operator_Envelopes.thy:208-210 (inline); Relative_Arbitrage/Operator_Envelope_Continuity.thy:501-503 (inline); Relative_Arbitrage/Operator_Envelopes.thy:874 ell_op_approx; Relative_Arbitrage/Value_Function_Supersolution_Case_1.thy:19 ell_op_lt_witness

The step from a ∈ feasible k L p to ell_op k L p M ≤ -trace(M**a)/2 is a two-line cInf_lower argument. It exists as two named lemmas, ell_op_le_witness (with a useless L ≥ 0) and ell_op_le_of_witness, and four more times inline. Its dual (there is an a with -tr(Ma)/2 < F + ε) is ell_op_approx. ell_op_lt_witness is ell_op_approx at ε = 1 - F, re-proved via the sconstraint bound ell_op_s_bdd_below.

Evidence: Operator_Envelopes:870 `ell_op k L p M ≤ - trace (M ** a) / 2`. Value_Function_Subsolution:54-55 `assumes a: "a ∈ feasible k L p" and le: "- trace (M ** a) / 2 ≤ c" shows "ell_op k L p M ≤ c"`. Value_Function_Supersolution_Case_1:22-23 `lt: "ell_op k L p H < 1" obtains a where "a ∈ feasible k L p" and "- trace (H ** a) / 2 < 1"`.

Suggested action: Put ell_op_le_witness (no L hypothesis) and ell_op_approx in Curvature_Operator, and use them at all eight sites.


### RA-operator-23. ell_op_le/ge_one_of_psd_diff re-prove ellipticity, which sits two theories downstream

*simplification, impact low, confidence high, ~60 lines.*  
Locations: Relative_Arbitrage/Curvature_Operator.thy:382 ell_op_le_one_of_psd_diff; Relative_Arbitrage/Curvature_Operator.thy:413 ell_op_ge_one_of_psd_diff; Relative_Arbitrage/Operator_Envelope_Continuity.thy:487 ell_op_elliptic, :513 ell_op_elliptic_le; Relative_Arbitrage/Curvature_Operator.thy:270-287 (header claims ellipticity is proved here)

Both 30-line lemmas are degenerate ellipticity applied at the matrix -(2/(n-k))I, followed by ell_op_eval. ell_op_elliptic and ell_op_elliptic_le need only ell_op_bdd_below and ell_op_pointwise_elliptic, both in Curvature_Operator, yet they live in Operator_Envelope_Continuity under the heading "Towards Section 4". The header of Curvature_Operator advertises "the degenerate ellipticity of F".

Evidence: ell_op_elliptic_le: `psd (N - M) ⟹ feasible k L p ≠ {} ⟹ ell_op k L p N ≤ ell_op k L p M`. With ell_op_eval and feasible_nonempty, the le-version is `ell_op_elliptic_le[OF Q feasible_nonempty] + ell_op_eval`, and the ge-version is symmetric.

Suggested action: Move ell_op_elliptic and ell_op_elliptic_le to Curvature_Operator. Reduce ell_op_le_one_of_psd_diff and ell_op_ge_one_of_psd_diff to 3-line corollaries, or inline them in Viscosity_Ball, their only user.


### RA-operator-24. The ball-uniqueness and Section-4 helper theorems are dead or duplicated

*dead_code, impact low, confidence high, ~140 lines.*  
Locations: Relative_Arbitrage/Ball_Solution.thy:322 ball_v_unique_solution_smooth; Relative_Arbitrage/Ball_Solution.thy:370 comparison_ball; Relative_Arbitrage/Value_Function_Uniqueness.thy:22 theorem_1_1_ball_fragment; Relative_Arbitrage/Operator_Envelope_Continuity.thy:575 max_principle_le, :603 comparison_from_max_principle, :625 uniqueness_from_max_principle; Relative_Arbitrage/Comparison_Principle.thy:2089 viscosity_uniqueness_compact

ball_v_unique_solution_smooth (u = ball_v inside the ball from visc_subsol_le_ball_v plus ball_v_le_visc_supersol) is re-proved verbatim as the third clause of theorem_1_1_ball_fragment. Neither is used. comparison_ball is unused. max_principle_le, comparison_from_max_principle and uniqueness_from_max_principle are named only in prose (Comparison_Principle:1271). viscosity_uniqueness_compact re-proves uniqueness inline by unfolding max_principle_boundary_def twice, in a more general form (bd: u = w on the boundary rather than u = w = 0). comparison_from_max_principle is a trivial special case of max_principle_le.

Evidence: Ball_Solution:340-346 and Value_Function_Uniqueness:45-49: both apply visc_subsol_le_ball_v and ball_v_le_visc_supersol with bd. Comparison_Principle:2107-2121 `using mpb subu supw cu cw unfolding max_principle_boundary_def by blast` appears twice. grep -w uniqueness_from_max_principle finds only prose outside its definition.

Suggested action: Replace the three OEC lemmas by one uniqueness_from_max_principle with bd: u y = w y, stated next to max_principle_boundary (better: generically over max_principle_boundary_gen in Viscosity_Solutions), and make viscosity_uniqueness_compact a one-liner. Delete comparison_ball, ball_v_unique_solution_smooth and theorem_1_1_ball_fragment, or keep exactly one of the last two.


### RA-operator-25. About forty orphan section headers and text blocks left behind by earlier moves

*documentation, impact low, confidence high, ~250 lines.*  
Locations: Relative_Arbitrage/Curvature_Operator.thy:157, 260-268, 289-296, 444-451, 471, 474; Relative_Arbitrage/Constraint_Set_Convexity.thy:195-204, 291-307; Relative_Arbitrage/Operator_Continuity.thy:25-37, 262; Relative_Arbitrage/Operator_Formula.thy:23-37, 276-280, 532-542, 685-698, 1036-1037, 1678-1693, 1757-1761, 1920-1936, 2103-2112; Relative_Arbitrage/Operator_Envelopes.thy:35-45, 543-552, 604-621, 1155-1161, 1290-1301, 1471-1494; Relative_Arbitrage/Operator_Envelope_Continuity.thy:527-544, 562-570, 648-651; Relative_Arbitrage/Ball_Solution.thy:121-124, 349-354, 391-415; Relative_Arbitrage/Viscosity_Comparison_Interface.thy:72-80, 137-141; Relative_Arbitrage/Viscosity_Definitions.thy:56-59

The pattern is a section or subsection heading, often with explanatory text, and no lemma under it. Examples:
- Operator_Formula:1920 "A rank obstruction: the deterministic core of Lemma 5.3" (text 1928 "The form used on a face ...") has no lemma.
- Operator_Formula:2103 "Closedness of the feasible set" promises compactness of the feasible set via feasible_iff_eigval and feasible_bounded, then gives only closed_eigen_ub.
- Operator_Envelopes:604 "Example 3.1 satisfies Definition 3.1 as stated in the paper" has no lemma (also promised in the header).
- Operator_Envelopes:1486 "A constant is a subsolution off K" has no lemma.
- Operator_Envelopes:1155-1161 promises "the three invariances of F" but the next lemma is ell_op_usc_zero_zero_lt_one.
- Ball_Solution:121 "The punctured ball is dense in the closed ball" is empty.
- Curvature_Operator:289 "Viscosity solutions of F=1 (Theorem 1.1, PDE side)" contains "Bounds on the feasible set" and "Perturbation bounds".
- OEC:527-544 has four consecutive text blocks for lemmas that no longer exist.
- Constraint_Set_Convexity:291-307 has a "Lemma 2.1 in full" text and a "Support-function characterisation" section with no content.
- Numerous "X lives in @{theory ...}" pointers (for example Operator_Envelopes:1292-1298, Operator_Continuity:27-37).

Evidence: Read in full; each listed range is followed immediately by another heading, another text, or `end`.

Suggested action: Delete the orphan headings and pointer texts; merge useful prose into the surviving lemma's text. Mechanical, no proof affected.


### RA-operator-26. Incorrect claims in prose

*documentation, impact low, confidence high, ~60 lines.*  
Locations: Relative_Arbitrage/Viscosity_Ball.thy:210-214; Relative_Arbitrage/Viscosity_Definitions.thy:127-143; Relative_Arbitrage/Viscosity_Definitions.thy:56-59, 165-168; Relative_Arbitrage/Ball_Solution.thy:356-368; Relative_Arbitrage/Operator_Envelope_Continuity.thy:648-651; Relative_Arbitrage/Comparison_Strictness.thy:446; Relative_Arbitrage/Comparison_Principle.thy:1142, 1271; Relative_Arbitrage/Operator_Formula.thy:2021-2026, 2082-2083; Relative_Arbitrage/Viscosity_Comparison_Interface.thy:12-18

Specific false statements:
- Viscosity_Ball:211 says "on the punctured open ball". The theorem is on ball 0 r, centre included, as Curvature_Operator:261 says.
- Viscosity_Definitions:127-143 says Crandall-Ishii is not available "in this HOL-Analysis or the AFP", that everything downstream is conditional on max_principle_boundary, and that this HOL-Analysis lacks a semicontinuity library. All three are false now: Crandall_Ishii_Sums, max_principle_boundary_holds and the Semicontinuous_Analysis session exist.
- Viscosity_Definitions:58 says test-function data is "the same as in Curvature_Operator". It is in Test_Functions.
- Viscosity_Definitions:165-168 claims the bridges let a reader reuse the machinery (see the generic-layer finding).
- Ball_Solution:361 says max_principle_boundary is "in Operator_Envelope_Continuity.thy" and [CI90] is "not formalized here". It is in Viscosity_Definitions, and CI90 is formalised.
- OEC:648-651 says removing the interface needs a proof of Theorem 4.2(a). That proof exists.
- Comparison_Strictness:446 says cInf_mult_pos lives in Operator_Envelopes. It is in Integrability_Criteria.
- Comparison_Principle:1142 places max_principle_boundary in Operator_Envelope_Continuity, and :1271 cites three lemmas that are never used.
- Operator_Formula:2023 and :2082 say eigen_lb_iff_eigval_ge and feasible_iff_eigval are what "Lemma 2.3's compactness" and "Section 2" consume. Nothing consumes them.
- VCI:17 calls p-scaling invariance part of Lemma 3.1. Paper Lemma 3.1 is the F_*/F^* formula.

Evidence: See the quoted lines. grep confirms the definitions' actual homes, for example `definition max_principle_boundary` at Viscosity_Definitions:153.

Suggested action: Correct or delete each statement.


### RA-operator-27. Paper prose about this cluster sits inside the paper-free Second_Order_Viscosity_Analysis and Symmetric_Matrix_Spectra

*misplacement, impact low, confidence high, ~60 lines.*  
Locations: Second_Order_Viscosity_Analysis/Test_Functions.thy:31-43; Second_Order_Viscosity_Analysis/Test_Functions.thy:70-74; Second_Order_Viscosity_Analysis/Test_Functions.thy:474-476, 486-497, 577, 328-331; Second_Order_Viscosity_Analysis/Doubling_Of_Variables.thy:3890, 4474, 4702; Symmetric_Matrix_Spectra/Poincare_Separation.thy:127, 1063-1065

Several blocks were carried into these sessions in phases 3 and 9 and still talk about this cluster:
- Test_Functions:31-43 is the old header of Viscosity_Definitions ("Every notion of viscosity sub- and supersolution the development uses ... collected here ... The envelope operators ell_op_lsc and ell_op_usc come along"), stranded in a library theory.
- Test_Functions:70-74 is the comment for `expandable` ("The paper's hypothesis on K for the uniqueness clause of Theorem 1.1"). It sits before test_fun_C2_imp_test_fun_at, 1,070 lines away from its definition (line 1144).
- Test_Functions:476 says "test_fun_C2 lives in Viscosity_Definitions", which is false: it is defined in the same file at line 64.
- Test_Functions:577 points into the paper session.
- Test_Functions:330-331 and 490-497 name ell_op_usc_scale, ell_op_usc_conj_rot, supersol_jet and ell_op_elliptic_le.
- Doubling_Of_Variables names eq36_rhs, supersol_jet and ell_op_env_strict_contradiction.
- Poincare_Separation:127 cites "Eq. (3.5) of LaiShkolnikovSoner", and 1063-1065 talks about M_p.

Evidence: Test_Functions:64 `definition test_fun_C2` versus :476 `text ‹test_fun_C2 lives in Viscosity_Definitions.›`. Test_Functions:39 `The envelope operators ell_op_lsc and ell_op_usc come along ...`.

Suggested action: Move the Viscosity_Definitions header back to Viscosity_Definitions and the expandable comment next to its definition. Delete the false pointer. Rephrase or remove the paper constant names in these library theories (PLAN §2.11 calls these sessions paper-free).


### RA-operator-28. Small repeated computations around ball_v and rank1proj

*clone, impact low, confidence high, ~40 lines.*  
Locations: Relative_Arbitrage/Curvature_Operator.thy:234-244 (inside ball_v_gradient) vs :456 ball_v_eq_quadratic; Relative_Arbitrage/Ball_Solution.thy:128 ball_v_pos; Relative_Arbitrage/Ball_Solution.thy:67-71 (re-derives Matrix_Algebra.norm_less_of_ball); Relative_Arbitrage/Operator_Continuity.thy:50 rank1proj_annihilates vs Relative_Arbitrage/Operator_Formula.thy:45 rank1proj_annihilates_perp; Relative_Arbitrage/Viscosity_Ball.thy:101-102 vs :197-198 (symH' proved two ways)

ball_v_gradient re-proves ball_v_eq_quadratic inline (the same chain norm y < r, then (norm y)² < r², then y•y < r²). ball_v_pos repeats the chain a third time. ball_v_scaled_test_fun re-derives norm_less_of_ball, which Ball_Solution uses elsewhere (line 196). rank1proj_annihilates is rank1proj_annihilates_perp applied to y = a *v x after p•(a x) = 0.

Evidence: Curvature_Operator:236-243 and :461-468 are the same five lines.

Suggested action: Use ball_v_eq_quadratic inside ball_v_gradient. Add a lemma `norm x < r ⟹ x•x < r²`. Derive rank1proj_annihilates from rank1proj_annihilates_perp once both live in one theory.


### RA-operator-29. Inf scaling by a positive constant is re-proved, and is an instance of HOL's continuous_at_Inf_mono

*library_duplicate, impact low, confidence medium, ~45 lines.*  
Locations: Relative_Arbitrage/Viscosity_Comparison_Interface.thy:98-131 (inf_scale inside ell_op_dilation); Continuous_Time_Martingales/Integrability_Criteria.thy:24 cInf_mult_pos; Relative_Arbitrage/Operator_Envelopes.thy:1198 (prose pointer); Relative_Arbitrage/Comparison_Strictness.thy:446 (pointer naming the wrong theory)

ell_op_dilation proves Inf((λx. c*x) ` A) = c * Inf A inline, although cInf_mult_pos in Continuous_Time_Martingales already states exactly that. Both are the instance f = (*) c of HOL's continuous_at_Inf_mono, since multiplication by c > 0 is mono and continuous. cInf_mult_pos is also a pure order/real-analysis fact placed in a martingale theory, and Operator_Envelopes imports Integrability_Criteria only to mention it in prose.

Evidence: HOL/Topological_Spaces.thy:3374 `lemma continuous_at_Inf_mono: assumes "mono f" and cont: "continuous (at_right (Inf S)) f" and S: "S ≠ {}" "bdd_below S" shows "f (Inf S) = (INF s∈S. f s)"`. Integrability_Criteria:24-27 `cInf_mult_pos: 0 < c ⟹ A ≠ {} ⟹ bdd_below A ⟹ Inf ((λt. c * t) ` A) = c * Inf A`. Comparison_Strictness:446 says it "lives in Relative_Arbitrage.Operator_Envelopes", which is false.

Suggested action: Prove cInf_mult_pos in two lines from continuous_at_Inf_mono, or delete it, and move it to Semicontinuous_Analysis or another order-theoretic library theory. Delete the inline inf_scale proof. Drop Operator_Envelopes' import of Integrability_Criteria and fix the prose at Comparison_Strictness:446.


### RA-operator-30. Near-duplicate arguments inside Operator_Formula and Eigenvalue_Bound_Exact

*simplification, impact low, confidence medium, ~200 lines.*  
Locations: Relative_Arbitrage/Operator_Formula.thy:1381 bracket_Mp_top_eigenvector vs :1596 bracket_ge_shifted; Relative_Arbitrage/Operator_Formula.thy:424 sum_min_eigval_ge vs Relative_Arbitrage/Eigenvalue_Bound_Exact.thy:413 Pi_constraint_capped_trace; Relative_Arbitrage/Operator_Formula.thy:297-324 vs :438-456 (threshold set, its minimum, eigval_eq_min_of_threshold); Relative_Arbitrage/Eigenvalue_Bound_Exact.thy:97 shift_convex_combination, :175-185 vs :192-198, :351-360; Relative_Arbitrage/Operator_Envelopes.thy:1167 ell_op_usc_zero_zero_lt_one vs :401 ell_op_usc_small_shift_lt_one

Five groups:
- bracket_Mp_top_eigenvector (equality) and bracket_ge_shifted (inequality) reindex the same sums ({2..n} versus {1..n'}, {2..m+1} versus {1..m}). One lemma, "if eigval i N ≥ eigval (Suc i) M for i < n then shifted ≤ bracket N", plus its reverse under equality, gives both.
- sum_min_eigval_ge (eigen_lb a m implies m ≤ Σ min(λ_u, 1)) is Pi_constraint_capped_trace instantiated through suff_volatile_subset_Pi_constraint (k = n - m).
- The obtain-T / obtain-w / eigval_eq_min_of_threshold block is copied verbatim.
- shift_convex_combination is 60 lines of field arithmetic (field_simps after a case split). diag_in_convex_hull_aux repeats its base case in the Suc branch. wsum spends 9 lines on d/(e+d) + e/(e+d) = 1.
- The two "F^* < 1 for small M" lemmas are both one instance of ell_op_usc_le_scaled_norm with norm M small.

Evidence: Operator_Formula:1412-1437 and :1625-1646 (`sum.reindex_bij_witness[where i = "λi. i - 1" and j = Suc]`, twice each). Operator_Formula:438-456 and :306-324 are identical apart from the variable names V/B.

Suggested action: Factor out bracket_shift_le and an eigval_threshold_witness lemma (in Ky_Fan). Derive sum_min_eigval_ge from Pi_constraint_capped_trace, or keep only one capped-trace argument. Shorten the arithmetic in Eigenvalue_Bound_Exact (needs a PIDE check). Merge the two small-M lemmas into one with a hypothesis norm M < 1/(2B).


### RA-operator-31. Remaining dead statements in the cluster

*dead_code, impact low, confidence medium, ~200 lines.*  
Locations: Relative_Arbitrage/Viscosity_Definitions.thy:79 visc_sol_env; Relative_Arbitrage/Viscosity_Definitions.thy:170-190 (five bridges); Relative_Arbitrage/Operator_Formula.thy:2028 eigen_lb_iff_eigval_ge, :2085 feasible_iff_eigval; Relative_Arbitrage/Operator_Envelope_Continuity.thy:466 ell_op_envelopes_eq_off_zero; Relative_Arbitrage/Eigenvalue_Bound_Exact.thy:560 lemma_2_1_exact and its helper chain (lines 28-406, 494-552); Relative_Arbitrage/Ball_Solution.thy:31-141 (continuous_on_ball_v, ball_v_scaled_test_fun, ell_op_ball_scaled, ball_v_pos: used only by the dead ball strand)

No other statement uses these; uses were found with grep -rnw over all .thy files. lemma_2_1_exact and ell_op_envelopes_eq_off_zero are paper deliverables (Lemma 2.1 and the Lemma 3.1 summary) and should be kept but surfaced (see the bridges finding). eigen_lb_iff_eigval_ge is the faithfulness bridge for eigen_lb. The rest can go together with the ball strand and the generic-layer cleanup.

Evidence: grep -rnw counts: visc_sol_env appears in its definition plus one prose pointer. visc_subsol_eq_gen and visc_supersol_eq_gen have 0 uses. feasible_iff_eigval has 0 uses. ell_op_envelopes_eq_off_zero has 0 uses. lemma_2_1_exact appears only in Exit_Class:21 prose.

Suggested action: Delete visc_sol_env, the bridges (unless the generic layer is made real), feasible_iff_eigval and the ball helpers. Keep and reference lemma_2_1_exact, eigen_lb_iff_eigval_ge and ell_op_envelopes_eq_off_zero from Statement/Paper_Readings.


## RA-market

The cluster is the "market" formulation of the paper. Everything is stated over an abstract probability space through the locale sufficiently_volatile_market (Volatile_Market:88). That locale has 19 assumptions on top of a martingale: the eigenvalue constraint of Eq. (1.4) via eigen_lb/eigen_ub, holding only up to a pre-exit time tau; the Dynkin identity dynkin_quadratic; a per-coordinate compensated-square martingale coord_Z_martingale; and stopping and continuity conditions. On top of the locale sit:
(i) Definition 1.1 (relative_arbitrage) and the Example 3.1 upper bound E[tau] <= ball_v (Volatile_Market);
(ii) a "gradient strategy" whose stochastic integral sint is defined by fiat to satisfy Ito's formula, giving ball_relative_arbitrage, plus a locale optimal_ball_market that assumes the reverse inequality (Optimal_Exit_Time);
(iii) three Ito-process locales that derive dynkin_quadratic from optional sampling (Ito_Market), none of them interpreted anywhere;
(iv) non-vacuity of the locale via continuous Brownian motion (Brownian_Market, Brownian_Optimal_Boundary);
(v) a value function val_fn = Sup of ess_inf_time over all markets on the fixed sample type 'n => real => real, with its ball bound, boundary identity and monotonicity in K (Value_Function_Market);
(vi) Lemma 2.2 for sequences of stopped, confined markets (Path_Tightness_Market);
(vii) a 2,634-line "law-closure" route (Exit_Time_Semicontinuity). It defines market path laws (mkt_path_laws) and their weak closure (mkt_law_closure), and proves sequential compactness, shift domination, confinement, and the martingale and covariation identities against bounded continuous tests and then against past events. It also introduces a third value function, stopped_val_fn, and clause (1) in "law-level form" (clause_one_law_level).

Central finding: the whole cluster is a second, parallel formalisation. theorem_1_1 and example_3_1_closed_form (Statement) are about xval/iexit_val/exit_val, the class formulation in Exit_Class*.
- A word-level scan of every name the cluster defines finds only two non-prose uses outside it: Value_Function_Uniqueness.theorem_1_1_ball_fragment (uses val_fn_le_ball_v and val_fn_boundary) and Exit_Class_Limits.stopped_market_acov_leaves_sconstraint (unfolds stopped_market). Both are used nowhere.
- The class chain needs the cluster only as an import conduit: Exit_Class_Witness, Exit_Class_Infinite, Value_Function_Euler_Construction and Supersolution_Case_1 use cbmX/bm_paths from Wiener_Measure.Continuous_Brownian_Motion. They reach that theory only via Exit_Class_Limits -> Exit_Time_Semicontinuity -> Value_Function_Market -> Brownian_Optimal_Boundary -> Brownian_Market.
- Six arguments are therefore proved twice, once per formalisation: Example 3.1 upper bound, boundary zero on the sphere, non-emptiness via Brownian motion, Lemma 2.2 extraction, clause (1) upper semicontinuity, and the Lemma 2.3 martingale-identity-through-weak-limits argument.
- The market objects are also not faithful to Eq. (1.6)/(1.7): they use (1.4) rather than (1.5), constraints only up to tau, and a fixed sample space.
- The cluster carries many orphan or stale text blocks, and misattributions ("Lemma 2.1" for the exit-time bound; "Eq. (1.10)" for the boundary condition).

Verification was textual: full reading plus repository-wide greps for names, imports, AFP and HOL. No PIDE session was running, and the parent's build had not produced heaps yet. So the import-removal claims are high-confidence by grep but should be confirmed by one build.


### RA-market-1. The whole market layer is a parallel formalisation that Theorem 1.1 does not use; only a transitive Wiener_Measure import ties it to the class chain

*structure, impact high, confidence high, ~4950 lines.*  
Locations: Relative_Arbitrage/Exit_Class_Limits.thy:5 (imports Exit_Class Exit_Time_Semicontinuity); Relative_Arbitrage/Exit_Class_Limits.thy:72-76 stopped_market_acov_leaves_sconstraint; Relative_Arbitrage/Value_Function_Uniqueness.thy:5-6 (imports Value_Function_Market, Exit_Time_Semicontinuity); Relative_Arbitrage/Value_Function_Uniqueness.thy:22-50 theorem_1_1_ball_fragment; Relative_Arbitrage/Exit_Class_Witness.thy:5-12 (first class theory using bm_paths/bmX/cbmX); Relative_Arbitrage/ROOT (theories Volatile_Market ... Exit_Time_Semicontinuity)

No theorem, definition or simp/measurable declaration of the 8 cluster theories is used on the dependency path of theorem_1_1 or example_3_1_closed_form (Statement/Theorem_1_1_Statement.thy:134, :199); both are about xval/iexit_val. A grep of every name the cluster defines finds exactly two non-prose uses outside the cluster, and both are leaves used nowhere: theorem_1_1_ball_fragment (val_fn_le_ball_v, val_fn_boundary) and stopped_market_acov_leaves_sconstraint (a one-line unfolding of stopped_market). The cluster has no global [simp]/[measurable] declarations; the only global interpretation, BM2, is unused. Yet Exit_Class_Limits imports Exit_Time_Semicontinuity, so all 4,901 lines and the serial chain Volatile_Market -> Optimal_Exit_Time -> Brownian_Optimal_Boundary -> Value_Function_Market -> Exit_Time_Semicontinuity lie on the class chain's critical path. The class chain uses one thing it reaches only through the cluster: Wiener_Measure.Continuous_Brownian_Motion (cbmX, bm_paths, bmX). It is first needed in Exit_Class_Witness (177 occurrences) and then in Exit_Class_Infinite, Value_Function_Euler_Construction and Value_Function_Supersolution_Case_1. notes/PLAN_THEOREM_1_1.md:55 already said three value functions exist (val_fn, stopped_val_fn, paper_v) and 'the theorem must end up about ONE'. The market two were never retired. notes/STATUS.md:18-24 records the precedent: the Relative_Arbitrage_Unused session was deleted because none of it was reachable from Theorem 1.1. The ROOT description does not mention a market layer at all.

Evidence: grep -rnw over all cluster-defined names, excluding cluster files and text lines, gives only Value_Function_Uniqueness.thy:25-36 (val_fn, val_fn_le_ball_v, val_fn_boundary) and Exit_Class_Limits.thy:74 (stopped_market). grep theorem_1_1_ball_fragment: defined at VFU:22, otherwise mentioned only in prose at Comparison_Principle.thy:2081. grep stopped_market_acov_leaves_sconstraint: definition plus text at Exit_Class_Limits:68. grep -E '\b(bm_paths|BMP\.|cbmX|bmX)\b' in Exit_Class.thy, Covariation_Density, Exit_Class_Limits, Exit_Class_Tightness, Exit_Class_Shift: 0 hits; Exit_Class_Witness: 177. Exit_Class_Witness imports Exit_Class_Shift only (plus libraries). Statement/Statement_Auxiliary.thy:10-12 imports Value_Function_Uniqueness, Exit_Class_Infinite, Exit_Class_Marginals.

Suggested action: Decouple, then either delete or segregate. (1) Add "Wiener_Measure.Continuous_Brownian_Motion" to the imports of Exit_Class_Witness. Drop Exit_Time_Semicontinuity from the imports of Exit_Class_Limits and delete stopped_market_acov_leaves_sconstraint and the market-bridge prose (Exit_Class_Limits:19-34, 40-69). (2) Drop Value_Function_Market and Exit_Time_Semicontinuity from the imports of Value_Function_Uniqueness. Delete theorem_1_1_ball_fragment, which is superseded by example_3_1_closed_form and ball_v_unique_solution. (3) Rebuild Relative_Arbitrage_Statement: it must be unchanged. (4) Move the 8 theories, minus what is deleted under the other findings, to a new session 'Relative_Arbitrage_Markets' (directory Markets/, = Relative_Arbitrage + Wiener_Measure). Or delete them outright, following the Relative_Arbitrage_Unused precedent. The only content without a class-level counterpart is Definition 1.1 and the (weak) ball_relative_arbitrage. (5) Also retire the bridge residue in other clusters: Pair_Path_Laws.acont/acont_set_borel_measurable/Yint (definitions with no non-prose uses) and Pair_Path_Space.path_laws_convergent_subsequence_market (used only by Path_Tightness_Market:318).


### RA-market-2. Six arguments are proved twice, once for markets and once for the class

*clone, impact high, confidence high, ~3500 lines.*  
Locations: Volatile_Market.thy:169-342 compensator_lower/expected_stopped_time_bound/expected_exit_time_bound + Value_Function_Market.thy:75-93 val_fn_le_ball_v  vs  Exit_Class_Witness.thy:949-1260 exit_class_trace_rate/exit_class_sq_norm_mean_ge/exit_val_le_ball_bound; Value_Function_Market.thy:100-111 val_fn_boundary  vs  Exit_Class_Witness.thy:1066 exit_val_boundary_zero; Brownian_Market.thy:16-163 + Brownian_Optimal_Boundary.thy:33-58 + Value_Function_Market.thy:54-66 + Exit_Time_Semicontinuity.thy:294-466 mkt_path_laws_nonempty  vs  Exit_Class_Witness.thy:544-879 bmpair_law_in_paper_pair_class/exit_class_nonempty; Path_Tightness_Market.thy:31-348 market_path_laws_convergent_subsequence  vs  Exit_Class_Tightness.thy:73-383 exit_class_convergent_subsequence; Exit_Time_Semicontinuity.thy:202-287, 2598-2623 vshift_sup_usc_mkt/clause_one_law_level  vs  Exit_Class_Shift.thy:298 exit_val_usc / Exit_Class_Witness.thy:888 exit_val_usc_unconditional; Exit_Time_Semicontinuity.thy:1086-2576 (closure martingale/covariation tests and events)  vs  Exit_Class_Limits.thy:107-720 (exit_class_martingale_test ... exit_class_martingale_event_limit); Exit_Time_Semicontinuity.thy:489-800 mkt_law_witness_shift  vs  Exit_Class_Shift.thy:39 exit_class_pshift

Each step of the paper the market layer formalises has a second, used proof in the class layer:
- Example 3.1 upper bound;
- zero value on the sphere;
- non-emptiness of the class via Brownian motion;
- Lemma 2.2 subsequence extraction;
- clause (1) by Berge through vshift_sup_usc_of_seq_compact (both routes call Pair_Path_Space:1489);
- the Lemma 2.3 step that carries the integrated martingale identity through weak limits and upgrades it from continuous tests to past events;
- translation invariance.
The market copies carry the same arguments over a different index set (stopped markets on a fixed sample type rather than laws on path space).

Evidence: Exit_Class_Shift.thy:330 'proof (rule vshift_sup_usc_of_seq_compact[OF T0 Aopen])' and Exit_Time_Semicontinuity.thy:271 'proof (rule vshift_sup_usc_of_seq_compact[OF T A])'. Exit_Class_Limits.thy:403 'define N1 where "N1 = distr (density Q (λω. ennreal (gp ω))) (borel_of ?PS) ?p"' and Exit_Time_Semicontinuity.thy:2024 'N1 = distr (density Λ (λf. ennreal (gp f))) (borel_of ?PS) ?p', each followed by identical push/finw/pdm sub-proofs and metric_measure_eqI_bounded_cts. Exit_Class_Limits.thy:177 even contrasts the two: 'Unlike the confined market laws of Exit_Time_Semicontinuity, the paper's class admits no clamp'.

Suggested action: Resolved by deleting or segregating the market layer (previous finding). If anything is kept, factor the event-upgrade argument into one generic Continuous_Path_Spaces.Path_Tightness lemma; see the next finding.


### RA-market-3. The 'continuous tests imply past events' upgrade is proved twice, verbatim; it should be one generic path-space lemma

*generalisation, impact medium, confidence high, ~500 lines.*  
Locations: Exit_Time_Semicontinuity.thy:1974-2196 mkt_law_closure_martingale_event; Exit_Time_Semicontinuity.thy:2207-2386 mkt_law_closure_covariation_event (same push/finw/pdm block, :2264-2315); Exit_Class_Limits.thy:350-575 exit_class_martingale_event_limit (same block, :400-445)

Three proofs share the same ~90-line skeleton:
- split an integrand g into gp and gm;
- form N1/N2 = distr (density Λ gp/gm) (borel_of ?PS) (λf. restrict f {0..s});
- prove 'push' (integral transfer) and 'finw' (finiteness);
- conclude N1 = N2, or N1 <= N2, from metric_measure_eqI_bounded_cts or metric_measure_mono_bounded_cts;
- read off the indicator case.
The statements mention only a finite measure on path_borel T, a measurable g that is bounded or integrable, and the restriction map, so they are paper-free.

Evidence: Exit_Time_Semicontinuity.thy:2030-2049 'have push: ... if um: "u ∈ borel_measurable (borel_of ?PS)" and wm: "w ∈ borel_measurable Λ" and w0' and :2266-2283, identical. Exit_Class_Limits.thy:410-424 is the same 'have push' with Q for Λ. The finw blocks at ETS:2050-2081, ETS:2284-2315 and Exit_Class_Limits:425-445 differ only in the bound used (constant versus integrable).

Suggested action: Add two lemmas to Continuous_Path_Spaces/Path_Tightness.thy next to metric_measure_eqI_bounded_cts, generic in the codomain 'b::{polish_space,banach}. (a) For finite Λ on path_borel T and integrable g: if ∫ g · h(restrict f {0..s}) dΛ = 0 for all bounded continuous h, then it holds for h = indicator B, for all B in path_borel s. (b) The monotone analogue with ≤ and g ≥ 0. Then exit_class_martingale_event_limit becomes an application, and any surviving market copy is a two-liner.


### RA-market-4. val_fn and sufficiently_volatile_market are not the paper's v and P_x, but are presented as such

*faithfulness, impact medium, confidence high, ~60 lines.*  
Locations: Value_Function_Market.thy:10-24 ('Formalizes the value function of Eq. (1.6)'); Value_Function_Market.thy:37-48 mkt_exit_vals/val_fn; Volatile_Market.thy:12-29 (header: 'capturing the class of measures P ∈ P_x', 'eigenvalue constraints of Eqs. (1.4)-(1.5)'); Volatile_Market.thy:105-109 acov_eigen_lb/acov_eigen_ub; Value_Function_Uniqueness.thy:22-50 theorem_1_1_ball_fragment

Eq. (1.6) takes the sup over P_x: laws on C([0,∞),R^n) under which the coordinate process is a martingale and d<X>/dt satisfies the convexified condition (1.5)/(1.7) for a.e. t >= 0. Since the class formulation itself reads (1.5) through sconstraint/Pi_constraint (Statement/Theorem_1_1_Statement.thy:41-49), the market objects differ from the paper's v and P_x in four ways:
- The market locale imposes the non-convex condition (1.4) (eigen_lb (acov s ω) (n-k)), which the paper deliberately replaces by (1.5) because (1.4) is not weakly closed. By Lemma 2.1 (convex hull), the (1.4)-class is a subset of the paper's class.
- The constraint holds only up to an arbitrary random time tau, not for a.e. t >= 0.
- The sample space is pinned to the type 'n ⇒ real ⇒ real.
- The value is ess_inf of tau rather than of τ_K.
So val_fn ≤ v at best, and equality is unproved. The header claims are therefore inaccurate. The 'Theorem 1.1 fragment' at Value_Function_Uniqueness:22 is stated for val_fn, not for the paper's value function.

Evidence: Volatile_Market.thy:105-107 'acov_eigen_lb: AE ω in M. ∀s. 0 ≤ s ⟶ s ≤ tau ω ⟶ eigen_lb (acov s ω) (CARD('n) - k)'. Value_Function_Market.thy:41 '∃(M :: ('n ⇒ real ⇒ real) measure) F X acov tau. sufficiently_volatile_market ...'. Paper EM_final_paper.tex:207-223: (1.5) uses Π_m; (1.7) requires the constraints 'a.e. t≥0'; line 199: (1.4) is λ_(n-k) ≥ 1. Lemma 2.1 (line 266) states that the (1.5)-set is the convex hull of the (1.4)-set.

Suggested action: If the market layer survives, rewrite the headers to say 'sup over markets satisfying the non-convexified constraint (1.4) up to a pre-exit time; ≤ the paper's v'. Rename val_fn to mkt_val_fn. Do not present theorem_1_1_ball_fragment as a Theorem 1.1 fragment. Otherwise delete with the layer.


### RA-market-5. Exit_Time_Semicontinuity claims the paper's class (1.7) consists of stopped markets, contradicting the paper and Exit_Class_Limits

*faithfulness, impact medium, confidence high, ~30 lines.*  
Locations: Exit_Time_Semicontinuity.thy:83-85; Exit_Time_Semicontinuity.thy:1893-1903 (stopped_market described as 'the paper's class (1.7)'); Exit_Time_Semicontinuity.thy:1932-1935 stopped_val_fn ('paper-class value function'); Exit_Time_Semicontinuity.thy:2580-2590

ETS:83-85 reads 'The four side conditions beyond the locale are part of the paper's class (1.7): the process is stopped at its horizon, the covariance vanishes after it, and its diagonal entries are pathwise integrable.' ETS:1893 reads 'The paper's class (1.7) consists of stopped markets'. Both are false. Exit_Class_Limits.thy:22-27 states the opposite: 'By (1.7)-(1.8) the processes in P_x are never stopped ... A stopped_market witness is therefore not a class member'. stopped_val_fn is called the 'paper-class value function' throughout and is not the paper's value function. There are three side conditions, not four.

Evidence: Quoted texts. EM_final_paper.tex:220-223: the constraints hold 'a.e. t≥0'.

Suggested action: Delete with the market layer. If kept, rename stopped_val_fn to stopped_mkt_val_fn and correct the prose to 'stopped markets, a device of this development, not the class (1.7)'.


### RA-market-6. Relative-arbitrage and optimality results are vacuous or axiomatised, and the claimed non-vacuity instance is not proved

*faithfulness, impact medium, confidence high, ~200 lines.*  
Locations: Optimal_Exit_Time.thy:83-97 sint, ito_formula_quadratic; Optimal_Exit_Time.thy:222-273 ball_relative_arbitrage; Optimal_Exit_Time.thy:286-296 optimal_ball_market/tau_optimal/optimal_exit_time_value; Optimal_Exit_Time.thy:279-284 (text: Brownian motion 'which no Isabelle/HOL library provides'); Brownian_Optimal_Boundary.thy:11-26, 60-65

- sint is defined as the value Ito's formula would give, so ball_relative_arbitrage shows that an explicitly defined V = v(x0) + sint is a relative arbitrage. Nothing connects V to a trading strategy θ or the self-financing equation (1.1), so Definition 1.1's content (a property of V^θ) is not reached. ito_formula_quadratic is 'by (simp add: sint_def)'.
- optimal_exit_time_value is antisym of a proved bound and an assumed reverse inequality.
- Brownian_Optimal_Boundary's header and section 'The optimality locale is inhabited' (60-65) assert that optimal_ball_market is consistent, but the theory contains no interpretation or proof of optimal_ball_market. Its only theorem is Brownian_boundary_market, an instance of sufficiently_volatile_market.
- The text at Optimal_Exit_Time:279-284 is stale: Wiener_Measure now provides Brownian motion.
- Example 3.1 is proved in full at class level (example_3_1_closed_form), so this part is superseded.

Evidence: grep optimal_ball_market: only Optimal_Exit_Time.thy:286 plus prose in Brownian_Optimal_Boundary.thy:14,63. grep ball_relative_arbitrage / optimal_exit_time_value: definition only.

Suggested action: Delete Optimal_Exit_Time's optimality section and Brownian_Optimal_Boundary. If Definition 1.1 is wanted for exposition, keep relative_arbitrage plus a remark that the strategy part is not formalised. Never claim an instance that is not proved.


### RA-market-7. 'Eq. (1.10)' is misattributed as the zero boundary condition, including in the acceptance-test Statement

*documentation, impact medium, confidence high, ~6 lines.*  
Locations: Value_Function_Market.thy:222; Value_Function_Uniqueness.thy:16, :62, :665; Statement/Theorem_1_1_Statement.thy:105

In the paper, Eq. (1.10) is the 'geometric' identity F(c1 p, c1 M + c2 pp^T) = c1 F(p,M) of Remark 1.1(b) (EM_final_paper.tex:244-246). Viscosity_Comparison_Interface.thy:141 correctly says 'Eq. (1.10) of Remark 1.1(b)'. The zero boundary condition is defined in Definition 3.1(a)/(b), not in any numbered equation of Section 1.

Evidence: Counting numbered equations in Section 1 (EM_final_paper.tex:152-261) gives (1.1)-(1.9), and (1.10) at line 245 inside the remark. Theorem_1_1_Statement.thy:105: '... together with the zero boundary condition of Eq. (1.10).'

Suggested action: Replace with 'the zero boundary condition of Definition 3.1' at all five sites. The Statement edit is prose-only and does not change any displayed constant.


### RA-market-8. Within Exit_Time_Semicontinuity, the martingale and covariation variants are copy-pasted pairwise

*clone, impact medium, confidence high, ~450 lines.*  
Locations: Exit_Time_Semicontinuity.thy:1128-1287 mkt_path_laws_martingale_test vs :1659-1812 mkt_path_laws_covariation_test (shared preamble :1145-1222 = :1678-1769); Exit_Time_Semicontinuity.thy:1289-1338 mkt_law_closure_martingale_test vs :1814-1886 mkt_law_closure_covariation_test; Exit_Time_Semicontinuity.thy:2030-2081 vs :2264-2315 (push/finw); Exit_Time_Semicontinuity.thy:2394-2483 mkt_law_closure_increment_event vs :2485-2576 mkt_law_closure_sq_increment_event (lines 2403-2462 = 2495-2554 verbatim)

Each pair repeats a 50-90-line block. The repeated blocks are:
- witness extraction, interpret, prj/Xm/cont/pm/rr/Z/Xm_Fs/cont_Fs/pms/hmeas/ZFs/ZM/XiM, step1/step2, bnd_t/bnd_s/ae_inc;
- the approximating sequence plus weak-convergence limit;
- the density push-forward;
- the clamp-invisibility block (ae, cmp_i, evdiff, inc_cont, incM, rcM, rc, pimL, iB, indM).

Evidence: Side-by-side reading: e.g. ETS:2410-2427 and :2502-2519 are character-identical 'have ae: "AE f in Λ. rclamp (2 * r) (f t $ i - f s $ i) = f t $ i - f s $ i" ...'.

Suggested action: Moot if the layer is deleted. Otherwise extract: mkt_law_witness_pathify (Xm, cont, pm), mkt_law_witness_past_test (Z, ZFs, ZM), mkt_law_closure_clamp_ae, and the generic event lemma of the previous finding.


### RA-market-9. Two bounded-integrand integral estimates are re-proved at five sites

*clone, impact medium, confidence high, ~300 lines.*  
Locations: Exit_Time_Semicontinuity.thy:1349-1434 witness_compensator_increment_bounds; Path_Tightness_Market.thy:229-303 (Arate' inside market_path_laws_convergent_subsequence); Volatile_Market.thy:176-209 (ptwise inside compensator_lower); Optimal_Exit_Time.thy:128-163 compensator_pathwise; Ito_Market.thy:407-462 compensator_bounded

Two estimates recur. The first holds on {u<..v} and on {0..t}: if a ≤ f ≤ b on the interval and f is set-integrable, then a·len ≤ ∫ f ≤ b·len. The second is that ∫_{0..v} - ∫_{0..u} = ∫_{u<..v} (set_integral_Un). The proofs re-derive c_int, set_integral_mono and set_integral_const every time. ETS:1349-1434 and PTM:229-303 are near-verbatim: same pt/splitset/int_*/add/zero_int/lower/Lint/upper. compensator_pathwise duplicates the inner argument of compensator_lower.

Evidence: PTM:247-248 'have pt: "0 ≤ aa i σ ω $ l $ l ∧ aa i σ ω $ l $ l ≤ L" if σ: "σ ∈ {u<..v}"' and ETS:1378-1379 'have pt: "0 ≤ acov σ ω $ i $ i ∧ acov σ ω $ i $ i ≤ L" if σ: "σ ∈ {s<..t}"', followed by the same 50 lines.

Suggested action: Add to Continuous_Time_Martingales/Integrability_Criteria.thy: set_integral_bounds_interval (a ≤ f ≤ b on {u..v} (or {u<..v}) and set-integrable ⟹ a(v-u) ≤ ∫ f ≤ b(v-u)) and set_integral_increment ({0..v} minus {0..u} = {u<..v}). Each of the five sites becomes 3-5 lines (if kept).


### RA-market-10. Matrix facts under eigen_lb/eigen_ub are proved repeatedly across the session

*clone, impact medium, confidence high, ~150 lines.*  
Locations: Volatile_Market.thy:145-157 trace_bound_pointwise  ≡ Curvature_Operator.thy:162-175 feasible_trace_lb (identical proof: obtain S ... trace_ge_dim); Ito_Market.thy:281-303 trace_le_eigen_ub  ≡ Value_Function_Subsolution.thy:3133 feasible_trace_le (and weaker sconstraint_trace_le :1823); Path_Tightness_Market.thy:17-27 eigen_ub_diag  ≡ Exit_Class.thy:133 psd_eigen_ub_diag(2) ≡ Ball_Solution.thy:422 feasible_diag_bound ≡ Value_Function_Euler_Construction.thy:897 sconstraint_diag_le ≡ Exit_Class.thy:430 sconstraint_diag; inline again at Ito_Market.thy:286-295; Symmetric_Matrix_Spectra/Matrix_Algebra.thy:1047 diag_eq_inner_axis ≡ :1069 diag_entry_quadform (same identity, both used in this cluster), also :607/:612 and :1237/:1259 pairs

The pointwise facts are:
- 'psd a, eigen_lb a m ⟹ m ≤ trace a';
- 'eigen_ub a L ⟹ a$i$i ≤ L', which needs no psd: psd_eigen_ub_diag carries a superfluous psd hypothesis for its second conclusion;
- 'eigen_ub a L ⟹ trace a ≤ n L'.
They are re-proved for each wrapper set (feasible, sconstraint, the locale's acov). trace_bound_pointwise is stated inside the locale although it mentions only one matrix.

Evidence: Volatile_Market.thy:149-155 and Curvature_Operator.thy:166-174 are line-for-line the same proof. PTM:25 'using assms diag_entry_quadform[...] by (auto simp: eigen_ub_def dest: spec[of _ "axis l 1"])' and Exit_Class.thy:138-148, Ball_Solution.thy:430-441 re-prove the axis quadratic-form step.

Suggested action: In Curvature_Operator, beside eigen_lb_def/eigen_ub_def, state eigen_lb_trace_ge (psd a ⟹ eigen_lb a m ⟹ real m ≤ trace a), eigen_ub_diag (no psd), psd_diag_nonneg (move from Pair_Path_Space:448) and eigen_ub_trace_le. Derive feasible_*, sconstraint_* and the market lemmas in one line each. In Symmetric_Matrix_Spectra keep one of diag_eq_inner_axis / diag_entry_quadform.


### RA-market-11. Ito-process locales: 17-19 assumptions restated four times, six hand enumerations, and no interpretation anywhere (update to plan G8)

*clone, impact medium, confidence high, ~744 lines.*  
Locations: Volatile_Market.thy:88-131 sufficiently_volatile_market (19 assumptions); Ito_Market.thy:80-123 ito_volatile_market (22; 17 shared verbatim); Ito_Market.thy:311-354 ito_stopped_market (23); Ito_Market.thy:564-600 ito_const_horizon_market (16, tau := c); enumeration proofs: Ito_Market.thy:222-272, :500-554, :662-726; Value_Function_Market.thy:124-183; Exit_Time_Semicontinuity.thy:361-443, :653-778; Brownian_Market.thy:25-163; Ito_Market.thy:150 Z_zero_expectation and :733 stopped_expected_time_bound (one-line wrappers that still exist)

Plan §10 rejected ito_market_core ('the entire yield of a shared ancestor is two one-line wrappers'), so the locale question needs settling on other grounds:
- Neither ito_volatile_market, ito_stopped_market nor ito_const_horizon_market is interpreted anywhere. None of their 15 statements has a use outside Ito_Market.
- Ito_Market is imported only by Path_Tightness_Market, which uses nothing from it.
- Brownian_Market:196-207 and Vector_Brownian_Martingales:924-929 claim an ito_const_horizon_market instance that does not exist.
So the right action is deletion, not refactoring. The plan's 'wrappers were deleted' is partly untrue: Z_zero_expectation and stopped_expected_time_bound remain.

The 'stopped market' notion is encoded three times:
- as locale assumptions X_stopped/acov_stopped in ito_stopped_market;
- as definition clauses in mkt_law_witness and stopped_market (ETS:68-74, :1913-1918, with mkt_law_witness ⟷ path_law ∧ stopped_market, :1920);
- as hypotheses stp/astop in Path_Tightness_Market:40-41.
The assumption names are inconsistent: coord_Z_martingale versus coordZ_martingale, tau_nonneg versus tau_nonneg'.

Evidence: grep -rnw ito_volatile_market|ito_stopped_market|ito_const_horizon_market outside Ito_Market → only prose in library sessions. Value_Function_Market.thy:136-139 explains why unfold_locales cannot be used, hence the 60-line enumeration of mono_K.

Suggested action: Delete Ito_Market. If any market locale survives, introduce one base locale market_core (martingale plus the 15 shared assumptions) and a stopped_market locale extending it; define mkt_law_witness as 'Q = path_law M X T ∧ stopped_market ...'. Prove mono_K and shift by unfolding sufficiently_volatile_market_axioms_def with AE_mp rather than enumerating 19 'show' lines.


### RA-market-12. Most headline results of the market layer have no consumer

*dead_code, impact medium, confidence high, ~4901 lines.*  
Locations: Volatile_Market.thy:46 relative_arbitrage_prob_pos; Optimal_Exit_Time.thy:222 ball_relative_arbitrage, :293 optimal_exit_time_value, :53 horizon_volatile_market (alias locale); Brownian_Market.thy:173 sufficiently_volatile_market_nonvacuous, :180 interpretation BM2; Ito_Market.thy:733 stopped_expected_time_bound (and all three ito_* locales); Value_Function_Market.thy:54 mkt_exit_vals_nonempty, :185 mkt_exit_vals_mono, :202 val_fn_mono; Exit_Time_Semicontinuity.thy:1937 stopped_val_fn_le_law_sup, :2598 clause_one_law_level, :2394 mkt_law_closure_increment_event, :2485 mkt_law_closure_sq_increment_event; Value_Function_Uniqueness.thy:22 theorem_1_1_ball_fragment; Exit_Class_Limits.thy:72 stopped_market_acov_leaves_sconstraint

Each name occurs only at its own statement (grep -rnw excluding prose). Through them, every other lemma of the cluster is ultimately unused.

Evidence: Non-prose occurrence counts are 1 for: relative_arbitrage_prob_pos, optimal_exit_time_value, BM2, stopped_expected_time_bound, clause_one_law_level, mkt_law_closure_increment_event, mkt_law_closure_sq_increment_event, val_fn_mono, mkt_exit_vals_nonempty, ball_relative_arbitrage. sufficiently_volatile_market_nonvacuous has 2 (the theorem and the BM2 interpretation that applies it, itself unused); stopped_val_fn_le_law_sup has 2 (its only use is in clause_one_law_level).

Suggested action: Delete with the layer. If a markets session is kept, these become its deliverables and should be named as such in its ROOT.


### RA-market-13. Import hygiene: unused or over-broad imports serialise the market chain onto the class chain's critical path

*build_time, impact medium, confidence medium, ~20 lines.*  
Locations: Path_Tightness_Market.thy:4-9 (imports Ito_Market, unused; Path_Law_Sampling, where only Pair_Path_Space is needed); Exit_Time_Semicontinuity.thy:4-10 (Path_Law_Sampling, where only Pair_Path_Space is needed; Value_Function_Market, only for sufficiently_volatile_market_mono_K); Ito_Market.thy:6 (Wiener_Measure.Vector_Brownian_Martingales; nothing used except prose); Value_Function_Market.thy:4 (Brownian_Optimal_Boundary → Optimal_Exit_Time; uses only Brownian_boundary_market); Exit_Class_Limits.thy:5 (Exit_Time_Semicontinuity); Relative_Arbitrage/ROOT (Volatile_Market and Optimal_Exit_Time interleaved among the operator theories; description lists no market layer)

- Exit_Time_Semicontinuity and Path_Tightness_Market use only psd_diag_nonneg, vshift_path_law, vshift_sup_usc_of_seq_compact and path_laws_convergent_subsequence_market from the path toolkit, all in Pair_Path_Space. They nevertheless import Path_Law_Sampling, the top of the toolkit.
- Because Exit_Class_Limits imports Exit_Time_Semicontinuity, the 2,634-line ETS and the serial chain behind it gate Exit_Class_Limits, Tightness, Shift, Witness and everything after.
- Optimal_Exit_Time sits on that path without any of its content being used.

Evidence: Name-level grep of the Pair_Path_Laws..Path_Law_Sampling lemma names in ETS and PTM → none. From Pair_Path_Space they use psd_diag_nonneg, vshift_path_law, vshift_sup_usc_of_seq_compact and path_laws_convergent_subsequence_market.

Suggested action: Moot after decoupling (first finding). If the markets are kept in a separate session, import Pair_Path_Space instead of Path_Law_Sampling, drop Ito_Market from PTM's imports, and make Value_Function_Market import Brownian_Market only.


### RA-market-14. 'Lemma 2.1' is misattributed for the exit-time bound, which is the first half of Example 3.1

*documentation, impact low, confidence high, ~9 lines.*  
Locations: Ito_Market.thy:276, :730; Brownian_Market.thy:203; Exit_Time_Semicontinuity.thy:1049, :2586, :2629; Volatile_Market.thy:142 ('Lemma 2.1 / Ky Fan'); Exit_Class_Witness.thy:928 and text before exit_class_sq_norm_mean_ge (outside cluster)

The paper's Lemma 2.1 (EM_final_paper.tex:266) is the convex-hull lemma. The estimate E[τ_K] ≤ (r²-|x|²)/(n-k) is proved inside Example 3.1 (lines 557-569), and trace ≥ n-k is the m = n case of (1.5).

Evidence: Ito_Market:276 'the exit-time bound of Lemma 2.1, which is SV.expected_stopped_time_bound'. ETS:2586 'the exit-time bound of Lemma 2.1 at the origin'.

Suggested action: Replace with 'the first half of Example 3.1' (or 'the m = n case of Eq. (1.5)' for the trace bound).


### RA-market-15. Orphan, empty and stale text blocks left by earlier moves

*documentation, impact low, confidence high, ~180 lines.*  
Locations: Value_Function_Market.thy:25-36 (empty section 'The essential infimum of a nonnegative random time' plus 11 blank lines); Value_Function_Market.thy:10-24 (claims ess_inf_time_le_nn_integral is proved here; it is Continuous_Time_Martingales/Essential_Infimum.thy:122); Value_Function_Market.thy:115-117 (claims val_fn_mono is 'used repeatedly by Section 2's dynamic programming': it is unused; 'fourteen assumptions': the locale has 19); Value_Function_Market.thy:209-231 (section with three texts and no lemmas: finiteness, vanishing off K, Lemma 5.3); Brownian_Market.thy:186-207 (three texts promising an unconditional 'expected squared norm 2' fact and an ito_const_horizon_market instance; neither exists, and Brownian_Market does not even import Ito_Market); Ito_Market.thy:29-31 (empty section), :274-280 (blank lines), :738-740 (pointer); Exit_Time_Semicontinuity.thy:21-23 (stale 'Equicontinuity.usc_sup_over_compact', now Semicontinuous_Analysis/Berge.thy:34; 'a separate leaf', but two theories import it); Exit_Time_Semicontinuity.thy:25-58 (three empty subsections plus 15 blank lines); Exit_Time_Semicontinuity.thy:1888-1889 (orphan 'matching lower bound' text), :2625-2630 (empty subsection); Exit_Time_Semicontinuity.thy:1971-1972, :2391-2392, :2587-2590 (refer to a 'canonical-market construction' that does not exist); Exit_Time_Semicontinuity.thy:223, 291, 486, 1124, 1963, 2198 ('X lives in Y' pointers; 275 such pointers repository-wide); Path_Tightness_Market.thy:12-16 (blank); Pair_Path_Space.thy:110-122 and Pair_Path_Laws.thy:16-31 (texts describing Path_Tightness_Market/Exit_Time_Semicontinuity content, placed in the wrong theories)

Several sections now have headers but no content, and several text blocks describe lemmas that moved, were deleted, or never existed.

Evidence: grep 'lives in|live in' --include=*.thy | wc -l → 275. grep -rn usc_sup_over_compact → only Semicontinuous_Analysis/Berge.thy:34, :454. grep val_fn_mono → definition only. grep ito_const_horizon_market → no interpretation anywhere.

Suggested action: Delete with the market layer. Repository-wide, delete all 'X lives in Y' pointer texts and empty sections in one mechanical pass.


### RA-market-16. Paper-free library sessions carry prose about this cluster, much of it stale

*documentation, impact low, confidence high, ~60 lines.*  
Locations: Semicontinuous_Analysis/Berge.thy:130 ('Exit_Time_Semicontinuity.etime_shift_box'; it is in Relative_Arbitrage/Pair_Path_Space.thy:615); Continuous_Path_Spaces/Path_Space.thy:955 ('Value_Function_Market.ess_inf_time_ge_iff_measure'; it is in Essential_Infimum.thy:193); Continuous_Path_Spaces/Path_Exit_Times.thy:1682 ('ess_inf_time_mono lives in Value_Function_Market'; it is in Essential_Infimum.thy:234); Continuous_Time_Martingales/Martingale_Algebra.thy:563 ('Ito_Market.martingale_vecI'; it is Martingale_Algebra.thy:500); Wiener_Measure/Continuous_Brownian_Motion.thy:17 ('bm_paths of Brownian_Market'; it is in Product_Brownian_Motion.thy:202), :143; Wiener_Measure/Vector_Brownian_Martingales.thy:327-333 (says the instantiation is in Continuous_Brownian_Motion; it is in Relative_Arbitrage.Brownian_Market), :924-929 (asserts an Ito_Market instantiation that exists nowhere); Wiener_Measure/Product_Brownian_Motion.thy:15-21; Continuous_Time_Martingales/Integrability_Criteria.thy:318-322 (market text sitting above set_integral_at_origin); Continuous_Time_Martingales/{Moment_Bounds:19, Sampled_Quadratic_Variation:25, Sampled_Martingale:91, Stopping_Times:14,22, Quadratic_Variation:29, Time_Discretisation:29, Optional_Sampling:467, Modification_Transfer:15,520, Essential_Infimum:272}; Continuous_Path_Spaces/Path_Tightness.thy:2896, :2926-2935 (header text for an adapter that lives in Pair_Path_Space:49); Relative_Arbitrage/Exit_Class_Shift.thy:294, Exit_Class_Limits.thy:83-84, :296 (attribute to Exit_Time_Semicontinuity lemmas that live in Pair_Path_Space, Path_Tightness or Martingale_Algebra)

Sessions advertised as paper-free name the paper session's locales (sufficiently_volatile_market, ito_volatile_market, ito_const_horizon_market) and theories (Volatile_Market, Ito_Market, Brownian_Market, Value_Function_Market, Exit_Time_Semicontinuity). Many of these references point to the wrong theory.

Evidence: grep -rn -E 'sufficiently_volatile|ito_volatile|ito_const_horizon|Volatile_Market|Ito_Market|Brownian_Market|Value_Function_Market|Exit_Time_Semicontinuity|market' over the six library sessions → the listed hits. The definition sites were checked by grep of the lemma headers.

Suggested action: Rewrite each as library-internal motivation without naming the paper session, or delete. Fix the 7 stale attributions now, whatever happens to the market layer.


### RA-market-17. Facts about mat 1 and constant stopping times are each proved three times

*clone, impact low, confidence high, ~90 lines.*  
Locations: Brownian_Market.thy:43-64 (psd1, elb, eub for mat 1); Exit_Time_Semicontinuity.thy:344-360 (psd1, elb, eub for mat 1, verbatim); Exit_Class.thy:365-391 mat_1_in_sconstraint (eigen_ub part again), Pair_Path_Laws.thy:33 psd_mat_1; Brownian_Market.thy:138-160, Ito_Market.thy:706-722, Exit_Time_Semicontinuity.thy:433-440 ('{ω ∈ space M. c ≤ s} ∈ sets (F s)' for a constant horizon)

psd (mat 1), eigen_lb (mat 1) (n-k) and eigen_ub (mat 1) L for 1 ≤ L are proved inline several times. 'A constant time is a stopping time' is proved by the same case split three times.

Evidence: Brownian_Market.thy:47-57 and ETS:346-353 are identical apart from 'n versus 'm. Brownian_Market.thy:144-158 and Ito_Market.thy:710-721 are identical ('proof (cases "c ≤ s") ... sets.top ... sets.empty_sets ... by metis').

Suggested action: Add psd_mat_1, eigen_lb_mat_1 and eigen_ub_mat_1 to Curvature_Operator (psd_mat_1 itself to Symmetric_Matrix_Spectra). Add filtered_measure.const_stopping_time to Continuous_Time_Martingales/Stopping_Times. Or delete with the layer.


### RA-market-18. Several cluster proofs re-derive facts that HOL, the AFP or a lower session already provides

*library_duplicate, impact low, confidence high, ~110 lines.*  
Locations: Volatile_Market.thy:220-234 x0_in_K and Optimal_Exit_Time.thy:255-269 (AE False ⟹ False via AE_E/emeasure_mono); Optimal_Exit_Time.thy:206-215 and Exit_Time_Semicontinuity.thy:1472-1481 (set_lebesgue_integral over {0..0} = 0); Optimal_Exit_Time.thy:99-102 X_meas_M; Ito_Market.thy:611-635 Z_expectation_const; Optimal_Exit_Time.thy:30-44 borel_measurable_ball_v

- The AE-False contradictions are HOL-Probability Probability_Measure.thy:113 prob_space.AE_False / :129 AE_const [simp]; each 15-line proof becomes 'using ... by simp'.
- The {0..0} integral is Continuous_Time_Martingales/Integrability_Criteria.thy:308 set_integral_lborel_singleton [simp]; Ito_Market.thy:64-66 already gets it 'by simp'.
- X_meas_M is the AFP Martingales/Stochastic_Process.thy:16 locale fact random_variable, which ETS uses as sv.random_variable.
- Z_expectation_const is Continuous_Path_Spaces/Increment_Moments.thy:26 martingale_expectation_eq, a lower session and the same proof.
- borel_measurable_ball_v re-proves Ball_Solution.thy:31 continuous_on_ball_v with the same case split.

Evidence: Lemma statements quoted in the locations. Increment_Moments.thy:26-44 and Ito_Market.thy:615-634 both use 'space M ∈ sets (F 0)', set_integral_eq and set_integral_space.

Suggested action: Cite the library lemmas. Move continuous_on_ball_v to Curvature_Operator. Move martingale_expectation_eq into Continuous_Time_Martingales, since it is pure martingale theory.


### RA-market-19. Pair-free and paper-light lemmas sit in market theories, and a market adapter sits in Pair_Path_Space

*misplacement, impact low, confidence high, ~120 lines.*  
Locations: Exit_Time_Semicontinuity.thy:2592 ball_v_le → Curvature_Operator (next to ball_v_nonneg :215); Optimal_Exit_Time.thy:30 borel_measurable_ball_v → Curvature_Operator (with continuous_on_ball_v from Ball_Solution:31); Volatile_Market.thy:145 trace_bound_pointwise, Ito_Market.thy:281 trace_le_eigen_ub, Path_Tightness_Market.thy:17 eigen_ub_diag → Curvature_Operator; Relative_Arbitrage/Pair_Path_Space.thy:49-102 path_laws_convergent_subsequence_market (pair-free, used only by Path_Tightness_Market:318) → Continuous_Path_Spaces/Stopped_Localization (its header text is already at Path_Tightness.thy:2926-2935) or delete; Relative_Arbitrage/Pair_Path_Space.thy:448 psd_diag_nonneg → Symmetric_Matrix_Spectra; Volatile_Market.thy:39-69 relative_arbitrage (paper Definition 1.1, independent of the locale; only meaningful in a markets session)

These statements mention nothing of their own theory, or nothing of the paper. ball_v_le and borel_measurable_ball_v mention only ball_v. The trace and diagonal bounds mention only eigen_lb/eigen_ub. The market adapter in Pair_Path_Space has a statement of type real^'m with no pair path and no paper constant.

Evidence: Statements quoted at the locations. Path_Tightness.thy:2926 'subsection ‹A convergent subsequence of path laws, in the vector case›' contains only text, whereas Pair_Path_Space.thy:49 holds the corollary.

Suggested action: Move as indicated. path_laws_convergent_subsequence_market can simply be deleted with the market layer.


### RA-market-20. Some hypotheses are unused or derivable

*generalisation, impact low, confidence medium, ~40 lines.*  
Locations: Optimal_Exit_Time.thy:74-76 assumption compensator_meas of ball_gradient_strategy; Optimal_Exit_Time.thy:99-114 X_meas_M, sint_meas; :30-44 borel_measurable_ball_v; Path_Tightness_Market.thy:43-44 hypothesis aint; Exit_Time_Semicontinuity.thy:73-74 and :1917-1918 (5th clause of mkt_law_witness / stopped_market); Exit_Class.thy:133-136 psd_eigen_ub_diag: psd hypothesis for the upper conclusion

- compensator_meas serves only sint_meas. sint_meas, X_meas_M and borel_measurable_ball_v serve only each other: ball_relative_arbitrage uses no measurability, and Optimal_Exit_Time has no 'measurable' method call after line 114. All four can go.
- Pathwise integrability of the diagonal entries follows from the other hypotheses: on [0,tau], psd gives 0 ≤ a_ll ≤ trace a and acov_trace_integrable bounds it; after tau, astop gives acov = 0; acov_time_measurable gives measurability. Bochner integrable_bound then applies. So aint is redundant in market_path_laws_convergent_subsequence, mkt_law_witness and stopped_market.
- The upper diagonal bound needs only eigen_ub (Path_Tightness_Market.eigen_ub_diag proves it without psd).

Evidence: grep -n 'measurable|sint_meas|X_meas_M|compensator_meas' Optimal_Exit_Time.thy → only lines 30-113. Volatile_Market.thy:104 acov_psd, :113 acov_trace_integrable, :110 acov_time_measurable; ETS:72 astop clause.

Suggested action: Drop compensator_meas and the three measurability lemmas. Derive aint as a lemma of stopped markets (if the layer is kept). Split psd_eigen_ub_diag into a nonnegativity lemma (psd) and eigen_ub_diag (no psd).


### RA-market-21. Local proof bloat in the cluster

*simplification, impact low, confidence medium, ~150 lines.*  
Locations: Exit_Time_Semicontinuity.thy:142-166 (five nested SOME definitions MM/FF/XX/aa/tt); Path_Tightness_Market.thy:59-102 (good-event construction; 10 repeated 'interpret sv: sufficiently_volatile_market "MM i" ...'); Path_Tightness_Market.thy:140-152, Exit_Time_Semicontinuity.thy:513-524, :981-991, Ito_Market.thy:365-384 (inline copies of mkt_law_witness_bound, which is only stated later at ETS:1099); Volatile_Market.thy:246-251, :273-281; Ito_Market.thy:378-383; ETS:588-593, :1496-1500 ('norm x ≤ r ⟹ x • x ≤ r²'); Ito_Market.thy:443-450 ('measure lborel {0..s} = s' in 8 lines); Optimal_Exit_Time.thy:92-97 ito_formula_quadratic (a restatement of sint_def), :177-178 (re-derives the locale lemma c_pos)

- One application of choice to a tuple-valued witness function replaces 25 lines of nested SOME.
- HOL's AE_E3 (Measure_Space.thy:1087) gives the full-measure good set directly.
- The per-i facts the 10 interpretations provide (prob_space, random_variable, X_paths_cont, coord_Z_martingale) can be stated once.
- mkt_law_witness_bound should come first and be reused.
- A one-line lemma 'norm x ≤ r ⟹ x • x ≤ r²' would serve 5 sites.

Evidence: Code at the cited lines.

Suggested action: Apply only if the code is kept; otherwise moot.


## RA-class

This cluster formalises the class P_x of Eq. (1.7) as laws of the pair (X, Y=<X>) on C([0,T]) (`exit_class k L T x`, Exit_Class.thy:224) and the capped value function of Eq. (1.6) (`exit_val`, :743). It also proves the structural results the paper uses from Section 2.
- Exit_Class: the constraint set `sconstraint k L` (convex, closed, bounded, norm bound n*L, diagonal bound, mat 1 in it), the projections and moment bounds as specialisations of the generic `covariation_class` (Pair_Path_Laws:4038), and the closedness under weak limits of the start clause and the difference-quotient clause.
- Covariation_Density: proves that the difference-quotient reading and the a.e.-density reading of the constraint agree (`dq_iff_density`). The theory is entirely generic and has no connection to the class.
- Exit_Class_Limits: Lemma 2.3 (`exit_class_weak_closed`). The X-martingale clause goes through a weak limit by test functions. The compensated clause needs a uniform fourth moment, obtained by localisation (`ploc`), optional stopping and Fatou (`exit_class_fourth_moment`).
- Exit_Class_Tightness: Lemma 2.2 through Kolmogorov dyadic charges (`tight_on_set_paper_pair_class`) and sequential compactness (`exit_class_convergent_subsequence`).
- Exit_Class_Shift: shift equivariance (`exit_class_pshift`, `exit_class_shift_image`) and upper semicontinuity of `exit_val` via Berge.
- Exit_Class_Witness: about 520 lines of Brownian-motion martingale facts, the Brownian witness `bmpair` (nonemptiness), and the value bounds `exit_val_le_T`, `exit_val_le_ball_bound` and `exit_val_boundary_zero`.
- Exit_Class_Pasting: closure under `pcut`, `pglue_law` (fixed continuation) and `kglue_law` (countably indexed continuation), plus horizon monotonicity.
- Exit_Class_Optimizer: attainment of the supremum, compactness of the class in the Levy-Prokhorov metric, a measurable optimiser (Bertsekas-Shreve 7.33) and the Giry-monad kernel glue `exit_class_kglue_law'`.

The organisation is a strict linear import chain: Exit_Class -> Limits -> Tightness -> Shift -> Witness -> Pasting -> Optimizer. Limits additionally pulls in the whole market stack through Exit_Time_Semicontinuity.

Main problems found:
1. About 1 300 lines of clones:
   - the X-martingale weak-limit chain in Limits duplicates the generic F-chain in Pair_Path_Laws;
   - the pglue and kglue martingale proofs repeat each other's set-up;
   - the rational-reduction argument appears three times;
   - `exit_val_boundary_zero` duplicates `exit_val_le_ball_bound`, and `exit_val_attained` duplicates `exit_val_measurable_selector`;
   - `exit_class_weak_limit_prob_space` duplicates `weak_conv_on_prob_space`.
2. Library re-proofs: `Lipschitz_imp_absolutely_continuous` (HOL-Analysis) and `indep_vars_PiM_coordinate` (AFP Kolmogorov_Chentsov).
3. Misplaced paper-free material: the Brownian lemmas belong in Wiener_Measure, all of Covariation_Density belongs in Continuous_Path_Spaces, and the matrix facts belong with eigen_ub and Pi_constraint.
4. Much stale prose left behind by earlier moves.

On G11: in this cluster the class is uniform in k everywhere except the value bounds. The only properties of S that are used are: closed, convex, a norm bound, a diagonal bound, `mat 1 : S`, and a trace lower bound. The abstraction is therefore mechanical here. It would also restore the paper's generality of Lemmas 2.2 and 2.3 (an arbitrary bounded, respectively compact convex, S contained in the psd matrices).


### RA-class-1. X-martingale weak-limit chain in Exit_Class_Limits re-proves the generic F-chain of Pair_Path_Laws

*clone, impact high, confidence high, ~510 lines.*  
Locations: Relative_Arbitrage/Exit_Class_Limits.thy:121 exit_class_martingale_test; Relative_Arbitrage/Exit_Class_Limits.thy:207 exit_class_martingale_test_limit; Relative_Arbitrage/Exit_Class_Limits.thy:305 exit_class_limit_sq_nn; Relative_Arbitrage/Exit_Class_Limits.thy:322 exit_class_limit_increment_integrable; Relative_Arbitrage/Exit_Class_Limits.thy:350 exit_class_martingale_event_limit; Relative_Arbitrage/Exit_Class_Limits.thy:577 exit_class_coord_martingale_limit; Relative_Arbitrage/Pair_Path_Laws.thy:2462 martingale_test_F; Relative_Arbitrage/Pair_Path_Laws.thy:2515 martingale_test_F_limit; Relative_Arbitrage/Pair_Path_Laws.thy:2777 martingale_event_F_limit; Relative_Arbitrage/Pair_Path_Laws.thy:3126 martingale_F_limit

The six Limits lemmas are the generic chain specialised to F = (λp. fst p $ i), copied line by line: same `let`s, the same prod_int / int_t / int_s / eqts blocks, and the same 214-line positive/negative density argument through metric_measure_eqI_bounded_cts. The generic chain is already used once in Limits (line 1770, compensated entry). The X clause does not use it. The section text at Limits:1510-1514 even claims the chain is done 'once, parametric in F, and instantiates it twice'.

Evidence: Pair_Path_Laws:2462 `theorem martingale_test_F ... mgF: martingale N ... (λu ω. F (ω (min u T))) ... shows (∫ω. h (restrict ω {0..s}) * (F (ω t) - F (ω s)) ∂N) = 0`. Limits:121 is the same statement at F = fst _ $ i with an identical proof body. grep shows that martingale_test_F, martingale_test_F_limit and martingale_event_F_limit are used only inside Pair_Path_Laws, and martingale_F_limit only at Limits:1770.

Suggested action: Prove exit_class_coord_martingale_limit as `martingale_F_limit[where F="λp. fst p $ i", OF T _ exit_class_prob[OF mem] exit_class_sets[OF mem] exit_class_coord_martingale[OF mem] wc prob setsQ C0 exit_class_sq_nn_bound[OF T L mem]]`, with continuity from continuous_intros or fst_coord. Delete the other five lemmas. Then check whether the coordinate-only helpers pair_test_integrable (Pair_Path_Laws:98), pair_test_sq_bound, pair_test_functional_cont, pair_test_measurable and pair_law_limit_sq_nn_bound (Pair_Path_Laws:170) have become dead.


### RA-class-2. exit_class_weak_limit_prob_space re-derives weak_conv_on_prob_space; prob/setsQ hypotheses of every *_limit lemma are redundant

*simplification, impact high, confidence high, ~110 lines.*  
Locations: Relative_Arbitrage/Exit_Class_Tightness.thy:308-376 exit_class_weak_limit_prob_space; Relative_Arbitrage/Exit_Class_Tightness.thy:414-416 (only use); Continuous_Path_Spaces/Path_Space.thy:918 weak_conv_on_prob_space; Continuous_Path_Spaces/Path_Tightness.thy:2504 weak_conv_on_prob_limit; Relative_Arbitrage/Exit_Class_Limits.thy:1820 exit_class_weak_closed (prob, setsQ); Relative_Arbitrage/Exit_Class.thy:632,662 exit_class_start_limit, exit_class_diffquot_limit

The 70-line proof uses tightness, portmanteau and an epsilon argument to show that the weak limit has mass 1. weak_conv_on itself already gives convergence of ∫1, and the lower library lemma weak_conv_on_prob_space says exactly this. Exit_Class_Optimizer.thy:170 already calls it. Also, weak_conv_on_def yields `sets Q = sets (borel_of X)`, and `path_borel T` is an abbreviation for `borel_of (mtopology_of (path_metric T))`. So the `prob` and `setsQ` hypotheses of exit_class_weak_closed, exit_class_limit_three_clauses, exit_class_start_limit, exit_class_diffquot_limit, exit_class_martingale_*_limit, exit_class_X/comp_martingale_limit and exit_class_comp_entry_martingale_limit follow from `wc` and `mem`. Two side findings: weak_conv_on_prob_space and weak_conv_on_prob_limit are themselves identical lemmas inside Continuous_Path_Spaces, and exit_class_fourth_moment_integrable at Tightness:27 re-derives setsQ from Q.

Evidence: Path_Space.thy:918 `lemma weak_conv_on_prob_space: assumes wc: weak_conv_on Ni N sequentially X and P: ∧i. prob_space (Ni i) shows prob_space N`. Path_Tightness.thy:2504 weak_conv_on_prob_limit has the same statement. Path_Space.thy:40 `abbreviation path_borel T ≡ borel_of (mtopology_of (path_metric T))`. AFP General_Weak_Convergence.thy:85 weak_conv_on_def includes `sets N = sets (borel_of X) ∧ finite_measure N`.

Suggested action: Delete exit_class_weak_limit_prob_space and use `weak_conv_on_prob_space[OF wcN exit_class_prob[OF memA]]`. Drop `prob`/`setsQ` from the limit lemmas, or derive them inside via one helper `weak_conv_path_limit_basics`. Delete one of weak_conv_on_prob_space / weak_conv_on_prob_limit.


### RA-class-3. G11 assessment: in this cluster the class needs only six properties of S; exit_class duplicates covariation_class_def and 28 proofs unfold it

*generalisation, impact high, confidence high, ~600 lines.*  
Locations: Relative_Arbitrage/Exit_Class.thy:224-240 exit_class_def vs Relative_Arbitrage/Pair_Path_Laws.thy:4038-4054 covariation_class_def; Relative_Arbitrage/Exit_Class_Limits.thy:107 exit_class_X_martingale; Relative_Arbitrage/Exit_Class_Pasting.thy (15× 'unfolding exit_class_def'); Relative_Arbitrage/Exit_Class_Limits.thy (4×), Exit_Class_Shift.thy (3×), Exit_Class_Witness.thy (3×), Exit_Class.thy (2×), Exit_Class_Tightness.thy (1×)

I checked which S-facts each theory uses:
- Limits: closed (diffquot_limit), norm bound n*L, diagonal bound L.
- Tightness: norm bound and diagonal bound.
- Shift: nothing.
- Witness: mat 1 ∈ S, closed, trace >= n-k (only in the value bounds).
- Pasting: convex (pglue_diffquot), closed, norm bound.
- Optimizer: the above plus nonemptiness.

The parameter k is unused in Limits, Tightness, Shift, Pasting and Optimizer. The only `sconstraint_def` unfold outside the interface is sconstraint_trace_ge (Witness:937), which is itself an interface fact. The definition of exit_class repeats the five clauses of covariation_class verbatim instead of being defined as `covariation_class (sconstraint k L) T x`. 28 proofs in the cluster (56 repo-wide) do `using Q unfolding exit_class_def by blast` to extract the start, diffquot or X-martingale clause instead of using covariation_class_start / _diffquot / _martingale_fst. Membership proofs (exit_class_pshift, exit_class_pcut, exit_class_pglue_law, exit_class_kglue_law, bmpair_law_in_paper_pair_class, exit_class_weak_closed) unfold the definition plus CollectI/conjI instead of using covariation_classI. exit_class_X_martingale is a projection, but it sits in Limits with 24 consumers.

Evidence: grep -c 'unfolding exit_class_def': Pasting 15, Limits 4, Shift 3, Witness 3, Exit_Class 2, Tightness 1; repo total 56. Exit_Class.thy:248 `exit_class k L T x = covariation_class (sconstraint k L) T x by (simp add: exit_class_def covariation_class_def)`. The Statement session never mentions exit_class (grep), so redefining it is invisible to the acceptance test.

Suggested action: Steps, in this order:
1. Define `exit_class k L T x = covariation_class (sconstraint k L) T x` and add projections exit_class_start, exit_class_diffquot and exit_class_X_martingale to Exit_Class; replace the 56 unfoldings.
2. Introduce `locale covariation_constraint = fixes S assumes closed S, convex S, S ⊆ {a. psd a}, bounded S` (the paper's Lemma 2.2/2.3 hypotheses). Derive the norm bound B and the diagonal bound 0 <= a_ii <= B.
3. Move Limits, Tightness, Shift(pshift), Pasting(pcut/pglue/kglue) and the compactness part of Optimizer into the locale.
4. Interpret it at sconstraint k L (needs 0 <= L).
5. Keep mat_1_in_sconstraint and sconstraint_trace_ge at the paper level.


### RA-class-4. About 520 lines of Brownian-motion theory in Exit_Class_Witness belong in Wiener_Measure

*misplacement, impact high, confidence high, ~520 lines.*  
Locations: Relative_Arbitrage/Exit_Class_Witness.thy:23 bm_coordinates_indep; Relative_Arbitrage/Exit_Class_Witness.thy:50 bm_increment_coord_indep; Relative_Arbitrage/Exit_Class_Witness.thy:78 bm_increment_cross; Relative_Arbitrage/Exit_Class_Witness.thy:111 bm_meas_increment_fun_indep_var; Relative_Arbitrage/Exit_Class_Witness.thy:200 bm_cross_set_integral_zero; Relative_Arbitrage/Exit_Class_Witness.thy:251 bm_cross_increment_set_integral_zero; Relative_Arbitrage/Exit_Class_Witness.thy:331 bmX_coord_measurable_F; Relative_Arbitrage/Exit_Class_Witness.thy:346 bmX_cross_integrable; Relative_Arbitrage/Exit_Class_Witness.thy:384 martingale_bm_cross; Relative_Arbitrage/Exit_Class_Witness.thy:446 martingale_cbm_cross; Relative_Arbitrage/Exit_Class_Witness.thy:495 martingale_cbm_outerp

These lemmas are about bm_paths, bmX and cbmX only, and use only Wiener_Measure (Product_Brownian_Motion, Vector_Brownian_Martingales, Continuous_Brownian_Motion) and Continuous_Time_Martingales (martingale_matI, martingale_of_modification_gen, adapted_of_natural_filtration). They are the off-diagonal companions of martingale_bm_coord_square (Vector_Brownian_Martingales:936) and martingale_cbm_coord_square (Continuous_Brownian_Motion:221). The Wiener_Measure ROOT advertises 'the compensated square of the norm and of each coordinate'; the cross term completes it. martingale_cbm_outerp is also used by Value_Function_Euler_Construction. It mentions `outerp` (defined in Relative_Arbitrage.Pair_Path_Space:718), so in Wiener_Measure it should be stated with (χ i j. B_i B_j) or with outer_prod. The prose cites 'Brownian_Market.bm_meas_increment_indep_var' (107), 'Brownian_Market.bm_set_integral_coord_sq_eq' (196), 'Brownian_Market.bm_meas_increment_product_zero' (248) and 'BMC ... present in Brownian_Market' (31). All of these live in Wiener_Measure.

Evidence: Name-level grep: every non-local lemma they use is in Wiener_Measure/* or Continuous_Time_Martingales/* (e.g. bm_filtration_increment_indep in Product_Brownian_Motion, bm_meas_increment_product_zero in Vector_Brownian_Martingales, cbmX_ae_eq in Continuous_Brownian_Motion).

Suggested action: Move lines 23-441 into Wiener_Measure.Vector_Brownian_Martingales and 446-537 into Wiener_Measure.Continuous_Brownian_Motion (restating martingale_cbm_outerp without outerp, with an outerp bridge in the paper session). Fix the cited theory names.


### RA-class-5. pglue and kglue martingale proofs repeat one another's set-up; pglue_law is a special case of kglue_law

*clone, impact high, confidence medium, ~520 lines.*  
Locations: Relative_Arbitrage/Exit_Class_Pasting.thy:477-676 pglue_law_X_martingale; Relative_Arbitrage/Exit_Class_Pasting.thy:680-936 pglue_law_comp_martingale; Relative_Arbitrage/Exit_Class_Pasting.thy:1298-1632 kglue_law_X_martingale; Relative_Arbitrage/Exit_Class_Pasting.thy:1828-2411 kglue_law_comp_martingale; Relative_Arbitrage/Exit_Class_Pasting.thy:296 pglue_law_start / :1123 kglue_law_start; Relative_Arbitrage/Exit_Class_Pasting.thy:331 pglue_law_diffquot / :1161 kglue_law_diffquot

The pglue X and compensated proofs share about 110 identical lines: the s1_0/s1_mono/s2_0/s2_mono clocks, mQ, mR, FQ, FR, FFm, evQ, evR, the 35-line gadap case split, start and Zm. The kglue X and compensated proofs share about 150: mQ0, mQ, FQf, NmQ, mZ, mBj, FSf, evQ, Nidx, evK, gadap, the intSj/istep, bndSj/bstep and secBnd/bBS integrability bounds, and Zm. The start and diffquot lemmas for pglue and kglue are the same proof with AE_pglue_law replaced by AE_kglue_law. Finally, pglue_law r T Q R should equal kglue_law r T (λ_. 0) Q (λ_. R): push Q ⊗ Π_M R forward along (ω,f) ↦ (ω, f 0), using distr_PiM_component and the distr_pair_snd of Martingale_Transfer. If so, exit_class_pglue_law, used by exit_val_horizon_mono and Exit_Class_Infinite, becomes a corollary of exit_class_kglue_law.

Evidence: Side-by-side: Pasting:500-536 vs 705-756; :545-584 vs :803-840 (gadap, character-identical); :1336-1361 vs :1878-1903; :1439-1497 vs :2098-2152.

Suggested action: Factor `pglue_product_filtration` (clocks, FF, adaptedness of the glue, start) and `kglue_product_filtration` (plus continuation integrability bounds) lemmas. Prove the measure identity pglue_law = kglue_law at constant index and drop pglue_law_start/_diffquot/_X_martingale/_comp_martingale.


### RA-class-6. The class layer is serialised behind the market/Itô stack and is a strict 7-theory chain

*build_time, impact high, confidence medium, ~30 lines.*  
Locations: Relative_Arbitrage/Exit_Class_Limits.thy:5 (imports Exit_Time_Semicontinuity); Relative_Arbitrage/Exit_Class_Limits.thy:72 stopped_market_acov_leaves_sconstraint (only use of the market layer); Relative_Arbitrage/Exit_Class_Tightness.thy:5, Exit_Class_Shift.thy:5, Exit_Class_Witness.thy:5, Exit_Class_Pasting.thy:5, Exit_Class_Optimizer.thy:5

Exit_Time_Semicontinuity pulls in Path_Tightness_Market, Value_Function_Market, Brownian_Optimal_Boundary, Brownian_Market, Ito_Market, Volatile_Market and Optimal_Exit_Time. A name-level scan of every definition and lemma in those theories against the cluster finds only `stopped_market`, used in the dead lemma Limits:72. The Brownian facts the Witness needs come from Wiener_Measure. On top of that, the chain Exit_Class → Limits → Tightness → Shift → Witness → Pasting → Optimizer is linear, although:
- exit_class_pshift and exit_class_shift_image need only Exit_Class plus the X-martingale projection;
- the Witness (nonemptiness, value bounds) needs only Exit_Class plus Wiener_Measure;
- pcut, pglue and kglue need only Exit_Class.
Only USC (Shift), compactness (Optimizer) and exit_val_horizon_mono (pasting plus the witness) combine branches.

Evidence: Scan output: 'Exit_Time_Semicontinuity.stopped_market -> Exit_Class_Limits.thy' is the only hit from the market theories (Eigenvalue_Bound_Exact hits are prose words). Pair_Path_Laws:84 acont etc. are not used by the cluster.

Suggested action: Delete stopped_market_acov_leaves_sconstraint and import Wiener_Measure.Continuous_Brownian_Motion directly where needed. Reshape as a DAG: Exit_Class → {Class_Limits → Class_Tightness (compactness), Class_Shift (pshift), Class_Witness, Class_Pasting} → Class_Optimizer (USC, attainment, selector). This lets the class layer build in parallel with the market and operator layers.


### RA-class-7. Lemmas 2.2 and 2.3 are proved only for S = sconstraint k L, not for the paper's arbitrary bounded / compact convex S

*faithfulness, impact medium, confidence high, ~40 lines.*  
Locations: Relative_Arbitrage/Exit_Class_Tightness.thy:233 tight_on_set_paper_pair_class; Relative_Arbitrage/Exit_Class_Limits.thy:1820 exit_class_weak_closed; Relative_Arbitrage/Exit_Class_Optimizer.thy:113 exit_class_compactin_weak; Relative_Arbitrage/Exit_Class_Optimizer.thy:16 text

The paper states Lemma 2.2 for any bounded S ⊂ S^n_+ and Lemma 2.3 for any compact convex S ⊂ S^n_+ ('In particular, each P_x is ...'). The formal results are only the 'in particular' instance. This is enough for Theorem 1.1, but the lemma-level statements are strictly weaker than the paper's. The proofs only use closed, convex, norm-bounded and diagonal-bounded S (see the G11 finding), so the general form is within reach. Separately, Optimizer:16 calls exit_val 'the faithful rendering of Eq. (1.6)'. exit_val is the horizon-capped value over pair laws on C([0,T]). Its identification with the paper's v over P_x on C([0,∞)) is only made later, in Exit_Class_Infinite.iexit_val_eq_exit_val (787) and Exit_Class_Marginals.iexit_val_eq_xval (1300).

Evidence: EM_final_paper.tex:313-317 'If S ⊂ S^n_+ is bounded, then the set of continuous martingale laws ... is relatively compact'. :358-361 'If S ⊂ S^n_+ is a compact convex set, then ... is compact. In particular, each P_x is compact.'

Suggested action: State tightness and weak closedness for covariation_class S under the paper's hypotheses (see the G11 finding). Reword Optimizer:16 to point to the bridge theorems.


### RA-class-8. exit_val_boundary_zero is the |x| = r special case of exit_val_le_ball_bound, proved again in full

*clone, impact medium, confidence high, ~95 lines.*  
Locations: Relative_Arbitrage/Exit_Class_Witness.thy:1066-1165 exit_val_boundary_zero; Relative_Arbitrage/Exit_Class_Witness.thy:1175-1277 exit_val_le_ball_bound

Both proofs run the same argument: Sup_least, ccontr, c = enn2real e, t between, ae2 'fst (ω t) • fst (ω t) <= r*r', integrability, exit_class_sq_norm_mean_ge, contradiction. The ae2/ni/lo/hi blocks are textually identical. With K = cball 0 r and x•x = r*r, the ball bound gives exit_val <= ennreal 0. The text at 1170 itself says 'exit_val_boundary_zero is the case |x| = r'.

Evidence: exit_val_le_ball_bound: `assumes k < CARD('n), 0 <= T, 0 <= L, K ⊆ cball 0 r shows exit_val k L T K x <= ennreal ((r*r - x•x) / real (CARD('n) - k))`. exit_val_boundary_zero: `assumes k < CARD('n), 0 < T, 0 <= L, norm x = r shows exit_val k L T (cball 0 r) x = 0`.

Suggested action: Make exit_val_boundary_zero a corollary of exit_val_le_ball_bound[OF k _ L order_refl], about 5 lines; it can then also weaken 0 < T to 0 <= T. Optionally factor ae2 into a lemma 'ess_inf exit time > t implies X_t ∈ K a.s.'.


### RA-class-9. exit_val_attained follows from exit_val_measurable_selector; exit_class_compactin_weak re-proves compactness obtainable from sequential compactness

*clone, impact medium, confidence high, ~130 lines.*  
Locations: Relative_Arbitrage/Exit_Class_Optimizer.thy:31-96 exit_val_attained; Relative_Arbitrage/Exit_Class_Optimizer.thy:269 exit_val_measurable_selector; Relative_Arbitrage/Exit_Class_Optimizer.thy:113-178 exit_class_compactin_weak; Relative_Arbitrage/Exit_Class_Tightness.thy:383 exit_class_convergent_subsequence; Semicontinuous_Analysis/Berge.thy:281 compactin_of_seq_compact; Continuous_Path_Spaces/Path_Space.thy:1096 metrizable_weak_conv_path_topology

1. The selector's conclusions 3 and 4 at y = x give a member Q = pshift_law T x (S x) of exit_class k L T x with ess_inf_time Q ... = exit_val k L T K x. The hypotheses are the same (0 < T, 1 <= L, closed K). So exit_val_attained (66 lines, its own subsequence and usc argument) is a 5-line corollary.
2. The class's compactness is proved twice: tightness plus a Prokhorov subsequence (Tightness:383), and tightness plus tight_imp_relatively_compact plus closure (Optimizer:113, 66 lines). compactin_of_seq_compact turns the first into the second in a few lines; vshift_sup_usc_of_seq_compact (Pair_Path_Space) already does exactly that for vshift.
3. The LP-interpretation set-up (Optimizer:123-133 vs 213-222) and the 'class ⊆ topspace (weak_conv_topology)' block (144-152, 223-231, 405-413) are each written two or three times.

Evidence: exit_val_measurable_selector shows `∧y. pshift_law T y (S y) ∈ exit_class k L T y` and `∧y. ess_inf_time (pshift_law T y (S y)) (λω. pexit T K (λt. fst (ω t))) = exit_val k L T K y`. exit_val_attained shows `∃Q ∈ exit_class k L T x. ess_inf_time Q (...) = exit_val k L T K x`.

Suggested action: Derive exit_val_attained from the selector, or keep only the attainment and derive what is needed. Prove exit_class_compactin_weak as `compactin_of_seq_compact[OF metrizable_weak_conv_path_topology topC] exit_class_convergent_subsequence`. Move it into Tightness next to the convergent subsequence, and add one lemma exit_class_subset_weak_topspace.


### RA-class-10. Covariation_Density re-proves HOL-Analysis Lipschitz_imp_absolutely_continuous and parts of Rademacher; its 'not in the library' claim is false

*library_duplicate, impact medium, confidence high, ~110 lines.*  
Locations: Relative_Arbitrage/Covariation_Density.thy:27-69 lipschitz_imp_absolutely_continuous_on; /opt/Isabelle2026-RC3/src/HOL/Analysis/Absolute_Continuity.thy:859 Lipschitz_imp_absolutely_continuous; Relative_Arbitrage/Covariation_Density.thy:131-173 (inside vector_derivative_in_closed_set); Second_Order_Viscosity_Analysis/Rademacher.thy:343 dquot_tendsto_vector_derivative, :569 filterlim_inverse_Suc; Relative_Arbitrage/Covariation_Density.thy:193-230 (inside dq_imp_density); Continuous_Path_Spaces/Increment_Moments.thy:2276 diffquot_lipschitz; Second_Order_Viscosity_Analysis/Rademacher.thy:18 lipschitz_differentiable_ae_1d; Relative_Arbitrage/Covariation_Density.thy:20-22 text

1. lipschitz_imp_absolutely_continuous_on has literally the statement of HOL's Lipschitz_imp_absolutely_continuous (M in place of B). HOL's lemma is already used in this repository (Rademacher.thy:27, 680).
2. vector_derivative_in_closed_set spends about 40 lines showing that the difference quotients at 1/(n+1) converge to the derivative. That is dquot_tendsto_vector_derivative composed with filterlim_inverse_Suc.
3. dq_imp_density re-derives the Lipschitz bound (lip1/lip, about 30 lines; diffquot_lipschitz exists).
4. Its Lebesgue-differentiation-over-[0,n] step mirrors lipschitz_differentiable_ae_1d.
5. The header text says 'Neither of the two analytic steps the paper takes is available in the Isabelle distribution or in the AFP, so both are proved here'. Lipschitz ⇒ absolutely continuous is in HOL, and the FTC step is HOL's fundamental_theorem_of_calculus_absolutely_continuous, which the theory itself uses at line 267. Only integral_mean_in_convex and vector_derivative_in_closed_set are new.

Evidence: Absolute_Continuity.thy:859 `lemma Lipschitz_imp_absolutely_continuous: assumes ∧x y. x ∈ S ⟹ y ∈ S ⟹ norm (f x - f y) <= B * |x - y| shows absolutely_continuous_on S f`. Covariation_Density.thy:27 has the same statement with M.

Suggested action: Delete lipschitz_imp_absolutely_continuous_on and use the HOL lemma. Shorten vector_derivative_in_closed_set via dquot_tendsto_vector_derivative and the lip step via diffquot_lipschitz. Correct the header prose.


### RA-class-11. Covariation_Density is a paper-free real-analysis theory in the paper session, importing Exit_Class for nothing

*misplacement, impact medium, confidence high, ~299 lines.*  
Locations: Relative_Arbitrage/Covariation_Density.thy:4-6 (imports Exit_Class); Relative_Arbitrage/Covariation_Density.thy:179 dq_cond, :182 density_cond, :291 dq_iff_density; Relative_Arbitrage/Exit_Class_Marginals.thy:69 (only consumer); Continuous_Path_Spaces/Increment_Moments.thy:2185,2276,2325 diffquot_all_of_rational / diffquot_lipschitz / diffquot_all_of_rational_ge

Every statement is at `'a::euclidean_space` and mentions no constant of Relative_Arbitrage. The theory uses nothing from Exit_Class; its only consumer is Exit_Class_Marginals. Its natural home is beside the difference-quotient lemmas in Continuous_Path_Spaces.Increment_Moments, or a new Continuous_Path_Spaces.Difference_Quotients theory collecting diffquot_lipschitz, diffquot_all_of_rational(_ge), integral_mean_in_convex(_ae), vector_derivative_in_closed_set, dq_cond, density_cond and dq_iff_density. Its import of Exit_Class needlessly puts it behind the whole market stack in the build order.

Evidence: grep of Exit_Class constants in Covariation_Density.thy: no hits (exit_class 0, sconstraint 0). Uses: dq_iff_density only in Exit_Class_Marginals.thy:69.

Suggested action: Move the theory to Continuous_Path_Spaces (imports HOL-Analysis plus Increment_Moments) and remove it from the Relative_Arbitrage ROOT.


### RA-class-12. bm_coordinates_indep re-proves AFP indep_vars_PiM_coordinate (falsely claimed out of scope); bm_meas_increment_fun_indep_var duplicates bm_meas_increment_indep_var

*library_duplicate, impact medium, confidence high, ~110 lines.*  
Locations: Relative_Arbitrage/Exit_Class_Witness.thy:23-48 bm_coordinates_indep; /opt/afp/thys/Kolmogorov_Chentsov/Kolmogorov_Chentsov_Extras.thy:162 product_prob_space.indep_vars_PiM_coordinate; Wiener_Measure/Product_Brownian_Motion.thy:6 (imports Kolmogorov_Chentsov.Kolmogorov_Chentsov_Extras); Relative_Arbitrage/Exit_Class_Witness.thy:111-193 bm_meas_increment_fun_indep_var; Wiener_Measure/Vector_Brownian_Martingales.thy:349 bm_meas_increment_indep_var

1. The comment at Witness:27 says 'Kolmogorov_Chentsov_Extras.indep_vars_PiM_coordinate is not in scope here, so its six-line argument is repeated'. Product_Brownian_Motion imports Kolmogorov_Chentsov_Extras, and BMC is the product_prob_space interpretation at bm_paths' factors. So `BMC.indep_vars_PiM_coordinate[of UNIV]` plus `bm_paths_def` is the lemma.
2. bm_meas_increment_fun_indep_var is a verbatim generalisation of bm_meas_increment_indep_var: the same L/R sigma_sets blocks, with h(Δ) in place of Δ $ i. The library lemma is its instance h = (λv. v $ i).

Evidence: Kolmogorov_Chentsov_Extras.thy:162 `lemma (in product_prob_space) indep_vars_PiM_coordinate: assumes I ≠ {} shows prob_space.indep_vars (Π_M i∈I. M i) M (λx f. f x) I`, proved by the same distr_cong / PiM_cong / indep_vars_iff_distr_eq_PiM' steps.

Suggested action: Replace bm_coordinates_indep by the AFP lemma. Keep only the general bm_meas_increment_fun_indep_var in Vector_Brownian_Martingales and derive bm_meas_increment_indep_var from it.


### RA-class-13. Constraint-set facts duplicated across theories and scattered (psd_eigen_ub_diag, sconstraint_diag_le, sconstraint_trace_le)

*clone, impact medium, confidence high, ~60 lines.*  
Locations: Relative_Arbitrage/Exit_Class.thy:133-148 psd_eigen_ub_diag; Relative_Arbitrage/Pair_Path_Space.thy:448 psd_diag_nonneg; Relative_Arbitrage/Path_Tightness_Market.thy:17 eigen_ub_diag; Relative_Arbitrage/Exit_Class.thy:430 sconstraint_diag; Relative_Arbitrage/Value_Function_Euler_Construction.thy:897-912 sconstraint_diag_le; Relative_Arbitrage/Value_Function_Subsolution.thy:1823 sconstraint_trace_le, :1862 sconstraint_orth_feasible; Relative_Arbitrage/Exit_Class_Witness.thy:930 sconstraint_trace_ge

1. psd_eigen_ub_diag is psd_diag_nonneg (in scope, Pair_Path_Space) plus eigen_ub_diag. eigen_ub_diag is stranded in the market layer (Path_Tightness_Market), which Exit_Class does not import, so it was re-proved.
2. sconstraint_diag_le (Euler_Construction) re-proves sconstraint_diag(2), which is in scope, via axis1_inner and matvec_axis1.
3. sconstraint_trace_le derives the weaker bound trace <= n·(n·L) through the norm, while sconstraint_diag gives trace <= n·L directly.
4. The G11 interface is spread over four theories: Exit_Class, Witness, Euler_Construction and Subsolution.

Evidence: Euler_Construction:897 `lemma sconstraint_diag_le: assumes a ∈ sconstraint k L shows a $ i $ i <= L`. Exit_Class:430 `lemma sconstraint_diag: assumes a ∈ sconstraint k L shows 0 <= a $ i $ i and a $ i $ i <= L`.

Suggested action: Move eigen_ub_diag next to eigen_ub (Curvature_Operator) and delete psd_eigen_ub_diag and sconstraint_diag_le. Collect sconstraint_trace_ge, sconstraint_trace_le (restated as n·L) and sconstraint_orth_feasible in Exit_Class's constraint section.


### RA-class-14. Measurability and integrability blocks re-proved inline many times though named lemmas exist

*clone, impact medium, confidence high, ~180 lines.*  
Locations: Relative_Arbitrage/Exit_Class_Pasting.thy:184,793,1872 (cB); Relative_Arbitrage/Exit_Class_Witness.thy:808 (cB); Relative_Arbitrage/Exit_Class_Infinite.thy:200,740; Exit_Class_Marginals.thy:1099; Value_Function_Euler_Construction.thy:329 (cB); Relative_Arbitrage/Pair_Path_Laws.thy:2404 outerp_borel; Continuous_Time_Martingales/Integrability_Criteria.thy:749 pair_fst_borel; Relative_Arbitrage/Exit_Class_Pasting.thy:158,609,663,1251,1331; Exit_Class_Witness.thy:770 (fstB); Relative_Arbitrage/Exit_Class_Pasting.thy:392-398,1002-1017 (pexit measurability); Relative_Arbitrage/Path_Splicing.thy:1350 pexit_path_measurable; Relative_Arbitrage/Exit_Class_Limits.thy:1206-1219 vs 1352-1365 (AQ/Ai); Relative_Arbitrage/Exit_Class_Limits.thy:870-891 vs 962-976 (Doob envelope)

1. `(λp. outerp (fst p) - snd p) ∈ borel_measurable borel` is proved about 9 times repo-wide by an entrywise rewrite. Pasting:1872 shows the 2-line proof from outerp_borel and pair_fst_borel/pair_snd_borel.
2. `fst ∈ borel_measurable borel` is re-proved six times in the cluster, though pair_fst_borel exists and is used elsewhere in the same file.
3. The pexit measurability via pfst_measurable + pexit_measurable + pexit_pfst is re-derived three times in Pasting, though pexit_path_measurable is used at Pasting:1091.
4. In Limits, the AQ/Ai integrability blocks of the stopped compensator and the Doob-envelope set-up are copied between stopped_coord/comp_martingale and stopped_cond_exp/fourth_moment.
5. The 'start set is measurable' block is repeated (Witness:615-622, Pasting:105-111, 306-314, 1135-1143).

Evidence: Pasting:1872 `have cB: ... using measurable_compose[OF pair_fst_borel outerp_borel] pair_snd_borel by (rule borel_measurable_diff)`. Pasting:184-191 proves the same fact through `e: ... = (λp. χ i j. ...)` and continuous_on_vec_lambda.

Suggested action: Add `compensated_map_borel` next to outerp_borel and a `start_set_sets` lemma. Replace the inline blocks with pair_fst_borel and pexit_path_measurable. Factor `exit_class_stopped_A_integrable` and `exit_class_doob_envelope` in Limits.


### RA-class-15. Stale and orphan prose left by earlier moves (sections without content, wrong theory names, false claims)

*documentation, impact medium, confidence high, ~200 lines.*  
Locations: Relative_Arbitrage/Exit_Class.thy:242-246, 292-300, 318-334, 393-399; Relative_Arbitrage/Exit_Class_Limits.thy:19-70, 81-84, 103, 296, 565-572, 1508-1537; Relative_Arbitrage/Exit_Class_Shift.thy:224 (empty subsection); Relative_Arbitrage/Exit_Class_Optimizer.thy:14-24, 180-192; Relative_Arbitrage/Exit_Class_Witness.thy:27-32, 107-109, 196, 248; Relative_Arbitrage/Covariation_Density.thy:9-22

Exit_Class:
- 242-246 claims that everything reading one clause is 'the generic statement specialised'. False for exit_class_diffquot_full_mass, start_full_mass, start_limit and diffquot_limit, which unfold exit_class_def.
- 292-300 describes the density statement, which lives in Covariation_Density.
- 318-334 'Averages of constrained densities stay constrained' describes a lemma that is gone.
- 393-399 'Continuing a stopped volatility' has no lemma (acont is in Pair_Path_Laws:84).

Exit_Class_Limits:
- 19-70 describes a market-witness bridge with 'Exit_Class.acont', 'the locale carries ... L >= 1', 'acov_time_measurable' and 'Exit_Class.acont_set_borel_measurable'. None of these is in Exit_Class; the sections contain no lemma except the dead one.
- 81-84 and 296 attribute martingale_bounded_test and metric_measure_eqI_bounded_cts to Exit_Time_Semicontinuity; they are in Martingale_Algebra:930 and Path_Tightness:2537.
- 1508-1519 promises a parametric chain 'instantiated twice' over an empty subsection.
- The section title 'Lemma 2.3: the class is closed under weak limits' is used twice (lines 1 and 1814).

Exit_Class_Optimizer:
- 14-24 says clause (2) 'is not covered here' and clause (3) holds 'only for the ball; the interior value ... remains unproved'. Statement_Auxiliary has clause_2_* and clause_3_*.
- 180-192 'Joint continuity of the shift' has no lemma.

Exit_Class_Witness:
- 27-32 wrongly says indep_vars_PiM_coordinate is out of scope.
- 107, 196 and 248 cite Brownian_Market for Wiener_Measure lemmas.

Covariation_Density: 9-22 'the class below' (there is none) and the false library claim.

There are 20 runs of 4-23 blank lines (e.g. Shift:16-38, Limits:1522-1538, Optimizer:460-471).

Evidence: Examples: Limits:29 `(Exit_Class.acont)`, while `definition acont` is at Pair_Path_Laws.thy:84. Optimizer:21-22 `Clause (3) is here only for the ball; the interior value for n - k >= 2 remains unproved.`

Suggested action: Delete the orphan blocks and empty sections, fix the theory names, rewrite Optimizer:14-24 as a pointer to Statement_Auxiliary, and squeeze the blank-line runs.


### RA-class-16. The rational-reduction argument for the difference-quotient clause appears three times; with a closed full set it is not needed at all

*clone, impact medium, confidence medium, ~200 lines.*  
Locations: Relative_Arbitrage/Exit_Class.thy:698-738 (exit_class_diffquot_limit); Relative_Arbitrage/Exit_Class_Witness.thy:681-722 (bmpair_law_diffquot); Relative_Arbitrage/Exit_Class_Pasting.thy:21-71 exit_class_diffquot_of_pairs; Relative_Arbitrage/Exit_Class.thy:302 diffquot_constraint_weak_limit, :569 exit_class_diffquot_full_mass

The same 45-line AE_ball_countable' / AE_ball_countable' / diffquot_all_of_rational block is written three times. Witness:681 even says 'the rational reduction, exactly as in Exit_Class.exit_class_diffquot_limit'. Pasting then factored it as exit_class_diffquot_of_pairs, used by pcut, pglue, kglue and four DP / Infinite theories, but too late in the chain for the first two copies. Moreover, the whole set {ω ∈ mspace. ∀s t. 0<=s<t<=T → dq ∈ S} is an intersection of the closed sets of closedin_diffquot_constraint, hence closedin (closedin_INT). It can be fed directly to weak_conv_closed_full_mass, to AE_distr_iff, and to AE_pglue_law / AE_kglue_law (which accept any measurable target set, Path_Law_Pasting:817). That removes the pairwise-then-rational detour, together with exit_class_diffquot_full_mass and diffquot_constraint_weak_limit.

Evidence: Witness:681 comment `the rational reduction, exactly as in Exit_Class.exit_class_diffquot_limit`. Path_Law_Pasting.thy:823 AE_pglue_law takes `mset: {ω ∈ mspace (path_metric T). P ω} ∈ sets (path_borel T)` for arbitrary P. Abstract_Topology.thy:146 closedin_INT.

Suggested action: Add `closedin_diffquot_constraint_all` (closed S ⟹ closedin of the full set) in Pair_Path_Space next to closedin_diffquot_constraint, generic in S. Rewrite exit_class_diffquot_limit, bmpair_law_diffquot, the cov' clause of exit_class_pcut, pglue_law_diffquot and kglue_law_diffquot as one-step pushforward / portmanteau arguments. Otherwise, at least move exit_class_diffquot_of_pairs into Exit_Class and use it in all three places.


### RA-class-17. Matrix facts in Exit_Class belong in the constraint-set theories; Exit_Class imports Operator_Formula only for closed_eigen_ub

*misplacement, impact medium, confidence medium, ~110 lines.*  
Locations: Relative_Arbitrage/Exit_Class.thy:31 convex_eigen_ub, :66 Pi_proj_ge_iff, :85 closed_Pi_constraint, :150 psd_eigen_ub_entry_abs_le, :353 Pi_proj_mat_1; Relative_Arbitrage/Operator_Formula.thy:2114 closed_eigen_ub; Relative_Arbitrage/Exit_Class.thy:4-5 (imports Operator_Formula Ball_Solution)

These lemmas are about Pi_proj, Pi_constraint and eigen_ub (Constraint_Set_Convexity, Curvature_Operator) and mention nothing of the class. closed_eigen_ub is the last lemma of Operator_Formula, its only user is Exit_Class, and its proof needs only continuous_on_quadform. A name-level scan finds no other Operator_Formula fact and no Ball_Solution fact used anywhere in the eight cluster theories. So the class layer waits for the 2 127-line operator theory and for Ball_Solution for one 9-line lemma. psd_eigen_ub_entry_abs_le is a generic psd fact: if eigen_ub moved to Symmetric_Matrix_Spectra, it would belong there too.

Evidence: grep closed_eigen_ub: Operator_Formula.thy:2114 (definition) and Exit_Class.thy:125 (only use). Name-level scan of Ball_Solution and Operator_Formula against the cluster files: only closed_eigen_ub.

Suggested action: Move closed_eigen_ub and convex_eigen_ub to Curvature_Operator, and the Pi_* facts to Constraint_Set_Convexity. Let Exit_Class import Constraint_Set_Convexity and the path toolkit only, dropping Operator_Formula and Ball_Solution. Verify with a build, because simp/intro attributes could hide a dependency.


### RA-class-18. outerp_eq_outer_prod proved twice; covariation_class compensated-martingale projection proved twice

*clone, impact low, confidence high, ~25 lines.*  
Locations: Relative_Arbitrage/Exit_Class.thy:218 outerp_eq_outer_prod; Relative_Arbitrage/Pair_Path_Space.thy:771 outerp_eq_outer_prod; Relative_Arbitrage/Pair_Path_Laws.thy:4088 covariation_class_martingale_compensated; Relative_Arbitrage/Pair_Path_Laws.thy:4308 covariation_class_compensated_martingale; Relative_Arbitrage/Pair_Path_Laws.thy:4337-4344 and 4369-4378 (duplicated text blocks)

`outerp_eq_outer_prod` has the same name and statement in Pair_Path_Space (an ancestor) and in Exit_Class, so the later one shadows the earlier. The two covariation_class projections have identical statements up to bound-variable names. Exit_Class.exit_class_compensated_martingale wraps one of them, and covariation_class_mono uses the other. The text blocks 'Squaring the coordinate is the diagonal entry ...' and '... live in Martingale_Algebra' each appear twice in a row.

Evidence: Exit_Class.thy:218 `lemma outerp_eq_outer_prod: outerp x = outer_prod x x by (simp add: outerp_def outer_prod_def)`. Pair_Path_Space.thy:771 `lemma outerp_eq_outer_prod: fixes v shows outerp v = outer_prod v v by (simp add: outerp_def outer_prod_def)`.

Suggested action: Delete Exit_Class:218, delete one of the two covariation_class projections, and remove the duplicated text blocks.


### RA-class-19. Moment bounds re-derived: exit_class_norm_mean_le repeats exit_class_inner_mean_le; one second-moment identity would serve four lemmas

*clone, impact low, confidence high, ~60 lines.*  
Locations: Relative_Arbitrage/Exit_Class_Pasting.thy:1233-1296 exit_class_norm_mean_le (1274-1295); Relative_Arbitrage/Exit_Class_Pasting.thy:1736-1764 exit_class_inner_mean_le; Relative_Arbitrage/Exit_Class_Witness.thy:984 exit_class_norm_sq_integrable, :1000 exit_class_sq_norm_mean_ge; Relative_Arbitrage/Exit_Class_Pasting.thy:1766 exit_class_comp_norm_mean_le

Lines 1274-1295 of exit_class_norm_mean_le are the whole proof of exit_class_inner_mean_le (∫X•X = Σ∫X_i^2 <= n·nLT). All four lemmas follow from the identity E[X_t•X_t] = x•x + E[trace Y_t], which is the trace of exit_class_compensated_mean. Combined with 0 <= diagonal <= L, it gives both the lower bound (n-k)t and an upper bound n·L·t, which is sharper than n·n·L·T. These lemmas also belong in Exit_Class beside exit_class_sq_mean_le, not in Pasting and Witness.

Evidence: Pasting:1276-1295 and 1743-1763: the same integral_cong / integral_sum / sum_mono over exit_class_sq_mean_le.

Suggested action: Add exit_class_sq_norm_mean_eq to Exit_Class and derive the four bounds from it. At minimum, make norm_mean_le call inner_mean_le.


### RA-class-20. Redundant hypotheses: setsQ next to Q, and other derivable or unused assumptions

*simplification, impact low, confidence high, ~60 lines.*  
Locations: Relative_Arbitrage/Exit_Class_Limits.thy:815 exit_class_cont_adapted, :833 exit_class_ploc_stopping, :861 exit_class_stopped_coord_martingale, :934 exit_class_stopped_comp_martingale, :1106 exit_class_stopped_abs_le, :1168 exit_class_stopped_cond_exp, :1323 exit_class_stopped_fourth_moment, :1395 exit_class_fourth_moment; Relative_Arbitrage/Exit_Class_Optimizer.thy:475 exit_class_kglue_law' (T0); Relative_Arbitrage/Pair_Path_Laws.thy:4130 covariation_class_lipschitz_ae (T); Relative_Arbitrage/Exit_Class.thy:406 exit_class_lipschitz_ae (T); Relative_Arbitrage/Pair_Path_Laws.thy:4189 covariation_class_Y_diag_increment (B0)

1. Eight Limits lemmas assume both `setsQ: sets Q = sets (path_borel T)` and `Q: Q ∈ exit_class k L T x`. The former is exit_class_sets[OF Q], and callers such as Tightness:27 and Limits:1548 re-derive it only to pass it back.
2. exit_class_kglue_law' assumes `T0: 0 < T` beside `r: 0 <= r` and `rT: r < T`.
3. covariation_class_lipschitz_ae, and hence exit_class_lipschitz_ae, never use `T: 0 <= T`: the proof is diffquot_lipschitz[OF B0] on the AE quotient fact.
4. In covariation_class_Y_diag_increment, B0 is used only in the s = t case, where B*(t-s) = 0.

Evidence: Limits:861 `assumes T: 0 < T and L: 0 <= L and setsQ: sets Q = sets (path_borel T) and Q: Q ∈ exit_class k L T x`. Optimizer:474-475 `r: 0 <= r and rT: r < T ... and T0: 0 < T`.

Suggested action: Drop setsQ (obtain it internally), drop T0, drop T from the Lipschitz lemmas and B0 from the diagonal lemma, and update callers.


### RA-class-21. Unused lemmas in the cluster

*dead_code, impact low, confidence high, ~170 lines.*  
Locations: Relative_Arbitrage/Exit_Class_Limits.thy:72 stopped_market_acov_leaves_sconstraint; Relative_Arbitrage/Exit_Class.thy:464 exit_class_Y_entry_measurable; Relative_Arbitrage/Exit_Class.thy:754 exit_val_eq_covariation_val; Relative_Arbitrage/Exit_Class_Pasting.thy:382-450 exit_val_horizon_stable; Relative_Arbitrage/Exit_Class_Pasting.thy:1076-1114 exit_val_paste_ge; Relative_Arbitrage/Exit_Class.thy:302 diffquot_constraint_weak_limit (one-use wrapper); Relative_Arbitrage/Pair_Path_Laws.thy:722 pair_holder_charge_split

1. stopped_market_acov_leaves_sconstraint is a one-line projection of stopped_market_def. Its statement (`acov s ω = 0`) does not mention sconstraint, so the name is misleading. It is listed in notes/UNUSED_THMS.md and unused.
2. exit_class_Y_entry_measurable has 0 uses.
3. exit_val_eq_covariation_val (G11 bridge) has 0 uses.
4. exit_val_horizon_stable is referenced only in prose (Pasting:961).
5. exit_val_paste_ge is referenced only by an @{thm} in Dynamic_Programming_Pasting:20.
6. pair_holder_charge_split is an unused alternative to the inline split in exit_class_pair_holder_charge (Tightness:73).

Evidence: `grep -rnw NAME --include=*.thy` outside the defining line: exit_class_Y_entry_measurable 0; exit_val_eq_covariation_val 0; exit_val_horizon_stable prose only; exit_val_paste_ge antiquotation only; stopped_market_acov_leaves_sconstraint none.

Suggested action: Delete them, or keep exit_val_eq_covariation_val as the G11 bridge. Rewrite the prose that cites exit_val_paste_ge and exit_val_horizon_stable.


### RA-class-22. Lower layers reference cluster lemmas (forward references), including a paper-free session; misnamed exit_class_* lemmas in the path toolkit

*documentation, impact low, confidence high, ~40 lines.*  
Locations: Continuous_Path_Spaces/Path_Space.thy:1268-1274; Relative_Arbitrage/Pair_Path_Space.thy:821, 1440-1446; Relative_Arbitrage/Pair_Path_Laws.thy:79-82, 1171; Relative_Arbitrage/Path_Splicing.thy:1313; Relative_Arbitrage/Path_Law_Pasting.thy:1552, 1793, 2657; Relative_Arbitrage/Pair_Path_Laws.thy:1017 exit_class_path_cont, :1033 exit_class_coord_paths_cont, :1174 exit_class_comp_paths_cont

Continuous_Path_Spaces (advertised as paper-free) has a section 'Kernel pasting' whose text begins 'exit_class_kglue_law glues with a countably valued index' and speaks of the clauses of (1.7). The path-toolkit theories, which the ROOT says 'know nothing of the constraint set or the value function', describe bmpair_law_in_paper_pair_class, exit_val_horizon_mono, exit_class_pcut, exit_val_le_ball_bound and exit_class_diffquot_of_pairs, all proved later. Three generic path-continuity lemmas consumed by Exit_Class_Limits are named exit_class_*, but their statements mention only `sets Q = sets (path_borel T)`.

Evidence: Path_Space.thy:1270 `text ‹exit_class_kglue_law glues with a countably valued index, which Metric_space.usc_measurable_selection cannot supply.›` Pair_Path_Laws:1017 `lemma exit_class_path_cont: fixes Q :: ((real ⇒ 'a × 'b)) measure ... assumes ... setsQ ... shows continuous_on {0..} (λs. ω (min s T))`.

Suggested action: Move these remarks to the cluster theories they describe. Rename the path-continuity lemmas (e.g. path_law_stopped_path_cont).


### RA-class-23. Exit_Class_Witness and Exit_Class_Pasting carry material unrelated to their titles; USC hypothesis exists only because the witness comes later

*misplacement, impact low, confidence high, ~40 lines.*  
Locations: Relative_Arbitrage/Exit_Class_Witness.thy:906 exit_val_le_T, :930 sconstraint_trace_ge, :949 exit_class_trace_rate, :984 exit_class_norm_sq_integrable, :1000 exit_class_sq_norm_mean_ge, :1066 exit_val_boundary_zero, :1175 exit_val_le_ball_bound; Relative_Arbitrage/Exit_Class_Pasting.thy:1233,1736,1766 (moment bounds), :382,966 (horizon lemmas); Relative_Arbitrage/Exit_Class_Shift.thy:298 exit_val_usc (hypothesis ne); Relative_Arbitrage/Exit_Class_Witness.thy:888 exit_val_usc_unconditional

'Concrete pair processes, and nonemptiness of the class' also holds the value-function bounds. These need only Exit_Class, and exit_val_le_ball_bound has 17 users in 7 theories. 'Shortening the horizon, concatenation' holds class moment bounds. exit_val_usc takes `ne: exit_class k L T 0 ≠ {}` only because the nonemptiness witness is proved in a later theory; Witness:888 then re-wraps it.

Evidence: Dependency read of the proofs: exit_val_le_ball_bound uses exit_class_prob, ess_inf_time_*, etime_*, exit_class_norm_sq_integrable and exit_class_sq_norm_mean_ge, all Exit_Class-level.

Suggested action: Create a theory Exit_Value_Bounds (directly after Exit_Class) for exit_val_le_T, the trace and moment bounds and the ball bounds. Put the witness before USC and state exit_val_usc unconditionally (L >= 1).


### RA-class-24. Redundant session imports repeated in every class theory

*structure, impact low, confidence high, ~20 lines.*  
Locations: Relative_Arbitrage/Exit_Class_Shift.thy:5-10; Relative_Arbitrage/Exit_Class_Witness.thy:5-11; Relative_Arbitrage/Exit_Class_Pasting.thy:5-10; Relative_Arbitrage/Exit_Class_Optimizer.thy:5-9; Relative_Arbitrage/Exit_Class_Tightness.thy:5-8

Each theory re-lists Continuous_Time_Martingales.Integrability_Criteria, Essential_Infimum, Continuous_Path_Spaces.Path_Exit_Times, Path_Law_Sampling, Matrix_Algebra and Increment_Moments, all already imported by Exit_Class. This is harmless for the build but hides the real dependency structure that the DAG reshaping needs.

Evidence: Exit_Class.thy:4-10 already imports Path_Exit_Times, Essential_Infimum, Increment_Moments, Matrix_Algebra and Path_Law_Sampling.

Suggested action: Trim the imports to the immediate predecessor plus genuinely new sessions.


### RA-class-25. Two encodings of the exit functional and a re-proved sequential Berge argument in the selector

*simplification, impact low, confidence medium, ~60 lines.*  
Locations: Relative_Arbitrage/Exit_Class_Optimizer.thy:343-397 (hypB in exit_val_measurable_selector); Relative_Arbitrage/Exit_Class_Optimizer.thy:306-341 (hypA); Relative_Arbitrage/Exit_Class_Shift.thy:231 exit_val_eq_vshift_sup, :298 exit_val_usc; Semicontinuous_Analysis/Berge.thy:454 usc_sup_over_compactin; Relative_Arbitrage/Pair_Path_Space.thy:854 vshift_sup_usc

The USC proof works with the real-valued vshift T A (x,0) Q and the library Berge lemma. The selector works with the ennreal ess_inf_time (pshift_law T y R) (...) and re-proves inline that the supremum over a compact set of a jointly usc function is usc in the parameter (hypB, about 55 lines with an ennreal_strict_between contradiction). The 'key' step of exit_val_eq_vshift_sup already links the two representations.

Evidence: Optimizer:350 `have closed {y. c <= Sup (?g y ` Cs)}` proved by closed_sequential_limits plus compactin_sequentially plus ess_inf_pexit_pshift_usc. Berge.thy:454 `theorem usc_sup_over_compactin ... shows eventually (λy. Sup (F y ` C) < c) (nhds x)`.

Suggested action: Derive hypB from vshift_sup_usc / usc_sup_over_compactin via the vshift representation (bounded by T), or add an ennreal / sequential Berge variant to Semicontinuous_Analysis. Keep one representation of the functional.


### RA-class-26. Four-clause class-membership transports follow one template

*simplification, impact low, confidence medium, ~150 lines.*  
Locations: Relative_Arbitrage/Exit_Class_Shift.thy:39-168 exit_class_pshift; Relative_Arbitrage/Exit_Class_Pasting.thy:79-217 exit_class_pcut; Relative_Arbitrage/Exit_Class_Witness.thy:604-877 bmpair_law_start/_diffquot/_X_martingale/_comp_martingale/_in_paper_pair_class

Each proof establishes prob, sets, the start clause (pushforward of an AE set), the dq clause (pointwise invariance of quotients), the X clause and the compensated clause. The two martingale clauses use the same pattern: martingale_cong_ge on a source martingale, a Zm adaptedness block via nat_filt_eval/measurable_family_vimage_algebra, and martingale_pair_law / martingale_pshift_law. In pcut and bmpair the X and compensated cases differ only in the composed map.

Evidence: exit_class_pcut:155-212 vs bmpair_law_X_martingale:759-793 / bmpair_law_comp_martingale:795-840: same skeleton, same `fstB`/`cB`/`ev` lemmas.

Suggested action: State one transport lemma: if φ is measurable path_borel S → path_borel T, adapted, preserves the start point and the quotient clause pointwise, and maps the two martingales to martingales, then the pushforward is in covariation_class. Derive pshift, pcut and bmpair from it. Do this after the G11 move.


## RA-dpp

The cluster formalises the dynamic programming principle that the paper (Prop. 2.4) defers to Larsson-Ruf, for the finite-horizon value function exit_val k L T K. It never states the DPP as an equality (eq. (2.9)). What it proves are the two halves in the form the Value_Function_* theories use.
(a) The >= half, by two separate constructions:
  - At a deterministic time, by kernel pasting with kglue_law' (Dynamic_Programming_Pasting: exit_val_kpaste_ge, exit_val_dpp_ge_const, exit_val_dpp_ge, exit_val_dpp_sup_ge).
  - At a path stopping time, by the additive glue aglue_law of the stopped past with a horizon-parametrised selector kernel. This spans Additive_Glue (exit_class_aglue), Delayed_Class (pdelclass, exit_val_measurable_selector_horizon, pstopped_law_*) and Assembly (aglue_law_pexit_ge, exit_class_aglue_selector, exit_val_ge_of_stopped_bound, exit_val_dpp_sup_ge_time).
(b) The conditioning (<=) half, by a regular conditional distribution at a deterministic time (Conditioning: exit_class_rcd_member, exit_val_cond). It is extended to an arbitrary [0,T]-valued time by rational approximation and upper semicontinuity (exit_val_cond_pointwise, exit_val_cond_time).
About a third of the cluster is the residue of abandoned approaches:
  - Dynamic_Programming_Kernels holds an iterated mixed-kernel construction for simple stopping times (exit_class_kglue_mixed, exit_val_dpp_ge_const_two, exit_val_dpp_ge_step, dpp_chain, dpp_disj) and an rcd at a stopping time (AE_rcd_stopping_diffquot_*). About 1050 lines, none of it used.
  - Conditioning keeps an elementary-conditioning route (exit_class_future_of_past chain, about 225 lines), also unused.
  - Pasting keeps an undischarged <= reduction (exit_val_dpp_le_of_cond).
The deterministic >= half (about 350 lines) is the constant-time instance of the stopping-time >= half.
Organisation problems:
  - The eight theories form a strictly linear import chain, although the real dependencies are sparse. Additive_Glue and Stopping_Clauses use nothing of the cluster, and Conditioning uses only exit_val_neq_top.
  - Dynamic_Programming_Optional_Sampling is an empty shell. Stopping_Clauses holds 3 class lemmas unrelated to its title.
  - About 240 lines are blank runs, and dozens of text blocks describe lemmas that moved into the path layer in phase 6 of the restructuring.
  - The mirror image also exists: DPP prose stranded in Path_Splicing, Path_Law_Pasting, Path_Law_Sampling and Exit_Class_Optimizer.
  - Pervasive X-process / compensated-process twin lemmas double much of Delayed_Class and Assembly.
  - Of the constraint set the cluster uses only closedness and convexity of sconstraint k L, so all of its covariation statements can move to covariation_class S. This is concrete progress on the plan's open G11.
Estimated size after cleaning: about 3000 lines in 3-4 theories, with Conditioning and Delayed_Class building in parallel.


### RA-dpp-1. About 1050 lines of Dynamic_Programming_Kernels are an abandoned simple-stopping-time construction used by nothing

*dead_code, impact high, confidence high, ~1050 lines.*  
Locations: Relative_Arbitrage/Dynamic_Programming_Kernels.thy:34 kernel_class_LP_measurable; Dynamic_Programming_Kernels.thy:99 exit_class_sets_prob_algebra; Dynamic_Programming_Kernels.thy:148 kernel_repair_into_class; Dynamic_Programming_Kernels.thy:212-488 exit_class_kglue_mixed; Dynamic_Programming_Kernels.thy:601 exit_val_horizon_zero; Dynamic_Programming_Kernels.thy:614-698 pexit_pglue_selector_ge; Dynamic_Programming_Kernels.thy:708-869 exit_val_dpp_ge_const_two; Dynamic_Programming_Kernels.thy:884-1045 exit_val_dpp_ge_step; Dynamic_Programming_Kernels.thy:1055 dpp_chain, :1074 dpp_disj; Dynamic_Programming_Kernels.thy:1131-1256 AE_rcd_stopping_diffquot_at; Dynamic_Programming_Kernels.thy:1264-1343 AE_rcd_stopping_diffquot_rat

The only live statement in Dynamic_Programming_Kernels is exit_val_dpp_sup_ge_time_of_const (500-593), used by Assembly:953. Everything else forms one closed dependency island:
- kernel_class_LP_measurable, exit_class_sets_prob_algebra and kernel_repair_into_class are used only by exit_class_kglue_mixed.
- exit_class_kglue_mixed and pexit_pglue_selector_ge are used only by exit_val_dpp_ge_const_two and exit_val_dpp_ge_step.
- Those two are used by nothing.
- dpp_chain and dpp_disj are defined, but the induction the text at 1081-1085 announces was never written.
- AE_rcd_stopping_diffquot_rat is named only in prose.
The island is an abandoned approach: iterated kernel glue over the values of a simple stopping time, plus an r.c.d. at a stopping time. The additive-glue route in Assembly superseded it. Deleting it also frees these path-layer helpers: AE_kglue_law_of_kernel (Path_Law_Pasting), pcut_pglue_self (Path_Splicing), kglue_law'_rcd_eq (Path_Law_Pasting, prose only) and kernel_mix_measurable (Semidirect_Kernels, library API, may stay).

Evidence: grep -rnw over *.thy:
- exit_val_dpp_ge_step: 3 hits, all in Kernels (definition, prose).
- exit_val_dpp_ge_const_two: 1 hit, the prose at Kernels:876.
- exit_class_kglue_mixed: 3 hits, all in Kernels.
- dpp_chain: 5 hits, all in Kernels.
- AE_rcd_stopping_diffquot_rat: 1 hit, the prose at Kernels:1349.
- exit_val_horizon_zero: 1 hit, the prose at Kernels:703.
notes/UNUSED_THMS.md:205-211 already lists several of these under the stale name Exit_Class_DPP.

Suggested action: Delete the chain together with its prose (Kernels 1-489, 595-1372, keeping only exit_val_dpp_sup_ge_time_of_const). Then re-run probe5 / unused_thms for the cascade into Path_Law_Pasting and Path_Splicing.


### RA-dpp-2. Twin lemmas for the X process and the compensated process (outerp X - Y) throughout the cluster

*clone, impact high, confidence high, ~450 lines.*  
Locations: Dynamic_Programming_Conditioning.thy:180-206 exit_class_shifted_X_martingale vs :208-236 exit_class_shifted_comp_martingale (and inline again at :115-130 in pfut_law_X_martingale); Dynamic_Programming_Stopping_Clauses.thy:23-46 exit_class_horizon_component vs :81-106 exit_class_horizon_compensated; Dynamic_Programming_Delayed_Class.thy:441-505 pdelclass_X_martingale vs :507-580 pdelclass_comp_martingale; Dynamic_Programming_Delayed_Class.thy:953-1080 pstopped_law_horizon_component vs :1082-1202 pstopped_law_horizon_compensated; Dynamic_Programming_Delayed_Class.thy:1217-1255 pdelclass_norm_mean_le vs :1257-1301 pdelclass_comp_norm_mean_le; Dynamic_Programming_Delayed_Class.thy:720-790 pdelclass_{X,comp}_{int,increment,mean}; Dynamic_Programming_Assembly.thy:347-472 KXpadd/KCpadd, KXabnd/KCabnd; :496-535 msecX/msecC, gintX/gintC; Additive_Glue.thy:263-318 hypothesis pairs QH/QHC, Kmean/KmeanC, ...

In each pair the proofs are identical up to the process f (ω (min u T)), with f = fst (then $ i) or f = λz. outerp (fst z) - snd z (then $ i $ j). The only differences are the Borel measurability / continuity of f and the source martingale.
The largest pair, pstopped_law_horizon_*, differs only in ?Z, fcB/entB and contT. The generic statement is paper-free: if Z u ω = f (ω (min u T)) is a horizon_sq_int_martingale under P with continuous f, its pushforward along pstopped T θ is one too. It belongs in the path layer next to pstopped_law_prob.
The time-change pairs (shifted_*, pdelclass_*) are all one lemma: martingale P F 0 (λu ω. f (ω (min u T))) together with a monotone s with 0 <= s u <= T gives martingale P (F o s) 0 (λu ω. f (ω (s u))). The same pattern is inlined in Exit_Class_Pasting:713-743 (mQ/cQ/mR/cR).

Evidence: Delayed 1022-1028 (component) vs 1133-1146 (compensated): the only differences are
  have fcB: "(λz. fst z $ c) ∈ borel_measurable borel"
vs
  have entB: "(λz. (outerp (fst z) - snd z) $ c $ d) ∈ borel_measurable borel"
and exit_class_horizon_component vs exit_class_horizon_compensated for HZ.
Conditioning 189-205 vs 218-235: identical apart from MGX vs MGY.

Suggested action: Introduce generic lemmas parameterised by a continuous f: martingale_time_change_capped (Pair_Path_Laws or Martingale_Algebra), pdelclass_martingale_of, pstopped_law_horizon_of and pdelclass_norm_mean_le_of. Instantiate each twice in one line. In exit_class_aglue, bundle each X/C hypothesis pair as one hypothesis over f ∈ {component, entry}.


### RA-dpp-3. Eight theories in a linear chain with sparse real dependencies; one empty theory, two fragments

*structure, impact high, confidence high, ~6214 lines.*  
Locations: Relative_Arbitrage/ROOT (theories Dynamic_Programming_*); Dynamic_Programming_Optional_Sampling.thy (33 lines, no statement); Dynamic_Programming_Stopping_Clauses.thy (3 lemmas); Dynamic_Programming_Additive_Glue.thy (4 lemmas, uses nothing of its imports in the cluster); Exit_Class_Infinite.thy:4 (imports Dynamic_Programming_Assembly)

The chain is Pasting → Conditioning → Kernels → Optional_Sampling → Stopping_Clauses → Additive_Glue → Delayed_Class → Assembly. Actual uses of earlier cluster facts:
- Conditioning uses only exit_val_neq_top (Pasting);
- Kernels uses exit_class_rcd_member (in its dead part) and Pasting basics;
- Optional_Sampling is empty; the plan already moved its content to Path_Stopping_Times;
- Stopping_Clauses and Additive_Glue use no cluster fact;
- Delayed_Class uses Pasting (selector_kernel', exit_class_start), Conditioning (only the duplicate exit_class_comp_martingale) and Stopping_Clauses;
- Assembly uses Delayed, Additive_Glue, Pasting and one Kernels lemma.
So Conditioning and the selector/delayed-class/additive-glue branch could build in parallel, and Value_Function_Subsolution waits for eight sequential theories.
Exit_Class_Infinite imports Dynamic_Programming_Assembly but uses none of the 77 facts of the cluster, which also serialises Exit_Class_Infinite and Exit_Class_Marginals behind the whole DPP layer.
Every DPP theory re-imports Integrability_Criteria, Increment_Moments, Essential_Infimum, Path_Exit_Times and Path_Law_Sampling, already transitively present. Pasting also re-imports Disintegration and Conditional_UI.
The theory names no longer match their content:
- 'Kernels' holds mostly dead code plus an ess-inf reduction;
- 'Stopping_Clauses' holds horizon martingale facts;
- 'Pasting' holds exit_val basics.

Evidence: Use scan (names defined in one DP theory and occurring outside text in another): Additive_Glue uses none, Stopping_Clauses none, Conditioning only exit_val_neq_top.
The same scan on Exit_Class_Infinite.thy and Exit_Class_Marginals.thy finds no cluster fact.

Suggested action: Restructure the cluster into:
- (1) Dynamic_Programming_Conditioning: the <= half. Contents: rcd membership, exit_val_cond, exit_val_cond_pointwise, exit_val_cond_time, plus exit_val_cond_at_time from Value_Function_Subsolution:2120. Imports Exit_Class_Optimizer and Path_Law_Sampling.
- (2) Dynamic_Programming_Delayed_Class: pdelclass with merged X/C lemmas, exit_val_measurable_selector_horizon. Parallel to (1).
- (3) Dynamic_Programming_Stopped_Glue: Additive_Glue + Assembly, the >= half at stopping times, with the deterministic corollary.
- (4) Optionally, a short Dynamic_Programming theory stating Prop. 2.4.
Delete Optional_Sampling, Kernels (after moving the ess-inf lemma) and Stopping_Clauses (to Exit_Class_Limits). Move Pasting's basics down (see the misplacement finding). Point Exit_Class_Infinite at the theory it actually needs, and drop the redundant imports.


### RA-dpp-4. The deterministic-time >= half (kglue route) is the constant-theta instance of the stopping-time >= half

*generalisation, impact high, confidence medium, ~350 lines.*  
Locations: Dynamic_Programming_Pasting.thy:26-80 exit_val_kpaste_ge; Dynamic_Programming_Pasting.thy:257-448 exit_val_dpp_ge_const; Dynamic_Programming_Pasting.thy:454-532 exit_val_dpp_ge; Dynamic_Programming_Pasting.thy:536-552 exit_val_dpp_sup_ge; Dynamic_Programming_Assembly.thy:943 exit_val_dpp_sup_ge_time

exit_val_dpp_sup_ge (deterministic r, 0 <= r < T) has exactly the statement of exit_val_dpp_sup_ge_time at theta = (λ_. r), once the conclusion is beta-reduced.
The side conditions hold trivially:
- path_stopping_time T (λ_. r) holds by unfolding the definition (0 <= r <= T, the continuity clause is vacuous);
- the constant is measurable;
- 0 < T follows from 0 <= r < T.
The kglue-based proof is therefore a second, independent proof of a special case: about 350 lines of pasting, selector-kernel packaging, integrand measurability and pathwise DPP. After replacing it:
- pexit_pglue_dpp (Path_Splicing:1261) and exit_val_paste_ge (Exit_Class_Pasting:1076, already unused) become dead;
- the second (Levy-Prokhorov) conclusion of exit_val_measurable_selector_kernel' becomes unused.

Evidence: exit_val_dpp_sup_ge:
  shows "(SUP P ∈ exit_class k L T x. ess_inf_time P (λω. pexit r K (λt. fst (ω t)) + (if pexit r K ... = r ∧ fst (ω r) ∈ K then enn2real (exit_val k L (T - r) K (fst (ω r))) else 0))) ≤ exit_val k L T K x"
exit_val_dpp_sup_ge_time:
  assumes "0 < T" ... "path_stopping_time T θ" "θ ∈ borel_measurable (path_borel T)"
  shows the same with r := θ ω.
The definition path_stopping_time (Path_Stopping_Times:427) only asks 0 ≤ θ ω ≤ T plus a determinism clause that a constant satisfies.
External uses of the deterministic version: Value_Function_Assembly:251, Value_Function_Supersolution_Case_1:2625.

Suggested action: Prove a two-line lemma path_stopping_time_const. Replace Pasting 26-80 and 257-552 by a corollary exit_val_dpp_sup_ge := exit_val_dpp_sup_ge_time[where θ="λ_. r"]. Then delete pexit_pglue_dpp, exit_val_paste_ge and the LP-measurability half of exit_val_measurable_selector_kernel' if nothing else needs them.


### RA-dpp-5. Unused elementary-conditioning chain in Conditioning, and an undischarged <= reduction in Pasting

*dead_code, impact medium, confidence high, ~345 lines.*  
Locations: Dynamic_Programming_Conditioning.thy:27-80 pfut_law_diffquot; Dynamic_Programming_Conditioning.thy:88-150 pfut_law_X_martingale; Dynamic_Programming_Conditioning.thy:403-457 pfut_law_comp_martingale; Dynamic_Programming_Conditioning.thy:464-516 exit_class_future_of_past; Dynamic_Programming_Pasting.thy:564-682 exit_val_dpp_le_of_cond

Conditioning: exit_class_future_of_past (uniform_measure conditioning on a past event, 'needs no regular conditional distribution') and its three clause lemmas are used by nothing. The live <= half goes through the r.c.d. (exit_class_rcd_member, exit_val_cond). The chain also keeps martingale_future_of_past and pfut_law_start (Path_Law_Pasting) alive, and nothing else uses those.
Pasting: exit_val_dpp_le_of_cond reduces the <= half of (2.9) at a deterministic time to the conditioning statement. Its hypothesis is never discharged, it is used nowhere, and its hypotheses L1 and 'closed K' are unused in the proof.

Evidence: - grep -rnw exit_class_future_of_past: only the prose at Conditioning:524.
- pfut_law_diffquot, pfut_law_X_martingale and pfut_law_comp_martingale are each used once, by exit_class_future_of_past.
- exit_val_dpp_le_of_cond: mentioned only in prose (Conditioning:1080, Path_Splicing:1387).
All are listed in notes/UNUSED_THMS.md:206,210.

Suggested action: Delete the four Conditioning lemmas, together with martingale_future_of_past and pfut_law_start if nothing else needs them. Either delete exit_val_dpp_le_of_cond or use it to state the DPP equality (see the faithfulness finding).


### RA-dpp-6. The ess-inf to real-constant reduction is proved three times; exit_val_dpp_ge is a special case of exit_val_dpp_sup_ge_time_of_const

*clone, impact medium, confidence high, ~180 lines.*  
Locations: Dynamic_Programming_Pasting.thy:454-532 exit_val_dpp_ge; Dynamic_Programming_Kernels.thy:500-593 exit_val_dpp_sup_ge_time_of_const; Dynamic_Programming_Pasting.thy:585-608 (inside exit_val_dpp_le_of_cond)

All three blocks run the same reduction:
- the integrand g lies in [0,T];
- so ess_inf_time P g <= ennreal T < top (ess_inf_time_le_const);
- set c = enn2real (ess_inf_time P g), with ennreal c = ess_inf_time P g;
- then AE c <= g by ess_inf_time_AE.
exit_val_dpp_ge is line-for-line exit_val_dpp_sup_ge_time_of_const with θ ω replaced by r, including the vbnd case split and the redundant geta: g = (λω. ...).
The argument is paper-free: for a probability space M and 0 <= g <= T, if every real a.s. lower bound c gives ennreal c <= v, then ess_inf_time M g <= v.

Evidence: Pasting 503-520 and Kernels 561-578 are identical:
  have fin: "ess_inf_time P g ≤ ennreal T" by (rule ess_inf_time_le_const[OF PP gle])
  ... define c where "c = enn2real (ess_inf_time P g)" ... aec0 ... ess_inf_time_AE[of P g]
Pasting 586-608 repeats it for pexit T.

Suggested action: Add the paper-free lemma ess_inf_time_le_of_real_bounds (prob_space M, 0 ≤ g ≤ T, ∀c. AE c ≤ g ⟶ ennreal c ≤ v ⟹ ess_inf_time M g ≤ v) to Continuous_Time_Martingales.Essential_Infimum. exit_val_dpp_sup_ge_time_of_const then becomes about 10 lines, and exit_val_dpp_ge disappears with the previous finding.


### RA-dpp-7. Selector optimality transported to the glued path, proved twice, and AE_pshift_law_iff / pexit_pshift re-derived by hand

*clone, impact medium, confidence high, ~200 lines.*  
Locations: Dynamic_Programming_Pasting.thy:346-420 (inner, in exit_val_dpp_ge_const); Dynamic_Programming_Kernels.thy:614-698 pexit_pglue_selector_ge; Dynamic_Programming_Assembly.thy:125-211 selector_value_AE

pexit_pglue_selector_ge is literally the 'inner' block of exit_val_dpp_ge_const. Its own text says 'This is the inner step of exit_val_dpp_ge_const, pulled out', but the original was never replaced by a call to it.
The 'opt' sub-step appears in both. It turns ess_inf_time (pshift_law (T-r) y (S y)) τ = exit_val into AE v <= pexit (T-r) K (y + X) by pushing through pshift with shm, m1, mset and AE_distr_iff (Pasting 369-388, Kernels 648-668). That push is AE_pshift_law_iff (Path_Law_Pasting:996), which needs no measurability hypothesis.
selector_value_AE does call AE_pshift_law_iff, but re-derives pexit_pshift (Path_Splicing:548) twice (Assembly 166-168, 188-190) and pexit_path_measurable once (145-153).

Evidence: Kernels:609-612:
  text ‹The selector's optimality, transported to the glued path. This is the inner step of exit_val_dpp_ge_const, pulled out ...›
Pasting:375 vs Kernels:654, identical:
  have shm: "pshift (T - r) (fst (ω r)) ∈ S (fst (ω r)) →M ?MR" ...
Assembly:166-168:
  by (rule pexit_cong_on) (simp add: pshift_fst)
This is the proof of pexit_pshift verbatim.

Suggested action: State one lemma: from ess_inf_time (pshift_law S y μ) τ_K = exit_val k L S K y, conclude AE ω in μ. enn2real (exit_val k L S K y) ≤ pexit S K (λt. y + fst (ω t)), using AE_pshift_law_iff, pexit_pshift and enn2real_leI. Derive selector_value_AE from it with one AE_distr_iff through prebase. The kglue copies go with the deterministic-half finding.


### RA-dpp-8. Class projections re-proved: exit_class_comp_martingale duplicates exit_class_compensated_martingale; 11 ad-hoc unfoldings of exit_class_def

*library_duplicate, impact medium, confidence high, ~40 lines.*  
Locations: Dynamic_Programming_Conditioning.thy:169-174 exit_class_comp_martingale; Dynamic_Programming_Pasting.thy:161-165 exit_class_start; Dynamic_Programming_Stopping_Clauses.thy:29-31; Dynamic_Programming_Conditioning.thy:497, 803, 993; Dynamic_Programming_Delayed_Class.thy:608-610; Dynamic_Programming_Assembly.thy:883-885

- exit_class_comp_martingale (Conditioning) is character-for-character the statement of exit_class_compensated_martingale (Exit_Class.thy:499). It is used in Conditioning:220 and Delayed_Class:530.
- exit_class_start sits in Dynamic_Programming_Pasting, yet it is used by nine theories, among them Value_Function_Euler_Construction, Value_Function_Assembly and Value_Function_Supersolution_Case_1/2. Exit_Class.thy has every other projection except this one and a diffquot projection; it should be exit_class_eq_covariation + covariation_class_start (Pair_Path_Laws:4068).
- Stopping_Clauses:29-31 re-derives exit_class_X_martingale (Exit_Class_Limits:107) with 'unfolding exit_class_def', and Conditioning:992-993 re-derives exit_class_start the same way.
- The cluster unfolds exit_class_def in 11 places in all (Additive_Glue:217, Assembly:885, Conditioning:174,497,499,803,837,993, Delayed:610, Pasting:165, Stopping_Clauses:31). These are exactly the G11 blockers the plan counts.
- Separately, Pair_Path_Laws itself has the duplicate pair covariation_class_martingale_compensated (4088) / covariation_class_compensated_martingale (4308).

Evidence: Exit_Class.thy:499:
  lemma exit_class_compensated_martingale: assumes Q: "Q ∈ exit_class k L T x" shows "martingale Q (natural_filtration Q 0 (λu ω. ω u)) 0 (λu ω. outerp (fst (ω (min u T))) - snd (ω (min u T)))"
Conditioning:169-173 is the same statement, proved by 'using Q unfolding exit_class_def by blast'.

Suggested action: Delete exit_class_comp_martingale and use exit_class_compensated_martingale. Move exit_class_start to Exit_Class.thy, and add exit_class_diffquot and exit_classI there (via covariation_class_*). Replace the 11 unfoldings. Merge the two covariation_class compensated-martingale projections.


### RA-dpp-9. Measurability bridge between the weak topology and prob_algebra rebuilt by hand three times; a 16-line block is measurable_restrict_space2_iff

*library_duplicate, impact medium, confidence high, ~90 lines.*  
Locations: Dynamic_Programming_Kernels.thy:65-80 (amb, in kernel_class_LP_measurable); Dynamic_Programming_Pasting.thy:114-140 (in exit_val_measurable_selector_kernel'); Value_Function_Euler_Construction.thy:766-779 (sbm_kernel_package); Dynamic_Programming_Kernels.thy:51-61, 82-89

The 'amb' step (a map into restrict_space N Ω that lands in Ω is measurable into N) is proved by hand with measurableI. That is one direction of HOL-Analysis measurable_restrict_space2_iff.
The conversions in both directions between 'measurable into borel_of (weak_conv_topology X), landing in the probability measures with sets = borel_of X' and 'measurable into prob_algebra (borel_of X)' are built three times from weak_conv_topology_eq_prob_algebra + borel_of_subtopology + measurable_restrict_space2:
- Pasting Sk;
- Euler r1/r2;
- Kernels r1/amb, in the reverse direction.
The LP-class part is built twice: Pasting Ssub = Kernels 82-89.
All of it is paper-free: it holds for any Polish X and any subset C.

Evidence: /opt/Isabelle2026-RC3/src/HOL/Analysis/Sigma_Algebra.thy:2185:
  lemma measurable_restrict_space2_iff: "f ∈ measurable M (restrict_space N Ω) ⟷ (f ∈ measurable M N ∧ f ∈ space M → Ω)"
Kernels:63-64:
  ‹a map into a restricted space that LANDS in the restricting set is measurable into the ambient space›
weak_conv_topology_eq_prob_algebra: AFP Levy_Prokhorov_Metric/Space_of_Finite_Measures.thy:552.

Suggested action: Add one paper-free iff lemma in Continuous_Path_Spaces (or next to the path metric), for Polish X: f ∈ M →M prob_algebra (borel_of X) ⟷ (f ∈ M →M borel_of (weak_conv_topology X) and f lands in the probability measures). Add a corollary for a subset C carrying a subspace metric. Use it in Pasting, Kernels and Euler_Construction.


### RA-dpp-10. Rational-pair to real-time diffquot argument copied many times; exit_class_diffquot_of_rational_pairs duplicates exit_class_diffquot_of_pairs

*clone, impact medium, confidence high, ~250 lines.*  
Locations: Dynamic_Programming_Conditioning.thy:554-604 exit_class_diffquot_of_rational_pairs; Exit_Class_Pasting.thy:21-73 exit_class_diffquot_of_pairs; Dynamic_Programming_Conditioning.thy:686-704, 1275-1301; Dynamic_Programming_Kernels.thy:1291-1314, 1320-1341; Dynamic_Programming_Delayed_Class.thy:650-670, 887-907

exit_class_diffquot_of_rational_pairs has the same proof as exit_class_diffquot_of_pairs; only the hypothesis carries the extra premises p ∈ ℚ, q ∈ ℚ. It is the stronger lemma, and the other is a one-line corollary.
Separately, the nested block 'AE_ball_countable' [OF _ countable_rat] twice, then a case split on the guard' (about 20 lines) appears 7 times in the cluster and 13 times in the repository.
The one-pair-to-all-pairs pipeline (closedin_diffquot_constraint, AE_distr_iff, rationals, diffquot_all_of_rational(_ge)) is re-run in pfut_rcd_diffquot, pdelclass_diffquot, pstopped_law_diffquot, aglue_law_diffquot (via exit_class_diffquot_of_pairs) and the dead pfut_law_diffquot and AE_rcd_*.

Evidence: Conditioning:557:
  "⋀p q. p ∈ ℚ ⟹ q ∈ ℚ ⟹ p ∈ {0..T} ⟹ q ∈ {0..T} ⟹ p < q ⟹ AE ω in Q. ... ∈ sconstraint k L"
Exit_Class_Pasting:24:
  "⋀p q. p ∈ {0..T} ⟹ q ∈ {0..T} ⟹ p < q ⟹ AE ..."
The bodies (spQ, rat, eventually_elim, diffquot_all_of_rational) are identical.
grep -c "AE_ball_countable'\[OF _ countable_rat\]": 26 hits across 8 theories.

Suggested action: Keep only the rational-pair version, stated for covariation_class / a closed S, in Exit_Class_Pasting or lower, and derive the other in one line. Add a lemma AE_rat_pairs (AE over ℚ×ℚ from per-pair AE) to Continuous_Path_Spaces.Increment_Moments. Consider also a lemma that the whole set {w ∈ space (path_borel T). ∀s t. ... ∈ S} is measurable for closed S (the finite-horizon analogue of pairpath_diffquot_sets, Exit_Class_Marginals:864). Each transfer would then be a single AE_distr_iff.


### RA-dpp-11. The cluster needs only closedness and convexity of sconstraint k L: concrete G11 data

*generalisation, impact medium, confidence high, ~100 lines.*  
Locations: Dynamic_Programming_Additive_Glue.thy:77 (sconstraint_convex); Dynamic_Programming_Conditioning.thy:47,601,650; Dynamic_Programming_Delayed_Class.thy:622,690,840,928; Dynamic_Programming_Kernels.thy:1179; Dynamic_Programming_Additive_Glue.thy:125

Of the constraint set, the cluster uses only these:
- closed_sconstraint and closedin_diffquot_constraint (9 uses), for measurability of the per-pair set and for the rational-to-real extension;
- sconstraint_convex, once, in padd_diffquot.
sconstraint_def is never unfolded.
So every covariation statement can be stated for an arbitrary closed (convex) S at the covariation_class level of Pair_Path_Laws:4038 with unchanged proofs: pfut_rcd_diffquot, exit_class_rcd_member, pdelclass*, pstopped_law_diffquot, aglue_law_diffquot, padd_diffquot, exit_class_aglue*. Only the 11 exit_class_def unfoldings need rewriting.
The value-function statements still mention exit_val k L, but exit_val_eq_covariation_val already exists. This answers part of what §11 of the plan lists as open ('the remaining ~215 consumers ... fifteen theories').

Evidence: grep -n "closed_sconstraint\|sconstraint_convex\|closedin_diffquot_constraint\|sconstraint_def" Dynamic_Programming_*.thy: 10 hits, none of them sconstraint_def.
sconstraint appears 99 times in the cluster, all inside statements.

Suggested action: When migrating G11, do this cluster in one pass: replace sconstraint k L by a closed (convex) S and exit_class k L by covariation_class S, keeping exit_class versions as one-line specialisations where Value_Function_* needs them.


### RA-dpp-12. Prop. 2.4 (eq. (2.9)) is never stated, despite the session abstract and Conditioning's section header

*faithfulness, impact medium, confidence high, ~40 lines.*  
Locations: Relative_Arbitrage/document/root.tex:34-36; Dynamic_Programming_Conditioning.thy:1076-1087; Dynamic_Programming_Pasting.thy:12-16, 684-685; Statement/EM_final_paper.tex:376-385 (Prop. 2.4)

Prop. 2.4 asserts v(x) = sup_P P-ess-inf(θ∧τ_K + v(X_θ) 1{θ ≤ τ_K}) for every stopping time θ, with the supremum attained by any optimizer. The formalisation proves:
- (i) the >= half at measurable path stopping times (exit_val_dpp_sup_ge_time);
- (ii) a pathwise conditioning bound AE c ≤ θ + v_{T-θ}(X_θ) for every c ≤ ess-inf τ_K (exit_val_cond_time);
- (iii) an undischarged reduction of the deterministic <= half (exit_val_dpp_le_of_cond).
No theorem combines them into the equality, at any time. The attainment clause is absent.
This is harmless for Theorem 1.1: Value_Function_* uses only (i) and (ii), and the finite-horizon value with v_{T-θ} in the integrand is a deliberate design. But:
- root.tex claims 'The dynamic programming principle ... is proved here in full, at a deterministic time and at a stopping time';
- Conditioning:1076 opens a section 'The dynamic programming principle at a deterministic time' that contains only text describing a non-existent combination.
The formal integrand also encodes 1{θ ≤ τ_K} as 'pexit θ K X = θ ∧ X θ ∈ K'. That is equivalent for closed K and continuous paths, and is documented.

Evidence: grep -rn 'shows "exit_val k L T K x =' and '= (SUP P ∈ exit_class' over *.thy: no DPP equality.
root.tex:34-36:
  'The dynamic programming principle their proof defers to Larsson and Ruf is proved here in full, at a deterministic time and at a stopping time'.
Conditioning:1078-1082:
  'Proposition 2.4 ... at a deterministic θ = r, unconditionally. The ≥ half is exit_val_dpp_sup_ge ...; the ≤ half is exit_val_dpp_le_of_cond with its one hypothesis discharged by exit_val_cond'. No such theorem follows.

Suggested action: Either add a short theorem exit_val_dpp (the equality) or correct the abstract and the section text. At a deterministic time it is exit_val_dpp_sup_ge plus exit_val_dpp_le_of_cond[OF exit_val_cond]. At stopping times, the <= half follows from exit_val_cond_time by the pathwise case split of exit_val_dpp_le_of_cond with r := θ ω. Otherwise delete exit_val_dpp_le_of_cond.


### RA-dpp-13. About 240 blank lines and about 35 orphan text blocks: prose separated from lemmas moved in restructuring phase 6, in both directions

*documentation, impact medium, confidence high, ~400 lines.*  
Locations: Dynamic_Programming_Pasting.thy:84-89 (describes a strict variant of pexit_pglue_split; followed by exit_val_measurable_selector_kernel'), 153-160, 556-563, 684-686; Dynamic_Programming_Conditioning.thy:15-26, 518-524 (empty subsection), 526-536 (empty subsection), 538-553, 606-610, 727-770 (subsection + 35 blank lines), 842-854, 880-891, 1076-1087 (empty section); Dynamic_Programming_Kernels.thy:92-98, 183-211 (four text blocks, no lemma), 871-872, 1065-1068, 1081-1085, 1087-1130 (subsection + 34 blank lines), 1345-1368 (empty section 'The F_sigma layer'); Dynamic_Programming_Optional_Sampling.thy:11-30; Dynamic_Programming_Stopping_Clauses.thy:48-52, 108-135 (empty section); Dynamic_Programming_Additive_Glue.thy:12-29, 175-194, 236-251; Dynamic_Programming_Delayed_Class.thy:87-90, 232-246, 794-807, 940-952, 1303-1330 (empty section and subsection); Path_Splicing.thy:1312-1316, 1386-1400, 1906-1923; Path_Law_Sampling.thy:2816, 3336-3346; Path_Law_Pasting.thy:1083, 2036, 2916; Exit_Class_Optimizer.thy:452-470

The DPP theories are full of text blocks whose lemma left in the phase-6 carve-out, followed by runs of 4 to 35 blank lines (18 runs, about 240 lines). Several sections and subsections are empty:
- Conditioning 518, 526, 1076;
- Kernels 1087, 1355;
- Stopping_Clauses 108;
- Delayed 1303/1319.
The mirror image is in the paper-free path layer, where prose describing DPP lemmas that stayed behind now sits next to unrelated lemmas:
- Path_Splicing:1312 introduces 'exit_val_measurable_selector_kernel' below' right before ploc_nonneg;
- Path_Splicing:1386-1400 is the proof sketch of exit_val_cond;
- Path_Splicing:1906-1923 describes the deleted stopping-time r.c.d. clauses;
- Path_Law_Sampling:3336-3346 is the docstring of exit_class_rcd_member, at the end of a path-layer theory, mentioning 'the paper's class (1.7)';
- Exit_Class_Optimizer:452-458 describes exit_val_measurable_selector_kernel', which lives in DP_Pasting.
Because the `section` headers are doubled, each theory also opens with two consecutive section headings (Kernels 1 and 15 are identical). There are layout slips too: Stopping_Clauses:40 'show "0 < T" by (rule T0)    fix s', Additive_Glue:171 'qed    qed'.

Evidence: A blank-run scan (runs of 4 or more) gives, e.g., Conditioning:736-770 (35 blank), Kernels:1097-1130 (34), Optional_Sampling:12-30 (19), Additive_Glue:13-29 (17). 505 blank lines in 6214.
Path_Law_Sampling:3338-3345:
  ‹The regular conditional distribution ... lies ... in the paper's class (1.7) at the origin ...›
immediately followed by 'end'.

Suggested action: Re-attach each text block to its lemma or delete it. Remove the blank runs, empty sections and the duplicate inner `section` commands (make them `subsection`). Move the DPP prose out of Path_Splicing, Path_Law_Pasting, Path_Law_Sampling and Exit_Class_Optimizer back to the DPP lemmas it describes.


### RA-dpp-14. Basic exit_val and class facts live in the DPP layer although the rest of the development needs them

*misplacement, impact medium, confidence high, ~330 lines.*  
Locations: Dynamic_Programming_Pasting.thy:161 exit_class_start (used in 9 theories); Dynamic_Programming_Pasting.thy:174 exit_val_open_less, :187 exit_val_neq_top, :197 exit_val_borel_measurable; Dynamic_Programming_Pasting.thy:91 exit_val_measurable_selector_kernel'; Dynamic_Programming_Delayed_Class.thy:139 exit_val_horizon_cap; Dynamic_Programming_Assembly.thy:706 enn2real_paper_v_horizon_cap; Dynamic_Programming_Conditioning.thy:180-396 exit_class_shifted_*, exit_class_pfut_comp_martingale; Value_Function_Subsolution.thy:91 exit_val_cond_ball, :2120 exit_val_cond_at_time

Several facts sit in the wrong place:
- exit_class_start is a projection and belongs in Exit_Class.thy.
- exit_val_neq_top, exit_val_open_less and exit_val_borel_measurable are consequences of exit_val_le_T and exit_val_usc_unconditional, and belong in Exit_Class_Witness.
- exit_val_measurable_selector_kernel' is the packaging of exit_val_measurable_selector, and its explanatory text is still in Exit_Class_Optimizer:452-458.
- exit_val_horizon_cap and its enn2real form belong next to exit_val_horizon_mono (Exit_Class_Pasting:966). The enn2real form carries a stale 'paper_v' in its name, the only remaining one in the repository.
- The shifted-martingale facts are about the class restarted at r, like exit_class_pcut in Exit_Class_Pasting.
Conversely, exit_val_cond_at_time ('The DPP capped at an arbitrary [0,T]-valued time') is DPP content placed in Value_Function_Subsolution. exit_val_cond_ball (Value_Function_Subsolution:91) is its instance θ = pball_exit T x ε, proved separately with the same 30-line proof, 2000 lines before the general form.

Evidence: exit_class_start is used by Value_Function_Assembly, Euler_Construction, Subsolution and Supersolution_Case_1/2.
exit_val_cond_ball:
  'by (rule exit_val_cond_time[OF T0 L1 Kc P c th0 thT]) ... enn2real_paper_v_horizon_cap[OF a b L1 Kc]'
exit_val_cond_at_time: identical with θ.
grep 'paper_v' finds only enn2real_paper_v_horizon_cap.

Suggested action: Move each fact as listed. Rename enn2real_paper_v_horizon_cap to enn2real_exit_val_horizon_cap. Move exit_val_cond_at_time to the end of Dynamic_Programming_Conditioning and derive exit_val_cond_ball from it in one line.


### RA-dpp-15. Hypothesis Kb of exit_class_kglue_law' is derivable from Kp and Kc, so the LP-measurability packaging is unnecessary

*generalisation, impact medium, confidence medium, ~120 lines.*  
Locations: Exit_Class_Optimizer.thy:472-484 exit_class_kglue_law' (Kb); Dynamic_Programming_Kernels.thy:34-90 kernel_class_LP_measurable, :253-297 (derivation of Kb from Kp); Dynamic_Programming_Pasting.thy:96-99,128-140 (second conclusion of exit_val_measurable_selector_kernel'); Value_Function_Euler_Construction.thy:679-779 sbm_kernel_package (second conclusion)

kernel_class_LP_measurable shows that measurability into the class carrying its Levy-Prokhorov metric is free once the kernel is measurable into prob_algebra and lands in the class. Kernels 253-261 also shows that the natural filtration at r of the r-path space is all of sets Q (sets_natural_filtration_path).
Together these discharge Kb of exit_class_kglue_law' from its Kp and Kc, with no further assumption: 0 < T and 1 <= L are already hypotheses.
This removes a hypothesis from a central lemma (it has 4 call sites). It also makes the second conclusion of exit_val_measurable_selector_kernel' and of sbm_kernel_package unnecessary, about 40 lines of continuity-to-LP-measurability work in Euler_Construction.

Evidence: Kernels:22-24:
  ‹Every further kernel construction needs it too, so here it is as a factory: Kb is free once the kernel is measurable into prob_algebra and lands in the class.›
Kernels:289-297 derive KpF and Kb from Kp, Kc and nfQ, then feed them to exit_class_kglue_law'.

Suggested action: Move kernel_class_LP_measurable (stated for any subset C of the probability measures) next to exit_class_kglue_law' and derive Kb inside it. Drop Kb from the statement and from its callers.


### RA-dpp-16. Paper-free pieces of the DPP layer that belong to the path toolkit or the library sessions

*misplacement, impact medium, confidence medium, ~500 lines.*  
Locations: Dynamic_Programming_Assembly.thy:220-258 selker, selker_measurable; Dynamic_Programming_Delayed_Class.thy:953-1202 (core of pstopped_law_horizon_*), 808-938 pstopped_law_diffquot; Dynamic_Programming_Additive_Glue.thy:30-173 padd_diffquot, aglue_law_diffquot; Dynamic_Programming_Assembly.thy:827-857 dpp_integrand_pstopped; Dynamic_Programming_Kernels.thy:500-593 (core of exit_val_dpp_sup_ge_time_of_const); Dynamic_Programming_Kernels.thy:148-181 kernel_repair_into_class (if kept)

These statements say nothing about the paper once generalised as above:
- selker Sel θ p' = Sel (θ p', fst (p' (θ p'))) and its measurability: kernel at a stopping time, Path_Stopping_Times/Path_Law_Pasting;
- the stopped pushforward of a horizon square-integrable martingale of a continuous path functional: Path_Law_Sampling, next to pstopped_law_prob/start/idem/cont;
- pstopped_law_diffquot and aglue_law_diffquot for closed S, and padd_diffquot for convex S: Path_Law_Pasting / Path_Splicing;
- dpp_integrand_pstopped: any functional that reads only θ and the path on [0,θ] is pstopped-invariant, Path_Stopping_Times;
- the ess-inf constant reduction: Essential_Infimum;
- the capped-process time change: Martingale_Algebra / Pair_Path_Laws.
What remains paper-specific is pdelclass, the selector at every horizon, the conditioning statements and the assembled >= half.

Evidence: selker_measurable uses only path_eval_at_measurable_time, pair_fst_borel-style measurability and Sm.
The pstopped_law_horizon_* proofs use exit_class only to obtain HZ (exit_class_horizon_component) and setsP.

Suggested action: After the generalisations above, move these statements down. This also lowers the plan's '76 statements outside the path layer that name no paper constant'.


### RA-dpp-17. padd_diffquot repeats the convex-combination split of pglue_diffquot

*clone, impact low, confidence high, ~50 lines.*  
Locations: Dynamic_Programming_Additive_Glue.thy:30-93 padd_diffquot (mid case 66-91); Exit_Class_Pasting.thy:235-? pglue_diffquot (mid case)

Both lemmas share their key step verbatim:
- (r-s)/(t-s) ?a + (t-r)/(t-s) ?b ∈ S by convexD;
- the sum1 identity;
- the e1 and e2 rescalings;
- scaleR_right_distrib.
The generic fact is paper-free: for convex S and s < r < t, if (1/(r-s))(Y r - Y s) ∈ S and (1/(t-r))(Y t - Y r) ∈ S, then (1/(t-s))(Y t - Y s) ∈ S. Both lemmas are also pure function surgery, hard-wired to 'n pairpath and sconstraint k L.
Padd_diffquot's hypothesis T0 (0 ≤ T) is unused and implied by r0 and rT.

Evidence: Additive_Glue:73-91 and Exit_Class_Pasting (mid case) both contain:
  have sum1: "(r - s) / (t - s) + (t - r) / (t - s) = 1" by (subst add_divide_distrib[symmetric]) ...
  have cc: "... ∈ sconstraint k L" using pos by (intro convexD[OF sconstraint_convex aA bB] sum1) auto

Suggested action: Add diffquot_convex_split to Continuous_Path_Spaces.Increment_Moments, next to diffquot_all_of_rational. Restate padd_diffquot and pglue_diffquot for 'real ⇒ 'a × 'b::real_normed_vector' and a convex S, in Path_Splicing.


### RA-dpp-18. pexit_path_measurable, pair_fst_borel and enn2real_leI re-derived inline many times

*library_duplicate, impact low, confidence high, ~110 lines.*  
Locations: Dynamic_Programming_Delayed_Class.thy:170-177; Dynamic_Programming_Assembly.thy:42-49, 145-153, 762-769; Dynamic_Programming_Pasting.thy:276-278; Dynamic_Programming_Kernels.thy:730-732, 908-910; Dynamic_Programming_Delayed_Class.thy:495-497, 1025-1027, 1056-1058; Dynamic_Programming_Assembly.thy:248-250, 751-753; Dynamic_Programming_Pasting.thy:355-360, 473-492; Dynamic_Programming_Kernels.thy:525-548, 635-639; Dynamic_Programming_Assembly.thy:66-72

Three facts are re-proved inline instead of cited:
- The measurability of (λω. pexit T K (λt. fst (ω t))) is re-proved four times with pfst_measurable + pexit_measurable + pexit_pfst. That is exactly pexit_path_measurable (Path_Splicing:1350), which Pasting itself uses.
- 'fst :: real^n × real^n^n ⇒ real^n is Borel' is re-proved 8 times. It is pair_fst_borel (Continuous_Time_Martingales.Integrability_Criteria:749), which Conditioning and Kernels:279 do use.
- 'enn2real (exit_val k L S K y) ≤ S' is proved five times, in 6-20 lines each, through exit_val_neq_top + ennreal_enn2real + exit_val_le_T. With HOL's enn2real_leI it is one line: enn2real_leI[OF S0 exit_val_le_T[OF S0]].

Evidence: Path_Splicing:1350:
  lemma pexit_path_measurable ... shows "(λω. pexit T K (λt. fst (ω t))) ∈ borel_measurable N"
Integrability_Criteria:749:
  lemma pair_fst_borel: "(fst :: 'a × 'b ⇒ 'a) ∈ borel_measurable borel"
Extended_Nonnegative_Real.thy:1057:
  lemma enn2real_leI: "0 ≤ B ⟹ x ≤ ennreal B ⟹ enn2real x ≤ B"

Suggested action: Cite the library lemmas. Add enn2real_exit_val_le next to exit_val_le_T (Exit_Class_Witness:906) for readability.


### RA-dpp-19. exit_val_horizon_cap re-does the core computation of ess_inf_pexit_pcut_law

*clone, impact low, confidence high, ~30 lines.*  
Locations: Dynamic_Programming_Delayed_Class.thy:169-198 (val, in exit_val_horizon_cap); Path_Law_Pasting.thy:1032-1080 ess_inf_pexit_pcut_law

Both blocks prove ess_inf_time (pair_law_of S (pcut S) R) (pexit S K ...) = min (ess_inf_time R (pexit T K ...)) S. The steps are the same: cutm, taum (re-deriving pexit_path_measurable), ess_inf_time_distr, pexit_cong_on with pcut_apply, pexit_min_horizon, ess_inf_time_min_const. The path-layer version only adds a pshift.

Evidence: Delayed:180-198 vs Path_Law_Pasting:1058-1080: the same ess_inf_time_distr[OF cutm mset] followed by pexit_min_horizon[OF S0 ST, of K ...].

Suggested action: Split ess_inf_pexit_pcut_law into an unshifted core lemma plus the pshift step, and use the core in exit_val_horizon_cap.


### RA-dpp-20. exit_val_borel_measurable takes 42 lines where HOL-Analysis gives about 4; exit_val_neq_top and exit_val_real_usc are over-built

*simplification, impact low, confidence high, ~55 lines.*  
Locations: Dynamic_Programming_Pasting.thy:197-238 exit_val_borel_measurable; Dynamic_Programming_Pasting.thy:187-195 exit_val_neq_top; Value_Function_Uniqueness.thy:158-196 exit_val_real_usc (fin block 174-181)

- exit_val_borel_measurable: exit_val, as an ennreal function, is Borel by borel_measurableI_less, because its sublevel sets are open (exit_val_open_less) and hence Borel. The real version is then borel_measurable_enn2real. The current proof case-splits on 0 < a and converts enn2real < a by hand, and needs finiteness.
- exit_val_neq_top: neq_top_trans[OF ennreal_neq_top exit_val_le_T].
- exit_val_real_usc (Value_Function_Uniqueness): re-proves finiteness of exit_val from the ball bound and so needs hypotheses kn and KB that exit_val_neq_top makes unnecessary.
- More generally, 'usc ⇒ Borel' is paper-free and belongs in Semicontinuous_Analysis, which has no measurability lemma for semicontinuous functions.

Evidence: /opt/Isabelle2026-RC3/src/HOL/Analysis/Borel_Space.thy:618:
  lemma borel_measurableI_less: "(⋀y. {x∈space M. f x < y} ∈ sets M) ⟹ f ∈ borel_measurable M"
Borel_Space.thy:1555: borel_measurable_enn2real
Extended_Nonnegative_Real.thy:1807: neq_top_trans

Suggested action: Re-prove exit_val_borel_measurable in about 4 lines. Optionally add 'upper semicontinuous ⇒ borel_measurable' to Semicontinuous_Analysis. Drop kn and KB from exit_val_real_usc's finiteness step.


### RA-dpp-21. pdelclass_frozen_at is an instance of pdelclass_frozen; the pdelclass unpacking block is repeated seven times

*clone, impact low, confidence high, ~90 lines.*  
Locations: Dynamic_Programming_Delayed_Class.thy:50-85 pdelclass_frozen_at; Dynamic_Programming_Delayed_Class.thy:91-123 pdelclass_frozen; Dynamic_Programming_Delayed_Class.thy:36-43, 57-64, 98-105, 452-458, 518-524, 601-606, 1228-1233, 1268-1273

- pdelclass_frozen_at (AE w. w u = 0 for one u ≤ s) follows from pdelclass_frozen by eventually_mono. Its separate 36-line proof duplicates the latter. It is used only by pdelclass_start_zero.
- Seven pdelclass lemmas open with the same block: 'obtain μ from pdelclass_def, setsmu, pm: pembed s T ∈ μ →M ?B'.
- pdelclass is a generic construction, the pembed image of any set of laws on the (T-s)-space. Its prob, sets and frozen facts need only the start clause.

Evidence: Delayed:57-64 and 98-105:
  from m obtain μ where mu: "μ ∈ exit_class k L (T - s) 0" and nu: "ν = distr μ ?B (pembed s T)" unfolding pdelclass_def by blast
  have setsmu ... have pm: "pembed s T ∈ μ →M ?B" ...

Suggested action: Add pdelclassE, returning μ, ν = distr μ ... and pm. Derive pdelclass_frozen_at, or drop it and use pdelclass_frozen directly in pdelclass_start_zero. Consider defining pdelclass over an arbitrary set of laws, or over covariation_class S.


### RA-dpp-22. Class facts in Stopping_Clauses duplicate inline constructions in Exit_Class_Limits and belong there

*misplacement, impact low, confidence high, ~110 lines.*  
Locations: Dynamic_Programming_Stopping_Clauses.thy:23-46 exit_class_horizon_component; Dynamic_Programming_Stopping_Clauses.thy:54-77 exit_class_comp_entry_sq_integrable; Dynamic_Programming_Stopping_Clauses.thy:81-106 exit_class_horizon_compensated; Exit_Class_Limits.thy:887-889, 972-974; Exit_Class_Limits.thy:1627 exit_class_comp_entry_sq_nn

Exit_Class_Limits builds 'horizon_sq_int_martingale Q ?F (pcoord T i) T' inline twice. Since pcoord T i u ω = fst (ω (min u T)) $ i (Path_Splicing:1208), that is literally the statement of exit_class_horizon_component.
exit_class_comp_entry_sq_integrable is the immediate corollary (integrableI_bounded) of exit_class_comp_entry_sq_nn in Exit_Class_Limits.
None of the three mentions stopping times or the DPP.

Evidence: Exit_Class_Limits:887-889:
  interpret HM: horizon_sq_int_martingale Q ?F "pcoord T i" T by (intro horizon_sq_int_martingale.intro horizon_sq_int_martingale_axioms.intro mg T prob sq)
Path_Splicing:1209:
  pcoord T i u ω = fst (ω (min u T)) $ i

Suggested action: Move the three lemmas to Exit_Class_Limits, after exit_class_comp_entry_sq_nn, and use exit_class_horizon_component at 887 and 972. Delete Dynamic_Programming_Stopping_Clauses.


### RA-dpp-23. Redundant or unused hypotheses in cluster statements

*simplification, impact low, confidence high, ~60 lines.*  
Locations: Dynamic_Programming_Additive_Glue.thy:205 exit_class_aglue_law (K0); Dynamic_Programming_Assembly.thy:286-288 exit_class_aglue_selector (QXint, QCint); Dynamic_Programming_Assembly.thy:23 aglue_law_pexit_ge (L1); Dynamic_Programming_Assembly.thy:128 selector_value_AE (Pnu); Dynamic_Programming_Pasting.thy:566 exit_val_dpp_le_of_cond (L1, K); Dynamic_Programming_Additive_Glue.thy:32 padd_diffquot (T0); Dynamic_Programming_Assembly.thy:829 dpp_integrand_pstopped (T0); Dynamic_Programming_Pasting.thy:29 exit_val_kpaste_ge (T0, implied by r and rT)

- K0 of exit_class_aglue_law is Kfr at u = 0. The proof of exit_class_aglue says so itself (325-327) and derives it.
- QXint and QCint of exit_class_aglue_selector follow from QH and QHC. Its only caller derives them exactly so (Assembly 623-653).
- L1 (aglue_law_pexit_ge), Pnu (selector_value_AE), L1 and closed K (exit_val_dpp_le_of_cond), and T0 (padd_diffquot, dpp_integrand_pstopped) never occur in their proofs.

Evidence: Additive_Glue:325:
  ‹K0 is redundant: it is Kfr at u = 0.›
Assembly:622-653: QXint from QH via integrable_vec_components, QCint from QHC via martingale_matI.
A heuristic scan for labels absent from the proof body flagged L1 (Assembly:23), Pnu (Assembly:128) and T0 (Additive_Glue:32, Assembly:829); L1 and K in Pasting:566 were checked by hand.

Suggested action: Drop K0 from exit_class_aglue_law. Move the QXint/QCint derivation into exit_class_aglue_selector and drop those hypotheses. Remove the unused hypotheses.


### RA-dpp-24. Glue families repeat the same three-step pattern: class membership, pathwise DPP bound, AE bound to value bound

*clone, impact low, confidence high, ~60 lines.*  
Locations: Exit_Class_Pasting.thy:1076 exit_val_paste_ge (pglue, unused); Dynamic_Programming_Pasting.thy:26 exit_val_kpaste_ge (kglue); Dynamic_Programming_Assembly.thy:580 exit_val_ge_of_stopped_bound (aglue); Dynamic_Programming_Conditioning.thy:856 exit_val_ge_of_AE_pshift (pshift); Dynamic_Programming_Kernels.thy:863-868, Assembly.thy:684-692; Path_Splicing.thy:1261 pexit_pglue_dpp vs :1950 pexit_padd_dpp

Each glue operation (pglue, kglue, aglue) re-proves three things:
- class membership: exit_class_pglue_law, exit_class_kglue_law' and exit_class_aglue_law/exit_class_aglue;
- a pathwise DPP inequality: pexit_pglue_dpp vs pexit_padd_dpp;
- the step 'R ∈ exit_class k L T x and AE ω in R. c ≤ pexit T K (fst ∘ ω) give ennreal c ≤ exit_val k L T K x'. This last step is inlined 5 times as an ess_inf_time_def/Sup_upper plus exit_val_def/SUP_upper pair.
With the kglue >= half and the dead kglue_mixed route gone, only aglue (stopping time) is needed for the DPP. kglue stays for the Euler construction (Value_Function_Euler_Construction:797) and the optimizer. pglue stays for Exit_Class_Infinite.

Evidence: Pasting:74-78:
  'unfolding ess_inf_time_def using ae by (intro Sup_upper) simp ... unfolding exit_val_def using G by (intro Sup_upper imageI)'
The same at Assembly:684-691, Conditioning:870-876, Kernels:863-867 and Exit_Class_Pasting (exit_val_paste_ge).

Suggested action: Add exit_val_ge_of_AE (two lines) to Exit_Class_Witness and use it everywhere. Delete exit_val_paste_ge, which is unused. Once the deterministic >= half is a corollary, pexit_pglue_dpp loses its last users.


### RA-dpp-25. DPP-integrand measurability proved at deterministic times (three copies) next to the general stopping-time lemma

*clone, impact low, confidence high, ~70 lines.*  
Locations: Dynamic_Programming_Pasting.thy:319-343; Dynamic_Programming_Kernels.thy:744-766, 922-943; Dynamic_Programming_Assembly.thy:732-821 dpp_integrand_measurable_stopping

Pasting and Kernels each rebuild g (the DPP integrand at r) with taum, endm, vm, predm, gm, gset and gcut. dpp_integrand_measurable_stopping is the general θ version, of which these are the constant instances. Kernels:1065-1068 even announces that the gm/gcut pair is 'pulled out so the chain's measurability induction can reuse them', but no such lemma exists.

Evidence: Kernels:1065:
  text ‹The integrand at a fixed time is a random variable on the t-path space, and it only reads [0,t] --- the two facts the gm/gcut pair of exit_val_dpp_ge_step needs, pulled out ...›
No lemma follows.

Suggested action: Goes away with the deterministic >= half and Kernels clean-up. Otherwise instantiate dpp_integrand_measurable_stopping at θ = λ_. r.


### RA-dpp-26. Essential_Infimum, in a paper-free session, carries paper prose, an empty section and a near-duplicate lemma that the DPP layer uses

*documentation, impact low, confidence high, ~40 lines.*  
Locations: Continuous_Time_Martingales/Essential_Infimum.thy:74, 114, 140, 158-160, 245-247, 249-253, 268-271; Continuous_Time_Martingales/Essential_Infimum.thy:255 ess_inf_time_distr_measurable vs :274 ess_inf_time_distr

This theory lives in Continuous_Time_Martingales, outside this cluster, but it is the ess-inf library the DPP layer runs on. It cites Eq. (1.6), (1.7) and (2.9), Proposition 2.4, Lemma 2.3, Larsson-Ruf's Lemma 2.1 and Berge's theorem.
It also has:
- a section 'The class P_x and the value function of Eq. (1.6)' containing no class;
- a 'Superadditivity' text block with no lemma (245-247).
And ess_inf_time_distr_measurable is a corollary of ess_inf_time_distr: measurability of tau gives the sets hypothesis. Both exist with separate proofs.

Evidence: Essential_Infimum:268:
  section ‹The class P_x and the value function of Eq. (1.6)›
followed only by ess_inf_time_distr and ess_inf_distr.
Line 158:
  'Calculus for ess_inf_time, needed by Proposition 2.4: the dynamic programming principle of Eq. (2.9) ...'

Suggested action: Rewrite the prose in paper-free terms. Delete the empty section and the orphan text. Derive ess_inf_time_distr_measurable from ess_inf_time_distr. This is also the home for the ess-inf constant-reduction lemma proposed above.


## RA-value1

The cluster is Relative_Arbitrage/Value_Function_Subsolution.thy (3484 lines) and Relative_Arbitrage/Value_Function_Euler_Construction.thy (3491 lines). I read both files in full. I checked claims about other theories with grep and Read. No PIDE session was running and no heaps for these sessions were built, so nothing below was replayed in Isabelle: every derivation claim is a textual check of statements and proofs.

Subsolution half (Section 3.1, clause (2) of Thm 1.1). The proof that is actually used runs in this order:
- exit_val_attained gives an optimiser.
- DPP at the stopping time min t (pball_exit): exit_val_cond_at_time.
- Moments at that stopping time: exit_class_stopped_moments, obtained by optional stopping through pstopped_law_horizon_* and horizon_sq_int_martingale_stopped.
- The averaged covariation lies in sconstraint: exit_class_Y_stopped_mean_sconstraint.
- Anti-concentration dichotomy (exit_val_touch_near_orth), then a compactness step to an exactly orthogonal direction (exit_val_touch_orth).
- Capped spectral split from sconstraint to a feasible witness (sconstraint_orth_feasible).
- Conclusions: exit_val_visc_subsol, and the boundary clause exit_val_subsol_bc.

The formal statements are at least as strong as Definition 3.1(a): local touching, ell_op <= 1 in the interior, and ell_op_lsc <= 1 at boundary points with v>0. No faithfulness problem here.

The first part of the file (Ito-free expansion at a deterministic time, ell_op_s, exit_val_subsol_quadratic_global) is a superseded route and is dead code. NOTES_FOR_AUTHORS.md §1 describes that dead route as the proof. Its claims of "no stopping time, no optional sampling" and "only the supersolution half needs a p = 0" are false for the formal proof.

Euler construction (used by Supersolution Case 1). The parts are:
- The constant-volatility Gaussian member sbmpair and its class membership.
- Weak continuity in S, and the kernel measurability package.
- The Euler law eulerp built by kglue_law', with class membership by induction.
- Second-moment and Chebyshev bounds for the compensated grid functional euXi.
- Orthogonal increments and the exact quadratic telescope along the grid.
- Weak limit, vanishing bad event, and the a.s. growth statement at the ball exit (eulerp_limit_exit).

Main structural problems:
(1) About 750 lines of the Euler file are ball special cases of "region" theorems proved downstream in Value_Function_Supersolution_Case_1.
(2) The sbmpair package (about 390 lines) is a copy of the bmpair package in Exit_Class_Witness; bmpair is sbmpair at S = mat 1.
(3) Value_Function_Subsolution contains a verbatim duplicate of the main theorem, a duplicated moment computation, two hand-unfolded "mean in a closed convex set" arguments, and about 520 lines of dead code.
(4) Paper-free material is mixed in:
  - pball_exit and its lemmas: path layer;
  - Brownian fourth moments: Wiener_Measure;
  - generic Markov/portmanteau/second-moment re-proofs;
  - the outer-product toolkit, which was moved into Pair_Path_Laws.
(5) Value_Function_Euler_Construction imports Value_Function_Subsolution only for pball_exit, and Doubling_Of_Variables only for dist_pair_le. This serialises the build behind the 7 Dynamic_Programming theories and Subsolution.

Restructuring proposal:
- Value_Function_Subsolution splits into:
  (a) pball_exit lemmas: pair path layer (Path_Stopping_Times), with generic open-set exit facts going to Continuous_Path_Spaces.Path_Exit_Times;
  (b) Exit_Class_Stopped_Moments (after Dynamic_Programming_Delayed_Class);
  (c) the subsolution argument proper, at about 1500 lines.
- sconstraint_orth_feasible goes to Eigenvalue_Bound_Exact, and its outer-product/threshold toolkit to Symmetric_Matrix_Spectra.
- Value_Function_Euler_Construction:
  - imports Exit_Class_Optimizer, Exit_Class_Shift, Exit_Class_Limits, Path_Law_Pasting and the pball layer instead of Value_Function_Subsolution;
  - absorbs the region theorems from Case_1 and keeps the ball versions as corollaries;
  - gets sbmpair from an upstream theory merged with bmpair;
  - moves the Brownian moments to Wiener_Measure.
Expected sizes: Subsolution about 3484 -> 1700 lines, Euler about 3491 -> 2300 lines (net, after absorbing about 600 region lines).


### RA-value1-1. Ball-specialised Euler limit chain duplicates the region theorems proved downstream in Case_1

*clone, impact high, confidence high, ~760 lines.*  
Locations: Relative_Arbitrage/Value_Function_Euler_Construction.thy:1994 eulerp_orth_increments vs Value_Function_Supersolution_Case_1.thy:1131 eulerp_orth_increments_cond; Value_Function_Euler_Construction.thy:2381 eulerp_quad_lower vs Case_1.thy:1318 eulerp_quad_lower_region; Value_Function_Euler_Construction.thy:2877 eulerp_bad_event_null vs Case_1.thy:1478 eulerp_bad_event_null_region; Value_Function_Euler_Construction.thy:3236 eulerp_limit_good vs Case_1.thy:1858 eulerp_limit_good2_region; Pair_Path_Laws.thy:3509 open_quad_bad_event vs :1443 open_quad_bad_event_region; :3852 quad_good_rat_to_real vs :3760 _region; :3944 quad_good_upto vs :3668 _region

Each ball theorem is the region theorem at R = cball x rb or RO = ball x rb. Its kill hypothesis, "transpose (SF z) *v (q + M *v (closest_point (cball x rb) z - x)) = 0" for all z, implies the region hypothesis on R through closest_point_self. The global marg hypothesis implies the restricted one, and ROb holds with Rn = rb. eulerp_limit_good2_region with M1=M2=M, q1=q2=q, cm1=cm2=cm gives eulerp_limit_good. eulerp_orth_increments_cond with the premise discharged gives eulerp_orth_increments. The proofs are near-verbatim copies.

Evidence: diff -w of the bodies: bad_event_null 345 lines vs region 369 lines, only 88 differing lines; quad_lower 151 vs 154, 51 differing; orth_increments 141 vs 176, 73 differing. Case_1:1309 text: "The quadratic lower bound of eulerp_quad_lower, decoupled from the start-centred clamp"; Case_1:1127 "The proof is the committed induction of eulerp_orth_increments with the implication carried through the glue." The only live consumer of the ball chain is eulerp_limit_exit, used at Case_1.thy:598.

Suggested action: Move the four region theorems (and open_quad_bad_event_region, quad_good_*_region from Pair_Path_Laws) into Value_Function_Euler_Construction. Restate eulerp_limit_exit on top of eulerp_limit_good2_region (or a one-quadratic region version), or derive the ball versions as 10-line corollaries. Delete the ball proofs and the ball variants in Pair_Path_Laws.


### RA-value1-2. sbmpair package is a copy of the bmpair package of Exit_Class_Witness (bmpair = sbmpair (mat 1))

*clone, impact high, confidence high, ~380 lines.*  
Locations: Relative_Arbitrage/Value_Function_Euler_Construction.thy:46-433 (sbmpair, sbmpair_apply, continuous_on_sbmpair_path, sbmpair_measurable, prob_space_sbmpair_law, sbmpair_law_start, sbmpair_law_diffquot, sbmpair_adapted, sbmpair_law_X_martingale, sbmpair_law_comp_martingale, sbmpair_law_in_paper_pair_class); Relative_Arbitrage/Exit_Class_Witness.thy:544-878 (bmpair, bmpair_apply, continuous_on_bmpair_path, bmpair_measurable, prob_space_bmpair_law, bmpair_law_start, bmpair_law_diffquot, bmpair_adapted, bmpair_law_X_martingale, bmpair_law_comp_martingale, bmpair_law_in_paper_pair_class); Relative_Arbitrage/Exit_Class_Infinite.thy:396 ibmpair

Exit_Class_Witness defines bmpair T w = restrict (λt. (cbmX 0 t w, t *R mat 1)) {0..T}. Euler defines sbmpair S T w = restrict (λt. (S *v cbmX 0 t w, t *R (S ** transpose S))) {0..T}. The two packages pair up lemma for lemma with the same proofs: the S-version replaces mat 1 by S. bmpair T = sbmpair (mat 1) T, because mat 1 *v v = v and mat 1 ** transpose (mat 1) = mat 1. The rational-countable reduction in *_law_diffquot (about 50 lines each) is also unnecessary: snd of the path is deterministic on [0,T], so the full event is an intersection of closed sets (closedin_diffquot_constraint), hence closed and measurable, and it holds for every ω.

Evidence: bmpair_law_diffquot (Witness:639) and sbmpair_law_diffquot (Euler:153) are textually identical except mat 1 / S ** transpose S and mat_1_in_sconstraint / SST. The comment in bmpair_law_diffquot reads "the rational reduction, exactly as in Exit_Class.exit_class_diffquot_limit".

Suggested action: Define sbmpair upstream (Exit_Class_Witness, right after martingale_cbm_outerp, or a small Gaussian_Member theory) and prove the package once. Add lemma bmpair_eq_sbmpair: bmpair T = sbmpair (mat 1) T, derive the bmpair lemmas as one-liners (or delete them), and relate ibmpair to it. Replace the rational reduction by a closedness argument.


### RA-value1-3. exit_val_visc_subsol is a verbatim copy of exit_val_visc_subsol_any

*clone, impact high, confidence high, ~95 lines.*  
Locations: Relative_Arbitrage/Value_Function_Subsolution.thy:3153-3247 exit_val_visc_subsol; Relative_Arbitrage/Value_Function_Subsolution.thy:3255-3348 exit_val_visc_subsol_any

The two proofs are identical line for line. The only difference is the assumption "x ∈ interior K" in the first, which is never used. The text at 3251 says so: "The proof of exit_val_visc_subsol does not use x ∈ interior K".

Evidence: Both obtain r from test_fun_quadratic_dominates, define ebar = min e0 r / 2, prove touch, apply exit_val_touch_orth and sconstraint_orth_feasible, the same split (trace ((H + δ *R mat 1) ** a) = ...), and finish with field_le_epsilon. exit_val_visc_subsol is used at Value_Function_Uniqueness.thy:657.

Suggested action: Keep exit_val_visc_subsol_any and make exit_val_visc_subsol a one-line corollary at Ω = interior K. Also extract the repeated `split` computation as a trace lemma.


### RA-value1-4. Stopped-moment computation and the DPP/touching block are written out twice in the subsolution argument

*clone, impact high, confidence high, ~300 lines.*  
Locations: Relative_Arbitrage/Value_Function_Subsolution.thy:1637-1730 (inside exit_val_subsol_quadratic_ball) vs 2156-2309 exit_class_stopped_moments; Value_Function_Subsolution.thy:1546-1812 (exit_val_subsol_quadratic_ball) vs 2436-2577 (exit_val_touch_near_orth); Value_Function_Subsolution.thy:593-607, 1567-1581, 2449-2463 (cAE block)

exit_val_subsol_quadratic_ball inlines iXc, EXc, iCc, ECc, iX, EX, ig1-3, Eg1-3, icomp, Ecomp, itrY, EtrY, g4eq, ig4 and Eg4. That is exactly what exit_class_stopped_moments packages 350 lines later. The a.s. part (cAE, dpp, stc, cwAE, posAE, inball, key, ith, et0, bmem, and the final w derivation) is repeated almost verbatim in exit_val_touch_near_orth with θ' = min t pball_exit. The optimiser block, ess_inf_time_AE + Pv + enn2real_mono giving AE u x <= pexit, appears three times. exit_val_subsol_quadratic_ball is used only for the q = 0 case of exit_val_touch_near_orth.

Evidence: Line 1687-1714 and line 2235-2265 are character-identical (the Ecomp proof). Continuous_Time_Martingales.Essential_Infimum:170 ess_inf_time_ge_iff gives the AE bound from equality directly.

Suggested action: Move exit_class_stopped_moments before its first use. Factor a lemma exit_val_subsol_quadratic_stopped: for a path stopping time θ <= pball_exit with θ > 0 a.s., return b ∈ sconstraint with -tr(Mb)/2 <= 1 together with the moments. Derive quadratic_ball and the first half of near_orth from it. Add exit_val_attained_AE (an optimiser with AE enn2real v <= pexit) in Exit_Class_Optimizer.


### RA-value1-5. Mean-in-closed-convex-set argument hand-unfolded twice (sconstraint hard-wired)

*generalisation, impact high, confidence high, ~330 lines.*  
Locations: Relative_Arbitrage/Value_Function_Subsolution.thy:173-295 exit_class_Y_mean_sconstraint; Relative_Arbitrage/Value_Function_Subsolution.thy:1279-1524 exit_class_Y_stopped_mean_sconstraint; Relative_Arbitrage/Pair_Path_Space.thy:788-796 (stranded text describing this argument); Relative_Arbitrage/Covariation_Density.thy:73 integral_mean_in_convex (same argument for HK integrals)

Both lemmas unfold sconstraint_def and Pi_constraint_def, obtaining psd, eigen_ub and Pi_proj facts a.s. They integrate each linear inequality separately (symmetry, the two quadratic-form bounds, one bound per projection) and reassemble. The deterministic version is the constant-θ special case of the stopped one. The real content is generic: for a probability measure, w > 0 a.s. integrable, w*g integrable, AE g ∈ S with S closed and convex, (1/∫w) *R ∫ w*g lies in S. This follows by the separating-hyperplane argument already used in Covariation_Density.integral_mean_in_convex. sconstraint_convex and closed_sconstraint (Exit_Class:56,123) supply the hypotheses. Nine of the 14 sconstraint_def/Pi_constraint_def unfoldings in this cluster are here, which bears on G11 in PLAN §10/§11.

Evidence: Pair_Path_Space.thy:791: "Every condition defining sconstraint is a linear (in)equality in the matrix ... The set is an intersection of closed half-spaces and passes through the integral." No such Bochner/probability lemma exists in HOL-Probability, HOL-Analysis or the repository (grep for convex+integral found only Covariation_Density's HK version). The memT block (1355-1380, 25 lines) re-derives transpose ((1/θ)*R Y) cancellation, which is HOL's transpose_scalar plus scaleR cancellation.

Suggested action: Add a generic lemma (weighted_integral_mean_in_closed_convex) to Continuous_Time_Martingales.Integrability_Criteria, or put it next to integral_mean_in_convex in a paper-free theory. Reduce both lemmas to a few lines over covariation_class S. Delete the deterministic variant (see the dead-code finding).


### RA-value1-6. Deterministic-time quadratic subsolution chain and ell_op_s are unused

*dead_code, impact high, confidence high, ~520 lines.*  
Locations: Value_Function_Subsolution.thy:570 exit_val_subsol_quadratic_global; Value_Function_Subsolution.thy:431 exit_class_quadratic_mean; Value_Function_Subsolution.thy:312 exit_class_X_mean; Value_Function_Subsolution.thy:353 exit_class_quadform_mean; Value_Function_Subsolution.thy:400 exit_class_quadform_integrable; Value_Function_Subsolution.thy:299 exit_class_X_integrable; Value_Function_Subsolution.thy:173 exit_class_Y_mean_sconstraint; Value_Function_Subsolution.thy:150 exit_class_Y_integrable; Value_Function_Subsolution.thy:499-543 ell_op_s, ell_op_s_bdd_below, ell_op_s_le_of_witness

exit_val_subsol_quadratic_global has no users; the grep count is definition plus one text mention. Every listed lemma is used only inside this chain. ell_op_s_bdd_below has one external use, Value_Function_Supersolution_Case_1.thy:29 (ell_op_lt_witness: bdd_below_mono[OF ell_op_s_bdd_below image_mono[OF feasible_subset_sconstraint]]). There Curvature_Operator.ell_op_bdd_below (no hypotheses, exactly the feasible-set statement) suffices. The live proof of clause (2) goes through the stopped-time moments instead.

Evidence: grep -rnw counts: exit_val_subsol_quadratic_global ext=0 int=2; exit_class_quadratic_mean ext=0 int=3 (def, text line 39, use in global); ell_op_s_le_of_witness ext=0 int=2; ell_op_s ext=1 (Pair_Path_Laws.thy:225 prose only).

Suggested action: Delete the chain (about 520 lines), after replacing ell_op_s_bdd_below in Case_1:29 by ell_op_bdd_below. If the identity E[φ(X_t)] = φ(x) + (t/2) tr(M b) is worth keeping for the authors, keep only exit_class_quadform_mean as a corollary of exit_class_stopped_moments at constant θ. Fix the prose that presents it as the proof (see the documentation finding).


### RA-value1-7. NOTES_FOR_AUTHORS §1 and the theory introduction misdescribe how Section 3.1 is proved

*documentation, impact high, confidence high, ~70 lines.*  
Locations: notes/NOTES_FOR_AUTHORS.md:21-57; Relative_Arbitrage/Value_Function_Subsolution.thy:17-44 (intro text, incl. 'PLAN section 2.1'); Relative_Arbitrage/Value_Function_Subsolution.thy:479-493 (what the orthogonality constraint does)

The notes say the subsolution half is proved "with no Itô formula, no exponential local martingale, no optional sampling, no stopping time", that the deterministic-time expansion gives "the operator of (1.9) itself, orthogonality constraint included", and that optional sampling is "used only in the supersolution half". They also say "the supersolution half, and only it, needs the constraint a p = 0". None of this matches the formal proof. exit_val_visc_subsol uses exit_val_touch_orth, then exit_val_touch_near_orth with the stopping time min t (pball_exit), then exit_class_stopped_moments. Those moments come from exit_class_X_entry_stopped via pstopped_law_horizon_component, which applies horizon_sq_int_martingale_stopped (Pair_Path_Laws:1516, optional_stopping with Doob's envelope). The orthogonality comes from the anti-concentration dichotomy plus sconstraint_orth_feasible. The deterministic-time identity only yields the relaxed operator ell_op_s, as the theory itself says at 565-568. The theory intro (lines 35-44) presents exit_val_subsol_quadratic_global as the result. It promises a final section "including two localisation routes that were checked and provably do not work", which does not exist; the file ends with exit_val_subsol_bc. "PLAN section 2.1" points to nothing: notes/PLAN_THEOREM_1_1.md has no §2.1. Text 485-493 says the a.s. orthogonality is something "the supersolution argument needs and the subsolution argument does not", which exit_val_touch_near_orth contradicts.

Evidence: Dynamic_Programming_Delayed_Class.thy:953 pstopped_law_horizon_component proof uses "horizon_sq_int_martingale_stopped(1)" and "path_stopping_time_event_filtration_all". Value_Function_Subsolution.thy:2356: "The Girsanov-free replacement for the paper's exponential martingale ((3.18)--(3.19))". Paper Statement/EM_final_paper.tex:598-668 (Subsection 3.1) uses θ = ball exit ∧ v(x), Itô and an exponential martingale.

Suggested action: Rewrite NOTES §1. The accurate statement: no stochastic integral or exponential martingale is needed. The subsolution half uses a ball exit time, optional stopping (Doob L2 envelope) for the two martingale clauses, an anti-concentration dichotomy replacing (3.17)-(3.19), and a capped spectral split for the a p = 0 constraint. Rewrite the theory intro (lines 17-44, 479-495) to describe the live route.


### RA-value1-8. Witness/boundedness lemmas for ell_op duplicate operator-layer lemmas

*library_duplicate, impact medium, confidence high, ~45 lines.*  
Locations: Value_Function_Subsolution.thy:52 ell_op_le_of_witness; Operator_Envelopes.thy:867 ell_op_le_witness; Value_Function_Subsolution.thy:502 ell_op_s_bdd_below; Curvature_Operator.thy:354 ell_op_bdd_below; Operator_Envelopes.thy:822 ell_op_bdd

ell_op_le_of_witness (a ∈ feasible, -tr(Ma)/2 <= c gives ell_op <= c) is Operator_Envelopes.ell_op_le_witness followed by order_trans. Operator_Envelopes is imported by this theory. ell_op_s_bdd_below repeats the entrywise trace estimate of ell_op_bdd_below with the bound n*L in place of L. Operator_Envelopes.ell_op_bdd is itself a second copy of ell_op_bdd_below, with a superfluous 0 <= L. A bounded set has a bounded-below image under a bounded linear functional, so all three follow from bounded_sconstraint / feasible ⊆ sconstraint.

Evidence: ell_op_le_witness: "assumes L0: 0 <= L and aF: a ∈ feasible k L p shows ell_op k L p M <= - trace (M ** a) / 2". ell_op_bdd_below and ell_op_bdd have the identical conclusion "bdd_below ((λa. - trace (M ** a) / 2) ` feasible k L p)".

Suggested action: Delete ell_op_le_of_witness (use ell_op_le_witness) and ell_op_s_bdd_below. Merge ell_op_bdd into ell_op_bdd_below (other cluster).


### RA-value1-9. Diagonal and trace bounds for eigen_ub matrices proved four or more times

*library_duplicate, impact medium, confidence high, ~80 lines.*  
Locations: Value_Function_Euler_Construction.thy:897 sconstraint_diag_le; Exit_Class.thy:430 sconstraint_diag(2); Exit_Class.thy:133 psd_eigen_ub_diag; Ito_Market.thy:281 trace_le_eigen_ub; Value_Function_Subsolution.thy:1823 sconstraint_trace_le; Value_Function_Subsolution.thy:3133 feasible_trace_le; Curvature_Operator.thy:300 feasible_entry_bound vs Exit_Class.thy:150 psd_eigen_ub_entry_abs_le

sconstraint_diag_le has the same statement as Exit_Class.sconstraint_diag(2), which comes earlier in the session. sconstraint_trace_le proves trace b <= n*(n*L) through |b_ii| <= norm b <= nL. That bound is weaker than the trace b <= n*L that trace_le_eigen_ub or feasible_trace_le give. feasible_trace_le re-proves it for feasible matrices. trace_le_eigen_ub is paper-free but sits in Ito_Market, which is not on the value-function import path. The weak constant shows in exit_val_touch_near_orth: β = 1/(2 n'^2 L), while the text at 2364 announces "the scaling t := ε²/(2nL)".

Evidence: Euler:897 "assumes a: a ∈ sconstraint k L shows a $ i $ i <= L"; Exit_Class:430 "shows 0 <= a $ i $ i and a $ i $ i <= L". Ito_Market:281 "assumes ub: eigen_ub a L shows trace a <= L * real CARD('n)".

Suggested action: Move eigen_ub/eigen_lb and trace_le_eigen_ub / psd_eigen_ub_diag into Symmetric_Matrix_Spectra.Matrix_Algebra. Delete sconstraint_diag_le and feasible_trace_le. Restate sconstraint_trace_le as trace b <= n*L and adjust β in exit_val_touch_near_orth and the TB_def users in Case_1:495 and Case_2:104.


### RA-value1-10. Chebyshev/Markov tail bounds re-proved instead of citing HOL and Continuous_Path_Spaces

*library_duplicate, impact medium, confidence high, ~130 lines.*  
Locations: Value_Function_Euler_Construction.thy:2330-2374 eulerp_Xi_chebyshev; Value_Function_Euler_Construction.thy:2708-2773 exit_class_increment_tail; Value_Function_Euler_Construction.thy:2775-2866 exit_class_increment_tail_norm; Continuous_Path_Spaces/Increment_Tails.thy:28 fourth_moment_tail; Continuous_Path_Spaces/Path_Tightness.thy:~2010-2050 (coordinate union bound); HOL/Analysis/Bochner_Integration.thy:2028 finite_measure.second_moment_method

eulerp_Xi_chebyshev re-derives {β <= |f|} = {β² <= f²} and calls integral_Markov_inequality_measure. That is HOL's second_moment_method, which states measure {|f x| >= a} <= ∫ f² / a². exit_class_increment_tail (lines 2742-2771) repeats fourth_moment_tail of Increment_Tails line for line (seteq, power_le_imp_le_base, Markov). exit_class_increment_tail_norm's union bound over coordinates (norm_le_l1_cart, measure_UNION_le) repeats an inline block of Path_Tightness.

Evidence: Increment_Tails:28 "shows measure M {ω ∈ space M. l <= |f ω|} <= (∫ω. (f ω)^4 ∂M) / l^4". Bochner_Integration:2028 "shows measure M {x∈space M. |f x| >= a} <= lebesgue_integral M (λx. f x ^ 2) / a²".

Suggested action: Use second_moment_method in eulerp_Xi_chebyshev (about 8 lines) and fourth_moment_tail in exit_class_increment_tail (about 15 lines). Extract a generic coordinate-to-norm tail lemma into Increment_Tails and use it here and in Path_Tightness.


### RA-value1-11. pball_exit and its nine lemmas are paper-free path facts; generic open-set versions belong in Path_Exit_Times

*misplacement, impact medium, confidence high, ~330 lines.*  
Locations: Value_Function_Subsolution.thy:80 pball_exit, 83 pball_exit_nonneg, 87 pball_exit_le, 672 pball_exit_cong, 689 pball_exit_outside, 708 pball_exit_pos, 756 pball_exit_path_stopping_time, 802 pball_exit_le_iff_dense, 927 pball_exit_measurable, 1004 pball_exit_stays_cball; Value_Function_Euler_Construction.thy:3449-3458 (inside) and Value_Function_Supersolution_Case_2.thy:~373 (same inside block)

pball_exit T x ε ω = pexit T (ball x ε) (λt. fst (ω t)) names no paper constant. Measurability (pball_exit_le_iff_dense plus pball_exit_measurable, about 200 lines, by rational approximation and a sequential-compactness argument) is the open-set counterpart of Path_Exit_Times.pexit_measurable, which handles closed K. For open U and a < T, {pexit T U f <= a} = {f. ∃r∈[0,a]. f r ∉ U} is closed in the path topology, so the open case follows from a pexit_sublevel_closed lemma. pball_exit_stays_cball proves dist <= ε up to the exit through IVT. The simpler route: before the exit the path is in U (contrapositive of pexit_le_of_mem), and at the exit it is in the closure by continuity. That contrapositive ("inside") is re-proved inline in eulerp_limit_exit and in Case_2. pball_exit_pos and pball_exit_outside likewise hold for any open U.

Evidence: Path_Exit_Times:178 pexit_measurable: "assumes K: closed K". Subsolution:792 text: "pexit_path_measurable covers closed targets and the ball is open, so this cannot be inherited directly." Euler 3451-3457 and Case_2 ~373-382 both prove "fst (ω s) ∈ ball x rr" for s < τ by pexit_le_of_mem contradiction.

Suggested action: Add to Continuous_Path_Spaces.Path_Exit_Times, generic in 'b::polish_space: pexit_sublevel_closed / pexit_measurable_open for open U, pexit_pos_of_open, pexit_before_mem, pexit_at_closure. Move pball_exit and its stopping-time and measurability corollaries to the pair layer (Path_Stopping_Times). Replace the inline `inside` blocks.


### RA-value1-12. Euler_Construction is serialised behind Subsolution and the whole DPP layer; Doubling_Of_Variables imported for one lemma

*build_time, impact medium, confidence high, ~30 lines.*  
Locations: Value_Function_Euler_Construction.thy:4-11 (imports); Second_Order_Viscosity_Analysis/Doubling_Of_Variables.thy:3867-3896 (text + dist_pair_le)

The only names Value_Function_Euler_Construction uses from Value_Function_Subsolution are pball_exit, pball_exit_le, pball_exit_outside, pball_exit_pos and pball_exit_stays_cball. It never uses exit_val or any DPP result (one text mention). It needs only Exit_Class_Optimizer (exit_class_compact_metric_space, exit_class_kglue_law'), Exit_Class_Shift, Exit_Class_Limits, Exit_Class_Witness and Path_Law_Pasting. The import of Doubling_Of_Variables exists solely for dist_pair_le, which is dist_Pair_Pair plus sqrt_sum_squares_le_sum (HOL Product_Vector:410, NthRoot:667).

Evidence: Name-usage scan: Doubling_Of_Variables lemmas used in Euler: only dist_pair_le (1 use, line 564). Subsolution names used in Euler: pball_exit 20, pball_exit_le 1, _outside 2, _pos 2, _stays_cball 2. grep -c exit_val Euler = 1 (text at 677).

Suggested action: After moving pball_exit to the path layer, let Euler import Exit_Class_Optimizer, Exit_Class_Shift, Exit_Class_Limits and Path_Law_Pasting only. It then builds in parallel with the 7 Dynamic_Programming_* theories and Value_Function_Subsolution. Replace dist_pair_le by the HOL facts and drop the import.


### RA-value1-13. Matrix toolkit for sconstraint_orth_feasible and its prose ended up in Pair_Path_Laws

*misplacement, impact medium, confidence high, ~420 lines.*  
Locations: Pair_Path_Laws.thy:1797 psd_kernel_eq, 1898 matvec_sum_outer, 1937 quadform_sum_outer, 1970 traceM_sum_outer, 2014 onormal_parseval, 2119 onormal_span_parseval, 2174 weighted_min_value; Pair_Path_Laws.thy:1861, 2135, 2307-2318 (section headings and text for the toolkit and for sconstraint_orth_feasible); :215-229 (ell_op_s text); Value_Function_Subsolution.thy:1848-1861 (heading 'Positive semidefinite forms kill their null directions' over sconstraint_orth_feasible); Value_Function_Subsolution.thy:1862-2116 sconstraint_orth_feasible

The outer-product sums, the Parseval identities, the threshold selection weighted_min_value and psd_kernel_eq are pure linear algebra. They sit in the pair-path layer interleaved with path lemmas (pair_test_F_*). Their headings ("Sums of outer products: the toolkit", "Selecting a value-minimal index set: the threshold argument", "From the convexified constraint to a feasible witness") and the explanatory text of sconstraint_orth_feasible moved with them. In the subsolution theory the heading over sconstraint_orth_feasible describes psd_kernel_eq. onormal_parseval is the span B = UNIV case of onormal_span_parseval. sconstraint_orth_feasible is a probability-free statement relating sconstraint and feasible; its natural home is Eigenvalue_Bound_Exact next to Pi_constraint_capped_trace. Inside it, sym_a, quad_a_nn and ub_a (1989-2075) are generic facts about Σ c_u outer_prod u u over an orthonormal family.

Evidence: Pair_Path_Laws.thy:2307 "section From the convexified constraint to a feasible witness", followed by lemma pair_test_F_sq_bound. Subsolution:1850 "The Cauchy--Schwarz inequality for a psd form, in the shape needed later: if the form vanishes at q then q is in the kernel.", followed by 9 blank lines and sconstraint_orth_feasible.

Suggested action: Move matvec/quadform/traceM_sum_outer and psd/eigen_ub-of-sum-of-outer-products lemmas to Symmetric_Matrix_Spectra.Outer_Products. Move onormal_span_parseval to Orthonormal_Families and delete onormal_parseval. Move weighted_min_value to Ky_Fan next to exists_min_subset, and psd_kernel_eq to Symmetric_Spectral. Move sconstraint_orth_feasible with its text to Eigenvalue_Bound_Exact, and the ell_op_s prose to wherever ell_op_s survives (or delete it).


### RA-value1-14. Two optional-sampling lemmas with identical proofs; martingale mean-constancy re-derived

*clone, impact medium, confidence high, ~110 lines.*  
Locations: Value_Function_Subsolution.thy:1047-1134 exit_class_X_entry_stopped; Value_Function_Subsolution.thy:1136-1241 exit_class_comp_entry_stopped; Value_Function_Subsolution.thy:327-331 (const in exit_class_X_mean); Continuous_Time_Martingales/Martingale_Algebra.thy:903 martingale_mean_zero_of_start

The two lemmas are the same 90-line argument for the X martingale and the compensated martingale. The steps: interpret horizon_sq_int_martingale on pstopped_law, apply set_integral_eq on the whole space, set_integral_space twice, the start value a.s., then transport the evaluation at T through integral_distr and pstopped_apply. Only the functional differs. The step "∫Z_0 = ∫Z_T from set_integral_eq at space" is also in exit_class_X_mean and is the body of martingale_mean_zero_of_start. The repeated "AE f = c ⟹ ∫ f = c on a probability space" block (start) appears 3 times.

Evidence: Lines 1081-1095 and 1176-1195 differ only in the integrand. Lines 1110-1118 and 1212-1222 (peq) likewise.

Suggested action: State one lemma for a continuous F :: pair ⇒ real with horizon_sq_int_martingale (λu p. F (p (min u T))), giving integrability and E_P F(ω(θ ω)) = F(x,0). Add martingale_mean_const (E Z_u = E Z_0) beside martingale_mean_zero_of_start.


### RA-value1-15. Euler induction-step boilerplate and grid-prefix facts repeated; fst-measurability re-derived five times

*simplification, impact medium, confidence high, ~180 lines.*  
Locations: Value_Function_Euler_Construction.thy:819-861 (eulerp_in_class), 1716-1753 (eulerp_Xi_sq_bound), 2032-2059 (eulerp_orth_increments), 2213-2244 (eulerp_Xi_sq_bound_le); also Case_1.thy eulerp_orth_increments_cond; Value_Function_Euler_Construction.thy:1569-1581, 2088-2102, 2147-2156 (mem/prefl for pglue at grid points); Value_Function_Euler_Construction.thy:831-834, 1739-1742, 2050-2053, 2232-2235, 2996-2999 (fst ∈ borel_measurable borel); Continuous_Time_Martingales/Integrability_Criteria.thy:749 pair_fst_borel

Each induction step on eulerp re-establishes the same objects and facts: r, T', ?K, hT, r0, rleT, Qc, setsQ, ne, pack, mfst, eQ, Kp, Ee and phim, about 30 lines each time. The pglue grid-prefix identity is proved three times. In eulerp_Xi_sq_bound_le, the case m <= Suc N recomputes the kglue/ksemi nn-integral only to observe that a prefix functional has the same integral under eulerp (Suc N) as under eulerp N. That is a generic prefix-invariance fact about kglue_law'. pair_fst_borel and pair_snd_borel are imported but not used; Subsolution:159-161 and 1260-1261 re-derive snd as well.

Evidence: Euler:1739 "have mfst: (fst :: ...) ∈ borel_measurable borel using measurable_fst[...] by (simp add: borel_prod)" vs Integrability_Criteria:749 "lemma pair_fst_borel: (fst :: 'a × 'b ⇒ 'a) ∈ borel_measurable borel".

Suggested action: Add lemma eulerp_Suc (packaging Ee, Kp, Kb, Kc, phim, sets) and pglue_grid_prefix. Add nn_integral_kglue_law'_prefix to Path_Law_Pasting and use it in eulerp_Xi_sq_bound_le. Use pair_fst_borel and pair_snd_borel.


### RA-value1-16. exit_class_weak_limit re-derives portmanteau already in Continuous_Path_Spaces

*simplification, impact medium, confidence medium, ~70 lines.*  
Locations: Value_Function_Euler_Construction.thy:2553-2651 exit_class_weak_limit; Continuous_Path_Spaces/Path_Exit_Times.thy:662 weak_conv_open_liminf, :739 weak_conv_closed_limsup; Exit_Class_Optimizer/exit_class_convergent_subsequence (used at Exit_Class_Optimizer.thy:52)

The proof builds an mweak_conv_fin interpretation by hand (ev1, ev2, MWfin, setsP, fmi, fmP) and calls MW.mweak_conv_eq3 and eq2. The class lemma exit_class_convergent_subsequence already gives weak_conv_on (Pseq ∘ r) P. weak_conv_open_liminf and weak_conv_closed_limsup then give the open and closed bounds, followed by lim_imp_Liminf and lim_imp_Limsup.

Evidence: Path_Exit_Times:662 "shows ereal (measure Λ U) <= Liminf sequentially (λi. ereal (measure (Λi i) U))".

Suggested action: Re-prove exit_class_weak_limit from exit_class_convergent_subsequence plus the two Path_Exit_Times lemmas (about 30 lines).


### RA-value1-17. Euler construction needs only a closed covariation set and a diagonal bound

*generalisation, impact medium, confidence medium, ~200 lines.*  
Locations: Value_Function_Euler_Construction.thy:153 sbmpair_law_diffquot, 382 sbmpair_law_in_paper_pair_class, 679 sbm_kernel_package, 803 eulerp_in_class, 916 sbm_entry_bound, 1455 xiC

The sconstraint k L membership of S Sᵀ (SFs) is used only in two ways: closedness, through closedin_diffquot_constraint and diffquot_all_of_rational, plus compactness of the class through exit_class_compact_metric_space; and the diagonal bound a_ii <= L, through sbm_entry_bound and xiC. Stated over covariation_class S (PLAN §11), the whole Euler layer is paper-free. It would also drop the sconstraint_def unfolding at 903.

Evidence: sbm_entry_bound uses only sconstraint_diag_le. No psd, Pi_proj or eigen_lb fact is used anywhere in Value_Function_Euler_Construction.

Suggested action: Once covariation_class has a compact-metric-space lemma and a kglue lemma, restate the Euler layer for closed bounded S with ∀a∈S. a_ii <= L. Then consider moving it below the paper layer as part of G11.


### RA-value1-18. The anti-concentration core of exit_val_touch_near_orth is a paper-free probability lemma

*simplification, impact medium, confidence medium, ~190 lines.*  
Locations: Value_Function_Subsolution.thy:2578-2769 (W, halfabs, A, s_split, EAc_le, EA_le, probA, EabsA); /opt/afp/thys/Concentration_Inequalities/Paley_Zygmund_Inequality.thy:13 paley_zygmund_inequality_holder

Inside the 684-line proof, about 190 lines prove two generic facts. For integrable W with E W = 0: E|W| = 2 E max(-W,0). If moreover |W| <= B a.s. and s = E W²: P(|W| >= sqrt(s/2)) >= s/(2B²) (a bounded Paley–Zygmund). None of this mentions paths or the paper. A Paley–Zygmund theorem exists in the AFP; it needs an L^p hypothesis and would add a dependency on Lp.

Evidence: The block uses only W, s, nq*ε as the bound, PP.prob and indicators. q, M and exit_val do not occur in 2578-2769 except through W's definition.

Suggested action: Extract mean_zero_abs_eq_twice_neg_part and bounded_anticoncentration into Continuous_Time_Martingales.Integrability_Criteria. The theorem body then shrinks to the scaling argument.


### RA-value1-19. Brownian fourth moments in the paper session re-derive a Wiener_Measure lemma

*misplacement, impact low, confidence high, ~135 lines.*  
Locations: Value_Function_Euler_Construction.thy:933 bm_coordinate_pow4; Value_Function_Euler_Construction.thy:977 bm_R2_moment; Wiener_Measure/Gaussian_Increments.thy:98 gauss_measure_fourth_moment

bm_coordinate_pow4 (E ω_i(h)^4 = 3h²) and bm_R2_moment (E(Σ_i ω_i(h)²)² <= 3n²h²) are statements about bm_paths only. The body of bm_coordinate_pow4 (948-958) repeats the computation fact(2*2)/(2^2*fact 2) = 3 that is gauss_measure_fourth_moment.

Evidence: Euler:951 "have c3: (fact (2 * 2) / (2 ^ 2 * fact 2) :: real) = 3". Gaussian_Increments:108-114 contains the same lines.

Suggested action: Move both lemmas to Wiener_Measure.Product_Brownian_Motion and prove bm_coordinate_pow4 from gauss_measure_fourth_moment plus bm_coordinate_distr.


### RA-value1-20. Euler-kernel prose stranded in paper-free Second_Order_Viscosity_Analysis

*misplacement, impact low, confidence high, ~6 lines.*  
Locations: Second_Order_Viscosity_Analysis/Doubling_Of_Variables.thy:3867-3871; Value_Function_Euler_Construction.thy:444-666 (sbmpair_pathwise_tendsto, sbm_law_weak_conv)

A text block in the paper-free session reads "The Euler kernel varies only through the frozen matrix, so its measurability reduces to continuity of S ↦ law (sbmpair S T) ...". It mentions sbmpair, a constant of this cluster, and documents sbm_law_weak_conv. It sits above dist_pair_le in Doubling_Of_Variables.

Evidence: Doubling_Of_Variables.thy:3868 "measurability reduces to continuity of S ↦ law (sbmpair S T)".

Suggested action: Move the text back to Value_Function_Euler_Construction before sbmpair_pathwise_tendsto (and delete dist_pair_le, see the build_time finding).


### RA-value1-21. Ad-hoc bounded_linear constructions and trace estimates where HOL lemmas apply

*simplification, impact low, confidence high, ~90 lines.*  
Locations: Value_Function_Subsolution.thy:642-644, 1751-1753, 2548-2550 (bl2: bounded_linear (λr. r/2)); Value_Function_Subsolution.thy:1427-1429, 1460-1462 (blc); Continuous_Time_Martingales/Integrability_Criteria.thy:582 integrable_cmult, 593 integral_cmult; Value_Function_Euler_Construction.thy:1297-1343 (bb), 1102-1143 (contxi, contg)

bounded_linear (λr. r/2) and (λr. r*c) are built three and two times only to get integrability and integrals. HOL already has integrable_divide_zero, integral_divide_zero, integrable_mult_left and integral_mult_left_zero (Bochner_Integration:993-1110); integrable_cmult and integral_cmult duplicate integrable_mult_right and integral_mult_right_zero. In sbm_xi_sq_bound, bb (47 lines, columns plus Cauchy–Schwarz) gives |tr(M S Sᵀ)| <= n² Cmm L. The entry bound |a_ij| <= L (Exit_Class.psd_eigen_ub_entry_abs_le) gives Cmm·L in a few lines. That entrywise trace estimate is also repeated in ell_op_bdd_below, ell_op_bdd and ell_op_s_bdd_below. Continuity of trace(M ** (outerp(..) - ..)) is proved by expanding sums; bounded_linear_trace_mult_left and outerp continuity give it directly. sbm_xi_sq_bound is used only by sbm_xi_sq_bound_uniform, so the two can be merged.

Evidence: HOL/Analysis/Bochner_Integration.thy:1003 integrable_divide_zero, :1110 integral_divide_zero.

Suggested action: Use the HOL simp lemmas, retire integrable_cmult and integral_cmult (other cluster), and add trace_mult_abs_le: (∀i j. |a$i$j| <= c) ⟹ |trace (M ** a)| <= (Σ|M_ij|)·c to Matrix_Algebra. Merge sbm_xi_sq_bound into its uniform corollary.


### RA-value1-22. exit_val_cond_ball is exit_val_cond_at_time at θ = pball_exit

*clone, impact low, confidence high, ~40 lines.*  
Locations: Value_Function_Subsolution.thy:91-126 exit_val_cond_ball; Value_Function_Subsolution.thy:2120-2147 exit_val_cond_at_time; Value_Function_Subsolution.thy:611-621 (same horizon-cap step at constant h)

Both apply exit_val_cond_time and rewrite with enn2real_paper_v_horizon_cap by the same eventually_mono proof. exit_val_cond_at_time assumes only ∀ω. 0 <= θ ω <= T, which pball_exit_nonneg and pball_exit_le supply.

Evidence: Lines 109-125 and 2133-2146 are identical up to renaming θ.

Suggested action: Move exit_val_cond_at_time to Dynamic_Programming_Assembly next to enn2real_paper_v_horizon_cap, delete exit_val_cond_ball, and use it at constant h too.


### RA-value1-23. Hypotheses stronger than used; constant-time special cases next to stopped ones

*generalisation, impact low, confidence high, ~40 lines.*  
Locations: Value_Function_Subsolution.thy:1243 exit_class_Y_stopped_integrable; Value_Function_Subsolution.thy:1279 exit_class_Y_stopped_mean_sconstraint; Value_Function_Subsolution.thy:150 exit_class_Y_integrable; Value_Function_Subsolution.thy:353 exit_class_quadform_mean vs 2156 exit_class_stopped_moments(6)

The two stopped-Y lemmas assume path_stopping_time T θ but use it only through path_stopping_time_nonneg and path_stopping_time_le. The proofs need just 0 <= θ <= T and Borel measurability. With that weaker hypothesis, exit_class_Y_integrable is the case θ ≡ t. exit_class_quadform_mean is the constant-time case of stopped_moments(6) (which assumes T > 0).

Evidence: Lines 1259 and 1267 are the only uses of st in exit_class_Y_stopped_integrable. In Y_stopped_mean_sconstraint st is used only at 1295 and 1297 (bounds) and in passing to Y_stopped_integrable.

Suggested action: Replace st by 0 <= θ <= T in those statements, and drop the constant-time duplicates (most are already dead).


### RA-value1-24. Stale, empty or mismatched headings and pointer texts left by earlier moves

*documentation, impact low, confidence high, ~80 lines.*  
Locations: Value_Function_Subsolution.thy:146-149 (empty 'Matrix functionals that are bounded linear'); Value_Function_Subsolution.thy:495 (pointer to trace_mult_commute, which exists nowhere); Value_Function_Subsolution.thy:666-671 (empty 'Quadratics are test functions, and the relaxed predicates'); Value_Function_Subsolution.thy:785-788, 2149-2152 (sections holding only pointer text); Value_Function_Subsolution.thy:1815-1822 ('From quadratics to arbitrary test functions' describes the Taylor step — that is Test_Functions.test_fun_quadratic_dominates — followed by sconstraint_trace_le); Value_Function_Euler_Construction.thy:16-33 ('see the subsection Exact rotations below': it is in Case_1.thy:142; 'the trace pairing for sums of column outer products' moved away); Value_Function_Euler_Construction.thy:35-45 (empty subsection; 'trace pairing' heading over the sbmpair definition); Value_Function_Euler_Construction.thy:435-443 ('Writing the field as a square: columns into a matrix' — colm is now Case_1.thy:206); Value_Function_Euler_Construction.thy:1197-1198 (says sq_diff_le is in Quadratic_Variation; it is Continuous_Time_Martingales/Power_Inequalities.thy:26)

After the restructuring moves, many section headings in both files describe lemmas that are no longer there, and several sections hold only "X lives in Y" pointers. One pointer is wrong (sq_diff_le). The constant names still carry pre-rename vocabulary (sbmpair_law_in_paper_pair_class, enn2real_paper_v_horizon_cap).

Evidence: grep: trace_mult_commute has no definition in the repository. sq_diff_le is defined at Continuous_Time_Martingales/Power_Inequalities.thy:26.

Suggested action: Delete empty sections and pure pointer texts, fix the sq_diff_le pointer, rewrite the Euler header to describe this theory, and rename *_paper_pair_class to *_in_exit_class when the Statement session is touched next.


### RA-value1-25. exit_val/exit_class projections live in the wrong theories and are re-derived by unfolding

*misplacement, impact low, confidence high, ~40 lines.*  
Locations: Value_Function_Subsolution.thy:3353 exit_val_zero_outside; Dynamic_Programming_Pasting.thy:161 exit_class_start; Value_Function_Subsolution.thy:190,192,336,1061,1151,1309,1311,1592,2476,2784; Value_Function_Euler_Construction.thy:1148,2416 ('using P unfolding exit_class_def by blast')

exit_val_zero_outside is a basic property of exit_val (v = 0 off K), used by Value_Function_Uniqueness. It belongs with exit_val_le_T and exit_val_boundary_zero in Exit_Class_Witness. exit_class_start is defined in Dynamic_Programming_Pasting rather than Exit_Class (where exit_class_prob and exit_class_sets live). The cluster extracts the start clause and the diffquot clause 12 times by unfolding exit_class_def, which works against the covariation_class abstraction of G11.

Evidence: Pair_Path_Laws.thy:4068 covariation_class_start and :4074 covariation_class_diffquot already exist; Exit_Class has no exit_class_diffquot projection.

Suggested action: Add exit_class_start and exit_class_diffquot to Exit_Class (via exit_class_eq_covariation), use them throughout, and move exit_val_zero_outside to Exit_Class_Witness.


### RA-value1-26. Generic weak-convergence and prob_algebra bridges inlined

*simplification, impact low, confidence medium, ~90 lines.*  
Locations: Value_Function_Euler_Construction.thy:592-666 sbm_law_weak_conv; Value_Function_Euler_Construction.thy:761-780 (prob_algebra bridge in sbm_kernel_package); Dynamic_Programming_Pasting.thy:115-139 (same bridge in exit_val_measurable_selector_kernel'); Dynamic_Programming_Kernels.thy:55, 127; Path_Law_Pasting.thy:420-500 pshift_law_weak_conv_joint (same mweak_conv_eq1 setup)

sbm_law_weak_conv is an instance of a paper-free fact: if measurable maps φ_m converge pointwise to φ in a metric space X on a probability space, then distr M X φ_m converges weakly to distr M X φ (dominated convergence). Path_Space has only the continuous-mapping lemma weak_conv_on_pushforward. The bridge "S ∈ borel →M borel_of W and S y ∈ P ⟹ S ∈ borel →M prob_algebra B" (measurable_restrict_space2, borel_of_subtopology, weak_conv_topology_eq_prob_algebra) is written out four times.

Evidence: Euler:769-780 and DP_Pasting:115-127 are the same 10-line chain (polish, setsPA, r1, r2, measurable_cong_sets).

Suggested action: Add weak_conv_on_distr_pointwise and measurable_prob_algebra_of_weak_conv_topology to Continuous_Path_Spaces.Path_Space and use them in the four places.


## RA-value2

The cluster is Relative_Arbitrage/{Value_Function_Supersolution_Case_1 (2648 lines), Value_Function_Supersolution_Case_2 (1493), Value_Function_Tangential_Field (866), Value_Function_Assembly (334)}. It proves the supersolution half of clause (2) of Theorem 1.1 (Section 3.2 of the paper) and the interior lower bound of Example 3.1.

Case 1 (nonzero gradient). `rotSF_exists` builds a covariance field by exact Householder rotation in place of the paper's skew field. The Euler scheme gives a class member whose paths grow along the quadratic, and the time-θ DPP gives the contradiction. The proof that is actually used is `exit_val_supersol_contradiction_case1_lsc`, which touches the lsc envelope and runs from an approximating point y. It is located in the Case_2 theory. The Case_1 theory contains an older version that touches v itself (`exit_val_supersol_contradiction_case1`), and nothing uses it.

Case 2 (zero gradient). This is the paper's dichotomy:
- `exit_val_case2_separation` gives a strict quadratic minorant.
- Horn A, `exit_val_case2_at_minimiser`, applies the lsc Case 1 at minimisers of tilted quadratics.
- Horn B, `exit_val_not_locally_constant`, refutes local constancy of v_* via the tangential field and `exit_val_ball_lower_plus`.
- `exit_val_case2_eps` and `exit_val_case2` take the limits through `ell_op_usc_ge_one_limit`.
- `exit_val_supersol_lsc`, `_local`, `exit_val_supersol_envK` and `_bounded` assemble Definition 3.1(b), with the horizon cap discharged by `exit_val_cap_inert`. These feed `Value_Function_Uniqueness` and, through `iexit_val_supersol_lsc_K`/`_bc_K`, the Statement session.

The proof follows the paper faithfully. The exact-rotation field and the Hessian softening `M = H - (2γ+δ)·1` are documented replacements for the paper's skew field and eigenvalue modification. The singular-Hessian case is handled explicitly through `singular_matrix_avoids_range`. Proving the property for the larger class `test_fun_at` is stronger than the paper's C² class.

Value_Function_Tangential_Field generalises the Case_1 `tanp`/`uvec` field to `tanpU (projmat b m)` on an m-dimensional subspace and proves `subspace_tangential_exact_growth`. Value_Function_Assembly proves only the sharp Example 3.1 lower bound (`exit_val_ball_lower_subspace`, `exit_val_ball_lower_sharp`). The assembly of clauses (0)-(3) that its name and section title promise is in Value_Function_Uniqueness.

Organisation problems:
- About 945 lines of Case_1 (1119-2063) are generic "region" versions of the Euler-limit chain. The "ball" versions in Value_Function_Euler_Construction are special cases of them.
- About 860 more lines of Case_1 (811-1117 and 2065-2640) are Case-2 / Example-3.1 tangential-field material, and Tangential_Field re-proves the same material in generalised form.
- The only consumer of the whole ball chain is the dead non-lsc Case 1. About 1,600 lines become deletable once it goes.


### RA-value2-1. Non-envelope Case 1 is dead, and with it about 1,600 lines of the ball-version Euler chain

*dead_code, impact high, confidence high, ~1610 lines.*  
Locations: Relative_Arbitrage/Value_Function_Supersolution_Case_1.thy:462-801 exit_val_supersol_contradiction_case1; Relative_Arbitrage/Value_Function_Supersolution_Case_1.thy:39-140 touching_grad_lt_horizon; Relative_Arbitrage/Value_Function_Euler_Construction.thy:1994-2135 eulerp_orth_increments; Value_Function_Euler_Construction.thy:2381-2532 eulerp_quad_lower; Value_Function_Euler_Construction.thy:2877-3222 eulerp_bad_event_null; Value_Function_Euler_Construction.thy:3236-3357 eulerp_limit_good; Value_Function_Euler_Construction.thy:3370-3488 eulerp_limit_exit; Relative_Arbitrage/Pair_Path_Laws.thy:2051 euOrth_mset, 3509 open_quad_bad_event, 3852 quad_good_rat_to_real, 3944 quad_good_upto

`exit_val_supersol_contradiction_case1` (340 lines) is used nowhere. Its only occurrence is in prose, at Pair_Path_Laws.thy:3748 ("relative to \<open>exit_val_supersol_contradiction_case1\<close>"). Every consumer path goes through `exit_val_supersol_contradiction_case1_lsc` (Case_2:51).

Deleting it makes a chain of lemmas unused, each having exactly one user, the next lemma in the chain:
- its private helper `touching_grad_lt_horizon`;
- `eulerp_limit_exit`, used only at Case_1:598;
- `eulerp_limit_good`, used only by eulerp_limit_exit;
- `eulerp_bad_event_null`, used only by eulerp_limit_good;
- `eulerp_quad_lower`, used only at Euler:3020;
- `eulerp_orth_increments`, used only at Euler:2413;
- `euOrth_mset`, `open_quad_bad_event`, `quad_good_rat_to_real` and `quad_good_upto`.
In total: 442 lines in Case_1, 881 in Euler_Construction and 291 in Pair_Path_Laws. None of these lemmas carries a [simp]/[intro] attribute, so grep reliably finds all uses.

Evidence: grep -rnw exit_val_supersol_contradiction_case1 → only the declaration and Pair_Path_Laws.thy:3748 (text).
grep eulerp_limit_exit → only Case_1:598 (inside the dead theorem).
grep eulerp_limit_good → only Euler:3404 (inside eulerp_limit_exit).
grep eulerp_bad_event_null → only Euler:3277.
grep eulerp_quad_lower → only Euler:3020.
grep eulerp_orth_increments → only Euler:2413.
grep euOrth_mset → only Euler:2069.
grep quad_good_upto → only Euler:3472.
No lemma in the four cluster theories carries an attribute.

Suggested action: Delete exit_val_supersol_contradiction_case1 and touching_grad_lt_horizon, then the ball chain bottom-up: eulerp_limit_exit, eulerp_limit_good, eulerp_bad_event_null, eulerp_quad_lower, eulerp_orth_increments, euOrth_mset, open_quad_bad_event, quad_good_rat_to_real, quad_good_upto.

Update the prose that names them: Case_1:1127 and 1309; Euler:2543, 2703 and 3225-3232; Pair_Path_Laws:3565 and 3748.

Run the semantic unused-theorem pass to confirm before deleting.


### RA-value2-2. The ball-version Euler-limit chain is a literal special case of the region chain in Case_1

*clone, impact high, confidence high, ~1250 lines.*  
Locations: Value_Function_Euler_Construction.thy:1994 eulerp_orth_increments vs Value_Function_Supersolution_Case_1.thy:1131 eulerp_orth_increments_cond; Euler:2381 eulerp_quad_lower vs Case_1:1318 eulerp_quad_lower_region; Euler:2877 eulerp_bad_event_null vs Case_1:1478 eulerp_bad_event_null_region; Euler:3236 eulerp_limit_good vs Case_1:1858 eulerp_limit_good2_region; Pair_Path_Laws.thy:3852 quad_good_rat_to_real vs 3760 quad_good_rat_to_real_region; 3944 quad_good_upto vs 3668 quad_good_upto_region; 3509 open_quad_bad_event vs 1443 open_quad_bad_event_region; 2051 euOrth_mset vs 846 euOrth_mset_cond

Each ball version is obtained from the region version by the same instantiation:
- R or RO := cball x rb or ball x rb;
- the global clamped kill "transpose (SF z) *v (q + M *v (closest_point (cball x rb) z - x)) = 0" restricts to R through closest_point_self;
- the global marg restricts to R;
- Rn := rb.

The proofs are verbatim copies:
- Euler:2426-2528 equals Case_1:1358-1467 line for line, apart from the cps step.
- The bounds and dissection in Euler:2900-3222 equal Case_1:1499-1845.
- AErn/AEall/rat in Euler:3267-3346 equal AErn1/AEall1/rat1 in Case_1:1904-2024.
- The unconditional orthogonality (Euler:2005-2133) is the conditional one (Case_1:1143-1304) with its premise always true.

The region chain is generic Euler-scheme material and sits in the wrong theory: it has nothing to do with Case 1.

Evidence: Case_1:1325 kill: "\<And>z. z \<in> R \<Longrightarrow> transpose (SF z) *v (q + M *v (z - x)) = 0". Euler:2388 kill: "\<And>z. transpose (SF z) *v (q + M *v (closest_point (cball x rb) z - x)) = 0".

Conclusions are identical modulo R = cball x rb (Euler:2392 vs Case_1:1330).

Pair_Path_Laws:3852 quad_good_rat_to_real has the assumption "fst (\<omega> s) \<in> ball x rb"; quad_good_rat_to_real_region has "fst (\<omega> s) \<in> RO". Otherwise the statements are identical.

Suggested action: Move the region chain (Case_1:1119-2063) into Value_Function_Euler_Construction, or into a new theory Euler_Limit_Growth, replacing subsections 1928-2135, 2376-2532 and 2696-3488.

If any ball form is still wanted after the dead-code deletion, derive it as a few-line corollary. Keep only the *_region lemmas in Pair_Path_Laws.


### RA-value2-3. Case 1 is proved twice: plain touching (dead) and envelope touching (used), about 300 shared lines

*clone, impact high, confidence high, ~300 lines.*  
Locations: Value_Function_Supersolution_Case_1.thy:476-552 and 599-798 (exit_val_supersol_contradiction_case1); Value_Function_Supersolution_Case_2.thy:66-160 and 205-578 (exit_val_supersol_contradiction_case1_lsc)

The two theorems share these parts verbatim:
- the parameter construction: η₀, TB, sft, γ, δ, M = H - (2γ+δ)·1, trM, trMa, rphi, eK;
- the application of rotSF_exists and the marg derivation;
- the stopping time θ = min cc (pball_exit T x rr), the FN functional and the dpp;
- the eventually_elim body: inK, pex, XinK, cap, feq, minor, soften, the QQ case split and fun_ge with its three cases;
- the closing essge/esle/vfin chain.

The lsc version only adds the approximating point y (with psiY), and recovers the plain one with y = x and lsc_env replaced by v. The plain version is dead (see the dead-code finding). If both were wanted, the plain one would follow from the lsc one, since a global touching of v gives a local touching of lsc_env v.

Evidence: Case_1:487-544 and Case_2:96-152 are character-identical ("define \<eta>\<^sub>0 where ... define TB where ... define sft where ... define M where \"M = H - (2 * \<gamma> + \<delta>) *\<^sub>R mat 1\" ... have trMa: \"4 * \<eta> - 2 \<le> trace (M ** a)\""). Case_1:732-775 fun_ge and Case_2:505-556 fun_ge differ only by psiY.

Suggested action: Delete the plain version. Move exit_val_supersol_contradiction_case1_lsc into the Case_1 theory. Optionally extract the parameter block (ell_op witness → softened M with margin η) as a lemma `case1_softening` returning η, γ, δ, M, rphi.


### RA-value2-4. The tanp/uvec tangential field and tangential_exact_growth are the P = mat 1 instance of tanpU/uvecV and subspace_tangential_exact_growth

*clone, impact high, confidence high, ~500 lines.*  
Locations: Value_Function_Supersolution_Case_1.thy:830-1027 (tanp, tanp_mv, tanp_sym, tanp_quadform, tanp_psd, tanp_eigen_ub, tanp_eigen_lb, tanp_feasible, tanp_sconstraint, tanp_sq, tanp_trace, tanp_kill, uvec, uvec_unit, uvec_norm_le, uvec_par, uvec_cont); Case_1:2076-2370 (tanp_sq_sconstraint, tanRF_cont, tangential_exact_growth); Value_Function_Tangential_Field.thy:133-491 (tanpU, uvecV, tanpU_sym/mv/trace/psd/eigen_ub/eigen_lb/feasible/sq/sq_sconstraint/kill/kill_proj, uvecV_*, tanpUV_cont); Tangential_Field:555-851 subspace_tangential_exact_growth

The definitions coincide at P = mat 1:
- tanp u = mat 1 - outerp u = tanpU (mat 1) u, by outerp_eq_outer_prod;
- uvec y0 ρ w = uvecV (mat 1) ρ (w - y0).
Every tanp_* / uvec_* lemma is the P = mat 1 instance of its tanpU/uvecV counterpart:
- tanp_sq_sconstraint and tanpU_sq_sconstraint compute the same identity (tanp u)² = tanp(√(2 - u·u) u);
- tanRF_cont is tanpUV_cont;
- killRO and tanpU_kill.

Tangential_Field:544-545 says so itself: "Taking m = CARD('n) recovers @{thm [source] tangential_exact_growth} at y\<^sub>0 = 0". The only difference is the centre y0, which can be threaded through, since uvecV already takes the vector to project.

Evidence: Case_1:830 "definition tanp ... where \"tanp u = mat 1 - outerp u\""; Tangential_Field:133 "definition tanpU ... where \"tanpU P u = P - outer_prod u u\"". Case_1:981 "uvec y\<^sub>0 \<rho> w = (1 / max \<rho> (norm (w - y\<^sub>0))) *\<^sub>R (w - y\<^sub>0)"; Tangential_Field:136 "uvecV P \<rho> z = (1 / max \<rho> (norm (P *v z))) *\<^sub>R (P *v z)". Tangential_Field:544-545 text quoted above.

Suggested action: Generalise subspace_tangential_exact_growth to an arbitrary centre y0 (field λz. tanpU P (uvecV P ρ (z - y0)), quadratics centred at y0). Obtain tangential_exact_growth as the instance with an orthonormal basis of all of real^'n, built by orthonormal_family_containing with m = CARD('n). Then delete the tanp/uvec block from Case_1.


### RA-value2-5. exit_val_ball_lower_plus and exit_val_ball_lower_subspace share a 200-line confinement + DPP argument

*clone, impact high, confidence high, ~230 lines.*  
Locations: Value_Function_Supersolution_Case_1.thy:2383-2640 exit_val_ball_lower_plus; Value_Function_Assembly.thy:29-255 exit_val_ball_lower_subspace

Both prove that the tangential member stays in the annulus up to a deterministic time cc and then apply exit_val_dpp_sup_ge. The steps match one for one:
- the `IN` proof by pexit;
- ecc by contradiction with the dichotomy inner barrier / outer sphere, through radial_sq_upto (Case_1:2500) or radial_sq_upto_gen (Assembly:157-160);
- inB, inK, pex, fn, essge and esle.

The differences are small:
- lower_plus is centred at y0 with P = 1, and keeps the endpoint value (β term) with a T/2 cap;
- lower_subspace is centred at 0 with projector P, and drops the endpoint value.
One lemma with centre y0, projector P, free cc < min T δ and the β term would yield both: exit_val_ball_lower_plus with P = 1 and cc = min(T/2, δ/2), and exit_val_ball_lower_subspace with β = 0.

Evidence: Case_1:2470-2532 `have IN: "fst (\<omega> s) \<in> ?RO" if s0: "0 \<le> s" and sc: "s < cc"` is textually identical to Assembly:128-185, except that the radial lemma is radial_sq_upto vs radial_sq_upto_gen. The same holds for Case_1:2534-2565 vs Assembly:187-214 (inB) and Case_1:2602-2627 vs Assembly:228-253 (essge/esle).

Suggested action: Prove one `exit_val_ball_lower_gen` (centre y0, projector P, β ≥ value on the ball, any cc < min T δ) in the tangential-field theory. Derive exit_val_ball_lower_plus (used by exit_val_not_locally_constant) and exit_val_ball_lower_sharp from it.


### RA-value2-6. Theory boundaries do not match content: 'Case_1' is mostly Euler/tangential material, the used Case 1 lives in 'Case_2', and 'Assembly' assembles nothing

*structure, impact high, confidence high, ~2600 lines.*  
Locations: Value_Function_Supersolution_Case_1.thy (2648 lines); Value_Function_Supersolution_Case_2.thy:51; Value_Function_Assembly.thy:1-25; Value_Function_Uniqueness.thy:52-290

Content by theory:
- Case_1: of 2648 lines, about 440 are Case-1 material, and only rotSF (≈300 lines) of that is live. 945 lines (1119-2063) are the generic region Euler chain, and about 860 (811-1117, 2065-2640) are Case-2 horn-B / Example-3.1 tangential material.
- Case_2: the live Case 1 (exit_val_supersol_contradiction_case1_lsc, 531 lines) is here.
- Value_Function_Assembly: titled "Clause (2): the value function is a viscosity solution" and introduced as assembling sub- and supersolution, but it contains only the sharp Example 3.1 lower bound. The clause assembly (exit_val_supersol_bc, theorem_1_1_uniqueness_faithful, the iexit clauses) is in Value_Function_Uniqueness.

Proposed layout (L6 of the plan):
(a) Value_Function_Euler_Construction: Euler scheme + region chain only.
(b) Value_Function_Supersolution_Case_1: ell_op witness, rotSF_exists, case1_lsc.
(c) Value_Function_Tangential_Field: projector field at centre y0, exact growth, one general ball lower bound, exit_val_ball_lower_sharp. Merge Value_Function_Assembly into it, or rename the result Example_3_1_Lower_Bound.
(d) Value_Function_Supersolution_Case_2: separation, horns A/B, exit_val_case2*, supersolution assembly, cap_inert; imports (b) and (c).
(e) Value_Function_Uniqueness, renamed Theorem_1_1_Assembly.

Evidence: Section headers: Case_1:1119 "Conditional orthogonality", 1307 "The growth telescope on an arbitrary region", 1847 "One limit member, two quadratics, one region", 2065 "The tangential member", 2372 "Deterministic confinement and the ball lower bound". Assembly:13 `section \<open>Clause (2): the value function is a viscosity solution\<close>` with only exit_val_ball_lower_subspace and exit_val_ball_lower_sharp following.

Suggested action: Re-cut the four theories as in (a)-(e). Combined with the deletions above, the four theories plus the Euler chain shrink by roughly 2,500 lines and no theory exceeds about 2,000 lines.


### RA-value2-7. Clamped tangential field tanSF and the tanp feasibility lemmas are unused, and the prose claims otherwise

*dead_code, impact medium, confidence high, ~175 lines.*  
Locations: Value_Function_Supersolution_Case_1.thy:1029-1117 tanSF, tanSF_package (tanSF_cont, tanSF_sconstraint, tanSF_kill, tanSF_trace); Case_1:851-925 tanp_psd, tanp_eigen_ub, tanp_eigen_lb, tanp_feasible, tanp_sconstraint; Case_1:813-821 text

tanSF_package and its four named conclusions are referenced nowhere outside their own proof. tanp_sconstraint is used only at Case_1:1092 inside tanSF_package. tanp_feasible is used only by tanp_sconstraint, and tanp_psd, tanp_eigen_ub and tanp_eigen_lb only by tanp_feasible.

The working field is the unclamped λz. tanp (uvec y0 ρ z), with feasibility from tanp_sq_sconstraint. The text at 813-821 says the clamped field "feeds the same Euler machinery as Case 1 and is the positivity input for the second horn of the dichotomy, and for Example 3.1's lower bound". That is false.

Evidence: grep -rnw tanSF → only Case_1:1029-1115. grep tanp_sconstraint → declaration and Case_1:1092. grep tanp_feasible → declaration and Case_1:925.

Suggested action: Delete tanSF, tanSF_package and the tanp_psd..tanp_sconstraint block (about 165 lines). Rewrite or remove the text at Case_1:811-821.


### RA-value2-8. touching_grad_lt_horizon re-proves touching_grad_lt_horizon_gen from Second_Order_Viscosity_Analysis

*library_duplicate, impact medium, confidence high, ~102 lines.*  
Locations: Value_Function_Supersolution_Case_1.thy:39-140 touching_grad_lt_horizon; Second_Order_Viscosity_Analysis/Test_Functions.thy:1047 touching_grad_lt_horizon_gen

The two proofs are identical: obtain eK and e; differentiate h s = φ(x + s g x); choose s; take z = x + s g x. The only change is that the plain version takes W = enn2real ∘ exit_val, a global touching and the cap from enn2real_paper_v_horizon_cap. It is the instance W := tv, ρ := 1 with bnd from enn2real_paper_v_horizon_cap. It is also dead (see the dead-code finding).

Evidence: Case_1:57-73 "define h where \"h = (\<lambda>s. \<phi> (x + s *\<^sub>R g x))\" have hd: ..." is identical to Test_Functions.thy:1065-1081. Case_2:89 already uses touching_grad_lt_horizon_gen.

Suggested action: Delete touching_grad_lt_horizon together with exit_val_supersol_contradiction_case1, or replace it by a two-line instance of touching_grad_lt_horizon_gen.


### RA-value2-9. Two-quadratic limit theorem duplicates its own argument, and Case_2 calls it with the same quadratic twice

*simplification, impact medium, confidence high, ~110 lines.*  
Locations: Value_Function_Supersolution_Case_1.thy:1904-1957 (AErn1/AErn2), 1961-1978 (AEall1/AEall2), 2002-2047 (rat1/rat2); Value_Function_Supersolution_Case_2.thy:279-284, 312-313

eulerp_limit_good2_region proves the null-set, countable-intersection and rational-to-real steps twice, once per quadratic: about 100 duplicated lines.

Case_2 then instantiates it with identical slots ("killy margy killy margy"), and its conclusion AEg has the redundant conjunct "(t*(η-2)/2 ≤ …) ∧ (t*(η-2)/2 ≤ …)".

A cleaner structure:
1. `eulerp_limit_good_region_of_portmanteau`: for any P satisfying the portmanteau bound Praw obtained from eulerp_weak_limit, one quadratic grows almost surely.
2. A single-quadratic corollary.
3. The two-quadratic form as AE_conj of two applications to the same P.

Evidence: Case_2:312 `eulerp_limit_good2_region[OF T0 L1' SFc SFs symM symM ROo ROb killy margy killy margy]`. Case_1:1931-1957 is Case_1:1904-1930 with U1/kill1/marg1/sym1 renamed to U2/kill2/marg2/sym2.

Suggested action: Factor out the per-quadratic step as a lemma parameterised by P and Praw. Provide single- and two-quadratic corollaries, and use the single one in Case_2.


### RA-value2-10. The DPP lower-bound boilerplate re-derives exit_val_dpp_ge_const_time and ess_inf_timeI

*simplification, impact medium, confidence high, ~90 lines.*  
Locations: Value_Function_Supersolution_Case_1.thy:778-798; Value_Function_Supersolution_Case_2.thy:559-578; Value_Function_Supersolution_Case_1.thy:2602-2629; Value_Function_Assembly.thy:228-254

Each site goes `unfolding ess_inf_time_def by (rule Sup_upper)`, then SUP_upper[OF P], then exit_val_dpp_sup_ge(_time), then the vfin/ennreal juggling. This is the chain that Dynamic_Programming_Assembly.thy:859 exit_val_dpp_ge_const_time already packages ("P ∈ exit_class k L T x ⟹ AE ω in P. c ≤ FN ω ⟹ ennreal c ≤ exit_val k L T K x"), and the first step is Essential_Infimum.thy:87 ess_inf_timeI.

The DPP integrand `pexit θ K … + (if … then enn2real (exit_val k L (T - θ) K …) else 0)` is also spelled out in full about 10 times. A definition `dpp_integrand k L T K θ ω` would shorten the statements.

Evidence: Case_1:779 "unfolding ess_inf_time_def by (rule Sup_upper) (use AEfun in blast)"; Essential_Infimum.thy:87-90 `lemma ess_inf_timeI: assumes "AE ω in M. c ≤ ennreal (tau ω)" shows "c ≤ ess_inf_time M tau"`; Dynamic_Programming_Assembly.thy:859-867 exit_val_dpp_ge_const_time.

Suggested action: For the stopping-time sites (Case_1:778-798, Case_2:559-578) use exit_val_dpp_ge_const_time[OF T0 L1 Kc st thM Pc] with a real-valued AE bound. For the constant-time sites add a sibling lemma in Dynamic_Programming_Pasting, or a constant path_stopping_time lemma. Introduce a name for the DPP integrand.


### RA-value2-11. Paper-free linear algebra in the paper session (projectors, tangential fields, column square root, rotated columns)

*misplacement, impact medium, confidence high, ~550 lines.*  
Locations: Value_Function_Tangential_Field.thy:32-104 projmat, projmat_sym/mv/trace/fix/idem/span_fix; Tangential_Field:133-228, 401-539 tanpU, uvecV and their lemmas, apart from the eigen_lb/eigen_ub/feasible ones; Value_Function_Supersolution_Case_1.thy:206-271 colm, colm_square, rotSF_matrix, rotSF_conj; 148-200 rotSF, rotSF_cont; Case_1:830-1027 tanp/uvec algebra; Pair_Path_Space.thy:691 rot_col_cont; 796 trace_mult_outerp_sum; Pair_Path_Laws.thy:183 cols_mult_transpose

None of these statements mentions ell_op, sconstraint, exit_val or paths:
- projmat_* and tanpU/uvecV lemmas concern symmetric idempotents and rank-one corrections;
- colm_square is the psd square root a = C Cᵀ from an eigenbasis;
- rotSF_cont/matrix/conj concern rotm and closest_point.
Symmetric_Matrix_Spectra.Matrix_Algebra already hosts the companion lemmas (proj_inner_self, proj_norm_le, orthonormal_dim_span, orthonormal_family_containing, and even one named tanpU_sq_norm_le at Matrix_Algebra:2172), so the toolkit is split across sessions. PLAN_RESTRUCTURING_2 §3.1 scheduled rot_col_cont for Householder_Rotation; it is still in the path-toolkit theory Pair_Path_Space. cols_mult_transpose and trace_mult_outerp_sum are matrix facts sitting in the path layer.

Evidence: Tangential_Field:32 `definition projmat :: "(nat ⇒ real^'n) ⇒ nat ⇒ real^'n^'n" where "projmat b m = (∑i < m. outer_prod (b i) (b i))"`. Matrix_Algebra:2172 `lemma tanpU_sq_norm_le` (named after a paper-session constant). Pair_Path_Space.thy:691 rot_col_cont (statement only about rotm, M, q).

Suggested action: Create Symmetric_Matrix_Spectra theory Orthogonal_Projectors containing projmat, tanpU, uvecV, their algebra, colm/colm_square (as psd_sqrt_factor) and the proj_* / orthonormal_* lemmas from Matrix_Algebra, and rename tanpU_sq_norm_le. Move rot_col_cont and the rotSF continuity/conjugation lemmas next to rotm_vec_cont in Householder_Rotation. Keep only tanpU_eigen_lb/eigen_ub/feasible/sq_sconstraint and rotSF_exists in the paper session.


### RA-value2-12. Case-2 analysis lemmas and Case-2 prose stranded in the path-toolkit theories

*misplacement, impact medium, confidence high, ~215 lines.*  
Locations: Relative_Arbitrage/Pair_Path_Laws.thy:593 tilted_local_touching; Pair_Path_Laws.thy:1047 horn_B_locally_constant; Pair_Path_Laws.thy:1156-1170 text 'The second horn dies here …'; Pair_Path_Laws.thy:3745-3758 subsection 'Case 1 for the lower envelope' + text; Pair_Path_Space.thy:219-226 text on the subspace-tangential member confinement

tilted_local_touching and horn_B_locally_constant concern an lsc function W, a symmetric M and tilted quadratics. They mention nothing of paths or of the paper, and they are used only by Case_2 (786, 1193, 1222). PLAN_RESTRUCTURING_2 §3.2 scheduled tilted_local_touching for Semicontinuous_Analysis; it went into Pair_Path_Laws instead, which the ROOT describes as knowing "nothing of the constraint set or the value function".

The prose blocks are also out of place:
- Pair_Path_Laws:1156 motivates exit_val_not_locally_constant (Case_2:835);
- Pair_Path_Laws:3745-3758 motivates exit_val_supersol_contradiction_case1_lsc (Case_2:51) and is followed by an unrelated lemma;
- Pair_Path_Space:219-226 motivates exit_val_ball_lower_subspace (Assembly).

Evidence: Pair_Path_Laws:593 `lemma tilted_local_touching: fixes W :: "real^'n ⇒ real" … assumes lsc: …`; Pair_Path_Laws:1162 "so \<open>exit_val_ball_lower_plus\<close> gives \<open>v z ≥ θ + c\<close>"; Pair_Path_Laws:3745 `subsection \<open>Case 1 for the lower envelope\<close>` followed by lemma quad_good_rat_to_real_region.

Suggested action: Move tilted_local_touching and horn_B_locally_constant to Semicontinuous_Analysis (or Second_Order_Viscosity_Analysis.Test_Functions next to test_fun_strict_minorant_zero_grad). Move the three prose blocks to Case_2:829, Case_2:47 and Value_Function_Assembly:27 respectively.


### RA-value2-13. Linear import chain serialises independent theories; redundant imports

*build_time, impact medium, confidence high, ~20 lines.*  
Locations: Value_Function_Tangential_Field.thy:5 imports Value_Function_Supersolution_Case_2; Value_Function_Assembly.thy:5-8; Value_Function_Supersolution_Case_1.thy:5-9, Case_2:5-10

The chain is Euler_Construction → Case_1 → Case_2 → Tangential_Field → Assembly → Uniqueness.

Tangential_Field uses nothing from Case_2: projmat/tanpU are self-contained, and subspace_tangential_exact_growth needs only eulerp_limit_good2_region from Case_1. Assembly needs only Tangential_Field, the DPP lemmas and radial_sq_upto_gen. Its only dependency on Case_2 is the documentation antiquotation @{thm [source] exit_val_supersol_lsc} at Assembly:18. So Case_2 (1493 lines of heavy proofs) blocks both theories for no reason.

The extra imports "Symmetric_Matrix_Spectra.Matrix_Algebra", "Continuous_Time_Martingales.Essential_Infimum", "Continuous_Path_Spaces.Path_Exit_Times" and Path_Law_Sampling are already ancestors through Value_Function_Euler_Construction and Value_Function_Subsolution.

Evidence: grep in Tangential_Field/Assembly for names declared in Case_2 → only Assembly.thy:18 (text antiquotation). Euler_Construction imports already include Matrix_Algebra, Path_Exit_Times, Path_Law_Sampling; Subsolution includes Essential_Infimum.

Suggested action: After moving the region chain into Euler_Construction, make Tangential_Field import Euler_Construction only. Then Case_1 and Tangential_Field check in parallel, and Case_2 imports both. Move the clause-(2) prose from Assembly:15-25 to Uniqueness. Drop the redundant imports.


### RA-value2-14. Stale, orphaned and incorrect prose in the cluster

*documentation, impact medium, confidence high, ~120 lines.*  
Locations: Value_Function_Supersolution_Case_1.thy:803-809 (empty subsection 'Case 1, packaged for the envelope form'); Case_1:2642-2643 ('The original ball bound is the case β = 0' — no such lemma follows); Case_2:15-25 (second `section`; claims 'This section builds the envelope, states the faithful supersolution notion, and records two algebraic facts' — all moved elsewhere); Case_2:27-47 (four subsections containing only 'X lives in Y' pointers; 'Growth up to a time, on a region' heads case1_lsc); Case_2:641-682 ('all three are proved here in the abstract' / 'The envelope version proved above' — none are proved here); Case_2:1290-1292 ('Case 1 … is the skew-trick contradiction' — the formalisation uses exact rotations, rotSF_exists); Case_2:585-590 ('uniqueness theorem … works with continuous solutions' — theorem_1_1_uniqueness_faithful needs only usc); Tangential_Field.thy:11 and Assembly.thy:13 (duplicate `section` headers); Tangential_Field:13 ('The tanp block above' — it is in another theory); Tangential_Field:24-25 ('trace_diff_matrix from Relative_Arbitrage.Operator_Formula' — it is in Symmetric_Matrix_Spectra/Poincare_Separation.thy); Tangential_Field:115-125, 852-856, 858-861 (text blocks describing lemmas that are not there); Tangential_Field:464, 618, 635 (two Isar commands on one line: 'qed  show ?thesis', 'xfix)    have k0:', 'by (rule argc)    have k0:')

These are remnants of mechanical text moves. They produce a misleading document:
- empty subsections;
- headings over unrelated lemmas;
- false claims about where things are proved or which construction is used: the skew trick, and tanSF as the horn-B input;
- a wrong theory pointer;
- doubled section titles in three of the four theories.
The joined command lines at Tangential_Field 464, 618 and 635 show that a line-based rewriter dropped newlines.

Evidence: Quoted in the locations. `grep -n '^section' Value_Function_Tangential_Field.thy` → lines 1 and 11 with the identical title. trace_diff_matrix defined at Symmetric_Matrix_Spectra/Poincare_Separation.thy, not in Operator_Formula.

Suggested action: Delete the empty subsections and pointer-only text blocks, and remove the duplicate `section`s. Fix the skew-trick sentence (exact rotation via rotSF_exists), the trace_diff_matrix pointer and the 'proved here' claims. Split the joined command lines.


### RA-value2-15. ell_op_lt_witness duplicates ell_op_approx (Operator_Envelopes) and sits in the wrong layer

*clone, impact low, confidence high, ~18 lines.*  
Locations: Value_Function_Supersolution_Case_1.thy:19-36 ell_op_lt_witness; Relative_Arbitrage/Operator_Envelopes.thy:874-893 ell_op_approx

ell_op_lt_witness states "ell_op k L p H < 1 ⟹ ∃a ∈ feasible k L p. - trace (H ** a)/2 < 1". Its proof is the cInf_less_iff argument of ell_op_approx, and it rebuilds boundedness from ell_op_s_bdd_below plus feasible_subset_sconstraint instead of using ell_op_bdd. It is ell_op_approx with ε := 1 - ell_op k L p H. The statement mentions only the operator, so it belongs in Operator_Envelopes.

Evidence: Case_1:28-32 "bdd_below_mono[OF ell_op_s_bdd_below[OF L0] image_mono[OF feasible_subset_sconstraint]] ... using cInf_less_iff[OF ne bdd]"; Operator_Envelopes:884-889 "bdd ... by (rule ell_op_bdd[OF L0]) ... using cInf_less_iff[OF ne bdd]".

Suggested action: Restate it as a 3-line corollary of ell_op_approx placed in Operator_Envelopes, or inline ell_op_approx at the two call sites (Case_1:486, Case_2:95).


### RA-value2-16. exit_val_case2_tilt_step is unused and its second half duplicates exit_val_case2_at_minimiser

*dead_code, impact low, confidence high, ~80 lines.*  
Locations: Value_Function_Supersolution_Case_2.thy:753-827 exit_val_case2_tilt_step; Case_2:979-1023 exit_val_case2_at_minimiser; Case_2:975-977 text

exit_val_case2_tilt_step is referenced only in the prose at Case_2:975. Its body splits into tilted_local_touching plus a copy of exit_val_case2_at_minimiser: the steps yi, tfy, tminy and the ccontr through exit_val_supersol_contradiction_case1_lsc are identical to lines 997-1022.

Evidence: grep -rnw exit_val_case2_tilt_step → declaration and Case_2:975 (text). Case_2:799-825 and Case_2:998-1022 are line-identical.

Suggested action: Delete exit_val_case2_tilt_step and reword the text at 975-977.


### RA-value2-17. exit_val_supersol_lsc repeats the case split of exit_val_supersol_lsc_local

*clone, impact low, confidence high, ~35 lines.*  
Locations: Value_Function_Supersolution_Case_2.thy:1302-1343 exit_val_supersol_lsc; Case_2:1354-1384 exit_val_supersol_lsc_local

Both do the same `cases "g x = 0"`, with the ccontr through case1_lsc, ell_op_le_ell_op_usc, and exit_val_case2 in the other branch. exit_val_supersol_lsc is _local with ρ = 1 and loc derived from the global touching, which is exactly what lines 1318-1321 already compute.

Generalisation: _local is the pointwise content of the existing predicate supersol_jet (Viscosity_Definitions.thy:122, local touching on a ball). A theorem `exit_val_supersol_jet: supersol_jet k L (interior K) (lsc_env v)` would give both the lsc form and the envK form.

Evidence: Case_2:1323-1342 and Case_2:1366-1384 are identical up to the `rho0`/`zero_less_one` argument.

Suggested action: Prove exit_val_supersol_lsc as `by (rule exit_val_supersol_lsc_local[OF ... zero_less_one]) (use tmin in blast)` inside the ballI/allI/impI skeleton, or state the result once through supersol_jet.


### RA-value2-18. radial_sq_upto is the instance F = |· - y0|² of radial_sq_upto_gen; the 'transport to the endpoint' argument appears four times

*clone, impact low, confidence high, ~85 lines.*  
Locations: Relative_Arbitrage/Pair_Path_Laws.thy:3265-3347 radial_sq_upto; Relative_Arbitrage/Pair_Path_Space.thy:138 radial_sq_upto_gen; Pair_Path_Laws.thy:3668 quad_good_upto_region, 3944 quad_good_upto

radial_sq_upto, used only at Case_1:2500 and 2544, is radial_sq_upto_gen with F := λw. (norm (w - y0))² and c0 := (norm (x - y0))², and has the same proof skeleton (tj = e - e/(2(j+1)), continuity, LIMSEQ). quad_good_upto(_region) repeats the same approximation for an inequality instead of an equality.

Evidence: Pair_Path_Space.thy:132-136 text: "radial_sq_upto transports the growth identity ... Nothing in its proof is specific to λw. (norm (w - y0))²". Pair_Path_Laws:3277 and Pair_Path_Space:148 have identical gc/tj proofs.

Suggested action: Delete radial_sq_upto and use radial_sq_upto_gen at Case_1:2500 and 2544. Consider one generic lemma (continuous g on {0..c}, a closed condition holding on [0,e) transfers to e) that covers the quad_good_upto pair as well.


### RA-value2-19. Small proof copies inside the tangential block

*clone, impact low, confidence high, ~60 lines.*  
Locations: Value_Function_Supersolution_Case_1.thy:2130-2151 (lbA in tanp_sq_sconstraint) vs 886-910 tanp_eigen_lb; Case_1:2160-2176 tanRF_cont vs 1064-1084 (tanSF continuity); Case_1:2223-2240 killRO vs 1093-1113 tanSF_kill proof; Case_1:2333 and Tangential_Field:775 negmv

Several proofs are pasted locally:
- tanp_sq_sconstraint re-proves the hyperplane eigen_lb argument (subspace_hyperplane, dim_hyperplane, case u = 0) instead of reusing tanp_eigen_lb.
- tanRF_cont and the tanSF continuity proof are the same entrywise `eq`/continuous_on_vec_lambda argument.
- killRO repeats the tanSF_kill computation.
- The local fact `(- A) *v d = - (A *v d)` is proved twice.
All of these disappear if the tanp block is replaced by tanpU instances (see the tanp/tanpU finding).

Evidence: Case_1:2132-2145 vs 891-904 (identical except the variable name v/x). Case_1:2170-2175 vs 1076-1083.

Suggested action: Resolve them through the tanp→tanpU unification. Failing that, reuse tanp_eigen_lb and tanRF_cont (compose with closest_point).


### RA-value2-20. tanpV and visc_supersol_lsc_iff_env are unused; visc_supersol_lsc is a near-duplicate predicate

*dead_code, impact low, confidence high, ~60 lines.*  
Locations: Value_Function_Tangential_Field.thy:111-113 tanpV; Value_Function_Supersolution_Case_2.thy:596-639 visc_supersol_lsc_iff_env; Relative_Arbitrage/Viscosity_Definitions.thy:110 visc_supersol_lsc; Value_Function_Uniqueness.thy:104-116 text

- tanpV has no use.
- visc_supersol_lsc_iff_env is named only in the prose of Uniqueness:110, and that prose ("The statement below assumes continuity of exit_val on K") describes a theorem that no longer follows it.
- By definition, visc_supersol_lsc k L K Ω u ⟷ visc_supersol_env k L K Ω (lsc_env u). Uniqueness:283 converts between them with `unfolding visc_supersol_lsc_def visc_supersol_env_def by blast`. The extra predicate only costs conversions.

Evidence: grep -rnw tanpV → definition only. grep visc_supersol_lsc_iff_env → declaration and Uniqueness.thy:110 (text). Viscosity_Definitions.thy:110-116 vs 70-76.

Suggested action: Delete tanpV and visc_supersol_lsc_iff_env along with the stale prose at Case_2:583-594 and Uniqueness:104-116. Consider stating exit_val_supersol_lsc directly as visc_supersol_env … (lsc_env v) and retiring visc_supersol_lsc (8 occurrences).


### RA-value2-21. Matrix-vector helpers consumed by the cluster duplicate HOL-Analysis

*library_duplicate, impact low, confidence high, ~20 lines.*  
Locations: Symmetric_Matrix_Spectra/Matrix_Algebra.thy:88 matvec_add_right; Matrix_Algebra.thy:653 matvec_diff_right; Matrix_Algebra.thy:658 matvec_scaleR_right; Matrix_Algebra.thy:68 scaleR_matrix_vector; used at Tangential_Field:80, 98, 453, 487, 508, 617, 622, 638, 803 and Case_1:1100, 2230

Four Matrix_Algebra helpers re-prove HOL-Analysis lemmas:
- matvec_add_right "A *v (x + y) = A *v x + A *v y" = matrix_vector_right_distrib (HOL/Analysis/Finite_Cartesian_Product.thy:1153);
- matvec_diff_right = matrix_vector_mult_diff_distrib (Finite_Cartesian_Product.thy:1157);
- matvec_scaleR_right "A *v (r *R x) = r *R (A *v x)" = matrix_vector_mult_scaleR (Finite_Cartesian_Product.thy:1162);
- scaleR_matrix_vector "(r *R A) *v x = r *R (A *v x)" = scaleR_matrix_vector_assoc[symmetric] (HOL/Analysis/Cartesian_Space.thy:371).
The Matrix_Algebra versions are restricted to square real matrices.

Evidence: Statements quoted above; e.g. Finite_Cartesian_Product.thy:1162 `lemma matrix_vector_mult_scaleR[algebra_simps]: fixes A :: "real^'n^'m" shows "A *v (c *\<^sub>R x) = c *\<^sub>R (A *v x)"`.

Suggested action: Replace these with the HOL names, or turn them into `lemmas … = …` aliases, in Symmetric_Matrix_Spectra. This belongs to that cluster but touches about 12 call sites here.


### RA-value2-22. Unused hypotheses

*generalisation, impact low, confidence medium, ~6 lines.*  
Locations: Value_Function_Supersolution_Case_1.thy:2181 tangential_exact_growth (kn: "k < CARD('n)"); Case_1:2390 exit_val_ball_lower_plus (b0: "0 ≤ β"); Case_1:1038 tanSF_package (kn)

Three hypotheses are never used:
- In tangential_exact_growth, kn is not referenced in the proof. SFs needs only k1 and L1 (tanp_sq_sconstraint), and eulerp_limit_good2_region needs only T0 and L1.
- In exit_val_ball_lower_plus, b0 is never referenced: min β (T/2) ≤ β holds regardless of sign, and ennreal_leI needs no sign.
- In tanSF_package, kn is unused (dead anyway).

Evidence: `sed -n 2188,2370p | grep -cw kn` → 0. `sed -n 2397,2640p | grep -c b0` → 0.

Suggested action: Drop kn from tangential_exact_growth and b0 from exit_val_ball_lower_plus. Adjust the call sites at Case_1:2429 and Case_2:918 (c0 argument).


### RA-value2-23. Repeated psd eigendecomposition boilerplate; outerp_eq_outer_prod declared twice

*clone, impact low, confidence medium, ~80 lines.*  
Locations: Value_Function_Supersolution_Case_1.thy:286-302 (rotSF_exists); Value_Function_Subsolution.thy:1868-1889; Eigenvalue_Bound_Exact.thy:568-583; Operator_Formula.thy:299, 489, 1515, 2040; Relative_Arbitrage/Exit_Class.thy:218 and Pair_Path_Space.thy:771 outerp_eq_outer_prod

About eight places repeat the same block: symmetric_eigenbasis, then onormal_finite, then onormal_span_card, then define lam u = u ∙ (a *v u), then lam_nn from psd, then spectral_decomposition. One `psd_eigendecomposition` obtains-lemma in Symmetric_Spectral returning a finite onormal B with card = n, nonnegative λ and the decomposition would cut about 10 lines per site. Separately, `outerp_eq_outer_prod` is proved twice in the same session: Exit_Class.thy:218 shadows Pair_Path_Space.thy:771. Case_1:834 uses it.

Evidence: Case_1:288-297 vs Subsolution:1871-1883 vs Eigenvalue_Bound_Exact:571-581 (same sequence of facts). Exit_Class.thy:218 `lemma outerp_eq_outer_prod: "outerp x = outer_prod x x"` and Pair_Path_Space.thy:771 `lemma outerp_eq_outer_prod:`.

Suggested action: Add psd_eigendecomposition (with an optional bij_betw enumeration, as exists_enum_of_card provides) to Symmetric_Matrix_Spectra.Symmetric_Spectral. Delete the Exit_Class copy of outerp_eq_outer_prod.


## RA-comparison

Every line of the seven theories was read. No PIDE check was possible: list_sessions showed no running session, and start_session(no_build) failed because not even HOL-Analysis has a heap ("Build failed with unfinished session(s): HOL-Analysis"). Use counts therefore come from grep -rnw over the repository.

What the cluster proves: Theorem 4.2(a) (max_principle_boundary_holds, CP:1902) and its corollary viscosity_uniqueness_compact; Theorem 4.2(b) (comparison_two_domain, CT:197); Theorem 4.3 (comparison_expandable, CT:550); Proposition 4.1 (uniqueness_expandable, CT:766); and the assembly of Theorem 1.1's uniqueness clause, Example 3.1 and the horizon-free iexit_val clauses (Value_Function_Uniqueness). Crandall_Ishii_Sums (CIS) proves the Crandall–Ishii theorem on sums for the quadratic coupling in two forms: a staged form and a closed-semijet form. No theory uses CIS.

Faithfulness. The path the Statement session uses is faithful to Def. 3.1 / Thm 4.2(b) / Thm 4.3 / Prop. 4.1: C² test functions, global touching on K, F_*/F^*, usc/lsc data, the boundary gates, and the K-relative lower envelope via Kext. That path is iexit_val_uniqueness_K → theorem_1_1_uniqueness_faithful → uniqueness_expandable → comparison_expandable → comparison_two_domain. One documented deviation: the proof uses soft_pen instead of the paper's ε⁻¹|x−y|⁴. The paper's Theorem 4.2(a), however, appears only in a weaker form (continuity, test_fun_at) that Theorem 1.1 never uses, and prose in three theories wrongly says 4.2(b), 4.3 and 4.1 are derived from it.

KEY QUESTION. Crandall_Ishii_Sums is not the clone. The Comparison_* layer contains a bespoke, penalty-specific re-derivation of the theorem on sums, written twice (quadratic, now dead, and _gen, live): shifted Jensen family → tilted slices → psd ordering → sup-convolution attainment → jet transfer → bounded family → subsequence → envelope limits. CIS.theorem_on_sums_stage runs the same pipeline once and packages it in standard semijet vocabulary. Rebasing is feasible: the semiconcave penalty is majorised by its tangent quadratic, which turns the coupling into a shifted quadratic one, so theorem_on_sums_quadratic_closed applies. That would remove the sup-convolutions from the paper session altogether and make the diagonal case elementary. Estimated deletion: about 2500–3500 lines across RA (live chain about 950 lines, replaced by about 200) and DoV (the _gen chain). Separately, about 1500 lines of the cluster are dead regardless.

Paper-free vs F-specific. Everything except about 10 operator facts is paper-free. Those facts are: degenerate ellipticity, 1-homogeneity in M and 0-homogeneity in p, F_* = F = F^* off p = 0, F^*(q, −δI) < 1, the Lipschitz gap in M, and rotation/dilation invariance of F^*. The paper-free remainder includes the sup-convolution attainment lemmas, localisation, cong/mono/locality lemmas of the viscosity notions, quartic deepening and the envelope limit lemmas.

Organisation: a strictly linear import chain Jets → Strictness → Localisation → Principle → Two_Domain → VFU. Comparison_Jets is an empty husk. Strictness and Localisation consist largely of 'X lives in Y' stubs left behind by the previous move.


### RA-comparison-1. About 1500 lines of the cluster are used by nothing (only prose mentions)

*dead_code, impact high, confidence high, ~1500 lines.*  
Locations: Relative_Arbitrage/Comparison_Principle.thy:13 comparison_supconv_doubling_complete (193); Relative_Arbitrage/Comparison_Principle.thy:217 comparison_supconv_maximiser_complete (430); Relative_Arbitrage/Comparison_Principle.thy:1241 max_principle_boundary_counterexample (24) + :1180 visc_supersol_cong_on (27, used only by it); Relative_Arbitrage/Comparison_Localisation.thy:203 comparison_env_complete (45), :146 comparison_env_from_jets (26), :455 comparison_supconv_complete (35), :676 env_strict_contradiction_of_limits (59), :107 supersol_no_vanishing_jet (30); Relative_Arbitrage/Comparison_Localisation.thy:902 supconv_attained_ball (73), :975 supconv_attained, :992 supconv_attained_in, :1012 supconv_attained_family_in, :1107 supconv_attained_in_rad, :1124 supconv_attained_family_in_rad; Relative_Arbitrage/Comparison_Strictness.thy:573 comparison_contradiction (48), :492 visc_subsol_scaled_strict (40), :832 strict_contradiction_of_shifts_any_p (53), :801 eq36_rhs_antitone, :680 ell_op_usc_envelope_elliptic_le (40), :649 ell_op_lsc_elliptic_le, :634 ell_op_pair_shift_snd_le, :953 ell_op_lsc_le_of_shifts (60), :1013 ell_op_usc_ge_of_shifts (59), :1078 env_strict_contradiction_of_shifts, :1157 subsol_shifted_bound, :1225 supersol_shifted_bound, :1256 supersol_shifted_bound_ne; Relative_Arbitrage/Value_Function_Uniqueness.thy:22 theorem_1_1_ball_fragment, :87 theorem_1_1_uniqueness_general

Grep (excluding the definition line and text mentions) shows that each of these is used by nothing, or only by another member of the list. Examples: comparison_supconv_doubling_complete is named only in the 'Map' text CP:2155; comparison_supconv_maximiser_complete only in texts CP:649 and CP:1313; eq36_rhs_antitone and ell_op_lsc_elliptic_le only in the map CP:2132-2135; theorem_1_1_uniqueness_general only in prose (VFU:85, Exit_Class_Optimizer:23).

Removing them makes further lower-session lemmas dead: shifted_jensen_family (DoV:4829, 134), tilted_doubled_psd_ordering (DoV:5191), norm_block_matrices_bounded (DoV:3071), penalty_gradient_nearby_upper/_bound (DoV:3529/3183), doubled_supconv_jet_exists (DoV:4270), block_matrices_from_jet (DoV:4586), jet_imp_local_max_test / jet_imp_local_min_test (DoV), small_multiple_exists and shift_limit_absurd(2) (DoV:3898-3923), jet_test_fun_at_abstract (Test_Functions:479), ball_prod_shift_snd (Matrix_Algebra), and the whole max_principle_boundary interface (see the faithfulness finding).

Evidence: grep -rnw comparison_supconv_doubling_complete → only 'Comparison_Principle.thy:2155: 6. The instantiation: \<open>comparison_supconv_doubling_complete\<close> runs'; comparison_env_complete → 0 other lines; env_strict_contradiction_of_limits → 0; supconv_attained_family_in used only at CP:161/169 (inside dead comparison_supconv_doubling_complete); grep in DoV for shifted_jensen_family / tilted_doubled_psd_ordering / norm_block_matrices_bounded / penalty_gradient_nearby_upper → no internal uses.

Suggested action: Confirm with the semantic dependency run, then delete the RA lemmas, rerun, and delete the DoV/SMS lemmas that become dead. Keep visc_subsol_scaled_uniform, supersol_shifted_bound_onesided and supersol_no_vanishing_jet_onesided, which are live.


### RA-comparison-2. Theorem 4.2(a) is formalised in a weaker form than the paper's, is not used by Theorem 1.1, and three prose blocks wrongly say 4.2(b)/4.3/4.1 rest on it

*faithfulness, impact high, confidence high, ~1000 lines.*  
Locations: Relative_Arbitrage/Comparison_Principle.thy:1902 max_principle_boundary_holds; Relative_Arbitrage/Viscosity_Definitions.thy:153 max_principle_boundary (requires continuous_on K u / w, visc_subsol_env = test_fun_at); Relative_Arbitrage/Comparison_Principle.thy:1266-1274 text; Relative_Arbitrage/Viscosity_Definitions.thy:127-143 text; Relative_Arbitrage/Operator_Envelope_Continuity.thy:562-655 (max_principle_le 'Theorem 4.2(b)', comparison_from_max_principle 'Theorem 4.3', uniqueness_from_max_principle 'Proposition 4.1')

Paper Thm 4.2(a) assumes u usc, w lsc and Def. 3.1 with C² test functions. The formal max_principle_boundary assumes 'continuous_on K u ⟶ continuous_on K w' and uses visc_subsol_env/visc_supersol_env, which quantify over test_fun_at test functions; that is a stronger hypothesis on u and w than the paper's C² class. The env/C² gap is free to close: the proof converts at once ('visc_supersol_env_imp_jet [OF visc_supersol_env_imp_env2[OF supE] ...]', CP:1935; 'visc_subsol_env_imp_visc_subsol [OF visc_subsol_env_imp_env2[OF subE] ...]', CP:1952). Continuity is used only by doubling_localised_maximiser_soft (uniform modulus), supconv_uniform_upper, continuous_extension_bounded and the usc derivation at CP:1417-1426. comparison_two_domain shows the same doubling works with usc/lsc data. The Statement session never reaches max_principle_boundary_holds: Thm 1.1 goes through comparison_two_domain. Yet CP:1272 says 'Everything downstream - 4.2(b), Theorem 4.3, Proposition 4.1 - is unchanged except for carrying this continuity'. Viscosity_Definitions:133 says 'everything downstream -- 4.2(b), Theorem 4.3, Proposition 4.1 -- is proved unconditionally' and :141-143 claims a 'lack of a semicontinuity library'. Operator_Envelope_Continuity labels its continuity-based corollaries with the paper's theorem numbers, while the real ones are comparison_two_domain, comparison_expandable and uniqueness_expandable.

Evidence: Viscosity_Definitions.thy:157-161: 'visc_subsol_env k L K (interior K) u ⟶ visc_supersol_env k L K (interior K) w ⟶ continuous_on K u ⟶ continuous_on K w ⟶ (∃x ∈ K - interior K. ...)'. Paper Thm 4.2(a): 'If u is an upper semicontinuous viscosity subsolution ... and w is a lower semicontinuous viscosity supersolution ...'. grep: max_principle_boundary_holds is used only via viscosity_uniqueness_compact → theorem_1_1_uniqueness_general (dead).

Suggested action: Either (a) restate max_principle_boundary with visc_*_env2 and usc/lsc, and prove it with the localisation shared with comparison_two_domain, so that Theorem 4.2(a) appears faithfully as a result 'of independent interest'; or (b) delete 4.2(a) and the whole continuity interface. The interface comprises max_principle_boundary(_raw), max_principle_boundary_gen (SOVA Viscosity_Solutions), max_principle_le, comparison_from_max_principle, uniqueness_from_max_principle, locale comparison_principle, ball_v_unique_solution, viscosity_uniqueness_compact, theorem_1_1_uniqueness_general and max_principle_boundary_counterexample. In both cases correct the three prose blocks.


### RA-comparison-3. KEY: the comparison layer re-derives the theorem on sums; rebase it on Crandall_Ishii_Sums (CIS is not the clone)

*structure, impact high, confidence medium, ~3000 lines.*  
Locations: Relative_Arbitrage/Comparison_Principle.thy:658 comparison_supconv_maximiser_complete_gen (482 lines); Relative_Arbitrage/Comparison_Localisation.thy:1663 comparison_supconv_bounded_family; Relative_Arbitrage/Comparison_Localisation.thy:800 comparison_supconv_sequence_complete; Relative_Arbitrage/Comparison_Localisation.thy:293,352,425 subsol_shifted_bound_supconv, supersol_shifted_bound_supconv(_ne); Relative_Arbitrage/Comparison_Localisation.thy:747 env_strict_contradiction_of_shifted_limits; Second_Order_Viscosity_Analysis/Crandall_Ishii_Sums.thy:613 theorem_on_sums_stage; Second_Order_Viscosity_Analysis/Crandall_Ishii_Sums.thy:2039 theorem_on_sums_quadratic_closed; Second_Order_Viscosity_Analysis/Doubling_Of_Variables.thy:4963 shifted_jensen_family_gen, :3305 tilted_doubled_jet_slices_gen, :5251 tilted_doubled_psd_ordering_gen, :3375 tilted_doubled_hessian_nonpositive_gen, :3149 norm_block_matrices_bounded_gen, :3641/:3658 penalty_gradient_nearby_*_gen, :2329/:2401 nearby_of_convergent_shifted(_neg), :3484 bounded_seq_limit_point_triple

The live Theorem 4.2(b) path is comparison_two_domain → comparison_2dom_off_diagonal → comparison_supconv_maximiser_complete_gen → comparison_supconv_bounded_family → comparison_supconv_sequence_complete. It builds the theorem on sums inline: shifted Jensen family at shrinking tilts on the doubled sup-convolution functional, tilted slices, psd ordering, sup-convolution attainment, jet transfer to the attainment points, bounded families, a subsequence, then envelope limits. CIS.theorem_on_sums_stage runs exactly this pipeline (doubled_supconv_jet_exists_shifted, tilted_doubled_jet_slices, tilted_doubled_hessian_nonpositive, sums_gives_ordering, supconv_attained_usc, supconv_jet_transfer). It does so once, for the quadratic coupling, and packages the result as superjet/subjet and closed semijets.

CIS is quadratic-only, while the paper (and the formalisation) need a penalty that is quartic near 0 so the diagonal case closes. The quadratic restriction can still be bridged. Let P be semiconcave (the hypothesis sc: convex_on UNIV (λd. (κ/2)|d|² − P d) already assumed at CP:668) with gradient G at d̂ = x̂ − ŷ. Then P(e) ≤ P(d̂) + G·(e − d̂) + (κ/2)|e − d̂|² = (κ/2)|e − c|² + const with c = d̂ − G/κ. So (x̂ − c, ŷ) is a global max of ũ(·+c)(x) − w̃(y) − (κ/2)|x − y|². CIS then gives (G, X) ∈ J̄²⁺ũ(x̂), (G, Y) ∈ J̄²⁻w̃(ŷ), X ≤ Y. The closed jets carry u(x_i) → u(x̂), which also discharges Definition 3.1's gate {u > 0} without atu_of_positive_ball.

The diagonal case needs no regularisation either. If (p, p) is a max, then w(y) ≥ w(p) − P(p − y) = w(p) − o(|y − p|²) directly, which is the paper's argument. So the sup-convolutions, their attainment, the ε-smallness and the radius bookkeeping all leave the paper session.

Evidence: CIS:739 'using doubled_supconv_jet_exists_shifted[...]', CIS:761 'note slices = tilted_doubled_jet_slices[...]', CIS:773 'by (rule sums_gives_ordering[OF expA scW hiW])'. CP:726 'using shifted_jensen_family_gen[OF Bu Bw e kap sc rho(1) rho(2) D0 mxK]', CP:769 'tilted_doubled_hessian_nonpositive_gen', CP:781 'tilted_doubled_psd_ordering_gen', CP:822 'tilted_doubled_jet_slices_gen(2)'. grep: no theory imports Crandall_Ishii_Sums; the only users of the quadratic DoV lemmas besides CIS are the dead CP:13/CP:217 theorems.

Suggested action: 1. In SOVA, next to CIS, add (a) the penalty-majorant reduction for a semiconcave penalty differentiable at d̂ (about 60 lines); (b) closure of superjet_cl/subjet_cl under adding a constant and translating (about 30 lines); (c) an lsc extension of w by a large constant off a closed set (mirror of usc_extend_const_below).
2. In the generic viscosity layer, prove that a closed superjet of a subsolution gives F_*(p, X) ≤ c, and dually for supersolutions (about 80 lines). This uses superjet ⇒ quadratic touching from above, which holds by definition, plus the nearby-point envelope lemma.
3. Rewrite comparison_2dom_off_diagonal as: localise, apply CIS, close with ell_op_env_strict_contradiction.
4. Delete comparison_supconv_maximiser_complete_gen, comparison_supconv_bounded_family, comparison_supconv_sequence_complete, the *_shifted_bound_supconv lemmas, env_strict_contradiction_of_shifted_limits and the DoV _gen chain.
5. Factor CIS's two theorems first (see the CIS-internal finding).
Do this in a worktree, gated, since it is mathematics rather than a move.


### RA-comparison-4. The comparison layer is paper-free modulo about 10 properties of F: state it for an abstract geometric operator

*generalisation, impact high, confidence medium, ~5000 lines.*  
Locations: Relative_Arbitrage/Comparison_Strictness.thy; Relative_Arbitrage/Comparison_Localisation.thy; Relative_Arbitrage/Comparison_Principle.thy; Relative_Arbitrage/Comparison_Two_Domain.thy; uses: ell_op_elliptic_le (OEC:513), ell_op_scaleR_matrix/_p, ell_op_lsc_off_zero/ell_op_usc_eq_at_nonzero, ell_op_usc_small_shift_lt_one, ell_op_usc_zero_zero_lt_one, ell_op_lsc_at_zero + ell_op_M_gap/mgap_shift_id, feasible_nonempty, ell_op_usc_scale, ell_op_usc_conj_rot

The only F-specific inputs of Theorems 4.2(a)/(b), 4.3 and Prop. 4.1 are:
(A1) degenerate ellipticity;
(A2) F(p, θM) = θF(p, M) and F(θp, M) = F(p, M) for θ > 0, which is the strictness mechanism;
(A3) F_* = F = F^* at p ≠ 0 for symmetric M;
(A4) F^*(q, −δI) < 1 uniformly for small δ, and F^*(0, 0) < 1;
(A5) F_*(0, ·) = F(0, ·) and the Lipschitz gap in M (used only in visc_subsol_env_imp_visc_subsol);
(A6) rotation/dilation invariance of F^*, for 4.3.
Everything else is paper-free: localisation, doubling, sup-convolution, envelope limits, cong/local lemmas, affine transport of supersolutions, the expandable limit. Yet k, L and CARD('n) bounds are threaded through every statement ('kk: "1 ≤ k" "k < CARD('n)" and LL: "1 ≤ L"' in about 40 theorems).

Evidence: grep of the cluster proofs for ell_op lemmas finds only the list in 'locations'. comparison_two_domain's 343 lines mention ell_op only through visc_*_env2 and the sub-lemmas.

Suggested action: Define a locale geometric_operator F (with A1-A6) in a paper-free theory or session on SOVA + Semicontinuous_Analysis, holding the comparison principle for F(∇u, ∇²u) = 1 with zero boundary condition. The paper session interprets it at ell_op k L, discharging A1-A6 from existing lemmas. This is the analogue of G2/G11 in PLAN_RESTRUCTURING_2 for the comparison layer. It is best done after the rebase on CIS, which shrinks what has to move.


### RA-comparison-5. Sup-convolution attainment proved four times, with seven corollary variants, and misplaced in the paper session

*clone, impact medium, confidence high, ~470 lines.*  
Locations: Relative_Arbitrage/Comparison_Localisation.thy:902 supconv_attained_ball (73, continuous); Relative_Arbitrage/Comparison_Localisation.thy:1036 supconv_attained_ball_rad (71, continuous; same proof with R parameter); Relative_Arbitrage/Comparison_Localisation.thy:1188 supconv_attained_usc_ball (81, usc, real^'n); Second_Order_Viscosity_Analysis/Crandall_Ishii_Sums.thy:153 supconv_attained_usc (91, usc, euclidean_space); Relative_Arbitrage/Comparison_Localisation.thy:975,992,1012,1107,1124,1269,1285,1301 corollaries; Relative_Arbitrage/Comparison_Localisation.thy:1317 supconv_le_of_local_bound vs Second_Order_Viscosity_Analysis/Doubling_Of_Variables.thy:4744 supconv_le_of_local_bound_usc

All four lemmas show that, for u bounded above (continuous or usc), sup_y u y − |x−y|²/(2ε) is attained within radius sqrt(max 0 (2ε(B−u x)))+1. Each re-proves usc of y ↦ u y − dist²/(2ε), the radius computation and the cSUP squeeze. The usc versions subsume the continuous ones, and the radius versions follow from the general one plus supconv_attain_radius (DoV:4707). supconv_le_of_local_bound needs continuity plus attainment, while DoV's supconv_le_of_local_bound_usc proves the same conclusion with no continuity. The CL hypothesis 'sqrt (max 0 (2ε(Bu − u x))) < R' together with loc at y = x implies DoV's '2ε(Bu − M) < R²'; DoV's own text says so. All 16 statements name no paper constant. PLAN_RESTRUCTURING_2 line 429 assigned supconv_attained_usc_ball to Sup_Convolution, and dispositions.tsv marks the rest REVIEW, but none were moved.

Evidence: CL:1188 'lemma supconv_attained_usc_ball: fixes u :: "real^'n::finite ⇒ real" ... uscu: "⋀c z. u z < c ⟹ ∃d>0. ..." obtains ys where "dist x ys ≤ sqrt (max 0 (2*ε*(Bu - u x))) + 1"'; CIS:153 'lemma supconv_attained_usc: fixes u :: "'a::euclidean_space ⇒ real" ... shows "∃ys. supconv u ε x = u ys - (dist x ys)²/(2*ε)"' with R = sqrt (2ε(B − u x)) + 1 at CIS:192. DoV:4733 'supconv_le_of_local_bound gets the same conclusion via attainment, needing continuous_on UNIV u'.

Suggested action: Keep one lemma, supconv_attained_usc, at euclidean_space with the radius conclusion, in Sup_Convolution. Derive the family/in-Ω versions there as 2-line corollaries, delete the continuous versions (after removing dead code only supconv_le_of_local_bound needs them), and replace supconv_le_of_local_bound by DoV's _usc version. Move the survivors and supconv_uniform_upper to SOVA.


### RA-comparison-6. Locality and monotonicity of the viscosity predicates proved separately for each predicate (one exact duplicate)

*clone, impact medium, confidence high, ~200 lines.*  
Locations: Relative_Arbitrage/Comparison_Strictness.thy:30 visc_subsol_env2_cong ≡ Relative_Arbitrage/Comparison_Localisation.thy:1156 visc_subsol_env_agrees; Relative_Arbitrage/Comparison_Strictness.thy:47 visc_supersol_env2_cong; Relative_Arbitrage/Comparison_Principle.thy:1152 visc_subsol_cong_on, :1180 visc_supersol_cong_on, :1208 supersol_jet_cong_on; Relative_Arbitrage/Comparison_Principle.thy:1280 visc_subsol_extend, :1291 supersol_jet_extend; Relative_Arbitrage/Comparison_Localisation.thy:1147 visc_subsol_mono_dom, Comparison_Strictness.thy:64 visc_supersol_env2_mono

visc_subsol_env_agrees states exactly visc_subsol_env2_cong with the assumptions reordered: 'visc_subsol_env2 k L K Ω u', 'Ω ⊆ K', '⋀y. y ∈ K ⟹ u' y = u y'. visc_supersol_cong_on and supersol_jet_cong_on are the same 27-line argument for visc_supersol_gen at ell_op and at ell_op_usc. The three _cong_on lemmas, the two _cong lemmas and the two _mono lemmas are operator-free facts. SOVA's Viscosity_Solutions has generic notions only for test_fun_at; it has no generic C²/env2 notion and no cong lemma. That gap is why the paper session re-proves these per predicate.

Evidence: CS:30-34 'assumes OK: "Ω ⊆ K" and eq: "⋀y. y ∈ K ⟹ f1 y = f2 y" and h: "visc_subsol_env2 k L K Ω f1" shows "visc_subsol_env2 k L K Ω f2"'; CL:1156-1160 'assumes sub: "visc_subsol_env2 k L K Ω u" and OK: "Ω ⊆ K" and eq: "⋀y. y ∈ K ⟹ u' y = u y" shows "visc_subsol_env2 k L K Ω u'"'. supersol_jet_def = visc_supersol_def with ell_op_usc for ell_op (Viscosity_Definitions:119-125).

Suggested action: Add visc_*_gen_env2 (C² test functions) and generic cong_on/cong/mono lemmas to Second_Order_Viscosity_Analysis.Viscosity_Solutions, plus bridge equations for visc_*_env2 and supersol_jet. Delete visc_subsol_env_agrees and reduce the RA lemmas to one-line bridge instances.


### RA-comparison-7. Quartic deepening (local touching ⇒ global touching on K) proved three times

*clone, impact medium, confidence high, ~180 lines.*  
Locations: Relative_Arbitrage/Comparison_Strictness.thy:90 visc_supersol_env2_local (62); Relative_Arbitrage/Comparison_Strictness.thy:152 visc_subsol_env2_local (62); Relative_Arbitrage/Operator_Envelopes.thy:1080 visc_subsol_env_local (62, test_fun_at version, dead)

All three share a 45-line body: C := max 0 (... / r⁴), ψ := φ ∓ C|z−x|⁴ through test_fun_*_quartic_shift, and a case split y ∈ ball vs outside with the r⁴ ≤ |y−x|⁴ estimate. The CS text at 84-88 says the C² versions are 'the originals with test_fun_C2_quartic_shift in place of test_fun_at_quartic_shift'. The core is operator-free.

Evidence: CS:165 'define C where "C = max 0 ((Bu - Bφ - (u x - φ x)) / r ^ 4)"' is identical to Operator_Envelopes.thy:1093; CS:181-208 is identical to OE:1109-1136. grep: visc_subsol_env_local is used nowhere (only text CS:307).

Suggested action: Prove one operator-free lemma in SOVA Test_Functions: 'local max of u − φ on ball x r, u ≤ Bu and φ ≥ Bφ on K ⟹ ∃C ≥ 0. global max on K of u − (φ + C|·−x|⁴), with the same 2-jet', in both test-function classes. Instantiate twice and delete visc_subsol_env_local.


### RA-comparison-8. Crandall_Ishii_Sums: the staged and closed theorems duplicate their whole parameter set-up, and the deconvolution algebra appears three times

*clone, impact medium, confidence high, ~300 lines.*  
Locations: Second_Order_Viscosity_Analysis/Crandall_Ishii_Sums.thy:1155-1351 vs :2054-2261 (b := −w with uscb, dl/q3/ee/ddn, ee0, ee4, dd0n, gapn, ddsmalln, SP, choice4, dlt, q3t, eet, ddt, bndt, gbt); Second_Order_Viscosity_Analysis/Crandall_Ishii_Sums.thy:1601-1633 (deconv_doubled_attains) vs :2262-2278 (galx) vs :2472-2502 (sumL: pend/penn/gsq/penc); Second_Order_Viscosity_Analysis/Crandall_Ishii_Sums.thy:486 superjet_of_transfer / :529 supconv_superjet_at_optimizer vs :1932 superjet_supconv_transfer

theorem_on_sums_quadratic and theorem_on_sums_quadratic_closed each define the same sequences dl n = 1/(n+2), q3 = dl·dl², ee = min(1/(4α+4), q3/(2C+2)) and ddn = q3/8. Each re-proves the same eight side conditions and the same five limits verbatim, with α replaced by al. The identity x0 − y0 = (1 − 2λα)(xh − yh) and the penalty-correction algebra are proved three times. superjet_of_transfer and superjet_supconv_transfer are the same e-δ argument, from an exact jet and from a superjet of the sup-convolution respectively.

Evidence: CIS:1181-1184 'define dl where "dl = (λn :: nat. 1 / (real n + 2))" define q3 ... define ee where "ee = (λn. min (1 / (4 * α + 4)) (q3 n / (2 * C + 2)))"' vs CIS:2109-2112 the same with al; CIS:1606-1611 vs CIS:2266-2271 vs CIS:2476-2481 identical e1/e2/e3.

Suggested action: Extract 'theorem_on_sums_family' (∃ a sequence of stages with all quantitative conjuncts and the limits dl, ee, ddn → 0) and a 'deconv_shift' algebra lemma. Derive both named theorems from them. Make superjet_of_transfer a corollary of 'exact jet ⇒ superjet' plus superjet_supconv_transfer. Consider dropping theorem_on_sums_quadratic: the closed form is what consumers need.


### RA-comparison-9. About 55 'X lives in Y' stubs, about 25 empty or text-only subsections, and orphaned text left by the previous move

*documentation, impact medium, confidence high, ~400 lines.*  
Locations: Relative_Arbitrage/Comparison_Strictness.thy:25-28, 214, 301, 447, 532-565, 569, 631, 752-760, 762-799, 817-825, 829, 885-951 (18 stubs); Relative_Arbitrage/Comparison_Localisation.thy:16-74 (4 empty subsections + 23 blank lines), 177-202, 252-279, 490-501, 597-636, 735-745, 871-890, 1139-1146, 1352-1383, 1646-1662 (25 stubs); Relative_Arbitrage/Comparison_Principle.thy:11, 647, 1278, 1302-1306, 1792-1794, 1899 (8 stubs); Relative_Arbitrage/Comparison_Two_Domain.thy:59-66, 174-194, 542; Relative_Arbitrage/Value_Function_Uniqueness.thy:102 (empty section), 104-116, 565, 660-663

The previous move left section skeletons behind. Many subsections ('Freezing one variable in the doubled maximum', 'What naive doubling delivers', 'The penalty estimate', 'Monotonicity of the doubled maximum', 'Existence of the maximising pair', 'Theorem 4.2(a) from the doubled jet alone', 'A tilt that needs no limit at all', ...) contain only pointers to lemmas in SOVA or SMS, or text describing a statement that no longer follows. Examples:
- CS:752 'The same for the non-strict sandwich ...' has no lemma after it.
- CS:817-825 describes a specialisation of ell_op_le_eq36 that is not stated.
- VFU:113-116 'The statement below assumes continuity of exit_val ... supersedes this one' refers to a deleted theorem.
- VFU:660-663 introduces 'Clause (2), supersolution half' with no theorem.
- VFU:102 'section ‹Example 3.1 realises the ball value exactly, for n − k = 1›' is empty, and example_3_1 is for general k.
- Headings mismatch content: CL:1360 '‹soft_pen› vanishes on the diagonal and is coercive' is followed by supconv_uniform_upper; CL:1646 'Skolemising a four-component existential' is followed by comparison_supconv_bounded_family.
In the rendered PDF this produces dozens of headings with no content.

Evidence: grep -c 'lives in\|live in': Comparison_Localisation 25, Comparison_Strictness 18, Comparison_Principle 8, Comparison_Two_Domain 3, Value_Function_Uniqueness 1.

Suggested action: Delete every stub and empty subsection. Re-sectionise each theory around its actual theorems: strictness/scaling; Def. 3.1 conversions; envelope limits; localisation; off-diagonal; diagonal; 4.2(a); 4.2(b); 4.3; 4.1. Keep the one-paragraph roadmap texts that describe proofs actually present.


### RA-comparison-10. Stale or false claims about which theorem proves what

*documentation, impact medium, confidence high, ~100 lines.*  
Locations: Relative_Arbitrage/Comparison_Principle.thy:2127-2158 'Map of the Theorem 4.2(a) chain'; Relative_Arbitrage/Comparison_Principle.thy:1266-1274; Relative_Arbitrage/Value_Function_Uniqueness.thy:18-19; Relative_Arbitrage/Comparison_Strictness.thy:25-28, 303-307; Relative_Arbitrage/Comparison_Localisation.thy:24-26; Relative_Arbitrage/Exit_Class_Optimizer.thy:15-25; Second_Order_Viscosity_Analysis/Doubling_Of_Variables.thy:4234-4237, 4386, 4455, 4583, 4628, 4733, 5100-5109 (prose naming RA lemmas)

Item by item:
- The map at CP:2155 names 'comparison_supconv_doubling_complete' (dead) as the instantiation, and 2132-2138 name eq36_rhs_antitone, ell_op_lsc_elliptic_le and doubling_grad_lower_bound, none of which is on the live path. The live path is comparison_soft_complete → ... → comparison_supconv_maximiser_complete_gen.
- VFU:18-19 says the comparison principle is 'proved in Comparison_Principle'; the uniqueness used is in Comparison_Two_Domain.
- CS:25-28 refers to 'trace_mul_comm' and 'matrix_mult_scaleR_left', which no longer exist.
- CS:303-307 cites visc_subsol_env_local, but the proof uses visc_subsol_env2_local.
- CL:24-26 cites the dead supersol_no_vanishing_jet.
- Exit_Class_Optimizer:15-25 claims clause (2) is 'not covered', clause (3) is 'only for the ball', and clause (4) 'is theorem_1_1_uniqueness_general'; all three are wrong now.
- SOVA's Doubling_Of_Variables, a paper-free session, contains prose naming RA lemmas (comparison_env_from_jets, subsol_shifted_bound, comparison_supconv_sequence_complete, supconv_attained_ball_rad).

Evidence: CP:2155 '6. The instantiation: ‹comparison_supconv_doubling_complete› runs Jensen at shrinking tilts ... closing ‹max_principle_boundary›'; grep trace_mul_comm / matrix_mult_scaleR_left: no definitions; Exit_Class_Optimizer.thy:23 'Clause (4), uniqueness, is ‹Value_Function_Uniqueness.theorem_1_1_uniqueness_general›'.

Suggested action: Rewrite the CP map from the actual dependency graph, or delete it. Fix VFU:18-19 and Exit_Class_Optimizer:15-25 to point to iexit_val_uniqueness_K, comparison_two_domain, comparison_expandable and uniqueness_expandable. Remove names of paper-session lemmas from SOVA prose.


### RA-comparison-11. Two independent localisation arguments and two off-diagonal parameter threads for the same doubled maximiser

*clone, impact medium, confidence medium, ~550 lines.*  
Locations: Relative_Arbitrage/Comparison_Localisation.thy:1466 doubling_localised_maximiser_soft (180, continuous data, uniform modulus); Relative_Arbitrage/Comparison_Two_Domain.thy:357-499 steps 3-8 of comparison_two_domain (usc data, soft_pen_kappa_exists pinning, two_domain_gap); Relative_Arbitrage/Comparison_Principle.thy:1538 comparison_soft_off_diagonal (70) + :1475/:1324 comparison_from_localised_maximiser_soft/_gen (49+136); Relative_Arbitrage/Comparison_Principle.thy:1617 comparison_2dom_off_diagonal (107); Relative_Arbitrage/Comparison_Principle.thy:1808 comparison_soft_complete vs Comparison_Two_Domain.thy:502-537 branch split

The paper proves (a) and (b) 'in parallel' with one maximiser. The formalisation has two localisation proofs for the same purpose: keeping the soft_pen-doubled sup-convolution maximiser away from the boundary with a small attainment radius. Both off-diagonal theorems repeat the same parameter threading: c = norm (soft_grad κP (xh−yh)), R = κg/4, soft_rho_exists, soft_rsmall_of_rho, glb by reflexivity, atu/atw via supconv_attain_radius + supconv_radius_uniform, KGnn. Both then call comparison_supconv_maximiser_complete_gen with an identical instantiation block. The diagonal branch is likewise threaded twice: CP:1856-1893 and CT:514-536.

Evidence: CP:1565-1577 'define c where "c = norm (soft_grad κP (xh - yh))" ... obtain ρ ... using soft_rho_exists[OF dne Bpos] ... soft_rsmall_of_rho' vs CP:1645-1661 the same lines. CP:1509-1519 and CP:1710-1720 both: 'Pn = "soft_pen κP" and Gf = "soft_grad κP" and Zf = "soft_hess κP" and KZ = "2*κP" and KG = "3*κP" ... soft_pen_semiconcave[OF ..] soft_pen_jet_field soft_hess_sym soft_hess_bound[OF ..] soft_grad_lipschitz[OF ..]'.

Suggested action: Prove one 'localised doubled maximiser' lemma for usc/lsc data over UNIV × K' (from CT steps 1-8), one off-diagonal closing lemma and one diagonal lemma. Derive 4.2(a) (K' = K, using the paper's argument that the maximiser lies in the interior) and 4.2(b) from them. This deletes doubling_localised_maximiser_soft, supconv_uniform_upper, supconv_sandwich, comparison_from_localised_maximiser_soft/_gen, comparison_soft_off_diagonal and comparison_soft_complete.


### RA-comparison-12. Envelope-limit facts proved for ell_op and several times over

*clone, impact medium, confidence medium, ~250 lines.*  
Locations: Relative_Arbitrage/Comparison_Localisation.thy:514 ell_op_lsc_le_of_nearby, :539 ell_op_usc_ge_of_nearby; Relative_Arbitrage/Operator_Envelopes.thy:89 ell_op_usc_ge_one_limit; Relative_Arbitrage/Comparison_Strictness.thy:953 ell_op_lsc_le_of_shifts, :1013 ell_op_usc_ge_of_shifts; Relative_Arbitrage/Comparison_Strictness.thy:649 ell_op_lsc_elliptic_le, :680 ell_op_usc_envelope_elliptic_le; Relative_Arbitrage/Comparison_Strictness.thy:281-298 inline sequence argument in visc_supersol_env_imp_jet

'c ≤ F at points arbitrarily close to z ⟹ c ≤ F^*(z)' appears as ell_op_usc_ge_one_limit (sequence form, c = 1) and as ell_op_usc_ge_of_nearby (ε form, any c). The _of_shifts pair (119 lines) are special cases of _of_nearby with (p, M ± dI) as the nearby point. Envelope ellipticity is a general fact about envelopes of a function antitone in M. None of this depends on ell_op; it holds for the INF/SUP-over-balls envelope of any ereal-valued function on a metric space. Note also ell_op_usc_off_zero (OEC:402, needs transpose M = M) vs ell_op_usc_eq_at_nonzero (OE:1143, no symmetry): CS:743 uses the weaker one.

Evidence: OE:89 'assumes ge: "⋀j. 1 ≤ ell_op_usc k L (ps j) (Ms j)" and lim: "(λj. (ps j, Ms j)) ⟶ (p0, M0)"'; CL:541 'assumes b: "⋀e. 0 < e ⟹ ∃p' M'. dist ((p', M')) (p, M) < e ∧ c ≤ ell_op k L p' M'"'. CS:987-1003 computes 'dist ((p, M + d *R mat 1)) (p, M) = d * N' to produce a nearby point.

Suggested action: Prove the generic envelope facts once, for the ball envelope of an arbitrary f : 'a::metric_space ⇒ ereal (in Semicontinuous_Analysis or the SOVA generic layer), and derive ell_op_usc_ge_one_limit and the _of_nearby lemmas as instances. Delete the _of_shifts and _elliptic_le lemmas, which are dead.


### RA-comparison-13. The operator and comparison layers are probability-free yet are built after the whole probabilistic stack

*build_time, impact medium, confidence medium, ~12000 lines.*  
Locations: Relative_Arbitrage/ROOT (session Relative_Arbitrage = Continuous_Path_Spaces); Relative_Arbitrage/Comparison_Jets.thy:5-9 imports; Relative_Arbitrage/Comparison_Two_Domain.thy:5-7 (redundant DoV, Matrix_Algebra); Second_Order_Viscosity_Analysis/Crandall_Ishii_Sums.thy:5 (DoV already imports Theorem_On_Sums); Relative_Arbitrage/Value_Function_Uniqueness.thy:5-9

The chain Curvature_Operator → Viscosity_Definitions → Viscosity_Ball → Constraint_Set_Convexity → Viscosity_Comparison_Interface → Ball_Solution → Operator_Envelopes → Operator_* → Comparison_* imports only Symmetric_Matrix_Spectra, Semicontinuous_Analysis and SOVA. The single exception is CTM.Integrability_Criteria, imported for cInf_mult_pos. Yet it lives in a session whose parent is Continuous_Path_Spaces, so its roughly 12000 lines start only after CTM, CPS and Wiener_Measure, and the Comparison_* chain itself is strictly linear (Jets → Strictness → Localisation → Principle → Two_Domain). The 4.2(a) branch (CP:1276-2125) is upstream of Comparison_Two_Domain only because of the file order.

Evidence: Imports listed via awk: Operator_Envelopes imports Ball_Solution, Householder_Rotation, Semicontinuity, Semicontinuous_Envelopes, Integrability_Criteria, Doubling_Of_Variables, Matrix_Algebra; Ball_Solution → Viscosity_Comparison_Interface → Constraint_Set_Convexity/Viscosity_Ball → Curvature_Operator → SMS only.

Suggested action: After removing the cInf_mult_pos dependency, make the operator and comparison layers a session of their own, e.g. 'Relative_Arbitrage_PDE' on SMS + SA + SOVA, built in parallel with CTM/CPS/WM; Relative_Arbitrage then lists both. Within it, put 4.2(a) in a leaf theory beside the two-domain chain. Clean the redundant imports.


### RA-comparison-14. Scaling/homogeneity lemmas of F re-proved in the comparison layer

*clone, impact low, confidence high, ~130 lines.*  
Locations: Relative_Arbitrage/Comparison_Strictness.thy:431 feasible_scaleR_p ≡ Relative_Arbitrage/Operator_Envelopes.thy:808 feasible_scale; Relative_Arbitrage/Comparison_Strictness.thy:474 ell_op_scaleR_p ⊇ Relative_Arbitrage/Operator_Envelopes.thy:1201 ell_op_scale; Relative_Arbitrage/Comparison_Strictness.thy:454 ell_op_scaleR_matrix ≡ Relative_Arbitrage/Viscosity_Comparison_Interface.thy:85 ell_op_dilation; Relative_Arbitrage/Comparison_Strictness.thy:492 visc_subsol_scaled_strict vs :1109 visc_subsol_scaled_uniform

feasible_scaleR_p and feasible_scale have the same statement ('θ ≠ 0' / 'c ≠ 0') and the same proof. ell_op_scaleR_matrix and ell_op_dilation have identical statements; ell_op_dilation also re-proves cInf_mult_pos inline. visc_subsol_scaled_strict repeats visc_subsol_scaled_uniform's 35-line proof line for line, only to conclude '< 1' from '≤ θ'. These are operator facts and belong in the operator layer (Curvature_Operator/Operator_Formula), not in Comparison_Strictness.

Evidence: CS:434 'shows "feasible k L (θ *R p) = feasible k L p"' vs OE:810 'shows "feasible k L (c *R q) = feasible k L q"'; CS:457 'shows "ell_op k L p (θ *R M) = θ * ell_op k L p M"' vs VCI:88 'shows "ell_op k L p (c *R M) = c * ell_op k L p M"'; CS:502-529 vs CS:1119-1145 identical up to the last line.

Suggested action: Keep one copy of each, in the operator layer: feasible_scale generalised to c ≠ 0, ell_op_scaleR_p, and ell_op_dilation proved by cInf_mult_pos. Make visc_subsol_scaled_strict a 2-line corollary or delete it (it is dead).


### RA-comparison-15. Small helpers in Crandall_Ishii_Sums re-prove library or lower-session facts

*library_duplicate, impact low, confidence high, ~120 lines.*  
Locations: Second_Order_Viscosity_Analysis/Crandall_Ishii_Sums.thy:125 usc_attains_sup_compact ≈ Semicontinuous_Analysis/Semicontinuity.thy:78 usc_attains_sup_gen; Second_Order_Viscosity_Analysis/Crandall_Ishii_Sums.thy:1763 usc_form_of_continuous ≈ Semicontinuous_Analysis/Semicontinuity.thy:168 usc_eps_of_continuous; Second_Order_Viscosity_Analysis/Crandall_Ishii_Sums.thy:547 tendsto_of_dist_bound ≈ HOL Real_Vector_Spaces.thy:1891 metric_tendsto_imp_tendsto (and DoV:2279 tendsto_of_norm_bound via Lim_null_comparison); Second_Order_Viscosity_Analysis/Crandall_Ishii_Sums.thy:592 add_sq_le_double ≡ Continuous_Time_Martingales/Power_Inequalities.thy:40 square_add_le_two; Second_Order_Viscosity_Analysis/Crandall_Ishii_Sums.thy:568 linear_add_scaleR = linear_compose_add[OF lF linear_scaleR] (HOL Vector_Spaces.thy:644, Real_Vector_Spaces.thy:136); Second_Order_Viscosity_Analysis/Crandall_Ishii_Sums.thy:37 linear_neg_iff (from linear_compose_neg); Second_Order_Viscosity_Analysis/Crandall_Ishii_Sums.thy:438/1438 norm_sq_add_expand / norm_sq_diff_expand ≈ HOL Inner_Product dot_norm / dot_norm_neg

usc_attains_sup_compact and usc_form_of_continuous exist because SOVA cannot see Semicontinuous_Analysis, which sits on HOL-Probability; the CIS text at 106-108 says so. add_sq_le_double exists because Power_Inequalities, which is pure real arithmetic, sits in CTM. The rest are one-liners in HOL.

Evidence: CIS:106 'The session sits on plain HOL-Analysis, so the two attainment facts below are proved here rather than imported from the Semicontinuous_Analysis session'. Power_Inequalities:40 'lemma square_add_le_two: "(a + b)² ≤ 2 * a² + 2 * b²"'.

Suggested action: Replace the HOL-derivable helpers by one-liners. Move the ε-form usc calculus (usc_eps_*, usc/lsc_attains_*_gen) into a HOL-Analysis-level theory that SOVA and Semicontinuous_Analysis can both see, for example SOVA itself, and delete the CIS copies. Move Power_Inequalities' pure-HOL lemmas to the lowest session.


### RA-comparison-16. Comparison_Jets is an empty husk: three copies of one text block and an empty subsection

*misplacement, impact low, confidence high, ~48 lines.*  
Locations: Relative_Arbitrage/Comparison_Jets.thy:1-48

The theory contains no definition or lemma. Its text appears three times (lines 14-19, 21-26, 28-33), followed by 'subsection ‹A jet gives a test function›' and 10 blank lines. The text claims the theory 'states Definition 3.1 with the paper's own C² test functions' and 'discharge[s] max_principle_boundary'; that material now lives in Viscosity_Definitions, Test_Functions and Comparison_Principle. Its six imports exist only to be inherited by Comparison_Strictness. One of them, Continuous_Time_Martingales.Integrability_Criteria, is needed only for cInf_mult_pos, a pure order lemma that is an instance of HOL's continuous_at_Inf_mono (Topological_Spaces.thy:3374).

Evidence: Comparison_Jets.thy:35 'subsection ‹A jet gives a test function›' followed by lines 36-45 empty, then '(*<*) end'. PLAN_RESTRUCTURING_2.md:542 still describes it as holding 'the jet interface, Definition 3.1 with genuine C2 test functions'.

Suggested action: Delete the theory. Let Comparison_Strictness import Operator_Envelope_Continuity, which already pulls in DoV, Semicontinuity, Matrix_Algebra and Integrability_Criteria. Move cInf_mult_pos next to ell_op or replace it by continuous_at_Inf_mono, so that the operator and comparison layers no longer depend on CTM.


### RA-comparison-17. Malformed source lines left by mechanical edits

*documentation, impact low, confidence high, ~10 lines.*  
Locations: Relative_Arbitrage/Comparison_Localisation.thy:655; Relative_Arbitrage/Comparison_Localisation.thy:668; Relative_Arbitrage/Comparison_Localisation.thy:907; Relative_Arbitrage/Comparison_Localisation.thy:1709; Relative_Arbitrage/Comparison_Principle.thy:78; Relative_Arbitrage/Value_Function_Uniqueness.thy:538; Relative_Arbitrage/Comparison_Strictness.thy:16

Two Isar commands share a line ('... (use ux in linarith)  have ey: ...', '... by simp  have cnorm: ...', '... by blast  have dzle: ...', '... by (rule order_trans)  qed'). A statement's closing quote runs into 'proof -' (CL:907). A subsection header is duplicated on one line (CL:668 'subsection ‹Symmetry and the ordering pass to the limit›subsection ‹Symmetry ...›'). CS:16 uses 'section' where 'subsection' is meant, creating a second top-level section inside the theory.

Evidence: See the quoted lines; found by grep for two commands per line.

Suggested action: Reformat these lines. Add a lint step (one command per line, no duplicate headers) to the move tooling in notes/restructuring_2.


### RA-comparison-18. Value_Function_Uniqueness repeats the horizon selection 8 times and the gate collapse 3 times

*simplification, impact low, confidence high, ~120 lines.*  
Locations: Relative_Arbitrage/Value_Function_Uniqueness.thy:569, 591, 624, 644, 668, 688, 763, 873 (obtain rK, obtain T via nonbinding_horizon_ex, eq via iexit_val_eq_exit_val_ball); Relative_Arbitrage/Value_Function_Uniqueness.thy:212-230 (exit_val_supersol_bc), 736-753 (exit_val_supersol_bc_K), 797-814 (iexit_val_supersol_lsc_K); Relative_Arbitrage/Value_Function_Uniqueness.thy:123 exit_val_real_nonneg

Every iexit_val clause opens with the same 8-10 lines: closed K, compact_cball_bound, nonbinding_horizon_ex, and 'have eq: iexit_val k L K y = exit_val k L T K y'. The proof 'interior K ∪ {x ∈ K − interior K. f x < 0} = interior K for f ≥ 0' is written out three times at about 18 lines each. exit_val_real_nonneg is a wrapper of the HOL simp lemma enn2real_nonneg (Extended_Nonnegative_Real.thy:1023).

Evidence: VFU:650-656 and VFU:676-682 are identical blocks: 'obtain rK ... using compact_cball_bound[OF cK] ... obtain T ... using nonbinding_horizon_ex[OF kn] ... have eq: "iexit_val k L K y = exit_val k L T K y" for y by (rule iexit_val_eq_exit_val_ball[OF kn L Kc KB T1])'.

Suggested action: Add 'iexit_val_eq_exit_val_large: compact K ⟹ obtains T rK. 0 < T ∧ 2rK²/(n−k) < T ∧ K ⊆ cball 0 rK ∧ (∀y. iexit_val k L K y = exit_val k L T K y)' and a gate-collapse lemma for nonnegative functions. Use enn2real_nonneg directly.


### RA-comparison-19. Hand-made bounds and limits in the 4.2(a) and 4.3 proofs

*simplification, impact low, confidence high, ~60 lines.*  
Locations: Relative_Arbitrage/Comparison_Principle.thy:1919-1950 vs 1988-1991 (max_principle_boundary_holds); Relative_Arbitrage/Comparison_Two_Domain.thy:689-715 (comparison_expandable: lim, cslim); Relative_Arbitrage/Comparison_Strictness.thy:281-298 (visc_supersol_env_imp_jet)

max_principle_boundary_holds derives upper and lower bounds for u and w on K by hand from compact_continuous_image + bounded_iff (30 lines). Twenty lines later it derives them again with bounded_on_compact. comparison_expandable proves 'zs ⟶ x' and 'cs ⟶ 1' by explicit metric_LIMSEQ_I/N-arguments where tendsto_sandwich or Lim_null_comparison give one-liners. visc_supersol_env_imp_jet builds the sequence es j = 1/Suc j to apply ell_op_usc_ge_one_limit, where the ε-form nearby lemma would do.

Evidence: CP:1937-1950 'obtain Bu where Bu: "⋀y. y ∈ K ⟹ u y ≤ Bu" proof - have "bounded (u ` K)" by (rule compact_imp_bounded[OF compact_continuous_image[OF cu cK]]) ...' and CP:1988 'obtain Bu where Bu0: "0 ≤ Bu" and BuK: "⋀y. y ∈ K ⟹ ¦u y¦ ≤ Bu" using bounded_on_compact[OF cK cu] by blast'.

Suggested action: Use bounded_on_compact once, tendsto_sandwich/Lim_null_comparison in CT, and the nearby-point lemma in CS.


### RA-comparison-20. Redundant hypotheses in the comparison and uniqueness statements

*generalisation, impact low, confidence medium, ~20 lines.*  
Locations: Relative_Arbitrage/Comparison_Two_Domain.thy:200 comparison_two_domain (neK); Relative_Arbitrage/Comparison_Two_Domain.thy:553, 769 (neK; also passed down); Relative_Arbitrage/Value_Function_Uniqueness.thy:248-249 theorem_1_1_uniqueness_faithful (neK, r0); Relative_Arbitrage/Value_Function_Uniqueness.thy:691, 824 iexit_val_uniqueness(_K) (neK) and Statement/Statement_Auxiliary.thy:93 clause_4_uniqueness; Relative_Arbitrage/Comparison_Localisation.thy:1468 doubling_localised_maximiser_soft (neK with zK ∈ K); Relative_Arbitrage/Comparison_Principle.thy:1346-1347 comparison_from_localised_maximiser_gen (cu, cw used only to get usc at 1417-1426)

comparison_two_domain declares 'neK: "K ≠ {}"' but never uses it, and its conclusion is about a given 'x ∈ K'. Every caller up to the Statement's clause_4_uniqueness, which also assumes 'x ∈ K', therefore carries 'K ≠ {}' needlessly. In supersol_bc_nonneg neK can be obtained from the point inside the proof. rK ≥ 0 follows from K ⊆ cball 0 rK and K ≠ {}. comparison_from_localised_maximiser_gen assumes continuity only to derive the usc ε-form that its consumer _gen takes directly.

Evidence: awk over CT:197-538 finds 'neK' only in the assumption line 200.

Suggested action: Drop neK where an x ∈ K is given (it is displayed in the Statement, so re-check Statement after the change). Replace cu/cw by usc hypotheses in comparison_from_localised_maximiser_gen if that theorem survives.


### RA-comparison-21. Value_Function_Uniqueness mixes three subjects; Example 3.1 does not belong in a uniqueness theory

*misplacement, impact low, confidence medium, ~400 lines.*  
Locations: Relative_Arbitrage/Value_Function_Uniqueness.thy:291-554 (exit_val_ball_fin, exit_val_ball_upper, example_3_1_from_lower 132 lines, example_3_1 80 lines); Relative_Arbitrage/Value_Function_Uniqueness.thy:556-887 (iexit_val_* clauses, horizon removal); Relative_Arbitrage/Value_Function_Uniqueness.thy:22-100 (theorem_1_1_ball_fragment, theorem_1_1_uniqueness_general: dead)

The theory holds three things: (i) the uniqueness clause, about 150 lines; (ii) Example 3.1, about 300 lines, which uses only exit_val bounds, exit_val_usc_unconditional and exit_val_ball_lower_sharp, not the comparison principle; (iii) the transfer of all clauses from finite horizon to iexit_val, about 330 lines. Only (i) needs Comparison_Two_Domain. (ii) and (iii) wait on the whole comparison chain for no reason, which serialises the build.

Evidence: example_3_1_from_lower and example_3_1 use exit_val_le_ball_bound, exit_val_boundary_zero, exit_val_zero_outside, exit_val_usc_unconditional and exit_val_ball_lower_sharp; none of these is a Comparison_* lemma.

Suggested action: Split it into Example_3_1.thy (imports Value_Function_Assembly and Exit_Class_Witness), Value_Function_Uniqueness.thy (theorem_1_1_uniqueness_faithful, exit_val_supersol_bc(_K)) and Theorem_1_1_Assembly.thy (the iexit_val clauses), the last importing the other two. Delete the dead ball fragment.


## RA-infinite+Statement

This cluster carries the last step from the internal objects to the paper's own statement, plus the final statement itself.

Relative_Arbitrage/Exit_Class_Infinite.thy (837 lines) defines the class on the half-line, iexit_class k L x. Its members are laws of the pair (X,<X>) on C([0,inf)) with the covariation constraint at every pair of times and no stopping. It also defines iexit_val as Sup of ess_inf of iexit. The theory then identifies this value with the capped value exit_val k L T K x once the horizon is long enough:
- Cutting a half-line member gives a capped member (iexit_class_pcut), so min(iexit_val,T) <= exit_val (iexit_val_cap_le).
- Conversely, every capped law Q has a half-line extension iextend T Q. It glues an independent half-line Brownian pair law ibm_law onto Q at T. It lies in iexit_class (iextend_in_iexit_class) and cuts back to Q (pcut_law_iextend).
- The a priori ball bound then removes the horizon hypothesis (iexit_val_eq_exit_val_ball).

Relative_Arbitrage/Exit_Class_Marginals.thy (1340 lines) defines the paper's class xclass k L x. Its members are laws of X alone, with an existential compensator A satisfying density_cond, i.e. absolutely continuous with a.e. derivative in sconstraint. It also defines xval. The theory proves:
- that the density form is the same as the difference-quotient form (xclass_eq_dq);
- that the second coordinate of a pair-class member equals the adapted QV functional qvmata (4L) (iexit_class_qvmat), and likewise for a P_x compensator (xclass_qvmata);
- both inclusions: the X-marginal of a pair law is in P_x, and the lift w |-> (w, qvmata w) of a P_x law is in the pair class;
- iexit_val = xval (iexit_val_eq_xval).

Statement/:
- Statement_Auxiliary (document=false) is 13 one-line re-exports plus the five-conjunct assembly theorem_1_1_iexit.
- Theorem_1_1_Statement displays the definitions and states theorem_1_1 for xval, plus Example 3.1.
- Paper_Readings checks the envelope reading and the expandability reading.

Faithfulness verdict: the definitions reachable from theorem_1_1 match Eq. (1.5)-(1.9), Definition 3.1 and Theorem 1.1, given three choices: orthogonal P in Pi_m, the envelope taken within K, and absolute continuity of <X> on compacts. But the headline formula assumes `expandable K` and `K ~= {}` for all five clauses. The paper assumes the T_iota family only for uniqueness, and needs no nonemptiness at all. Much of the prose is stale or wrong:
- The claim that the literal (non-orthogonal) reading of Pi_m makes S and every P_x empty is false. The identity matrix is in the literal S; this was checked in Isabelle.
- The xclass prose still describes the old difference-quotient definition.
- density_cond_def is not displayed in the statement.
- Several pointers name theories or lemmas that no longer exist.

Structurally, the paper session has no theory stating Theorem 1.1. The assembly sits in a hidden auxiliary theory of the Statement session. Exit_Class_Infinite imports the whole dynamic-programming stack without using any of it. The Marginals theory proves its two central arguments twice each: the QV identification, and the rational-pair measurability.


### RA-infinite+Statement-1. theorem_1_1 assumes `expandable K` and `K ~= {}` for all five clauses; the paper assumes the T_iota family only for uniqueness and needs no nonemptiness

*faithfulness, impact high, confidence high, ~25 lines.*  
Locations: Statement/Theorem_1_1_Statement.thy:134-137 theorem_1_1; Statement/Statement_Auxiliary.thy:107-111 theorem_1_1_iexit; Statement/theorem_1_1_unfolded.html:664-665 and 1476

Theorem 1.1 states existence (bounded usc viscosity solution) for every compact K and adds the T_iota hypothesis only for uniqueness ('Suppose, in addition, ...'). The formal headline is `assumes kn L1 k1 cK and neK: "K ~= {}" and expK: "expandable K"` followed by a single five-way conjunction, so clauses (0)-(3) are formally asserted only for nonempty expandable K. The clause lemmas need neither hypothesis (clause_0_finite .. clause_3_boundary_supersolution have only kn, L1, (k1), cK). K ~= {} is not needed even for uniqueness, because the conclusion `\<forall>x\<in>K. u x = v x` is vacuous for K = {}. The HTML claims 'K ~= emptyset is required only by the uniqueness argument' and lists the hypothesis as 'nonempty, for uniqueness', which the formula contradicts.

Evidence: Theorem_1_1_Statement.thy:136-137 `assumes kn: "k < CARD('n)" and L1: "1 \<le> L" and k1: "1 \<le> k" and cK: "compact K" and neK: "K \<noteq> {}" and expK: "expandable K"`; Statement_Auxiliary.thy:54-89 (clause_1..clause_3 lemmas have no neK/expK); paper line 232ff 'Suppose, in addition, that there are T_iota ... Then, the ... solution ... is unique.'

Suggested action: Drop neK (case-split K = {} inside the proof). Move expandability into conjunct 4: `\<and> (expandable K \<longrightarrow> (\<forall>u Bd. ...))`. Alternatively state two theorems (existence for compact K; uniqueness with expandable K). Update the prose at lines 125-130 and the HTML accordingly.


### RA-infinite+Statement-2. False claim: under the literal (non-orthogonal P) reading of Pi_m, 'S and every P_x would be empty'; the identity is in the literal S

*documentation, impact high, confidence high, ~15 lines.*  
Locations: Statement/Theorem_1_1_Statement.thy:47-53; Statement/theorem_1_1_unfolded.html:1428-1442 (FLAGS.orthogonality)

The prose argues that with P^2=P, tr P=m (P not necessarily symmetric) the infimum is unbounded below, 'so S and every P_x would be empty whenever k <= n-2'. That is false. For a = cI, tr(aP) = c*tr P = cm for every idempotent P of trace m, so Pi_m(cI) = cm. Only non-scalar a get Pi_m = -inf; the example u u^T with u = (1,0,1) is one of those. The literal S is therefore {cI : 1-k/n <= c <= L} (for k <= n-2). It contains I because L >= 1, and P_x contains standard Brownian motion. What the literal reading actually breaks is Lemma 2.1 and the class. For example, diag(1,..,1,0) has lambda_(n-k) = 1 and is psd, but it is not in the literal S. So the convex-hull identity fails and P_x shrinks to isotropic covariations. Checked in Isabelle (PIDE scratch over Complex_Main, matrices as 'n => 'n => real): `lemma Pi_literal_id: (\<exists>P. mmul P P = P \<and> tr P = real m) \<Longrightarrow> Pi_literal idm m = real m` and `corollary identity_in_literal_S: ... \<forall>m. k < m \<longrightarrow> real (m - k) \<le> Pi_literal idm m` both check without errors.

Evidence: Theorem_1_1_Statement.thy:49-50 'Read literally the infimum is unbounded below, so \<open>S\<close> and every \<open>P\<^sub>x\<close> would be empty whenever \<open>k \<le> n - 2\<close>'; HTML 1432-1433 same; Isabelle scratch tmp_pide_mcp_scratch_literal_pi_identity.thy (0 errors).

Suggested action: Rewrite: under the literal reading Pi_m(a) = -inf for every non-scalar a and m in (k,n), so S collapses to {cI : 1-k/n <= c <= L}. Lemma 2.1 then fails and v changes, so the orthogonal reading is the intended one. Better still, add this as a machine-checked section in Paper_Readings (literal Pi, mat 1 in it, diag(1,..,1,0) not in it).


### RA-infinite+Statement-3. The paper session never states Theorem 1.1; the assembly lives in a hidden Statement theory made of one-line re-exports, seven of which are dead

*structure, impact high, confidence high, ~200 lines.*  
Locations: Statement/Statement_Auxiliary.thy:15-193; Statement/ROOT ('theories [document = false] Statement_Auxiliary'); Relative_Arbitrage/Value_Function_Uniqueness.thy:556-900 (section 'The clauses for the value function of Eq. (1.6)')

Statement_Auxiliary consists of renamings: paper_value_function_agrees = iexit_val_eq_xval, paper_class_marginal, paper_class_lift, convex_sets_are_expandable, clause_0_finite, clause_0_not_infinite, clause_1_upper_semicontinuous, clause_2_subsolution, clause_2_supersolution, clause_3_*, clause_4_uniqueness, example_3_1_iexit. Each has the form `by (rule X[OF assms])`. The other content is the assembly theorem_1_1_iexit, whose formula and comments duplicate theorem_1_1 almost verbatim. Seven of them are referenced nowhere: paper_value_function_agrees, paper_class_marginal, paper_class_lift, convex_sets_are_expandable, clause_0_not_infinite, clause_2_subsolution and clause_2_supersolution. Their sources iexit_val_neq_top, iexit_val_visc_subsol and iexit_val_supersol_lsc_K (Value_Function_Uniqueness) are used only by them. Because the theory is document=false, the non-vacuity theorem that the statement prose relies on ('Every compact convex set with nonempty interior is expandable') is invisible. The iexit_val clause lemmas sit in Value_Function_Uniqueness, which therefore has to import Exit_Class_Infinite. So the final step is spread over three theories in two sessions.

Evidence: grep -rnw for each name: only definition sites (plus notes); Statement/ROOT lists Statement_Auxiliary with document=false; OPEN_ITEMS.md:42-44 still claims Theorem_1_1_Statement states these three theorems.

Suggested action: Create Relative_Arbitrage/Theorem_1_1.thy as the session's last theory (imports Value_Function_Uniqueness and Exit_Class_Marginals). Move into it the iexit_val clause section of Value_Function_Uniqueness, the assembly stated directly for xval, example 3.1 for xval, and convex_expandable as a corollary. Delete Statement_Auxiliary. Theorem_1_1_Statement then restates by `by (rule Theorem_1_1.theorem_1_1)` and displays the non-vacuity corollary. Delete the dead re-exports.


### RA-infinite+Statement-4. iexit_class_qvmat and xclass_qvmata are the same 150-line argument; make one generic AE lemma next to qvmat_eq_A_localised

*clone, impact high, confidence high, ~150 lines.*  
Locations: Relative_Arbitrage/Exit_Class_Marginals.thy:187-337 iexit_class_qvmat; Relative_Arbitrage/Exit_Class_Marginals.thy:706-855 xclass_qvmata; Relative_Arbitrage/Exit_Class_Marginals.thy:112-175 diffquot_psd/diffquot_entry/diffquot_sym

Both proofs follow the same steps line by line, only with X = fst o omega, A = snd o omega in one and X = w, A = A t w in the other:
- AE_E null sets N1,N2(,N3), G = space - union, Gfull, Gstart, Gdq;
- restrict_space to G; Xc via martingale_restrict_full and martingale_vec_nth; XAc via martingale_mat_nth;
- contc, A0c, psdc via diffquot_psd, ratec via diffquot_entry, X0c;
- `qvmat_eq_A_localised[where C = L and B = norm x]`;
- symmetrise with diffquot_sym; qvmata_eq_qvmat; AE_restrict_space_iff back to the full space.
diffquot_psd/entry/sym use only that S is contained in psd matrices with entries bounded by L.

Evidence: Side-by-side: lines 203-227 vs 725-756 (null sets), 231-278 vs 758-802, 280-303 vs 804-826, 305-336 vs 827-854.

Suggested action: State `qvmata_eq_compensator_AE` once, for a prob_space M, filtration F, X with continuous paths on space M and martingale components, outerp X - A a martingale, AE A 0 = 0, AE \<forall>s<t. dq(A) \<in> S with S \<subseteq> {psd} and a uniform entry bound C, and AE |X 0 $ i| <= B. Conclusion: AE \<forall>t\<ge>0. qvmata (4*C) X t = A t. Put it in Continuous_Path_Spaces.Adapted_Quadratic_Variation together with qvmat_eq_A_localised. The two current lemmas become about 10-line instances.


### RA-infinite+Statement-5. Prose about xclass not updated after the switch to density_cond (commit 614ecf8): 'all difference quotients', 'continuous adapted A', 'verbatim'

*documentation, impact medium, confidence high, ~40 lines.*  
Locations: Statement/Theorem_1_1_Statement.thy:55-59; Statement/Theorem_1_1_Statement.thy:63-69; Relative_Arbitrage/Exit_Class_Marginals.thy:19-24; notes/NOTES_FOR_AUTHORS.md:167,169-172,187-190; Statement/theorem_1_1_unfolded.html:966-970

xclass_def now ends in `(AE w in Q. density_cond (\<lambda>t. A t w) (sconstraint k L))`. That is absolute continuity on compacts with the a.e. derivative in S. Commit 614ecf8 touched only Covariation_Density, Exit_Class_Marginals and ROOT. The statement still says 'some continuous adapted A compensates X X^T with all difference quotients in S_k^L' (57). The whole paragraph 63-69 still says 'above, every difference quotient lies in S ... They part only if <X> has a singular part ... such a part only makes X exit sooner, so the value function is unaffected'. That last sentence is an unproved claim, and is now moot because density_cond excludes singular parts. Exit_Class_Marginals' header still says the inclusions 'fall out of qvmat_eq_A_sym'. That lemma is used nowhere; the proofs go through qvmat_eq_A_localised. NOTES calls the formal class 'your class verbatim' with 'the covariation constraint at every pair of times'.

Evidence: git show 614ecf8 --stat: 3 files (Covariation_Density, Exit_Class_Marginals, ROOT); grep -rnw qvmat_eq_A_sym: only Pathwise_Quadratic_Variation.thy:1054 (definition) and the prose at Exit_Class_Marginals.thy:23.

Suggested action: Rewrite 55-69 to describe density_cond. Record 'absolute continuity of <X> is how d<X>/dt is read' as an explicit reading, and drop the unproved 'exit sooner' remark or prove it. Fix the Marginals header (qvmat_eq_A_localised), NOTES 167-190 and the HTML gloss.


### RA-infinite+Statement-6. density_cond_def is not displayed in the statement document although xclass_def uses it

*faithfulness, impact medium, confidence high, ~5 lines.*  
Locations: Statement/Theorem_1_1_Statement.thy:61; Statement/document/root.tex abstract; Statement/ROOT description

The statement shows `ipath_def ipath_gen_def ipath_space_def outerp_def xclass_def`. xclass_def refers to density_cond, defined in Relative_Arbitrage/Covariation_Density.thy:182, which is not shown anywhere. The constraint of Eq. (1.7) itself is therefore invisible to a reader of the PDF. This contradicts root.tex ('together with every definition specific to the paper that its statement mentions') and the ROOT description.

Evidence: grep density_cond Statement/Theorem_1_1_Statement.thy -> no hit; xclass_def line 47 `density_cond (\<lambda>t. A t w) (sconstraint k L)`.

Suggested action: Add `@{thm [display] density_cond_def}` with a sentence on the absolute-continuity reading. Consider adding a check that every constant in the statement's displayed definitions is itself displayed or comes from a library.


### RA-infinite+Statement-7. Clause (0) comment in theorem_1_1_iexit is wrong (|enn2real v| <= B does not imply finiteness), and the two theorems state clause (0) differently

*documentation, impact medium, confidence high, ~20 lines.*  
Locations: Statement/Statement_Auxiliary.thy:112-115; Statement/Theorem_1_1_Statement.thy:139-143,177-188; Relative_Arbitrage/Value_Function_Uniqueness.thy:594-598

theorem_1_1_iexit states `\<exists>B. \<forall>y. \<bar>v y\<bar> \<le> B` with the comment 'Read through enn2real, so this also says the value is finite'. Both Theorem_1_1_Statement (140-143) and Value_Function_Uniqueness (594-598) correctly say the opposite: enn2real sends top to 0, so the bound holds vacuously at top. Because the forms differ, theorem_1_1 has to re-derive the ennreal bound from clause_0_finite and compact_cball_bound (lines 177-188) instead of merely rewriting with iexit_val_eq_xval.

Evidence: Statement_Auxiliary.thy:113 '\<comment> \<open>clause (0): finiteness.  Read through \<^const>\<open>enn2real\<close>, so this also says the value is finite'; Theorem_1_1_Statement.thy:142 'Bounding \<open>v\<close> instead would not, \<^const>\<open>enn2real\<close> sending \<open>\<top>\<close> to \<open>0\<close>.'

Suggested action: State clause (0) of the internal theorem as `\<exists>B::real. \<forall>y. iexit_val k L K y \<le> ennreal B`, which follows from iexit_val_le_ball_bound. Delete the wrong comment, and derive theorem_1_1 by `unfolding iexit_val_eq_xval`.


### RA-infinite+Statement-8. The non-binding-horizon preamble is repeated eight times in Value_Function_Uniqueness

*clone, impact medium, confidence high, ~60 lines.*  
Locations: Relative_Arbitrage/Value_Function_Uniqueness.thy:573-580,595-602,629-637,649-656,675-682,703-710,773-780,878-883; Relative_Arbitrage/Exit_Class_Infinite.thy:818 iexit_val_eq_exit_val_ball; Relative_Arbitrage/Pair_Path_Laws.thy:241 nonbinding_horizon_ex

Every iexit_val clause lemma opens with the same lines: `obtain rK ... using compact_cball_bound`, `obtain T where T0: 0 < T and T1: rK*rK/real(CARD('n)-k) < T using nonbinding_horizon_ex[OF kn]`, `have eq: iexit_val k L K y = exit_val k L T K y by (rule iexit_val_eq_exit_val_ball[OF kn L Kc KB T1])`. nonbinding_horizon_ex is a trivial gt_ex instance carrying paper constants. It sits in the path-toolkit theory Pair_Path_Laws, followed by the text '\<^bold>\<open>Clause (0): finiteness.\<close>'.

Evidence: grep -rn nonbinding_horizon_ex: 8 call sites in Value_Function_Uniqueness, each followed by iexit_val_eq_exit_val_ball.

Suggested action: Add to Exit_Class_Infinite `corollary iexit_val_eq_exit_val_compact: k < CARD('n) \<Longrightarrow> 1 \<le> L \<Longrightarrow> compact K \<Longrightarrow> \<exists>T>0. iexit_val k L K = exit_val k L T K` (as functions). Use it in all eight places, and inline or delete nonbinding_horizon_ex.


### RA-infinite+Statement-9. Entrywise modification detour (martingale_of_modification_gen + martingale_matI) re-derives martingale_cong_AE

*library_duplicate, impact medium, confidence high, ~90 lines.*  
Locations: Relative_Arbitrage/Exit_Class_Marginals.thy:490-555 (mgcomp in iexit_class_marginal_in_xclass); Relative_Arbitrage/Exit_Class_Marginals.thy:1116-1171 (mgcomp in xclass_lift_in_iexit_class); notes/OPEN_ITEMS.md:111-115

Both blocks show that `outerp X - qvmata C X` is a martingale because it is a.e. equal, for each t, to the compensated martingale of the class. They do it entrywise: martingale_matI, then martingale_of_modification_gen with X = X' (hence the trivial obligation `AE \<omega> in P. \<omega> u = \<omega> u`), real-valued only. Continuous_Time_Martingales/Martingale_Algebra.thy:152 `martingale_cong_AE` already states exactly this for any filtration and any {banach,second_countable_topology}-valued process: martingale M F 0 X, adapted Y, \<forall>i\<ge>0. AE X i = Y i, conclusion martingale M F 0 Y.

Evidence: martingale_cong_AE: `assumes mg: martingale M F 0 X and adap: adapted_process M F 0 Y and eq: \<And>i. 0 \<le> i \<Longrightarrow> AE \<omega> in M. X i \<omega> = Y i \<omega> shows martingale M F 0 Y` (matrix-valued Y is allowed).

Suggested action: Replace each block by `martingale_cong_AE[OF mgXA]` plus the matrix-valued adaptedness and the AE equality (about 15 lines each). Correct OPEN_ITEMS 111-115.


### RA-infinite+Statement-10. Rational-pair measurability of the difference-quotient event proved twice; inline pushforward-measurability proofs duplicate lemmas later in the same file

*clone, impact medium, confidence high, ~170 lines.*  
Locations: Relative_Arbitrage/Exit_Class_Marginals.thy:579-659 (equiv + predD inside iexit_class_marginal_in_xclass); Relative_Arbitrage/Exit_Class_Marginals.thy:864-972 pairpath_diffquot_sets; Relative_Arbitrage/Exit_Class_Marginals.thy:373-388 vs 1207-1231 iexit_class_fstify_measurable; Relative_Arbitrage/Exit_Class_Marginals.thy:999-1018 vs 1233-1256 xclass_liftify_measurable

Both blocks prove the same equivalence: 'for all real 0<=s<t, dq in S' iff 'for all rational p<q (as type rat), dq in S'. Each goes through diffquot_all_of_rational and the same 40-line rat/real conversion, then pred_intros_countable plus measurable_sets with closed_sconstraint. They differ only in the continuous functional: qvmata C w in one, snd o omega in the other. Separately, phim and psim inside the two inclusion theorems re-prove iexit_class_fstify_measurable and xclass_liftify_measurable, which are stated about 800 lines further down the same file.

Evidence: Lines 579-623 vs 883-927 identical up to the functional; 624-659 vs 928-971 identical up to the functional.

Suggested action: Add one generic lemma to Continuous_Path_Spaces/Increment_Moments next to diffquot_all_of_rational: closed S, continuous_on {0..} (Y w) on space M, and Y-evaluations measurable imply `Measurable.pred M (\<lambda>w. \<forall>s t. 0\<le>s\<longrightarrow>s<t\<longrightarrow>(1/(t-s)) *\<^sub>R (Y w t - Y w s) \<in> S)`. Quantify over \<rat> directly rather than over type rat. Move the two measurability lemmas before the inclusions and use them there.


### RA-infinite+Statement-11. Covariation_Density is paper-free analysis but lives in Relative_Arbitrage, imports Exit_Class for nothing, and re-proves diffquot_lipschitz

*misplacement, impact medium, confidence high, ~300 lines.*  
Locations: Relative_Arbitrage/Covariation_Density.thy:1-299; Relative_Arbitrage/Covariation_Density.thy:193-221 (lip1/lip in dq_imp_density); Continuous_Path_Spaces/Increment_Moments.thy:2276 diffquot_lipschitz

No statement in Covariation_Density mentions sconstraint, exit_class or any pair type. Everything is at 'a::euclidean_space: lipschitz_imp_absolutely_continuous_on, integral_mean_in_convex(_ae), vector_derivative_in_closed_set, dq_cond, density_cond, dq_iff_density. Yet it imports Exit_Class. Inside dq_imp_density, about 30 lines derive `norm (g u - g v) \<le> M * \<bar>u - v\<bar>` from difference quotients in a bounded S, which is diffquot_lipschitz. Only the prose is paper-specific: Eq. (1.7), Lemma 2.3, 'the paper uses both readings'.

Evidence: grep sconstraint Covariation_Density.thy -> none; only consumer is Exit_Class_Marginals.thy:5.

Suggested action: Move to Continuous_Path_Spaces as a theory importing Increment_Moments (or just HOL-Analysis). Use diffquot_lipschitz in dq_imp_density. Keep the paper commentary in the Marginals or Statement prose.


### RA-infinite+Statement-12. Paper-free QV identifications sit in the paper session's Pair_Path_Space, used only by this cluster; qvmat_eq_A_sym is now unused

*misplacement, impact medium, confidence high, ~700 lines.*  
Locations: Relative_Arbitrage/Pair_Path_Space.thy:237 qvps_eq_A_stopped; Relative_Arbitrage/Pair_Path_Space.thy:483 qvps_eq_A_localised; Relative_Arbitrage/Pair_Path_Space.thy:1035 qvmat_eq_A_localised; Continuous_Path_Spaces/Pathwise_Quadratic_Variation.thy:1054 qvmat_eq_A_sym

These theorems are stated for `X :: real \<Rightarrow> 'a \<Rightarrow> real^'n` (or real), any prob_space M and filtration F. They mention no pair path and no paper constant. They are the localised (unbounded-X) version of the Continuous_Path_Spaces QV identification. qvmat_eq_A_localised is consumed only by Exit_Class_Marginals (lines 285, 809). They also sit under unrelated headings: 'subsection Integrability from the L^2 bound' directly precedes qvmat_eq_A_localised, and a text about '{tau_K(y+.) < d}' directly precedes qvps_eq_A_localised. The bounded version qvmat_eq_A_sym that they supersede is referenced only by stale prose (Exit_Class_Marginals.thy:23).

Evidence: Statements at Pair_Path_Space.thy:237-252, 483-497, 1035-1052; grep -rnw qvmat_eq_A_localised -> only Exit_Class_Marginals.

Suggested action: Move the three theorems and their helpers (etime_shift_* if equally generic) into Continuous_Path_Spaces.Adapted_Quadratic_Variation, together with the AE wrapper proposed above. Delete qvmat_eq_A_sym or keep it as the bounded corollary.


### RA-infinite+Statement-13. Exit_Class_Infinite imports Dynamic_Programming_Assembly but uses nothing from the DP layer, which serialises the end of the build

*build_time, impact medium, confidence high, ~10 lines.*  
Locations: Relative_Arbitrage/Exit_Class_Infinite.thy:5-8; Relative_Arbitrage/Exit_Class_Marginals.thy:5-10; Relative_Arbitrage/ROOT (theory order)

A name scan of every lemma and definition of the Dynamic_Programming_*, Value_Function_*, Comparison_*, Exit_Class_Optimizer and Exit_Time_Semicontinuity theories finds no use in Exit_Class_Infinite or Exit_Class_Marginals. Their actual dependencies:
- Exit_Class_Pasting: exit_class_pglue_law, exit_class_pcut, exit_class_diffquot_of_pairs;
- Exit_Class_Witness: bmpair_law_in_paper_pair_class, exit_val_le_ball_bound;
- Exit_Class_Limits: exit_class_X_martingale;
- the path layer.
Exit_Class_Pasting imports all of these. The other imports of Exit_Class_Marginals are transitively present (Increment_Moments, Essential_Infimum, Path_Exit_Times, Path_Law_Sampling). ROOT lists Value_Function_Uniqueness before Exit_Class_Infinite, although it imports it.

Evidence: Scan of names defined in DP_*/VF_*/Comparison_*/Exit_Class_Optimizer/Exit_Time_Semicontinuity against the two files: only the false positives 'on', 'supplies'.

Suggested action: Import Exit_Class_Pasting (plus the needed library theories) in Exit_Class_Infinite. Place both theories after Exit_Class_Pasting in ROOT, i.e. in the class layer where the ROOT description says Eq. (1.7) is built. Trim the redundant imports.


### RA-infinite+Statement-14. Stale references and false claims in NOTES_FOR_AUTHORS.md, OPEN_ITEMS.md, Statement/ROOT and Essential_Infimum

*documentation, impact medium, confidence high, ~40 lines.*  
Locations: notes/NOTES_FOR_AUTHORS.md:11,141,160,196-198; notes/OPEN_ITEMS.md:24,28,42-44,120-124,151,191,235-236; Statement/ROOT description; Continuous_Time_Martingales/Essential_Infimum.thy:17

NOTES_FOR_AUTHORS.md:
- line 11: 'the single theory Theorem_1_1_Statement.thy'; the session has three theories, one hidden, and density_cond is missing from it.
- line 141: `rotSF_exists` in `Value_Function_Viscosity`; that theory no longer exists; the lemma is at Value_Function_Supersolution_Case_1.thy:273.
- line 160: the formalisation uses a 'finite T'; the statement now uses xval on C([0,inf)), and T is internal.
- lines 196-198: the library sessions are said to have 'none of which mentions this paper'; grep finds 28 .thy files and 91 lines in the six library sessions mentioning LaiShkolnikovSoner, 'Eq. (1.', 'the paper', Theorem 1.1, Definition 3.1, sconstraint or ell_op.
OPEN_ITEMS.md:
- lines 24 and 122-124: `Relative_Arbitrage/Pathwise_Quadratic_Variation.thy`; it is now Continuous_Path_Spaces/{Pathwise,Adapted}_Quadratic_Variation.thy, with the localisation in Relative_Arbitrage/Pair_Path_Space.thy.
- line 28: `iexit_class_X_own_filtration` does not exist.
- lines 42-44: three theorems are said to be stated in Theorem_1_1_Statement; they are in the hidden Statement_Auxiliary and unused.
- line 151: lsc_envK is said to be in Operator_Envelopes; it is in Semicontinuous_Analysis/Semicontinuous_Envelopes.thy:343.
- lines 191 and 235-236: Value_Function_Viscosity.
Other:
- Statement/ROOT: 'A single theory'.
- Essential_Infimum.thy:17 cites `ess_inf_time_eq`, which does not exist; the lemma is ess_inf_ennreal.

Evidence: grep -rnE '^\s*(lemma|theorem) rotSF_exists' -> Value_Function_Supersolution_Case_1.thy:273; no iexit_class_X_own_filtration, no ess_inf_time_eq anywhere; ls Relative_Arbitrage has no Pathwise_Quadratic_Variation.thy or Value_Function_Viscosity.thy.

Suggested action: Update both notes files, the ROOT description and the comment. Mark historical sections explicitly as history.


### RA-infinite+Statement-15. G4 still open: ess_inf_time duplicates ess_inf lemma by lemma, and this cluster pays with conversion steps

*library_duplicate, impact medium, confidence high, ~80 lines.*  
Locations: Continuous_Time_Martingales/Essential_Infimum.thy:24-110,255-295; Relative_Arbitrage/Exit_Class_Infinite.thy:257-273,337-347; Continuous_Time_Martingales/Essential_Infimum.thy:244-249 ('section The class P_x and the value function of Eq. (1.6)')

Several ess_inf_time lemmas are copies of ess_inf lemmas with the payoff wrapped in ennreal:
- ess_inf_time_AE (94-106) is a verbatim copy of ess_inf_AE (43-59);
- ess_inf_timeI copies ess_infI;
- ess_inf_time_mono copies ess_inf_mono;
- ess_inf_time_distr (274) and ess_inf_time_distr_measurable (255) copy ess_inf_distr (288).
The relation is already the one-line ess_inf_ennreal. iexit_val uses ess_inf while exit_val uses ess_inf_time, so every comparison in Exit_Class_Infinite goes through ess_inf_ennreal. The paper-free theory also carries a section heading on 'The class P_x and the value function of Eq. (1.6)', plus Larsson-Ruf, Lemma 2.3 and Proposition 2.4 prose.

Evidence: PLAN_RESTRUCTURING_2 G4: 'ess_inf_time M tau becomes an abbreviation for ess_inf M (ennreal o tau)' (not done; definition at line 77 is separate).

Suggested action: Make ess_inf_time a definition `ess_inf M (\<lambda>\<omega>. ennreal (tau \<omega>))` with the copied lemmas as one-line corollaries, or remove it. Move the paper prose and heading to the paper session.


### RA-infinite+Statement-16. iexit_class re-declares the six-clause covariation class with sconstraint hard-wired; the whole half-line bridge needs only closed/convex/bounded S of psd matrices

*generalisation, impact medium, confidence medium, ~300 lines.*  
Locations: Relative_Arbitrage/Exit_Class_Infinite.thy:29-84 (iexit_class, iexit_val, accessors); Relative_Arbitrage/Pair_Path_Laws.thy:4038 covariation_class, 4485 covariation_val; Relative_Arbitrage/Exit_Class.thy:224 exit_class; Relative_Arbitrage/Exit_Class_Marginals.thy:36 xclass, 977 `qvmata (4 * L)`; Statement/Statement_Auxiliary.thy:30

iexit_class is covariation_class without the horizon. G11 abstracted the capped class over S but stopped at the capped one. The bridge uses only these properties of S:
- iexit_class_pcut: closedness, via closedin_diffquot_constraint;
- iexit_class_qvmat / xclass_qvmata: S contained in psd matrices with an entry bound (diffquot_psd/entry/sym);
- xclass_eq_dq: convex, closed, bounded;
- iextend: some a in S (the only reason for `1 <= L` is mat_1_in_sconstraint, through bmpair_law_in_paper_pair_class).
The lift also hard-wires the paper constant through `qvmata (4 * L)`.

Evidence: PLAN_RESTRUCTURING_2 section 11 'What is left of G11' covers only exit_class consumers; iexit_class_def lines 32-41 have the same clauses as covariation_class_def minus `t \<le> T` and `min t T`.

Suggested action: Define `icovariation_class S x` and `icovariation_val S K x` in Pair_Path_Laws, and the X-law class `xcovariation_class S x` generically. Prove the cut, extension, marginal and lift results for abstract S under these hypotheses. Then iexit_class/xclass at `sconstraint k L` become one-line bridge equations, as for exit_class_eq_covariation.


### RA-infinite+Statement-17. Paper_Readings: 'Three places' but two treated; envelope subsection title overclaims; the orthogonality reading is unchecked

*documentation, impact medium, confidence medium, ~40 lines.*  
Locations: Statement/Paper_Readings.thy:9-11; Statement/Paper_Readings.thy:19-24; Statement/theorem_1_1_unfolded.html:1445-1453 (FLAGS.envelope), 1653

The opening says 'Three places ... admit more than one reading ... This theory settles what turns on each choice', but only the envelope and the expandability are treated. The HTML's 'three points' are a different three: orthogonality, envelope and L = 1. The orthogonality reading, whose prose argument is wrong (see the separate finding), is the one with no machine check.

The subsection 'For the value function the two readings do not differ' proves only that the boundary-gate sets are empty under both readings. But the supersolution clause touches the envelope globally over K, and lsc_envK K v and lsc_env v differ on K - interior K: OPEN_ITEMS section 1 gives the cube with k = 2. The HTML strengthens this to 'For the value function the two agree', which OPEN_ITEMS contradicts.

Evidence: Paper_Readings sections at lines 13 and 96 only; OPEN_ITEMS.md:144-149 '...its liminf within K is positive there while its liminf over balls of real^'n is 0. Neither clause implied the other'.

Suggested action: Add a checked section on the literal Pi_m reading and fix the count. Retitle the subsection, e.g. 'For the value function the boundary gates coincide'. Align the HTML.


### RA-infinite+Statement-18. Same Borel-measurability facts re-proved inline (outerp(fst p) - snd p six times; fst/snd/vec_nth several times)

*clone, impact low, confidence high, ~60 lines.*  
Locations: Relative_Arbitrage/Exit_Class_Infinite.thy:200-207,740-747; Relative_Arbitrage/Exit_Class_Marginals.thy:1099-1108; Relative_Arbitrage/Exit_Class_Pasting.thy:184-191; Relative_Arbitrage/Exit_Class_Witness.thy:808-815; Relative_Arbitrage/Value_Function_Euler_Construction.thy:329-336; Relative_Arbitrage/Exit_Class_Infinite.thy:175-177,716-717; Relative_Arbitrage/Exit_Class_Marginals.thy:376,870,1086,1213 (fstB/sndB), 429/431/1001/1109/1239 (projB/entB)

`have e: (\<lambda>p. outerp (fst p) - snd p) = (\<lambda>p. \<chi> i j. ...)` followed by `have cB: ... \<in> borel_measurable borel` is copied six times. `fstB`/`sndB` restate pair_fst_borel/pair_snd_borel (Continuous_Time_Martingales/Integrability_Criteria.thy:749,754).

Evidence: grep -rn "outerp (fst p) - snd p" --include=*.thy: 6 identical blocks; Pair_Path_Laws.thy:2404 outerp_borel exists but not the composite.

Suggested action: Add `outerp_fst_minus_snd_borel` (or a continuous_on rule for outerp in continuous_intros) next to outerp_borel. Cite pair_fst_borel/pair_snd_borel instead of the inline copies.


### RA-infinite+Statement-19. Repeated sub-arguments in Exit_Class_Infinite: two martingale clauses each twice, and the ess_inf transfer along pcut twice

*clone, impact low, confidence high, ~60 lines.*  
Locations: Relative_Arbitrage/Exit_Class_Infinite.thy:171-226 (iexit_class_pcut clauses iii/iv); Relative_Arbitrage/Exit_Class_Infinite.thy:712-765 (iextend_in_iexit_class clauses iii/iv); Relative_Arbitrage/Exit_Class_Infinite.thy:249-273 (iexit_val_cap_le) vs 331-347 (iexit_val_ge_of_extension)

In each theorem, the X-martingale clause and the compensated clause are the same proof with fst replaced by `\<lambda>p. outerp (fst p) - snd p`. They could be one lemma for an arbitrary continuous f of the coordinates. The ess_inf_time of pexit under `pair_law_of T (pcut T) P` is turned into ess_inf of ennreal pexit under P twice, with the same four steps: ess_inf_time_distr, pexit_pcut, ess_inf_ennreal, plus the measurability side goal.

Evidence: Lines 257-268 and 337-347 are textually the same calculation.

Suggested action: Extract `ess_inf_pexit_cut: P \<in> iexit_class .. \<Longrightarrow> closed K \<Longrightarrow> ess_inf_time (pair_law_of T (pcut T) P) (\<lambda>\<omega>. pexit T K (fst o \<omega>)) = ess_inf P (\<lambda>\<omega>. ennreal (pexit T K (fst o \<omega>)))`. Prove the martingale clauses once for a continuous f.


### RA-infinite+Statement-20. Orphaned and wrong text blocks and blank residue in Exit_Class_Infinite and Exit_Class_Marginals

*documentation, impact low, confidence high, ~80 lines.*  
Locations: Relative_Arbitrage/Exit_Class_Infinite.thy:18-28,61-67,86-92,308-313,380-395,460-467,620-629; Relative_Arbitrage/Exit_Class_Marginals.thy:32-35,95-103,179-185,351-357,857-863,1191-1206

Exit_Class_Infinite:
- 'subsection The uncapped exit time' (18) is followed by 10 blank lines and the class definition.
- 'Restriction to a compact horizon' plus its text about pcut_adapted (61-65) is followed by accessor lemmas.
- 86-92 says X's own-filtration martingale property follows 'via martingale_coarser_filtration'; no such step exists; it comes from the marginal theorem.
- 308-313 calls the construction 'an iterated application of exit_class_pglue_law'; iextend is a single glue with ibm_law.
- 382-385 says 'pcut_pglue lives in Dynamic_Programming_Kernels'; it is Path_Splicing.thy:556.
- 387-390 and 462-463 describe lemmas that are not there, followed by blank lines and unrelated definitions (ibmpair, iextend).
- 622-625 describes a filtration identification proved only inside martingale_of_cuts.
Exit_Class_Marginals:
- 95-98 speaks of 'the matrix locale' (there is none) and 'the plan never named'; it duplicates the heading text at 105-110.
- 100-103 and 353-355 are 'lives in' pointer residue.
- 351 says 'outerp_borel lives in Exit_Class_Pasting'; it is Pair_Path_Laws.thy:2404.
- 182 places the restrict_full package in Stopped_Localization; it is Continuous_Time_Martingales/Martingale_Transfer.thy:821-959.
- 179 'Obligation (b) of the bridge' refers to OPEN_ITEMS numbering.
- 857-861 announces 'two events', but only one follows.

Evidence: grep locations: pcut_pglue Path_Splicing.thy:556; outerp_borel Pair_Path_Laws.thy:2404; space_restrict_full etc. Martingale_Transfer.thy:821ff; iextend_def line 470 (single iglue).

Suggested action: Re-anchor the subsection headings to their content. Delete pointer residue and blank runs. Fix the three wrong locations and the 'iterated' claim. Drop or substantiate the coarser-filtration remark.


### RA-infinite+Statement-21. Correct but unbacked prose claims in the statement; non-vacuity hidden

*faithfulness, impact low, confidence high, ~60 lines.*  
Locations: Statement/Theorem_1_1_Statement.thy:22-27,71-75,93-96,115-121; Continuous_Path_Spaces/Path_Exit_Times.thy:1397-1406; Continuous_Path_Spaces/Path_Space_Infinite.thy:9-24

Several readings are asserted in prose only:
- (a) 'Not a widening: F factors through M |-> (M+M^T)/2 ... contraction': correct (checked by hand: F(p,M) = F(p,sym M), and sym is the Frobenius projection), but no lemma.
- (b) iexit is displayed only as SUP_T of capped exits. No lemma `iexit K f = Inf (ennreal ` {t. 0 \<le> t \<and> f t \<notin> K})` matches the paper's tau_K := inf{t >= 0 : X(t) notin K}. Path_Exit_Times.thy:1405 even keeps an orphan 'Hence the elementary bound identifying iexit as the first time the path is outside K' with no lemma.
- (c) ipath_space is the evaluation sigma-algebra; the paper uses the Borel sigma-algebra of locally uniform convergence. They are equal, but this is neither said nor proved.
- (d) The Courant-Fischer reading of eigen_lb is proved (Operator_Formula.thy:2028 eigen_lb_iff_eigval_ge) but not displayed.
- (e) 'Every compact convex set with nonempty interior is expandable' is proved only in the hidden Statement_Auxiliary.

Evidence: grep finds no iexit-as-Inf lemma, no ell_op symmetrisation lemma, no ipath_space = borel lemma; convex_sets_are_expandable is in a document=false theory.

Suggested action: Prove and display iexit_eq_Inf. Display eigen_lb_iff_eigval_ge and the non-vacuity corollary. Optionally add lemmas for (a) and (c), or at least state (c) in the prose.


### RA-infinite+Statement-22. Unused statements reachable only from the hidden auxiliary theory

*dead_code, impact low, confidence high, ~70 lines.*  
Locations: Statement/Statement_Auxiliary.thy:15,21,27,33,48,61,67; Relative_Arbitrage/Value_Function_Uniqueness.thy:607 iexit_val_neq_top, 644 iexit_val_visc_subsol, 789 iexit_val_supersol_lsc_K; Continuous_Path_Spaces/Pathwise_Quadratic_Variation.thy:1054 qvmat_eq_A_sym

Several statements are never used:
- In Statement_Auxiliary: paper_value_function_agrees, paper_class_marginal, paper_class_lift, convex_sets_are_expandable, clause_0_not_infinite, clause_2_subsolution and clause_2_supersolution are named nowhere.
- Their sources iexit_val_neq_top, iexit_val_visc_subsol and iexit_val_supersol_lsc_K are used only by them.
- qvmat_eq_A_sym is referenced only in prose.

Evidence: grep -rnw NAME --include=*.thy: only the definition site (plus a re-export in Statement_Auxiliary for the VFU lemmas).

Suggested action: Delete, or keep the useful ones (non-vacuity, finiteness) as displayed corollaries in the new final theory.


### RA-infinite+Statement-23. Small paper-free lemmas in the wrong place

*misplacement, impact low, confidence high, ~40 lines.*  
Locations: Statement/Paper_Readings.thy:52 lsc_envK_cong; Relative_Arbitrage/Exit_Class_Marginals.thy:864 pairpath_diffquot_sets; Relative_Arbitrage/Pair_Path_Laws.thy:241 nonbinding_horizon_ex

Three small lemmas sit in the wrong theory:
- lsc_envK_cong ('u = u' on K implies equal K-envelopes') is a fact about lsc_envK and belongs in Semicontinuous_Analysis/Semicontinuous_Envelopes.thy.
- pairpath_diffquot_sets says nothing about xclass. With S abstract it belongs next to pairpath_start_sets in Pair_Path_Laws.
- nonbinding_horizon_ex (rK^2/(n-k) < T) is paper arithmetic placed in the path toolkit.

Evidence: Statements quoted at the given lines.

Suggested action: Move as indicated (the last one is better replaced by the compact-horizon corollary).


### RA-infinite+Statement-24. HTML source labels drift from HEAD

*documentation, impact low, confidence high, ~3 lines.*  
Locations: Statement/theorem_1_1_unfolded.html:842 (ref 614ecf8), 1207, 1254

Links are pinned to 614ecf8, where outerp is at Pair_Path_Space.thy:720 and expandable at Test_Functions.thy:1145. At HEAD (after 51d2122) these are lines 718 and 1144, so the displayed src text no longer matches the working tree. The links still resolve correctly.

Evidence: git show 614ecf8:... | grep -n 'definition outerp' -> 720; HEAD -> 718.

Suggested action: Regenerate the page against the commit that fixes the issues above.


### RA-infinite+Statement-25. Minor simplifications in the identification proofs

*simplification, impact low, confidence medium, ~40 lines.*  
Locations: Relative_Arbitrage/Exit_Class_Infinite.thy:283-303 (iexit_val_cap_le case split); Relative_Arbitrage/Exit_Class_Infinite.thy:119-128 (start-event measurability, cf. Pair_Path_Laws.thy:1278 pairpath_start_sets); Relative_Arbitrage/Exit_Class_Marginals.thy:446-456 (predx); Statement/Paper_Readings.thy:121 (compact K only used for boundedness)

Four small proofs can be shortened:
- The final case split in iexit_val_cap_le re-derives min (Sup A) T <= v from the pointwise bounds. ennreal is a complete linear order, so inf_Sup / `min (Sup A) T = (SUP a\<in>A. min a T)` gives it directly.
- The start-event measurability is re-proved for path_borel S and for ipath_space ({w. w 0 = x}) beside pairpath_start_sets.
- paper_expandable_imp_expandable needs only `bounded K`.
- Example 3.1 is stated through enn2real. `xval .. = ennreal (max ..)` would rule out top consistently with clause (0).

Evidence: Code at the given lines.

Suggested action: Apply when touching these proofs.
