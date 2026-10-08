# Session design panel (Review III, 2026-10-07/08)

Three designers worked independently from REVIEW_3, the measured data in this directory and the
independent-interest verdicts. Each had a different priority: **afp-first** (maximise submittable library entries),
**build-first** (minimise build and iteration time) and **paper-first** (mirror the paper, minimise migration risk).
Two judges then scored all three designs, each through one lens. The designs refer to HEAD `0db486f`.

The mathematics judge ran twice, because a session limit interrupted the first run. Both runs are recorded:
the first preferred afp-first 8 to 7, the second paper-first 8 to 7. Both runs ask for the same synthesis:
paper-first's paper side (paper order, `Paper_Map`, evidence as roots, keeping Theorem 4.2(a) and Proposition 2.4)
combined with afp-first's library side (coherent paper-free scopes, re-homing, G-G). The engineering judge chose
paper-first, 8 against 7 for build-first and 6 for afp-first. PLAN_RESTRUCTURING_3 §1.4 adopts paper-first with the grafts below.

## Scores

| judge | design | overall | reuse/AFP | paper readability | correctness of claims | migration risk (high = safe) | build time |
|---|---|---:|---:|---:|---:|---:|---:|
| mathematics (run 1) | afp-first | 8 | 9 | 6 | 6 | 4 | 8 |
| mathematics (run 1) | paper-first | 7 | 5 | 9 | 7 | 7 | 6 |
| mathematics (run 1) | build-first | 5 | 4 | 6 | 5 | 6 | 9 |
| engineering | afp-first | 6 | 9 | 6 | 5 | 3 | 7 |
| engineering | build-first | 7 | 6 | 6 | 7 | 6 | 9 |
| engineering | paper-first | 8 | 5 | 9 | 8 | 8 | 6 |
| mathematics (run 2) | afp-first | 7 | 9 | 5 | 6 | 4 | 7 |
| mathematics (run 2) | build-first | 5 | 3 | 6 | 6 | 6 | 9 |
| mathematics (run 2) | paper-first | 8 | 6 | 9 | 7 | 8 | 6 |

## Judge: mathematics (run 1) (winner: afp-first)

### Verdict

The winner is afp-first, provided paper-first's paper-side organisation is grafted onto it.

My lens has four parts, and they split two against two:
- afp-first is the only design whose library sessions each have a coherent, paper-free scope worth an AFP entry.
- It is also the only one that places the abstract constraint set (Covariation_Control), the abstract geometric operator (Viscosity_Solutions.Geometric_Comparison with Expandable_Sets) and the unified viscosity predicates where other developments can reuse them. Each is gated, with a quantified fallback.
- It reads PLAN_2 §11 correctly: only the pair-free core goes into the toolkit library, and the pair/covariation layer goes to the class library. It derives special cases from general results rather than the reverse.
- paper-first is clearly better on the other two parts. It lays the paper sessions out in the paper's order with the paper's names. Its Paper_Map surfaces every numbered result with its deviations and doubles as the roots registry. It alone catches that the Eq. (3.6) evidence (eq36) is dead. It honestly keeps Theorem 4.2(a), Prop. 2.4 and the Section 5 record, as the owner's independent-interest directive asks.
- But paper-first deliberately leaves the libraries as they are. It moves the geometric notion `expandable` and the real-analysis lemma cInf_mult_pos down into the paper. It deletes the library's viscosity layer without replacing it, and it defaults to deleting the general path_rcd while keeping the special copies that re-prove it. Its generalisations are deferred with no library home.

All of paper-first's strengths are additive inside the paper entry: Paper_Map, the extra roots, paper-order names, the Example_3_1 assembly and the honest 4.2(a). They graft onto afp-first cheaply. Grafting afp-first's library work onto paper-first, by contrast, would simply rebuild afp-first.

afp-first's weaknesses are fixable:
- It is stale against HEAD 0db486f: its P0 items and the strengthening question are already done.
- It roots non-existent fact names and misnumbers Lemma 3.1.
- It misfiles the Example 3.1 lower bound into Supersolution.
- It would delete Theorem 4.2(a) if the 150-line attempt fails.
- It never mentions Section 5.
- If G-B passes, Section 2 disappears from the paper entry unless Paper_Map restates it.
- It carries the highest migration risk (G-B is extra-large, G-C has no dry run, nine entries to maintain). The gates and fallbacks bound that risk, and even its fallback layout (Section 4 in RA_PDE, Section 2 in Relative_Arbitrage_Class) beats the others on library organisation.

build-first is the strongest on build time but the weakest on my lens:
- It adds a repo-local aggregate session that makes the toolkit library unsubmittable as is.
- It quarantines Prop. 2.4 and Theorem 4.2(a) in an Extras leaf.
- It keeps the dead generic viscosity layer and places no generalisation.
- Its theory lists are stale against HEAD.

### Grafts

- From paper-first: add a Paper_Map theory as the last theory of the paper entry. It has one theorem per numbered item of Sections 1-4, proved by rule from the working lemma, with deviations noted, and doubles as the roots registry. In afp-first it must also restate Lemmas 2.2 and 2.3 and Prop. 2.4 from Covariation_Control at S = sconstraint k L, and Theorems 4.2(b), 4.3 and Prop. 4.1 from Geometric_Comparison. Otherwise, once G-B and G-C pass, the paper entry no longer shows Section 2.
- From paper-first: Section 5 is declared not formalised, in Paper_Map, root.tex and OPEN_ITEMS. Props 5.1 and 5.2 are a gated pilot (dilation plus Theorem 4.2(b)).
- From paper-first, to honour the owner's independent-interest directive: Theorem 4.2(a) is kept and labelled 'continuous data' if the faithful usc/lsc corollary misses its budget, instead of 'delete whatever the outcome'. With G-C it becomes an instance in Geometric_Comparison. Prop. 2.4 is also stated in the paper's horizon-T form, with the deviation recorded.
- From paper-first: root eq36 and ell_op_le_eq36 (Eq. 3.6, dead today) and poincare_separation. Replace the non-existent paper_class_marginal/lift roots with iexit_class_marginal_in_xclass and xclass_lift_in_iexit_class. Change 'Lemma 3.2' to 'Lemma 3.1'.
- From paper-first: give every library session explicit per-session deliverable roots in roots.txt, including the CIS headline and the general path_rcd, in place of afp-first's 'judgement call' policy for library dead code.
- From paper-first: Example_3_1 is built from Value_Function_Assembly (the sharp ball lower bound), Case_1 2065-2648 and Value_Function_Uniqueness 291-554, rather than merging Assembly into Supersolution. Add a Control_Problem-style §1 theory (sconstraint, xclass, xval) at the head of the paper session. List both paper sessions' ROOTs in paper order, and check that order with a script.
- From paper-first: before deleting Viscosity_Comparison_Interface, find by ML query where transpose_matrix_vector is actually absent from the simpset and replicate the declaration exactly there, instead of moving it blindly.
- From paper-first: order the phases so that a paper-readable state is reached early. Do the RA_PDE and Path_Space_Operations splits and the paper-order renames before the large CTM/CPS/SOVA re-layering, and keep G-B and G-C last.
- From build-first: put a statement fingerprint (an aconv assertion on theorem_1_1 and example_3_1) and an oracle assertion into Paper_Readings as build-time checks. Enforce the re-check whitelist from build logs in CI, and cache the AFP heaps, Levy_Prokhorov_Metric in particular.
- From build-first: move eigen_lb/eigen_ub to the head of Constraint_Set, so the RA_PDE theory order reads Eqs. (1.4)-(1.5) before (1.9). Keep the §2/§3 session split (Relative_Arbitrage_Class) as the named G-B fallback.

### Errors found per design

**afp-first**

- Several actions are already done at HEAD. Commit 0db486f gave theorem_1_1 the paper's hypotheses, created Relative_Arbitrage/Theorem_1_1.thy (164 lines), deleted Statement_Auxiliary, displayed density_cond_def and fixed the §1.2(b)-(f) prose. Commit 562a95e added roots.txt and check.sh (which builds with -D .) and untracked the .pyc. So these are stale: P0 'add theorem_1_1_strong / check script / prose fixes', P10 'create Theorem_1_1, delete Statement_Auxiliary', the pycache hygiene item, and the open question 'may the acceptance test be strengthened'.
- It roots 'paper_class_marginal/lift', but no .thy file contains these names. The live class bridge is Exit_Class_Marginals.iexit_class_marginal_in_xclass (l.358) and xclass_lift_in_iexit_class (l.974), already on the path via iexit_val_eq_xval.
- It misses dead faithfulness evidence: eq36 and ell_op_le_eq36 (Operator_Envelope_Continuity:75,205; Eq. (3.6), a clause of Lemma 3.1) are outside the closure in unused_by_theory.json and are not in Paper_Readings. With library dead code left to a 'judgement call' and no per-session roots, the next pass would delete them.
- The RA_PDE scope cites 'Lemma 3.2'. The paper's operator lemma is Lemma 3.1: \newtheorem{lemma}[thm] shares the per-section thm counter, and Section 3 has no earlier thm, lemma or prop.
- It merges Value_Function_Assembly into Value_Function_Supersolution. That theory holds exit_val_ball_lower_subspace/_sharp, the sharp ball lower bound, and its only consumer is the Example 3.1 proof at Value_Function_Uniqueness:522. This misfiles Example 3.1 material.
- It is internally inconsistent. 'Ball_Solution [MERGED with Viscosity_Ball]', but the deletion list deletes Viscosity_Ball (233 lines, 0 of 3 facts used). Yet the RA_PDE scope still advertises 'the explicit solution of Example 3.1', whose PDE-side proofs are in that theory.
- Theorem 4.2(a) is deleted with the compact-uniqueness branch 'whatever the outcome' of a 150-line faithful attempt. This contradicts the owner's directive that statements of the paper stay (plan_independent_interest.md) and PLAN_3 D3's 300-line budget.
- Section 5 (Props 5.1-5.5, Lemma 5.3) is not mentioned anywhere. Nothing records that it is unformalised.
- It deletes CTM.Quadratic_Variation's stopped section as dead. VERIFY claim 8 found no library statement that a stopped martingale is a martingale: Fair_Games covers submartingales only and is not a dependency. That makes the section a candidate under the independent-interest rule.
- If G-B passes, Lemmas 2.2 and 2.3 and Prop. 2.4 (added in the library's DP_Assembly) exist only as library theorems. The paper entry restates none of them and has no index, so a reader of the paper entry no longer finds Section 2.

**paper-first**

- It calls the Phase-1 work 'uncommitted'. It is committed (0db486f). Review_Analysis already reads roots.txt and the .pyc is already untracked (562a95e), so P0 and the hygiene item are partly redundant.
- It lists dq_iff_density as evidence outside today's closure. Covariation_Density has 9 of 9 facts used (dead_code_by_theory.txt), and dq_iff_density is live through xclass_eq_dq.
- It moves library material down into the paper. expandable/convex_expandable is a purely geometric notion (PLAN_2 §3.3 Expandable_Sets), and it goes into Equation.Comparison_Two_Domain. cInf_mult_pos, a real-infimum scaling fact, goes into the paper's Elliptic_Operator. Both moves work against reuse and against a later G-C.
- It deletes SOVA.Viscosity_Solutions and defers G-G. Second_Order_Viscosity_Analysis then has test functions but no notion of viscosity solution, and the predicates exist only for ell_op.
- G-B and G-C are deferred, or kept as a pilot leaf with no library home ('interface recorded in Paper_Map'). The generalisations are not placed where they enable reuse.
- The Path_Space_Operations entry carries the pair layer. That includes covariation_class S and the Euler/Case-2 helpers (about 1,500 lines, RA-path1#8 and RA-value2#17), whose return to the paper is only 'optional P8'. PLAN_2 §11 says Pair_* and Path_Law_Sampling 'are the pair layer proper and are not meant to leave it'.
- By default it deletes the general path_rcd/path_rcd_ksemi as dead. It keeps the class-specific copies that re-prove them (RA-path2#2). That is the wrong direction for reuse and for the independent-interest rule.
- Library re-layering is explicitly skipped. CPS keeps the CTM moment estimates and HOL-Complex_Analysis (removal is optional), Doubling_Of_Variables stays a 5,330-line drawer (SOVA2#22), and the misnomer Theorem_On_Sums is kept.
- The probability-free session's parent is Path_Space_Operations. The Section 4 seam is enforced only by an ML ancestor test, and Section 4 cannot be built without the probability stack. The design acknowledges this.

**build-first**

- It is stale against HEAD. The Statement session lists Statement_Auxiliary, deleted in 0db486f, and the Relative_Arbitrage list omits the existing Theorem_1_1.thy. The Phase 0 G-A switch is already done. 'Requalify the 3 Statement imports' is wrong: Theorem_1_1_Statement imports only Relative_Arbitrage.Theorem_1_1.
- Relative_Arbitrage_Base contradicts PLAN_3 D7 (no aggregating base session, no filler names). It also makes the library Path_Space_Operations depend on a repo-local heap, so the entry cannot be submitted to the AFP without a parent swap.
- It says the 'Quadratic_Variation stopped section (300; Fair_Games_Theorem covers it)'. VERIFY claim 8 says Fair_Games has only the submartingale version, no martingale one, and is not a repository dependency.
- Prop. 2.4, a Section 2 statement, and Theorem 4.2(a) are quarantined in an off-path Extras leaf, 'delete if nobody commits'. This puts paper statements away from their sections, against the owner's directive. Prop. 2.4 belongs in Relative_Arbitrage_Class.
- SOVA.Viscosity_Solutions (108 lines, 0 of 10 facts used, no env2 variant) is kept with no action. G-G is absent.
- G-B and G-C are 'open-ended' in phase 7 with no target session. The constraint set stays hard-wired in Relative_Arbitrage_Class.
- It roots the non-existent paper_class_marginal/lift and does not root eq36.
- Crandall_Ishii is split into a one-theory leaf session, so the SOVA scope no longer names the theorem on sums, the entry's headline.
- Section 5 is not mentioned.

## Judge: engineering (winner: paper-first)

### Verdict

Under the engineering-soundness lens, paper-first wins. Build-first is a close second for build time; afp-first is the best AFP target but the riskiest migration.

Paper-first's claims match the measurements. RA re-check falls from 560 s to about 140 s because the libraries land in ancestor heaps, and the design says plainly that total cold-build re-check barely moves. Its phases reuse the two PIDE dry runs unchanged: block moves, unchanged imports, one deletion per commit, and Paper_Map as the dead-code root set. It is the only design that handles the global `transpose_matrix_vector [simp del]` correctly, by measuring first because simpset merges are unions. My ML probe confirms that only Viscosity_Comparison_Interface and Ball_Solution lack the rule; 46 of 48 RA theories have it. Its weaknesses are build-time ones. RA_Equation in the chain makes Section 4 edits cost about 620 s CPU, and HOL-Complex_Analysis is kept by default. Its P8 'fingerprint identical' claim is wrong for theory renames and definition moves, because constant long names change.

Build-first has the best calibrated numbers (1,119 vs 1,123 s) and a valid base-heap trick: a heap whose theories all belong to other sessions is legal, and the earlier test build of one has no errors. But its Phase 1 copies the simp deletion into Exit_Class and Value_Function_Uniqueness, theories that currently have the rule. That would cause the very behaviour change it claims to prevent. Its Path_Space_Operations parent is not AFP-honest, and cold and library-edit builds get slower.

Afp-first correctly notes that re-check is once per Statement build, gates G-B and G-C well, and gives the cleanest AFP layout. But it front-loads large unverified refactors before the verified steps, so P5's dry-run evidence no longer applies. It understates antiquotation churn (about 140 in P4, not 24) and hides the dissolution of the 6.2k-line Pair_* theories inside P7. Its headline CPU halving assumes prebuilt AFP heaps, and its aconv check breaks at its own renames.

All three were designed against 3bc3803 and must be rebased on HEAD 4d5f47e, where Phase 0/1 and the market deletion are done. Recommended plan: paper-first, plus build-first's sibling-plus-base layout, CPS on Levy_Prokhorov_Metric with a local Arzela-Ascoli, afp-first's check script and gates, and fingerprints compared modulo constant renames.

### Grafts

- From build-first: make Relative_Arbitrage_Equation a parallel sibling with parent Second_Order_Viscosity_Analysis, so it is probability-free by construction. Add a repo-local Relative_Arbitrage_Base inside the paper entry, with parent Path_Space_Operations and no theories of its own, listing the SMS/SOVA/SemiC/Lower_Semicontinuous/WM/KC theories that RA and RA_Equation import; RA's parent becomes RA_Base. RA then re-checks only the RA_Equation theories (~60-70 s), Section 4 edits drop from ~620 s to ~150 s, and Path_Space_Operations keeps the AFP-honest parent Continuous_Path_Spaces. The base-heap pattern is confirmed buildable.
- From afp-first and build-first: CPS parent Levy_Prokhorov_Metric, plus the ~180-line attributed Arzela-Ascoli copy (Great_Picard l.612-800, general topology only) to drop HOL-Complex_Analysis. This saves 226 s CPU even cold, and cuts CPS re-check from 882 to about 230 s once the LPM heap is cached.
- From afp-first: the per-phase check script (standalone `isabelle build -D .` so Crandall_Ishii_Sums and library heaps cannot rot, an oracle check, a library lint for paper mentions, ML ancestor checks), and numeric gates with fallbacks for G-B and G-C.
- From build-first: the calibrated session-level build simulator and a build-log re-check whitelist enforced in CI. Also measure the rebuild semantics directly: touch one theory per session and record which sessions say 'Building'.
- For every design: compare statement fingerprints modulo a constant-rename map (or by base names) in any phase that renames a theory or moves a definition. Session moves alone keep props aconv; theory renames do not.
- Simp leak, all designs: delete VCI and Ball_Solution, and put a proof-local [simp del] only into the proofs moved out of them. Do not replicate the global declaration anywhere else, since 46 of 48 RA theories already have the rule as simp.
- From afp-first: put cInf_mult_pos in Semicontinuous_Analysis rather than Curvature_Operator, and later, gated, take the cheap library re-layering items: the Increment_Moments martingale part into CTM, one Dyadic_Grids theory, and G-C to turn RA_Equation into a library.
- From build-first: optionally put Theorem 4.2(a)'s exclusive chain and Crandall_Ishii_Sums in an `extras`-group leaf, so they stay checked but leave the paper edit loop.
- Rebase every phase on HEAD 4d5f47e before starting. Phase 0/1 and the market deletion are done, RA is 60,200 lines in 48 theories, and there are 32 @{theory Relative_Arbitrage.X} antiquotations in 15 files.

### Errors found per design

**afp-first**

- Stale baseline. P1 market deletion and P10 (create Theorem_1_1 in the faithful form, delete Statement_Auxiliary) are already committed (4d5f47e, 0db486f). The numbers '667-line Statement' and '64,967-line RA / 55 theories' no longer hold: HEAD has an 850-line Statement and RA at 60,200 lines in 48 theories.
- False simp-hazard premise. The P1 risk says 'the global simp del leak can change downstream simp behaviour'. Measured: the deletion is effective only in VCI and Ball_Solution, and 46 of 48 RA theories have the rule because simpset merge is a union. Relocating the declaration to 'theories that need it' without measuring first would itself change behaviour.
- The P0 check (4) requires theorem_1_1's prop to stay aconv to a stored term in every phase. P5 renames Curvature_Operator and Constraint_Set_Convexity, and P10 renames Exit_Class_Marginals; ell_op, eigen_lb/eigen_ub, Pi_proj, xclass and xval are defined there. Constant long names carry the theory base name, so the check fails unless it compares modulo a rename map.
- P5 cites the 16-theory PIDE dry run as verification. P4 has already split and renamed what those theories import: SOVA becomes Semiconvex_Functions + Viscosity_Solutions, Matrix_Algebra is split 3 ways, Doubling_Of_Variables is split 3 ways, and Viscosity_Solutions is rewritten under G-G. The dry-run evidence therefore does not cover the state P5 starts from. Verified steps should run before the refactors that invalidate them.
- P4 antiquotation churn is understated. The Matrix_Algebra split, the DoV split, the SOVA rename and the Theorem_On_Sums rename touch about 140 @{theory ...} antiquotations (75 + 50 + 12 + others), not the 24 the design cites, which belong to the PDE split alone. Reusing the name Theorem_On_Sums for the former Crandall_Ishii_Sums makes 12 mechanically requalified prose pointers point at a different theory.
- P7 is not the verified block move. Path_Splicing imports Pair_Path_Laws, so PSO can only exist after Pair_Path_Space (1,717 lines) and Pair_Path_Laws (4,500 lines) are dissolved across CPS, CTM, SMS, SemiC, PSO and Covariation_Control. P7's action list ('move 3 theories, 5 statements') and its Medium risk hide this. The PIDE dry run covered the six theories moved as a block, not this layout.
- The headline 'Statement-path CPU ~2,370 -> ~1,140 s, 18:43 -> ~11 min' assumes prebuilt AFP heaps. In a cold build the ~620 s CPU Levy_Prokhorov_Metric heap (Riesz 268 + SBS 178 + LPM 150, which CPS re-checks today) is still paid. Re-check moves into a cacheable heap; it is not removed.
- G-G, which rewrites the generic viscosity predicates and is new mathematics, sits ungated inside P4, the largest library phase.
- Minor plumbing. In P2, Semicontinuous_Selection gets a new session qualifier, so its 4 importers and RA's ROOT must change in P2 (the latter is listed only in P5). A second session in the SemiC directory needs its own document setup. Viscosity_Ball (dead, 27 s CPU) is merged into Ball_Solution instead of being deleted.

**build-first**

- The simp-del relocation is backwards. Phase 1 copies `declare transpose_matrix_vector [simp del]` into Ball_Solution, Value_Function_Uniqueness and Exit_Class 'so simp behaviour does not depend on import shape'. Measured: Exit_Class, VFU and 44 other RA theories already have the rule as simp, because VCI's deletion is voided by union merges. Only VCI and Ball_Solution lack it. The copy would newly delete the rule in Exit_Class and VFU, and in descendants whose maximal parents all descend from them, causing the change it means to prevent. VFU is also not a direct importer of VCI.
- Phase 4 validation claims 'Statement green with an unchanged fingerprint'. The same phase moves eigen_lb/eigen_ub into Constraint_Set and renames Curvature_Operator and Constraint_Set_Convexity, so constant long names change. The design's own risk list says so, and an aconv fingerprint cannot stay unchanged without name normalisation.
- Stale baseline. Phase 1 'delete 7 dead re-exports' and phase 4 'requalify 3 Statement imports' target Statement_Auxiliary, which 0db486f deleted; the Statement now imports only Relative_Arbitrage.Theorem_1_1. Phase 0 (the faithful theorem_1_1) and the phase 1 market deletion are already done.
- The shipped ROOT differs from the tested one. Path_Space_Operations has the repo-local Relative_Arbitrage_Base as parent, so the library is not AFP-submittable as built, and its honest form (parent CPS) is exercised only by a nightly job.
- Real regressions, accepted explicitly: edits to SMS, SOVA or WM go from 555 to about 684 s, and a cold build is about 15% slower because more sessions are serialised at about 30 s of overhead each.
- The claim that RA_Class does not rebuild on non-Constraint_Set PDE edits rests on reading the RC3 sources, not on a measurement. The 134 s figure for a PDE edit depends on it.
- Base-list drift: a newly imported library theory missing from Base is silently re-checked inside a paper session. The proposed whitelist check is mandatory, not optional.

**paper-first**

- P8 validation says 'Fingerprint identical (moves may not change any statement)'. P8 renames Curvature_Operator to Elliptic_Operator and Comparison_Principle to Maximum_Principle, and moves the definitions of sconstraint, xclass and xval into Control_Problem. Constant long names include the theory name, so the props of every statement mentioning them change. The fingerprint must compare modulo a rename map. The P6/P7 session moves are fine, because session qualifiers are not part of constant names.
- D1 puts Relative_Arbitrage_Equation between PSO and RA. A Section 4 edit then costs about 620 s CPU (RA_Equation + RA), against about 134 s in build-first's sibling-plus-base layout. Every CPS or PSO edit also rebuilds RA_Equation, and Section 4 PIDE work needs the whole probability heap. The trade-off is stated, but it is the weakest build-time point.
- Merging Operator_Envelope_Continuity into Operator_Envelopes is not context-neutral. OEC imports Operator_Formula and OE does not, so OE's existing proofs would run with Operator_Formula's declarations in scope. The CSC+EBE and OC+OF merges are neutral, because the second theory already imports the first.
- Ball_Solution's two live facts move into Curvature_Operator, where transpose_matrix_vector is simp. Ball_Solution is one of the only two theories where it is not, so these proofs may need a local [simp del]. The measure-first protocol will surface this, but the text says 'replicate the declaration there' for a theory it deletes.
- HOL-Complex_Analysis stays by default and CPS keeps parent CTM. That keeps 226 s CPU and 13.4k lines re-checked in every CPS build (CPS build about 855 s), and the cheap verified win is left optional.
- Stale relative to HEAD: P0 (build and commit the working tree) and P2(a) (market deletion) are now committed (0db486f, 4d5f47e). The design itself correctly identified the then-uncommitted state.
- cInf_mult_pos goes to the paper theory Curvature_Operator instead of a library home such as SemiC. PSO keeps about 1,500 lines of paper helpers unless the optional P8 return is done, and the library re-layering is deferred.

## Judge: mathematics (run 2) (winner: paper-first)

### Verdict

The winner is paper-first. Through my lens the result splits: afp-first has the best library sessions and the best placement of the generalisations, and paper-first has by far the best paper session and the best protection of faithfulness evidence.

**Why not afp-first.** It buys its library shape by moving the paper's own Section 2 (Lemmas 2.2 and 2.3, Proposition 2.4, which the paper states for general S) and Section 4 into library entries that are forbidden to cite the paper. It merges the Example 3.1 lower bound into the supersolution theory. It deletes Theorem 4.2(a) and the compact uniqueness if a pilot fails, against the independent-interest verdicts now in notes/review_3/data. Its execution is the riskiest of the three: an XL generalisation step, and a swap of two theory names.

**Why not build-first.** It organises the paper well (a PDE session, a §2 session and a §3 session). But its libraries get worse:
- a theory-less Base session and an Extras leaf, both filler names already rejected by PLAN_3 D7;
- a toolkit that cannot be submitted to the AFP;
- Crandall-Ishii split off its home session;
- a grab-bag scope for Continuous_Path_Spaces;
- Proposition 2.4 and Theorem 4.2(a) quarantined in Extras.

**Why paper-first.** Its paper session follows the paper. Paper_Map is both the reader's index and the dead-code root set. It keeps 4.2(a), CIS and Proposition 2.4 where the owner wants them, and it carries the least risk. Its weaknesses are on the library side:
- the Equation session's parent is the probability stack;
- it deletes the generic viscosity layer;
- it leaves SMS's Poincaré separation undelivered and the toolkit's paper helpers in place, both as 'optional P8';
- it puts cInf_mult_pos in the paper.

All of these are fixed by the grafts listed above from afp-first and build-first.

**All three are partly stale against HEAD (4d5f47e).** The market layer is deleted, theorem_1_1 already has the paper's hypotheses, and Statement_Auxiliary is gone.

**Side effect of my checks.** I ran one probe build, in scratchpad/judge3_simp. It raced with other agents' builds, and a user-level Pure heap appeared in ~/.isabelle around 08:35. Someone else removed it by 08:36. The heaps now look intact, and I deleted my probe's log entries. Nothing in the repository was modified by me.

### Grafts

- From afp-first, G-G: replace SOVA.Viscosity_Solutions instead of deleting it. Use two generic predicates, parametrised by test class and touching locality, that cover all six used variants including env2/C2. Connect the paper's predicates by bridge equations, not abbreviations (PLAN_2 §10 lesson). SOVA then keeps its advertised deliverable.
- From afp-first: make the library re-homing mandatory, and do it before Path_Space_Operations is promoted:
  - general poincare_separation and eigval_ge_of_subspace go into SMS.Poincare_Separation, which fixes the undelivered headline;
  - the outerp family, the onormal/threshold toolkit and projmat/rank1proj (an Orthogonal_Projections theory) go to SMS;
  - the Brownian block of Exit_Class_Witness and the Brownian fourth moments go to WM;
  - the Euler-scheme and Case-2 helpers move out of Pair_Path_Laws back into §3.
- From afp-first: move the misplaced probability material by subject:
  - the martingale fourth-moment estimate (Increment_Moments l.1-1975), Conditional_UI, Stopped_Localization, path-free optional sampling, the ksemi lemmas and a Dyadic_Grids theory go to CTM;
  - the generic path-measurability API, the exit-time semicontinuity block and a generic ball exit time go to CPS.Path_Exit_Times.
- From afp-first:
  - put cInf_mult_pos in Semicontinuous_Analysis, not in the paper's Elliptic_Operator;
  - give SemiC the parent Lower_Semicontinuous;
  - add a check-script lint for paper mentions (LaiShkolnikovSoner, 'Eq. (', 'Lemma 2.') and root.bib entries in library sessions.
- From afp-first, G-C as a gated pilot. Build a Geometric_Comparison locale in the viscosity library with the gate '≤15 assumptions, each discharged by an existing ell_op lemma'. Expandable_Sets moves there too if the gate passes. The Equation session then interprets the locale and still states Proposition 4.1 and Theorems 4.2 and 4.3 under their paper numbers, so the Paper_Map entries do not change.
- From afp-first: split Doubling_Of_Variables at its section boundaries (l.4052 and l.5107), and consolidate sup-convolution attainment into Sup_Convolution as one supconv_attained_usc. Optionally, split Rademacher, Alexandrov, Jensen and Sup_Convolution off as a Semiconvex_Functions entry.
- From build-first and PLAN_3 D5: parent Relative_Arbitrage_Equation on SOVA, so that probability-freeness is structural. Revisit D1 only if a measured rebuild cost justifies it, and keep the ancestor-check theory either way.
- From build-first: optionally a separate §2 session (class and DPP) between Path_Space_Operations and the §3 session, to mirror the paper's sections. Also adopt build-first's re-check whitelist on build logs, enforced in CI.
- From independent_interest.md, which binds all three designs:
  - keep viscosity_uniqueness_compact as a corollary of 4.2(a) of at most 10 lines;
  - build Proposition 2.4 from exit_val_dpp_le_of_cond plus exit_val_cond_time.
- G-B: generalise Lemmas 2.2 and 2.3 (and the DPP) to abstract S inside the paper entry, as the paper states them. Keep covariation_class in Path_Space_Operations. Do not export the paper's Section 2 into a library entry that cannot cite it.

### Errors found per design

**afp-first**

- Stale against HEAD. P1 (market layer, deleted in 4d5f47e) is already done. So are P10's faithful theorem_1_1, the new Theorem_1_1 theory and the deletion of Statement_Auxiliary (0db486f). density_cond_def is already displayed (Theorem_1_1_Statement.thy:70). Paper_Readings already holds lemma_2_1, eigen_lb_reading, eq_3_5, convex_sets_are_expandable and literal_reading_keeps_identity. The open question asking to approve the strengthened acceptance test is moot.
- Example 3.1 ends up split across two theories. Value_Function_Assembly holds exit_val_ball_lower_subspace and exit_val_ball_lower_sharp, the lower bound of Example 3.1, and it is the only importer of Value_Function_Tangential_Field. The design merges it into Value_Function_Supersolution and splits Example_3_1 off Value_Function_Uniqueness only.
- The paper's own Section 2 moves into the library session Covariation_Control: Lemmas 2.2 and 2.3 and Proposition 2.4, which the paper itself states for general S. With G-C, Section 4 also moves, into Geometric_Comparison. By the stated constraint these libraries cannot cite the paper, which is an attribution problem. It also leaves the paper entry without its main probabilistic lemmas.
- Theorem 4.2(a) and the compact-uniqueness branch are deleted 'in any case', or whenever the 150-line pilot fails. That contradicts notes/review_3/data/independent_interest.md, where 4.2(a) is FIX_THEN_KEEP ('keep the current proof, honestly renamed, rather than delete it') and viscosity_uniqueness_compact is kept as a corollary of at most 10 lines.
- Theorem_On_Sums is renamed Doubled_Jets and Crandall_Ishii_Sums is renamed Theorem_On_Sums in one migration. A theory name is reused for different content, so qualified names in roots.txt, the notes and the history become ambiguous.
- It calls the quadratic-penalty lemmas 'one-line corollaries of _gen (verified pattern)'. VERIFY item 5 is only partial: sums_matrix_inequality is stated at euclidean_space and is not an instance of the real^'n-only _gen lemma.
- The scope of Covariation_Control ('largest essential-infimum exit time') is the paper's own control problem, so its reuse value as an AFP library is low. Paper_Class and Paper_Class_Marginals use a filler prefix, against the spirit of PLAN_2 §8 rule 7.

**build-first**

- Relative_Arbitrage_Base has no theories of its own, and Relative_Arbitrage_Extras is a leaf. Both names use filler nouns forbidden by PLAN_2 §8 rule 7, and PLAN_RESTRUCTURING_3 D7 explicitly rejects an aggregating base session. Path_Space_Operations then has the Base session as its ROOT parent, so it cannot be submitted to the AFP without a parent swap.
- Stale. The Statement session still lists Statement_Auxiliary, which was deleted in 0db486f. P0's 'switch theorem_1_1 to the paper's hypotheses' is already committed.
- Proposition 2.4 goes into Extras instead of next to the DPP (Dynamic_Programming_Assembly). Theorem 4.2(a) is quarantined away from 4.2(b) with 'delete if nobody commits'. Both are FIX_THEN_KEEP in independent_interest.md, and this layout goes against organising the paper session the way the paper is organised.
- Its deletions list says the 'SOVA quadratic-penalty duplicates (~1,400) [are] reachable only from dead code'. The readers' SOVA2 dead-code finding says their other consumer is Crandall_Ishii_Sums, which this design keeps as a leaf. Deleting them would break that leaf.
- Crandall_Ishii_Sums becomes a one-theory leaf session outside SOVA. It is SOVA's advertised headline (the SOVA ROOT description, and library_deliverables.md lists theorem_on_sums_quadratic[_closed]), and its quadratic support stays behind in SOVA.
- The scope of Continuous_Path_Spaces becomes a grab-bag of six subjects. It gains Covariation_Density and Semicontinuous_Selection and keeps material the readers flag as CTM's: the fourth-moment estimate and Conditional_UI (CPS1#9/#10), and Stopped_Localization and both QV theories (CPS2#21).
- It keeps the dead generic SOVA.Viscosity_Solutions layer, which lacks env2, without G-G. G-B and G-C are left open-ended with no home planned.

**paper-first**

- D1 parents Relative_Arbitrage_Equation on Path_Space_Operations. Its heap therefore carries HOL-Probability, CTM, CPS and the toolkit, so Section 4 cannot be checked or reused without the probability stack, which is what REVIEW_3 §6.2 criticises. Probability-freeness becomes a regression test rather than structure, and a later G-C extraction would need the parent switch anyway.
- It deletes SOVA.Viscosity_Solutions without the G-G replacement. SOVA's advertised deliverable, 'definition of a viscosity sub/supersolution for an arbitrary operator' (library_deliverables.md), would then disappear, and the second-order viscosity library could no longer say 'viscosity solution'.
- Several moves are only 'optional P8'. Until they are done, SMS's advertised Poincaré separation stays undelivered (library_deliverables.md), and about 1,500 lines of Euler-scheme and Case-2 helpers stay in Path_Space_Operations (RA-path1#8, RA-value2#17). The library scope sentence is therefore false after the mandatory phases.
- cInf_mult_pos, a fact about real infima, goes into the paper's Elliptic_Operator instead of a library. SemiC gets 'HOL-Analysis + sessions Lower_Semicontinuous' instead of parent Lower_Semicontinuous, so LSC is re-checked inside SemiC, and the Equation session lists it again.
- It deletes viscosity_uniqueness_compact, which independent_interest.md keeps as a corollary of 4.2(a) of at most 10 lines: the Dirichlet comparison on an arbitrary compact K.
- Stale in small ways. P0 assumes an uncommitted working tree that is now committed as 0db486f, and P2(a)'s market deletion is already done in 4d5f47e.
- It defers all library-internal re-layering: the CTM/CPS moves, Dyadic_Grids, G-C and G-G. The misplacements of REVIEW_3 §6.3 in CTM and CPS stay where they are.

## Design: PRINCIPLES (afp-first)
1. Every library session must have:
   - a one-sentence scope that never names the paper;
   - no paper prose, no LaiShkolnikovSoner bib entry and no constant of the paper;
   - a parent that it really needs, with no probability parent for analysis.
   A lint check enforces this in every phase. Today 119 lines in 28 library theories and 6 root.bib files mention the paper.
2. Material that the paper states in general form becomes library, and the paper entry only instantiates it. This covers Lemmas 2.2 and 2.3 and Proposition 2.4 for any S, and Section 4 for any geometric F.
3. A heap has one parent. So each AFP entry sits on the heaviest dependency it truly needs, preferably an AFP heap that never changes. Everything else is a 'sessions' import and is re-checked.
4. Library sessions keep natural API that the paper does not use. Deletions remove only clones, abandoned routes and paper-specific material.

SESSION GRAPH. '=' is the parent; '+s' lists 'sessions' imports; * marks an external AFP heap.
- Analytic spine: HOL-Analysis → Lower_Semicontinuous* → Semicontinuous_Analysis → Semiconvex_Functions → Viscosity_Solutions (+s Symmetric_Matrix_Spectra) → Relative_Arbitrage_PDE
- HOL-Analysis → Symmetric_Matrix_Spectra
- Standard_Borel_Spaces* → Semicontinuous_Selection (second session of the Semicontinuous_Analysis entry)
- HOL-Probability → Martingales* → Continuous_Time_Martingales → Wiener_Measure (+s Kolmogorov_Chentsov)
- Probabilistic spine: HOL-Probability → Levy_Prokhorov_Metric* (its heap already contains Standard_Borel_Spaces and Riesz_Representation) → Continuous_Path_Spaces (+s CTM, Kolmogorov_Chentsov, Standard_Borel_Spaces, Semicontinuous_Analysis) → Path_Space_Operations (+s CTM, Disintegration, Semicontinuous_Selection) → Covariation_Control (+s Wiener_Measure, Symmetric_Matrix_Spectra, CTM) → Relative_Arbitrage (+s Relative_Arbitrage_PDE, Viscosity_Solutions, Wiener_Measure, Symmetric_Matrix_Spectra) → Relative_Arbitrage_Statement

The probabilistic chain is the paper's parent, so the analytic chain is re-checked inside Relative_Arbitrage, about 200 s CPU running in parallel. The reverse choice would re-check the Levy_Prokhorov_Metric stack, CTM, Disintegration and the rest, over 1,300 s. One of the two is unavoidable with single-parent heaps, and this is the cheap one.

AFP ENTRIES (directories): Symmetric_Matrix_Spectra, Semicontinuous_Analysis (2 sessions), Semiconvex_Functions (new), Viscosity_Solutions (renamed from Second_Order_Viscosity_Analysis), Continuous_Time_Martingales, Wiener_Measure, Continuous_Path_Spaces, Path_Space_Operations (new), Covariation_Control (new, gated), Relative_Arbitrage (paper entry, 2 sessions). Statement/ stays outside the AFP. Submission order:
1. Semicontinuous_Analysis
2. Semiconvex_Functions
3. Symmetric_Matrix_Spectra
4. Viscosity_Solutions
5. CTM
6. Wiener_Measure
7. CPS
8. Path_Space_Operations
9. Covariation_Control
10. the paper

EXPLICIT DECISIONS
(1) Crandall_Ishii_Sums: keep it as library.
- Rename it Theorem_On_Sums, so the theory that proves the theorem on sums carries the name. Today's Theorem_On_Sums, which states no theorem on sums, becomes Doubled_Jets. Do both renames in one commit.
- Deduplicate its staged and closed set-up (about 300 lines). Delete its local copies of SemiC lemmas. Route its quadratic-penalty dependencies through one-line corollaries of the _gen lemmas. This is verified for doubling_maximiser_exists and tilted_doubled_hessian_nonpositive, and for sums_matrix_inequality in an 8-line proof at real^'n.
- Do not rebase the paper's comparison on it. The rebase is verified feasible, but the live path grows by 300 to 600 lines.
- No paper theory imports it, so it is never re-checked on the Statement path. It is exercised only by the standalone Viscosity_Solutions build, which every phase's CI must therefore run.
(2) Dead market layer: delete all 8 theories (4,901 lines; zero facts used; its relative-arbitrage results are vacuous or axiomatised). Two import lines change (Exit_Class_Limits, Value_Function_Uniqueness) plus about 10 prose references. A short financial-interpretation paragraph moves into the paper's root.tex.
(3) Path toolkit: promote it to the AFP entry Path_Space_Operations. It contains:
- Path_Splicing, Path_Stopping_Times and Path_Law_Pasting (219 of 224 statements pair-free per PLAN_2 §11);
- Path_Martingale_Limits, the generic F-chain: martingale laws with a uniform L² bound are closed under weak convergence.
The toolkit drops its SOVA imports (verified dry run). The 'pair layer' (Pair_Path_Space, Pair_Path_Laws, Path_Law_Sampling) is dissolved:
- generic measurability and exit-time pieces go to CPS;
- QV identifications go to CTM;
- the outerp, onormal and threshold toolkit goes to SMS;
- covariation_class and the aglue/pfut pasting go to Covariation_Control;
- Euler, Case-1/2 and horizon helpers go to the paper.
(4) Probability-free operator and comparison layer: it becomes the paper session Relative_Arbitrage_PDE with parent Viscosity_Solutions. The 16-theory dry run checked with 0 errors once cInf_mult_pos moved. cInf_mult_pos goes to Semicontinuous_Envelopes. Gate G-C then moves the comparison machinery into Viscosity_Solutions as Geometric_Comparison over a locale with the measured interface of about 12 properties: ellipticity, homogeneity, F_*=F=F^* off p=0, F^*(0,0)<1, small-shift bound, rotation/dilation invariance. The paper keeps a roughly 300-line instance stating Theorems 4.2(b), 4.3 and Proposition 4.1. If the gate fails, Section 4 stays in Relative_Arbitrage_PDE, which is already probability-free and checkable in about 1.5 min.
(5) Brownian material in the paper goes to Wiener_Measure:
- the coordinate-independence, cross-variation and X Xᵀ − tI block of Exit_Class_Witness (lines 23–543; three independence proofs become one; bm_coordinates_indep is a 2-line BMC corollary);
- the off-diagonal BM covariation section of Path_Law_Pasting;
- the Brownian fourth moments of Value_Function_Euler_Construction;
- the linearly transformed motion √Σ·B.
The sbmpair pair law becomes the generic class witness in Covariation_Control (any Σ ∈ S). bmpair becomes sbmpair (mat 1) (verified) and its 334-line package goes.
(6) Misplaced material.
- CTM gains:
  - Increment_Moments 1–1975 as Martingale_Moments;
  - Conditional_UI, Stopped_Localization, Pathwise_ and Adapted_Quadratic_Variation (none uses the path space);
  - the QV identifications qvps_eq_A_* from Pair_Path_Space;
  - path-free optional sampling at stopping times, the pre_sigma_of bridge and dyceil from Path_Stopping_Times, plus one Dyadic_Grids theory replacing five constructions;
  - the ksemi lemmas.
- CTM loses:
  - Moment_Bounds (paper Eq. 2.7, dead) and the dead stopped section of Quadratic_Variation;
  - the AFP duplicates martingale_add and martingale_diff;
  - bm_prj_measurable (= borel_measurable_nth);
  - the independence toolkit (to WM) and cInf_mult_pos (to SemiC);
  - the Laplace helpers, and all paper prose.
- CPS loses all of that and the dead 2,353-line Path_Tightness chain. It gains box_of_sequential, the generic path measurability API, the exit-time semicontinuity block and a generic ball exit time replacing pball_exit. G-E removes the hard-wired 8C² constant.
- SMS gains the general Courant–Fischer bound and Poincaré separation it advertises (from Operator_Formula), outer products, orthonormal Parseval, threshold selection, projectors, rank-1 projections and column square roots. It loses its non-spectral calculus (to Viscosity_Solutions.Second_Order_Calculus) and two paper lemmas.
- SemiC is rebased on Lower_Semicontinuous. Semicontinuous_Selection, the only probabilistic theory, becomes its own session.

PAPER ENTRY SHAPE
- Relative_Arbitrage_PDE: Eqs. (1.4)–(1.9), Lemma 2.1, Lemma 3.2, the envelopes, Definition 3.1 as bridge equations to the generic predicates (not abbreviations, after PLAN_2's divergence lesson), the explicit Example 3.1 solution, and Section 4.
- Relative_Arbitrage: exit_class/exit_val/xclass/xval as instances S = sconstraint k L with their bridges, the Section 3 sub/supersolution proofs, Example 3.1, and theorem_1_1, now stated here in the paper's hypothesis structure (G-A) instead of in a hidden Statement_Auxiliary.
- The Statement still states Theorem 1.1 for xval and xclass, whose definitions stay textually unchanged in the paper entry.

NOT DONE (deliberately)
- No CIS rebase.
- No G10 standing-hypotheses locale (measured not worth it).
- No outerp abbreviation (it diverged before).
- CTM is not split (one session is the right granularity per CTM#23).
- No repo-only aggregation heap, which would break AFP-readiness.

### Summary

The afp-first design has 9 library AFP entries (10 sessions), a 2-session paper entry and the unchanged acceptance session. Library sessions say nothing about the paper. The development shrinks from 120.6k to about 85.6k lines. The paper entry (Relative_Arbitrage_PDE + Relative_Arbitrage) shrinks from 65k lines in 55 theories to about 15k lines in 18 theories. That figure assumes both gated generalisations land: G-B, the class and DPP over an abstract constraint set S, and G-C, comparison for an abstract geometric operator. If both gates fail, the paper entry is about 33k lines.

Decisions:
- Crandall_Ishii_Sums is kept as the library's headline Theorem_On_Sums, but off the paper's path.
- The market layer is deleted.
- The path toolkit becomes the AFP entry Path_Space_Operations.
- The probability-free layer becomes the paper session Relative_Arbitrage_PDE (parent Viscosity_Solutions), with its comparison machinery pushed into the library if the G-C gate passes.
- Brownian material moves to Wiener_Measure.
- Misplaced material goes to CTM, CPS, SMS and SemiC as listed.

Continuous_Path_Spaces is rebased on Levy_Prokhorov_Metric and HOL-Complex_Analysis is dropped. This removes most of today's 882 s re-check in the CPS build. Re-check CPU on the Statement path falls from 1,533 s to about 780 s. The user-theory critical path falls from 577 s to about 285 s. A paper-only rebuild falls from 9:41 to about 3 min.

There are 11 phases, P0 to P10. Each ends with a green build of Relative_Arbitrage_Statement and standalone builds of every touched library session. The cheap, verified wins come first: deletions, the 69-line ess_inf proof, clone one-liners and parent switches. The two large generalisations come last, each gated with a fallback.

### Sessions

| session | parent | sessions imports | scope |
|---|---|---|---|
| `Symmetric_Matrix_Spectra` | HOL-Analysis |  | Spectral theory of real symmetric matrices: trace/transpose calculus, quadratic forms, outer products and orthonormal families, the spectral theorem, Ky Fan sums and ordered eigenvalues with their Lipschitz continuity, Courant-Fischer bounds, Poincare separation, Householder rotations and orthogonal projections. |
| `Semicontinuous_Analysis` | Lower_Semicontinuous |  | Upper and lower semicontinuity of real functions on metric spaces: attainment, bounded extension, semicontinuous envelopes globally and relative to a closed set, scaling of infima, and Berge's maximum theorem. |
| `Semicontinuous_Selection` | Standard_Borel_Spaces |  | A Borel-measurable selection of maximisers of an upper semicontinuous payoff over compact sections of a Polish space. |
| `Semiconvex_Functions` | Semicontinuous_Analysis |  | Almost-everywhere differentiability theory behind second-order analysis: subgradients, Rademacher's theorem, Moreau envelopes, Alexandrov's theorem for semiconvex functions, Jensen's lemma, and sup-convolutions of semicontinuous functions. |
| `Viscosity_Solutions` | Semiconvex_Functions | Symmetric_Matrix_Spectra | Second-order viscosity solutions of degenerate elliptic equations for an arbitrary operator: second-order calculus, test functions and jets, generic sub/supersolution predicates with touching on a set, doubling of variables with general penalties, soft penalties, the Crandall-Ishii theorem on sums, and (gated) comparison for positively homogeneous geometric operators with zero boundary data on expandable compact sets. |
| `Continuous_Time_Martingales` | Martingales |  | Continuous-time martingales beyond the Martingales entry: dyadic grids, Doob's maximal inequality, optional sampling and stopping at bounded stopping times, quadratic variation pathwise and adapted with its compensator, fourth-moment bounds from a bounded covariation rate, Vitali's theorem and uniform integrability, semidirect kernels, transfer of the martingale property, and the essential infimum. |
| `Wiener_Measure` | Continuous_Time_Martingales | Kolmogorov_Chentsov | Brownian motion as the projective limit of Gaussian finite-dimensional distributions with a continuous modification, and the n-dimensional and linearly transformed Brownian motion with independent increments, martingale, cross-variation and quadratic-covariation identities. |
| `Continuous_Path_Spaces` | Levy_Prokhorov_Metric | Continuous_Time_Martingales, Kolmogorov_Chentsov, Standard_Borel_Spaces, Semicontinuous_Analysis | The space of continuous paths C([0,T],'b) as a Polish space: portmanteau and continuous mapping, Kolmogorov-type tightness from increment moment bounds, path measurability, and first exit times of closed sets with their semicontinuity under weak convergence of laws. |
| `Path_Space_Operations` | Continuous_Path_Spaces | Continuous_Time_Martingales, Disintegration, Semicontinuous_Selection | Cutting, shifting, stopping and gluing continuous paths at stopping times and the same operations on path laws: regular conditional distributions on path space, kernel pasting, and the martingale property under these operations and under weak limits. |
| `Covariation_Control` | Path_Space_Operations | Wiener_Measure, Symmetric_Matrix_Spectra, Continuous_Time_Martingales | Laws of continuous martingales whose quadratic covariation has a density in a prescribed closed, convex, bounded set of positive semidefinite matrices: weak compactness of the class, upper semicontinuity of the largest essential-infimum exit time from a closed set, existence of measurable optimal laws, and the dynamic programming principle on finite and infinite horizons. |
| `Relative_Arbitrage_PDE` | Viscosity_Solutions | Symmetric_Matrix_Spectra, Semicontinuous_Analysis | Paper entry, probability-free half: the constraint set and the operator F of Eqs. (1.4)-(1.9), Lemma 2.1, Lemma 3.2, the envelopes, Definition 3.1, the explicit solution of Example 3.1, and Section 4 (Theorems 4.2(b), 4.3, Proposition 4.1). |
| `Relative_Arbitrage` | Covariation_Control | Relative_Arbitrage_PDE, Viscosity_Solutions, Wiener_Measure, Symmetric_Matrix_Spectra | Paper entry, probabilistic half and assembly: the class (1.7) and value (1.6) as the instance S = sconstraint k L, the viscosity sub- and supersolution properties of the value function (Section 3), Example 3.1, and Theorem 1.1 in the paper's hypothesis structure. |
| `Relative_Arbitrage_Statement` | Relative_Arbitrage |  | Acceptance test, not an AFP entry: Theorem 1.1 and Example 3.1 for the paper's own xval and xclass, with every definition they mention, plus the faithfulness readings. |

### Deletions

- Market layer, all 8 theories (4,901 lines; zero facts used; results vacuous or axiomatised): Volatile_Market, Ito_Market, Brownian_Market, Optimal_Exit_Time, Brownian_Optimal_Boundary, Value_Function_Market, Path_Tightness_Market, Exit_Time_Semicontinuity. Imports in Exit_Class_Limits and Value_Function_Uniqueness and about 10 prose references to be fixed.
- Empty theories: Comparison_Jets (48 lines) and Dynamic_Programming_Optional_Sampling (33).
- Statement_Auxiliary: 7 dead re-exports. The 7 used ones become the paper's Theorem_1_1 theory.
- Laplace-transform route in Path_Exit_Times (789 lines), plus 105 lines of the old ess_inf_pexit_usc body and Integrability_Criteria.exp_neg_time_* (51). Replaced by the verified 69-line proof; total -947.
- Dead RA strands. Section 2 and 3 side: simple-stopping-time kernel route in Dynamic_Programming_Kernels (1,059); ball-version Euler chain plus the plain (non-envelope) Case 1 (~1,600); deterministic-time quadratic subsolution chain and ell_op_s (822); tanSF clamped field; stopping-time kernel scaffolding in Path_Stopping_Times (785) and Path_Law_Pasting (428).
- Dead RA strands. Section 4 and ball side: smooth ball strand (Viscosity_Ball, the refuted comparison_principle locale of Viscosity_Comparison_Interface, 9 of 11 Ball_Solution facts); quadratic-penalty route to Theorem 4.2(a) and the compact-uniqueness branch theorem_1_1_uniqueness_general (Comparison_Principle 1,281, Comparison_Localisation 722, Comparison_Strictness 467, of which ~1,740 lines are exclusive). Theorem 4.2(a) is first attempted as a corollary of comparison_two_domain, with a 150-line budget.
- Library dead code (clones, abandoned routes, paper-specific material only): Path_Tightness projective-limit, continuous-modification (duplicates AFP Kolmogorov_Chentsov) and scalar-tightness chains (2,353); dead part of Stopped_Localization (410) and of Pathwise_Quadratic_Variation (315); Increment_Tails fragment (merged).
- Library dead code in CTM, WM and SemiC: Moment_Bounds (paper Eq. 2.7, dead); Quadratic_Variation stopped-martingale section (300); Sorted_Lists (fragment); duplicate increment-independence and martingale-square proofs in Wiener_Measure; type-class Berge copy.
- Library dead code in SOVA: the old generic Viscosity_Solutions layer and its 5 _eq_gen bridges (replaced by the G-G version); quadratic-penalty copies in Doubling_Of_Variables/Theorem_On_Sums (become one-line corollaries of the _gen lemmas, ~1,400 lines of twins); dead Rademacher/Alexandrov/Sup_Convolution copies.
- Library duplicates replaced by distribution or AFP facts (5 verified one-liners): Covariation_Density.lipschitz_imp_absolutely_continuous_on, Exit_Class_Witness.bm_coordinates_indep (becomes a 2-line BMC corollary), Martingale_Algebra.martingale_add/martingale_diff, Path_Tightness.continuous_map_real_diff, Doubling_Of_Variables.norm_Pair_le (shadows HOL's).
- Library duplicates found by the matcher: bm_prj_measurable, prob_space_pair_measure, integral_of_bounded_linear, trace_diff_matrix, inner_sum_scaleR_Basis, abs_norm_diff_le, norm_Pair_left/right_zero, and the 8 Matrix_Algebra distributivity lemmas.
- Internal clones, re-derived in PIDE: exit_val_boundary_zero (5 lines), diffquot_all_of_rational (1), exit_val_visc_subsol (1), exit_val_attained (5), feasible_scale and feasible_scaleR_p, ell_op_scaleR_p, ell_op_scaleR_matrix, Exit_Class.outerp_eq_outer_prod (name clash), the bmpair package (334 lines, becomes sbmpair (mat 1)), doubling_maximiser_exists, tilted_doubled_hessian_nonpositive.
- Proof-level twins collapsed by refactoring (estimates, not verified): X vs compensated process in Path_Law_Sampling and the DPP (~1,500 net); coordinate weak-limit chain replaced by the generic F-chain (~1,000); ball vs region Euler limit chain (dead side); tanp/uvec as the P = mat 1 instance of tanpU/uvecV (~500); sup-convolution attainment (4 proofs to 1); five dyadic grids to one; six 'approach t from below' copies to one lemma.
- NOT deleted, explicitly: Crandall_Ishii_Sums (kept as the library's Theorem_On_Sums); faithfulness evidence (rooted in Paper_Readings first); general path_rcd/path_rcd_ksemi and general increment independence (library API; the used special cases become corollaries).
- Hygiene: notes/restructuring_2/__pycache__/thy_parse.cpython-314.pyc (tracked by git); stale entries in notes/UNUSED_THMS.md and notes/OPEN_ITEMS.md; 168 'X lives in Y' pointer texts; the LaiShkolnikovSoner entry in the 6 library root.bib files.

### Phases

**P0. Guard rails (no structural change)**

- Add to Paper_Readings, as dead-code roots, every piece of faithfulness evidence: eigen_lb_iff_eigval_ge, lemma_2_1_exact, poincare_separation, convex_expandable, paper_class_marginal/lift, theorem_1_1_strong (60 lines, verified), ell_op_sym_part (25), literal_reading_keeps_identity.
- Fix the wrong prose of REVIEW_3 §1.2(b)-(f): literal reading, singular part, 'k smallest eigenvalues', 'Eq. (1.10)', DPP 'proved in full', the NOTES_FOR_AUTHORS claims.
- Add a check script, run in every phase: (1) build Relative_Arbitrage_Statement; (2) build every repo session standalone (`isabelle build -d . -D .`), because CIS and the library heaps are not exercised by the Statement path; (3) Thm_Deps.all_oracles of the deliverables must be []; (4) the prop of theorem_1_1 and example_3_1_closed_form must be aconv to stored terms; (5) a lint over library dirs for LaiShkolnikovSoner/arXiv/'Eq. (', 'Lemma 2.', 'Theorem 1.1', paper constants; (6) re-run notes/review_3 scripts (dead code, placement, critical path) and record the metrics.
- *risk*: Low. Only additions and prose.
- *validation*: Statement green; oracles []; baseline metrics recorded: 120,625 lines, critical path 577 s, re-check 1,533 s, lint baseline 119 lines in 28 library theories.
- *est_effort*: S (2-3 builds)

**P1. Delete dead weight that needs no moves**

- Delete the 8 market theories, Comparison_Jets and Dynamic_Programming_Optional_Sampling.
- Drop the imports: Exit_Class_Limits of Exit_Time_Semicontinuity; Value_Function_Uniqueness of Value_Function_Market and Exit_Time_Semicontinuity; Exit_Class of Ball_Solution; Covariation_Density of Exit_Class; Exit_Class_Infinite of Dynamic_Programming_Assembly (it needs only Exit_Class_Pasting).
- First move `declare transpose_matrix_vector [simp del]` out of Viscosity_Comparison_Interface into the theories that need it, then delete VCI's dead strand.
- Rewrite the about 10 prose references to market theories.
- *risk*: Low to medium. Hidden notation or simp declarations in deleted theories are invisible to the fact-level analysis. The global simp del leak can change downstream simp behaviour.
- *validation*: Check script green. theorem_1_1 prop aconv. Closure of the deliverables unchanged in size. RA -5.0k lines. Critical path about 577 → 545 s, since Path_Tightness_Market and Exit_Time_Semicontinuity leave the chain.
- *est_effort*: S (3-5 builds)

**P2. Verified drop-ins and build plumbing**

- Swap in the 69-line ess_inf_pexit_usc proof and delete the Laplace route (-947).
- Apply the 12 verified clone derivations and the 5 library one-liners (-~900, incl. bmpair = sbmpair (mat 1)).
- Drop the Sup_Convolution/Doubling_Of_Variables imports of Pair_Path_Space and the Vitali/Brownian_FDD imports (verified dry run; 1 text line).
- Equicontinuity: local Arzela-Ascoli copy (~180 lines, attributed); drop HOL-Complex_Analysis from the CPS ROOT.
- ROOT parents: Continuous_Path_Spaces = Levy_Prokhorov_Metric + sessions CTM, KC, SBS, SemiC; Continuous_Time_Martingales = Martingales; Wiener_Measure = CTM + sessions KC.
- Semicontinuous_Analysis = Lower_Semicontinuous, with Semicontinuous_Selection split into its own session (parent Standard_Borel_Spaces) in the same directory; cInf_mult_pos moves to Semicontinuous_Envelopes.
- *risk*: Low to medium. The proofs are verified. The parent switches can surface qualified-name or session-namespace errors, and a one-off Levy_Prokhorov_Metric heap build is needed (~620 s CPU).
- *validation*: Check script green; standalone builds of CTM, WM, CPS, SemiC and Selection. CPS re-check 882 s → ≤230 s. Toolkit has no SOVA ancestor (ML ancestor check). Critical path → ~430 s.
- *est_effort*: M (6-10 builds)

**P3. Rooted dead-code pass**

- Re-run the closure with the P0 roots.
- Delete RA dead strands: DP_Kernels route, ball Euler chain and plain Case 1, deterministic quadratic subsolution and ell_op_s, ball/VCI strand, tanSF, path-layer kernel scaffolding, dead Statement_Auxiliary re-exports, dead class lemmas.
- Theorem 4.2(a): try a faithful corollary of comparison_two_domain with a 150-line budget; whatever the outcome, delete the quadratic route and the compact-uniqueness branch (~1,740 exclusive lines), and record the result in NOTES_FOR_AUTHORS.
- Library: apply the dead-code policy (delete clones, abandoned routes and paper-specific code; keep natural API). This removes Path_Tightness' dead chain, Moment_Bounds, the QV stopped section, Sorted_Lists, the dead parts of SL/PQV and SOVA copies. CIS and its closure are kept.
- *risk*: Medium. Faithfulness evidence could be deleted (mitigated by the P0 roots). Simp-set changes. Deleting something a later phase wanted (mitigated: the placement table is consulted first).
- *validation*: Check script green; Paper_Readings green; lint unchanged or better; total about -18k lines; paper session about 58k → 42k.
- *est_effort*: M (8-12 builds, one theory cluster per commit)

**P4. Analytic libraries re-laid out**

- Split SOVA into Semiconvex_Functions (6 theories, parent SemiC) and Viscosity_Solutions (renamed directory, parent Semiconvex_Functions, sessions SMS).
- Renames: Theorem_On_Sums → Doubled_Jets, then Crandall_Ishii_Sums → Theorem_On_Sums, in one commit. Split DoV at l.4052 and l.5107. Create Second_Order_Calculus from the Matrix_Algebra analysis and the DoV helpers.
- Make the quadratic-penalty lemmas corollaries of _gen (verified pattern). Consolidate sup-convolution in Sup_Convolution. Deduplicate CIS.
- G-G: rewrite Viscosity_Solutions with predicates covering env2/C2. The paper's predicates get bridge equations, not abbreviations.
- SMS: split Matrix_Algebra into Matrix_Basics, Quadratic_Forms and Linear_Maps_As_Matrices. Move in the outerp family, the onormal/threshold toolkit, the Courant-Fischer bound and general Poincare separation, and the Orthogonal_Projections material. Delete the clones.
- SemiC: absorb usc copies, tilted_local_touching and lsc_envK_cong.
- Purge paper prose and bib entries from these four entries.
- *risk*: Medium. Moved prose antiquotations break (PLAN_2: ~160). Renamed theory names collide mid-migration. The PDE layer imports Matrix_Algebra and DoV by name, so its imports must be updated in the same commits.
- *validation*: Check script green; standalone builds of SMS, SemiC, Semiconvex_Functions and Viscosity_Solutions (CIS included); lint clean for these four; Matrix_Algebra's 72 s theory is replaced by three that check in parallel.
- *est_effort*: L (15-25 builds)

**P5. Paper PDE session**

- Create Relative_Arbitrage_PDE (parent Viscosity_Solutions) in the Relative_Arbitrage directory with the 16-theory layer (dry run verified).
- Renames: Curvature_Operator → Elliptic_Operator, Constraint_Set_Convexity → Constraint_Set.
- Merges: Operator_Continuity into Operator_Formula; Viscosity_Ball into Ball_Solution.
- Move sconstraint/Pi_proj/closed_eigen_ub from Exit_Class into Constraint_Set.
- Requalify the 24 @{theory Relative_Arbitrage.X} antiquotations.
- RA = CPS + sessions RA_PDE, Viscosity_Solutions, WM, SMS, Disintegration, Semicontinuous_Selection.
- *risk*: Low to medium (verified dry run; the remaining risk is mechanical).
- *validation*: RA_PDE builds standalone in ~1.5 min; ML ancestor check has no HOL-Probability/CTM/CPS ancestor; check script green.
- *est_effort*: M (4-6 builds)

**P6. Probabilistic libraries re-laid out (CTM, WM, CPS)**

- CTM gains: Martingale_Moments (Increment_Moments 1-1975), Conditional_UI, Optional_Stopping (Stopped_Adaptedness + Stopped_Localization), PQV, AQV and the QV identifications; Dyadic_Grids; path-free optional sampling, the pre_sigma bridge and the ksemi lemmas.
- CTM loses: the independence toolkit (to WM) and paper prose.
- WM gains the Brownian block of Exit_Class_Witness, the off-diagonal covariation, Brownian fourth moments and sqrt(Sigma)B.
- CPS gains the generic path measurability API, the exit-time semicontinuity block, the generic ball exit time and Difference_Quotients. G-E: generic moment constant and one tightness theorem.
- *risk*: Medium to high. Largest move volume. G-E changes statements used downstream. Increment_Moments has 13 statements repeating two hypothesis bundles, which should become a locale.
- *validation*: Check script green; standalone builds of CTM, WM and CPS; the CPS build re-checks ≤140 s; lint clean for the three entries.
- *est_effort*: L (15-20 builds)

**P7. Promote Path_Space_Operations**

- Make sorts uniform ({polish_space,banach}) across the already widened statements (PLAN_2 §11 lesson).
- Move Path_Splicing, Path_Stopping_Times and Path_Law_Pasting into the new session with parent CPS.
- Create Path_Martingale_Limits from the F-chain.
- Move the 5 pair-specific statements to Covariation_Paths/paper.
- Paper parent becomes Path_Space_Operations.
- *risk*: Medium. A widening can turn a terminating proof into a divergent search; build with -o timeout=900.
- *validation*: Gate: ≥95% of PSO statements pair-free (today 219/224 in the three core theories). PSO standalone; check script green; lint clean.
- *est_effort*: M (6-10 builds)

**P8. G-C: comparison over an abstract geometric operator (gated)**

- Introduce the Geometric_Operators locale from the measured interface (ell_op_bdd_below, elliptic_le, lsc/usc off zero, M_gap, lsc_at_zero, usc_conj_rot, usc_eq_at_nonzero, usc_ge_one_limit, usc_scale, small_shift_lt_one, zero_zero_lt_one, mgap_shift_id).
- Replace the 2 raw unfoldings (ell_op_def, feasible_def) by locale properties.
- Move the live Comparison_* into Viscosity_Solutions.Geometric_Comparison and expandable into Expandable_Sets.
- Write the paper's Comparison instance (~300 lines).
- *risk*: Medium to high. The interface may grow, and the 2 raw unfoldings may hide real dependence on the feasible-set structure.
- *validation*: Gate: ≤15 locale assumptions, each discharged by an existing ell_op lemma or ≤50 new lines; else revert and keep Section 4 in RA_PDE. If passed: Viscosity_Solutions standalone, RA_PDE green, check script green, paper -2.5k net.
- *est_effort*: L (10-15 builds)

**P9. G-B: Covariation_Control (gated)**

- Define exit_class as covariation_class (sconstraint k L) (reader RA-class#2). Replace the 56 'unfolding exit_class_def' by the projection/intro rules.
- Migrate the 15 class/DPP theories bottom-up to an abstract S (closed, convex, bounded, ⊆ psd, nonempty). Thread `closed S` through closedin_diffquot_constraint for the 4 lemmas that resisted in PLAN_2.
- Generic witness via sbmpair Sigma.
- Collapse the X/compensated twins.
- State Proposition 2.4 as an equality.
- Move the result into Covariation_Control with parent PSO. The paper keeps exit_class/exit_val/xclass/xval with their original definitions and bridges, so the Statement does not change.
- *risk*: High. Largest refactor (~215 consumers); divergent simp under generalisation; the 4 known resisting lemmas.
- *validation*: Gate after the class layer (Limits..Exit_Value): if the DPP layer still needs >10 sconstraint-specific facts, stop and keep the DPP in a paper session Relative_Arbitrage_Class (parent PSO). Otherwise: Covariation_Control standalone, lint (no sconstraint/ell_op/exit_class constants), theorem_1_1 aconv, check script green, paper about -14k.
- *est_effort*: XL (30-40 builds, one theory per commit)

**P10. Paper entry final shape and documents**

- Renames: Value_Function_Supersolution_Case_1 → Value_Function_Euler_Limits, Case_2 → Value_Function_Supersolution (absorbing Value_Function_Assembly), Exit_Class_Marginals → Paper_Class_Marginals.
- Split Example_3_1 off; create the Theorem_1_1 theory with the assembly and the faithful theorem_1_1 (G-A). The Statement displays it, and the old statement is re-derived in one line as a regression check.
- Delete Statement_Auxiliary.
- Update the ROOTS file, descriptions, every root.tex and NOTES_FOR_AUTHORS, and the AFP metadata.
- *risk*: Low. The displayed Statement changes only by strengthening, and the user must approve that.
- *validation*: Check script green; document builds of all 13 sessions; lint 0; final metrics against P0.
- *est_effort*: M (4-6 builds)

### Quantified effects

Sources: measured per-theory times and line counts (build log, bf_lines.tsv, dead_code_by_theory.txt). Target figures come from a proportional model, a scratch script (afp_first_model.py, not kept): each target theory takes N lines from named sources, and its CPU is scaled from the source theory's seconds per line. Expect about ±20% on lines and ±30% on time.

LINES
- Total: 120,625 → ~85,600 (-35,000, -29%). Breakdown:
  - about -26k dead code (review's 31k less the 0.7k overcount in the market layer, CIS kept 2.5k, faithfulness evidence and library API kept ~1.6k);
  - about -8k clone and twin collapse;
  - -1.7k verified drop-ins;
  - +1.4k new code (G-B/G-C interfaces, Prop. 2.4, faithful theorem, faithfulness roots).
- Paper entry (Relative_Arbitrage + Relative_Arbitrage_PDE): 64,967 lines / 55 theories → ~15,000 / 18 (RA_PDE 4,903, RA 10,101; -77%). Fallbacks: if G-C fails ~17,500; if G-B fails ~30,300; if both fail ~32,800. The Statement goes from 667 to ~580.
- Library: 55,658 lines in 6 sessions → ~70,600 in 10 sessions / 9 AFP entries:
  - SMS 7,060
  - SemiC 1,383 and Selection 749
  - Semiconvex 5,826
  - Viscosity 12,759 (9,190 without G-C)
  - CTM 12,078
  - WM 3,634
  - CPS 5,979
  - PSO 5,240
  - Covariation_Control 15,289
- Paper mentions in library sessions: 119 lines in 28 theories plus 6 root.bib entries → 0, lint-enforced.
- Statements in the paper session that name no paper constant: today 425 (349 of them in the toolkit) → about 0 outside the bridge lemmas.

RE-CHECKED THEORIES PER BUILD (sessions not ancestors; theory-time CPU)
- Today, on the Statement path: CTM 2.8k lines / 90 s; CPS 33.9k / 882 s (Riesz 268, HOL-Complex_Analysis 226, SBS 178, LPM 150, KC 34, SemiC 26); RA 40.3k / 561 s. Total 77.0k lines / 1,533 s.
- Target: CPS 5.1k / 134 s (Martingales 90, CTM 8, KC 34, SemiC 3); PSO 18.0k / 277 s (CTM remainder 101, Disintegration + S_Finite 169, Selection 6); Covariation_Control 9.7k / 171 s (WM 41, KC 76, needed SMS ~54); RA 24.2k / 201 s (RA_PDE 41, Viscosity minus CIS 68, Semiconvex 42, SemiC 20, Lower_Semicontinuous 30). Total ~57k lines / ~780 s: -26% lines, -49% CPU.
- Rebuild after a paper-only change: re-check 561 s → ~201 s, own theories 626 s → ~86 s.
- Re-check stays at about 2/3 of CPU because there are more AFP boundaries. Each library theory is still checked only once per Statement build; the waste is confined to incremental rebuilds of a downstream session.
- One-off cost: the Levy_Prokhorov_Metric heap, ~620 s CPU, ~6 min.

CRITICAL PATH (sum of theory times along the longest import chain, as in DATA_BRIEF)
- 577 s over 35 theories today (418 s over 24 if imports were minimal) → ~285 s over 27 in the target. The chain is Equicontinuity → Path_Space → Path_Exit_Times → PSO (3) → Covariation_Class chain (8) → DPP (4) → Paper_Class → VF (5) → Theorem_1_1 → Statement.
- Matrix_Algebra → Theorem_On_Sums → Doubling_Of_Variables leaves the head of the chain, and the market layer leaves the middle.
- The PDE half has its own critical path of ~100 s over 13 theories and is checkable without probability.
- Total theory CPU of user theories: 1,124 s → ~790 s. Statement-path build CPU (own + re-check): ~2,370 s → ~1,140 s.

WALL CLOCK (3 threads, AFP heaps prebuilt)
- isabelle build Relative_Arbitrage_Statement from scratch: 18:43 (CTM 1:37, CPS 7:25, RA 9:00, Statement 0:41) → ~11 min (CPS ~2:10, PSO ~3:20, Covariation_Control ~2:55, RA ~2:20, Statement ~0:20).
- Paper-only change: 9:41 → ~2:40.
- Section-4-only feedback: 9:41 → ~1.5 min (RA_PDE standalone).

PER PHASE (paper-entry lines / critical path)
- P1: 65.0k → 60.1k; 577 → ~545 s
- P2: → ~58.4k; ~430 s; CPS re-check 882 → ~230 s
- P3: → ~42k; ~380 s
- P4–P6: → ~38k
- P7: → ~32k
- P8: → ~29k
- P9: → ~15k; ~285 s
- P10: ~15k

### Risks and open questions

- G-B (P9) is the largest and least certain step: about 215 consumers in 15 theories, 4 lemmas that already resisted, and the risk of divergent simp after generalisation. Mitigation: a gate after the class layer, one theory per commit, -o timeout=900, uniform sorts. Fallback: the DPP stays in a paper session Relative_Arbitrage_Class (parent Path_Space_Operations); the paper entry is then ~30k lines and the library loses one entry.
- G-C (P8) is evidenced only by a measured interface of 23 facts, ~12 properties and 2 raw unfoldings, not by a dry run. The gate is ≤15 assumptions; the fallback keeps Section 4 in Relative_Arbitrage_PDE, which is probability-free either way.
- Open question for the user: may a library AFP entry cite the paper as the source of a result it states in general form (Lemmas 2.2/2.3 and Prop. 2.4 in Covariation_Control, Section 4 in Geometric_Comparison)? The stated constraint forbids any mention, and AFP editors and authors may prefer attribution.
- Open question for the user: the Statement's displayed theorem_1_1 changes in P10 to the faithful hypothesis structure (G-A, strictly stronger, verified in 60 lines). The old form is kept as a one-line corollary. Please confirm that the acceptance test may be strengthened this way.
- Open question for the user: Theorem 4.2(a) is dead, weaker than the paper and reached by a ~1,740-line exclusive branch. The plan tries a faithful corollary of comparison_two_domain within 150 lines and deletes the branch in any case. Is a missing 4.2(a) acceptable if that attempt fails?
- More AFP boundaries keep re-check at about 2/3 of build CPU even though absolute CPU halves. Merging Path_Space_Operations into CPS would not reduce it, because the re-check only moves. CTM is checked twice in a multi-session build (its own heap for WM, and re-checked in CPS/PSO); this is accepted for scope cleanliness.
- The Levy_Prokhorov_Metric parent for CPS needs a one-off ~6 min heap build, and AFP version bumps rebuild it. CPS still imports CTM for etime and ess_inf_time, and that is how ~90 s of Martingales gets re-checked in CPS.
- Moving prose breaks antiquotations: about 160 broke in PLAN_2, and 24 @{theory Relative_Arbitrage.X} are known for the PDE split. Every move needs a requalification pass and a standalone build of both the source and the target session.
- Hidden notation, abbreviations and simp declarations are invisible to the fact-level analyses. The global `declare transpose_matrix_vector [simp del]` in Viscosity_Comparison_Interface must be relocated before that theory is thinned. Market-layer deletions may expose similar leaks.
- Crandall_Ishii_Sums, kept as library, is exercised only when Viscosity_Solutions is built standalone, since no paper theory imports it. The check script must build every repo session (-D .), not just the Statement, or CIS rots silently.
- The dead-code policy for libraries is a judgement call: delete clones, abandoned routes and paper-specific code; keep natural API. Wrong calls either keep weight or remove useful API. The placement and closure scripts must be re-run with the Paper_Readings roots before every deletion batch.
- The two theory renames (Theorem_On_Sums → Doubled_Jets, Crandall_Ishii_Sums → Theorem_On_Sums) are confusing in history. Do them in one commit with an explicit note.
- All size and time figures for the target are model estimates (±20% lines, ±30% time). Refactor savings for proof-level twins (X vs compensated ~1,500 net, coordinate chain ~1,000, tanp ~500) come from reader estimates and are not verified.
- AFP logistics: 9 interdependent library entries must be submitted in dependency order and maintained together, which is a release-time burden. Session names were checked for collisions against /opt/afp/thys and none were found.

## Design: BUILD-FIRST LAYOUT ("chain with a library base, probability-free PDE sibling")

Principles, from the measurements:
(1) Isabelle rebuilds whole sessions. Re-checking a non-ancestor costs nothing extra only when the host session is rarely rebuilt. So every re-check moves into sessions that do not change during paper work (an AFP heap, CPS, or a repo-local base). The sessions people edit often (Class, Relative_Arbitrage, Statement) re-check almost nothing.
(2) Re-checks that sit upstream of a session's own theories land on its critical path (CP). Today RA's CP starts with Lemmas_SFMM -> Kernels -> Disintegration (169 s) and the SMS chain before Pair_Path_Space. The base heap removes them from every paper CP.
(3) Long serial chains belong in their own sessions below the paper: the toolkit (170 s serial) and the class/DPP chain (~140 s). Editing a value-function theory then rebuilds about 90 s of serial work, not 614 s.
(4) The operator/comparison layer is probability-free (dry run, 0 errors), so it becomes a sibling session on SOVA. Its heap and its PIDE logic need no probability at all. The paper's top session re-checks it (~8k lines, ~55 s CPU, ~40 s CP, mostly parallel to the V chain). This beats putting it in the chain: Class edits stay cheap and PDE edits do not rebuild Class.
(5) Every library session has an AFP-honest parent: a session it really builds on. The one exception is deliberate: Path_Space_Operations sits on the repo-local base. Its AFP form is a one-line parent swap.

Session graph (* = on the Statement build path; everything else is built only by `-g extras`, CI-all or for PIDE logics):
HOL-Analysis -> Symmetric_Matrix_Spectra -> Second_Order_Viscosity_Analysis -> Relative_Arbitrage_PDE   (probability-free sibling)
                                      \-> Crandall_Ishii (leaf, extras)
HOL-Analysis -> Lower_Semicontinuous[AFP] -> Semicontinuous_Analysis
HOL-Probability -> Martingales[AFP] -> Continuous_Time_Martingales -> Wiener_Measure
HOL-Probability -> *Levy_Prokhorov_Metric[AFP heap, cacheable] -> *Continuous_Path_Spaces -> *Relative_Arbitrage_Base (repo-local, no own theories; loads SMS, SemiC, SOVA, CTM, WM, KC, Disintegration once) -> *Path_Space_Operations -> *Relative_Arbitrage_Class -> *Relative_Arbitrage (+ re-checks Relative_Arbitrage_PDE) -> *Relative_Arbitrage_Statement
                                                                                                                                                      \-> Relative_Arbitrage_Extras (leaf, extras)

ROOT sketches (key lines):
  session Relative_Arbitrage_Base in "Relative_Arbitrage_Base" = Continuous_Path_Spaces + options [document = false]
    sessions Symmetric_Matrix_Spectra Semicontinuous_Analysis Second_Order_Viscosity_Analysis Continuous_Time_Martingales Wiener_Measure Kolmogorov_Chentsov Disintegration
    theories "Symmetric_Matrix_Spectra.Poincare_Separation" "Symmetric_Matrix_Spectra.Householder_Rotation" "Semicontinuous_Analysis.Semicontinuous_Envelopes" "Semicontinuous_Analysis.Berge" "Second_Order_Viscosity_Analysis.Viscosity_Solutions" "Continuous_Time_Martingales.Martingale_Transfer" "Continuous_Time_Martingales.Natural_Filtration" "Continuous_Time_Martingales.Semidirect_Kernels" "Continuous_Time_Martingales.Modification_Transfer" "Wiener_Measure.Continuous_Brownian_Motion" "Disintegration.Disintegration"   (the same pattern as HOL-Proofs = Pure + theories "HOL-Library.Realizers"; the rule is that every library theory a paper or toolkit theory imports is listed here)
  session Path_Space_Operations = Relative_Arbitrage_Base + sessions Symmetric_Matrix_Spectra Semicontinuous_Analysis Continuous_Time_Martingales Disintegration theories Pair_Path_Space ... Path_Law_Sampling
     (AFP form: "= Continuous_Path_Spaces +", the same sessions line)
  session Relative_Arbitrage_PDE = Second_Order_Viscosity_Analysis + sessions Semicontinuous_Analysis theories Constraint_Set ... Comparison_Two_Domain
  session Relative_Arbitrage_Class = Path_Space_Operations + sessions Relative_Arbitrage_PDE Wiener_Measure theories Exit_Class ... Dynamic_Programming_Assembly
     (it loads only Relative_Arbitrage_PDE.Constraint_Set. Isabelle2026's sources digest covers only the files a session loads (Build/sessions.scala: session_files = dependencies.theories), so editing any other PDE theory does not rebuild Class.)
  session Relative_Arbitrage = Relative_Arbitrage_Class + sessions Relative_Arbitrage_PDE Second_Order_Viscosity_Analysis theories Value_Function_* Example_3_1 Value_Function_Uniqueness
  session Relative_Arbitrage_Statement = Relative_Arbitrage + (unchanged; only the qualified imports of its 3 theories change)
  session Crandall_Ishii (extras) = Second_Order_Viscosity_Analysis; session Relative_Arbitrage_Extras (extras) = Relative_Arbitrage

Why this variant: all simulated on the measured per-theory times and import/need graphs. The model reproduces today's Statement build at 1,119 s against 1,123 s measured. Rebuild estimates after phase 5 (s, edit a V/U theory | PDE | class/DPP | toolkit):
- chosen V2C: 134 | 134 | 275 | 440
- honest toolkit parent (PSO = CPS, base above it): 134 | 134 | 275 | 623
- chain Class->PDE->RA: 121 | 181 | 322 | ~490
- chain PDE->Class->RA: 121 | 322 | 260 | ~490
- no base session: 160–208 | 160–208 | 327–375 | 576–592
- paper kept as one session on the base: 233 for every paper edit, 398 for the toolkit, but PIDE startup for V work is 205 s CP instead of 66 s
- today: 555 for everything
V2C is never more than 13 s worse than the best alternative and is the best in three of four categories.

Developer workflow:
- Iterate with `isabelle build -d . -o document=false Relative_Arbitrage_Statement`.
- PIDE logics:
  - `isabelle jedit -R Relative_Arbitrage` for value-function and uniqueness work (Class heap plus the PDE theories);
  - `-l Second_Order_Viscosity_Analysis` or `-R Relative_Arbitrage_PDE` for Section 4 work (builds only HOL-Analysis -> SMS -> SOVA, about 220 s cold, no probability);
  - `-R Relative_Arbitrage_Class` for class/DPP work;
  - `-R Path_Space_Operations` for the toolkit.
- CI caches the heaps of HOL-Analysis, HOL-Probability, Levy_Prokhorov_Metric, Martingales and Lower_Semicontinuous, keyed on the Isabelle and AFP versions. Today the AFP work cannot be cached at all, because it is re-checked inside CPS and RA.

Guards, so the layout does not rot:
(a) A re-check whitelist checked on the build logs (the script behind recheck.txt):
  - Relative_Arbitrage may re-check only Relative_Arbitrage_PDE.*;
  - Relative_Arbitrage_Class may re-check only Relative_Arbitrage_PDE.Constraint_Set;
  - Path_Space_Operations re-checks nothing.
  A new library import that is missing from the base list then fails CI instead of silently costing time.
(b) Relative_Arbitrage_PDE builds on SOVA, which proves by construction that it is probability-free.
(c) A nightly job builds a scratch copy with the AFP form of the Path_Space_Operations ROOT.
(d) Paper_Readings carries an oracle assertion and a statement fingerprint for theorem_1_1.
(e) The faithfulness evidence is cited from Paper_Readings, so it is a root of every dead-code pass.

### Summary

The design builds one Statement chain whose libraries have honest parents, plus a probability-free PDE sibling. The chain is: Levy_Prokhorov_Metric (AFP heap, cacheable) -> Continuous_Path_Spaces -> Relative_Arbitrage_Base (repo-local, no own theories, checks SMS/SemiC/SOVA/CTM/WM/KC/Disintegration once) -> Path_Space_Operations (the toolkit, promoted) -> Relative_Arbitrage_Class (Section 2: class, compactness, DPP) -> Relative_Arbitrage (Section 3 value function, uniqueness, Example 3.1; re-checks the PDE session) -> Relative_Arbitrage_Statement (unchanged ROOT). Relative_Arbitrage_PDE (Constraint_Set, Lemma 2.1, Eq. 1.9 operator, envelopes, viscosity notions, Section 4 comparison) has parent SOVA, so its probability-freeness is enforced by construction. Library parents become AFP-honest: SemiC on Lower_Semicontinuous, SOVA on SMS, CTM on Martingales, WM on CTM, CPS on Levy_Prokhorov_Metric. HOL-Complex_Analysis goes, replaced by a local Arzela-Ascoli. The dead market layer and the dead or empty theories are deleted. Crandall_Ishii_Sums and Theorem 4.2(a) with compact uniqueness go to off-path leaf sessions. Model estimates, calibrated to the measured build (1,119 s model vs 1,123 s measured):
- Rebuild after editing a value-function or PDE theory: 555 s -> ~134 s. Class/DPP edit: 555 -> ~275 s. Toolkit edit: 555 -> ~440 s.
- PIDE startup for value-function work: 446 s -> 66 s CP.
- Lines re-checked per paper edit: 40,316 -> ~8,000.
- Statement-path CPU: -18%. Clean Statement build with AFP heaps cached: -25%. A fully cold build is +15%, because the Levy_Prokhorov_Metric heap is built once.
- Theory-level critical path: 577 s -> 367 s.
- Size: 120.6k -> ~99k lines; the paper sessions go from 65.6k to ~32.8k.
Seven phases, each ending in a green Statement build. The cheap ROOT/import wins come first, the session splits next, and the edit-heavy deletions and clones last, when they are cheap to iterate.

### Sessions

| session | parent | sessions imports | scope |
|---|---|---|---|
| `Symmetric_Matrix_Spectra` | HOL-Analysis |  | Spectral theory of real symmetric matrices: trace and transpose calculus, outer products, orthonormal families, spectral theorem, Ky Fan sums, ordered eigenvalues and their continuity, Courant-Fischer bounds and Poincare separation, Householder reflections and rotations. |
| `Semicontinuous_Analysis` | Lower_Semicontinuous |  | Upper and lower semicontinuity of real functions on metric spaces: epsilon-delta calculus, attainment, bounded extension, semicontinuous envelopes, Berge's maximum theorem and scaling of infima. |
| `Second_Order_Viscosity_Analysis` | Symmetric_Matrix_Spectra | Semicontinuous_Analysis | Second-order machinery for comparison proofs between viscosity solutions: Rademacher, Alexandrov, Jensen's lemma, sup-convolution, doubling of variables, soft penalties, test functions and generic viscosity predicates. |
| `Crandall_Ishii` | Second_Order_Viscosity_Analysis | Semicontinuous_Analysis | The Crandall-Ishii theorem on sums for semicontinuous functions. |
| `Continuous_Time_Martingales` | Martingales |  | Continuous-time martingale theory beyond the AFP Martingales entry: Doob's inequality, optional sampling at bounded and general stopping times, quadratic variation, Vitali, modifications and transfers, essential infima. |
| `Wiener_Measure` | Continuous_Time_Martingales | Kolmogorov_Chentsov | Brownian motion as the projective limit of its Gaussian finite-dimensional distributions, its continuous modification, and the n-dimensional process with its independent increments and martingale properties. |
| `Continuous_Path_Spaces` | Levy_Prokhorov_Metric | Continuous_Time_Martingales, Kolmogorov_Chentsov, Semicontinuous_Analysis, Standard_Borel_Spaces | Weak convergence of continuous processes: C([0,T]) as a Polish space, portmanteau, tightness from increment moments, quadratic variation as a path functional, exit times, measurable selection and densities of absolutely continuous paths. |
| `Relative_Arbitrage_Base` | Continuous_Path_Spaces | Symmetric_Matrix_Spectra, Semicontinuous_Analysis, Second_Order_Viscosity_Analysis, Continuous_Time_Martingales, Wiener_Measure, Kolmogorov_Chentsov, Disintegration | Build-only heap that checks once every library theory the toolkit and paper sessions import; no own theories, no document, not an AFP entry. |
| `Path_Space_Operations` | Relative_Arbitrage_Base | Symmetric_Matrix_Spectra, Semicontinuous_Analysis, Continuous_Time_Martingales, Disintegration | Cutting, stopping, shifting and gluing continuous paths and their laws, and laws of a path paired with its covariation process: the measurable infrastructure of a dynamic programming principle on path space. |
| `Relative_Arbitrage_PDE` | Second_Order_Viscosity_Analysis | Semicontinuous_Analysis | Paper session, probability-free: the constraint set of Eqs. (1.4)-(1.5) and Lemma 2.1, the operator of Eq. (1.9), its envelopes, the viscosity notions of Definition 3.1, and the comparison principle of Section 4. |
| `Relative_Arbitrage_Class` | Path_Space_Operations | Relative_Arbitrage_PDE, Wiener_Measure | Paper session for Section 2: the class of Eq. (1.7) with the capped constraint set, its tightness and weak closedness (Lemmas 2.2-2.3), the Brownian witness, optimizers, the infinite-horizon class and xclass/xval bridges, and the dynamic programming principle. |
| `Relative_Arbitrage` | Relative_Arbitrage_Class | Relative_Arbitrage_PDE, Second_Order_Viscosity_Analysis | Paper session for Section 3 and the assembly: the value function is a viscosity sub- and supersolution, the uniqueness clauses, the infinite-horizon bridge and Example 3.1. |
| `Relative_Arbitrage_Statement` | Relative_Arbitrage |  | Acceptance test: Theorem 1.1 stated for xval and xclass with every definition it mentions, plus the readings and faithfulness evidence. |
| `Relative_Arbitrage_Extras` | Relative_Arbitrage | Relative_Arbitrage_PDE | Paper results of independent interest that Theorem 1.1 does not use, kept off the Statement path. |

### Deletions

- Market layer, 8 theories, 4,909 lines, 57 s CPU, zero facts used. ETS sat on the critical path via Exit_Class_Limits. The theories are Volatile_Market, Ito_Market, Brownian_Market, Optimal_Exit_Time, Brownian_Optimal_Boundary, Value_Function_Market, Path_Tightness_Market and Exit_Time_Semicontinuity.
- Theories with no lemma: Comparison_Jets (48) and Dynamic_Programming_Optional_Sampling (33).
- Viscosity_Ball (233 lines, 27 s CPU, the costliest dead theory per line) and Viscosity_Comparison_Interface (195). Before deleting VCI, its global `declare transpose_matrix_vector [simp del]` is copied into its direct importers, Ball_Solution and Value_Function_Uniqueness, and into Exit_Class.
- CTM.Moment_Bounds (94, dead).
- Statement_Auxiliary: 7 dead re-exports (43); the remaining ~150 lines go once theorem_1_1 is assembled directly.
- Dynamic_Programming_Kernels: the abandoned simple-stopping-time route (1,059). The live remainder is merged into Dynamic_Programming_Conditioning.
- Ball-version Euler chain plus the plain (non-envelope) Case 1 (~1,600 across Value_Function_Euler_Construction, _Supersolution_Case_1 and Pair_Path_Laws).
- Deterministic-time quadratic subsolution chain and ell_op_s (Value_Function_Subsolution, 822).
- Dead scaffolding of the stopping-time kernel route in Path_Stopping_Times and Path_Law_Pasting (~850); dead pair-layer definitions pairX/pairY/Yint/acont (~230).
- Dead operator statements (smooth ball strand in Ball_Solution 339, Operator_Formula/Operator_Envelope_Continuity dead facts ~650, tanSF/tanp feasibility 175, exit_val_case2_tilt_step 80), keeping all faithfulness evidence.
- Quadratic-penalty comparison route (comparison_supconv_doubling_complete, comparison_supconv_maximiser_complete, ~620). Theorem 4.2(a) and compact uniqueness (~1,740) are quarantined to Relative_Arbitrage_Extras, not deleted.
- Verified clones (~750 lines, one- to ten-line derivations):
  - exit_val_boundary_zero, diffquot_all_of_rational, exit_val_visc_subsol, exit_val_attained;
  - feasible_scale/feasible_scaleR_p, ell_op_scaleR_p, ell_op_scaleR_matrix;
  - Exit_Class.outerp_eq_outer_prod;
  - doubling_maximiser_exists and tilted_doubled_hessian_nonpositive as instances of their _gen versions.
- bmpair package (334): becomes a corollary of sbmpair (mat 1).
- Library re-proofs (~140 lines):
  - lipschitz_imp_absolutely_continuous_on;
  - bm_coordinates_indep;
  - martingale_add/diff;
  - continuous_map_real_diff;
  - Doubling_Of_Variables.norm_Pair_le, which shadows HOL's Product_Vector.norm_Pair_le.
- Laplace route in Path_Exit_Times (789 lines + 105 in the theorem body) and the CTM Laplace helpers (51), via the verified 69-line ess_inf_pexit_usc proof.
- Path_Tightness dead chains (2,353): C([0,inf)) projective limit, dyadic continuous modification (AFP KC has continuous_modification) and scalar tightness.
- CTM Quadratic_Variation stopped section (300; Fair_Games_Theorem covers it). SemiC type-class Berge copy (218).
- SOVA quadratic-penalty duplicates reachable only from dead code (~1,400). This is optional, a library judgement; it only affects cold and base builds.
- HOL-Complex_Analysis session dependency: 6 theories and 13.4k lines (226 s CPU) re-checked in every CPS build for Arzela_Ascoli. Replaced by a ~180-line attributed local copy.
- Crandall_Ishii_Sums is not deleted. It moves to the leaf session Crandall_Ishii, off every build path.

### Phases

**0 - Guard rails and baseline**

- Record the baseline with `isabelle build -d . -v -o timing -o threads=3 Relative_Arbitrage_Statement` and keep the per-session Timing lines. The model in the scratchpad (bf/sim2.py, layouts.py) predicts each later phase.
- Make the faithfulness evidence a root:
  - Paper_Readings proves ell_op_sym_part, literal_reading_keeps_identity and theorem_1_1_strong (all checked in PIDE);
  - it cites eigen_lb_iff_eigval_ge, lemma_2_1_exact, poincare_separation, convex_expandable and paper_class_marginal/lift.
- Switch theorem_1_1 in Theorem_1_1_Statement to the paper's hypothesis structure (G-A).
- Add an ML oracle assertion and a statement fingerprint (aconv against the stored prop) to Paper_Readings.
- Add the re-check whitelist script, which parses build logs for theories loaded from foreign qualifiers. In this phase it only reports.
- *risk*: Very low: additive. The one semantic change is that theorem_1_1 gets stronger, as intended.
- *validation*: Statement green, 0 oracles. Re-running the closure script shows every evidence lemma live.
- *est_effort*: 0.5 day

**1 - Import hygiene and whole-theory deletions inside today's sessions**

- First localise `declare transpose_matrix_vector [simp del]`. Copy it into Ball_Solution, Value_Function_Uniqueness and Exit_Class, so simp behaviour does not depend on import shape. Simpsets merge by union, so dropping VCI-derived imports would otherwise flip it.
- Drop the HOL-Complex_Analysis dependency: new theory Continuous_Path_Spaces/Arzela_Ascoli.thy (180 lines, attributed); Equicontinuity imports it; CPS ROOT loses the session.
- Drop verified or unused imports:
  - Pair_Path_Space: two SOVA imports, Vitali, Brownian_FDD; also delete Pair_Path_Laws:203 text;
  - Exit_Class: Ball_Solution;
  - Exit_Class_Limits: Exit_Time_Semicontinuity;
  - Exit_Class_Infinite: DP_Assembly becomes Exit_Class_Pasting;
  - Covariation_Density: Exit_Class;
  - Value_Function_Uniqueness: Value_Function_Market, Exit_Time_Semicontinuity;
  - CPS: Holder_Interpolation, Equicontinuity, Increment_Moments, Conditional_UI;
  - CTM: Optional_Sampling, Stopped_Adaptedness.
- Delete the 8 market theories, Comparison_Jets, Dynamic_Programming_Optional_Sampling, Viscosity_Ball, Viscosity_Comparison_Interface, Moment_Bounds and the 7 dead Statement_Auxiliary re-exports.
- *risk*: The fact-level need analysis does not see notation, abbreviations, type-class instances or simp attributes, so each import removal can break a proof far away. Mitigation: one import edit per build, `-o timeout=900`, bisect on failure. Both large removals (the toolkit's SOVA import, and the PDE layer's CTM import later) are covered by verified dry runs.
- *validation*: Statement green, 0 oracles, fingerprint unchanged. Model prediction:
- Statement-path CPU 2,369 -> 2,030-2,056 s;
- elapsed 1,119 -> 1,066-1,099 s;
- paper edit 555 -> 513-535 s;
- CPS build -226 s CPU and -13.4k re-checked lines;
- -5,450 lines.
The measured Timing lines must agree within about 20%.
- *est_effort*: 1.5 days

**2 - Library rebases (ROOT-level)**

- Semicontinuous_Analysis: parent Lower_Semicontinuous; Semicontinuous_Selection moves to CPS; cInf_mult_pos moves to SemiC.Semicontinuity, and Operator_Envelopes switches its import from CTM.Integrability_Criteria.
- Second_Order_Viscosity_Analysis: parent Symmetric_Matrix_Spectra, sessions Semicontinuous_Analysis. Replace usc_attains_sup_compact, usc_form_of_continuous and usc_extend_const_below by SemiC facts.
- Continuous_Time_Martingales: parent Martingales.
- Wiener_Measure: parent Continuous_Time_Martingales, sessions Kolmogorov_Chentsov.
- Continuous_Path_Spaces: parent Levy_Prokhorov_Metric, sessions CTM KC SemiC SBS. Move Covariation_Density into CPS.
- Requalify the imports and @{theory} antiquotations of the two moved theories.
- CI: cache the heaps of HOL-Analysis, HOL-Probability, Levy_Prokhorov_Metric, Martingales and Lower_Semicontinuous.
- *risk*: Low. Qualified names change only for Semicontinuous_Selection and Covariation_Density. The first cold build pays the Levy_Prokhorov_Metric heap once (~620 s CPU).
- *validation*: Statement green; the build log shows Levy_Prokhorov_Metric as a heap ancestor and no Riesz/SBS theories re-checked in CPS. Model prediction:
- clean Statement build with cached AFP heaps 1,119 -> 665-696 s, the best clean-build state of all phases;
- CPS rebuild 466 -> ~150 s;
- CTM edit 1,119 -> ~830 s.
- *est_effort*: 1 day

**3 - Base session and toolkit promotion**

- Create Relative_Arbitrage_Base/ROOT (no theories of its own, document = false, parent Continuous_Path_Spaces), listing the library theories the paper imports.
- git mv the 6 toolkit theories into Path_Space_Operations/ with ROOT, root.tex and root.bib; parent Relative_Arbitrage_Base. Relative_Arbitrage's parent becomes Path_Space_Operations.
- Requalify cross-session imports. Turn @{theory Relative_Arbitrage.X} antiquotations into the new qualifier or plain text: 40 occurrences in 19 files, rewritten by a script that also handles line breaks (lesson of PLAN_2 section 10).
- Add ROOTS entries.
- *risk*: Medium-low, mechanical. Risks: antiquotations and split antiquotations; a toolkit theory relying on a declaration made in a paper theory. Paper prose and helpers still in the toolkit are recorded as debt for phase 6.
- *validation*: Statement green. Touch a value-function theory: only Relative_Arbitrage and the Statement rebuild. The whitelist check shows Relative_Arbitrage re-checks nothing. Model prediction:
- paper edit 535 -> 261-281 s;
- lines re-checked per paper edit 40,316 -> 0.
- *est_effort*: 1.5 days

**4 - Paper split: PDE sibling, Class, value function**

- Move eigen_lb/eigen_ub (with their lemmas) from Curvature_Operator to the top of Constraint_Set_Convexity, renamed Constraint_Set. Move closed_eigen_ub, convex_eigen_ub and eigen_lb_iff_eigval_ge there. Curvature_Operator is renamed Elliptic_Operator and imports Constraint_Set.
- Create Relative_Arbitrage_PDE/ (parent SOVA) with the 13 operator/comparison theories. Rewrite the 24 antiquotations found by the dry run.
- Create Relative_Arbitrage_Class/ (parent Path_Space_Operations, sessions Relative_Arbitrage_PDE Wiener_Measure) with the 15 class/DPP theories. Exit_Class imports only Relative_Arbitrage_PDE.Constraint_Set.
- Relative_Arbitrage keeps the 7 value-function/uniqueness theories, plus Example_3_1 split out of Value_Function_Uniqueness.
- Requalify the 3 Statement imports.
- Tighten the whitelist to enforcement:
  - Relative_Arbitrage re-checks only Relative_Arbitrage_PDE.*;
  - Relative_Arbitrage_Class re-checks only Relative_Arbitrage_PDE.Constraint_Set.
- *risk*: Medium. Moving definitions changes constant long names (Curvature_Operator.eigen_lb becomes Constraint_Set.eigen_lb), which affects @{const}, @{thm} and names_short output in the Statement document. There are many cross-session qualified imports. sconstraint deliberately stays in Exit_Class to limit churn.
- *validation*: Relative_Arbitrage_PDE builds on SOVA, which proves it is probability-free. Statement green with an unchanged fingerprint.
Touch Comparison_Principle: only Relative_Arbitrage and the Statement rebuild. Touch Exit_Class_Pasting: Class, RA and the Statement rebuild.
Model prediction:
- value-function/PDE edit 158-166 s;
- Class edit 307-342 s;
- PIDE startup with -R Relative_Arbitrage for value-function work 446 -> ~66 s CP.
- *est_effort*: 2.5 days

**5 - In-session dead code, verified clones, Laplace route (cheap to iterate now)**

- Paper dead code:
  - Dynamic_Programming_Kernels route (merge the remainder into Conditioning);
  - ball Euler chain and plain Case 1;
  - deterministic subsolution chain;
  - Path_Stopping_Times/Path_Law_Pasting scaffolding;
  - operator dead statements;
  - quadratic comparison route.
  Move Theorem 4.2(a) and compact uniqueness into the leaf Relative_Arbitrage_Extras.
- Apply the verified clone derivations from REVIEW section 3.2, bmpair = sbmpair (mat 1), and the library one-liners. Delete the shadowing norm_Pair_le.
- CPS: swap in the 69-line ess_inf_pexit_usc proof and delete the Laplace block and its CTM helpers; delete the dead Path_Tightness chains. CTM: the stopped QV section. SemiC: the type-class Berge copy.
- Move Crandall_Ishii_Sums into the leaf session Crandall_Ishii (group extras).
- *risk*: Medium-low. Risks: deleting a [simp]/[intro] lemma changes automation; a hidden use through an attribute. Evidence is protected by the phase-0 roots.
- *validation*: Dead-code script with evidence roots: no rooted fact deleted. Statement green, 0 oracles, fingerprint unchanged. `isabelle build -g extras` green. Model prediction:
- value-function/PDE edit 134-141 s;
- Class edit 275-303 s;
- toolkit edit 440-458 s;
- Statement-path CPU 1,919-1,934 s (-18% vs today);
- clean build with cached AFP heaps 832-852 s.
- *est_effort*: 3-4 days

**6 - Content moves that make the libraries AFP-clean (batched)**

- Move these blocks:
  - Brownian-motion block of Exit_Class_Witness -> Wiener_Measure;
  - outerp/psd/onormal lemmas -> SMS;
  - general Poincare separation and Courant-Fischer bound -> SMS;
  - optional sampling at a stopping time, dyceil, pre_sigma_of -> CTM;
  - pball_exit, etime_shift, vshift -> CPS.Path_Exit_Times;
  - paper helpers (Euler scheme, quad_good, Case-2 lemmas) out of Path_Space_Operations into the value-function theories.
- Remove the 119 lines of paper prose from library theories and the 168 'X lives in Y' pointers.
- Batch the moves by target library: one build per library. In this layout a library edit rebuilds Base and the whole paper chain (~684-832 s).
- *risk*: Medium. Moved prose antiquotations; topological ordering of moved blocks against their new neighbours (PLAN_2 lesson); duplicate names when a moved lemma meets an existing twin.
- *validation*: Statement green. `grep -l LaiShkolnikovSoner` and 'Eq. (' in library sessions return nothing. Whitelist check passes. Line counts per session within about 10% of the targets.
- *est_effort*: 3 days

**7 - Critical-path surgery (measured, optional)**

- Split the longest single theories on the paper and base critical paths, each step justified by the `-o timing` profile:
  - Exit_Class_Pasting (45 s), Exit_Class_Limits (34 s);
  - Pair_Path_Laws (45 s), Path_Law_Sampling (40 s);
  - SMS Matrix_Algebra (72 s), SOVA Doubling_Of_Variables (29 s).
- Collapse the X-vs-compensated twins in Path_Law_Sampling and the DPP layer (~2,000 lines) and the sup-convolution attainment copies (~470).
- Then the generalisations G-B (abstract constraint set) and G-C (abstract geometric operator). G-C would let Relative_Arbitrage_PDE become an AFP library.
- *risk*: Low per step, but each split may not pay: the model says a split helps only if it shortens the critical path by more than the ~30 s per-session or per-theory overhead.
- *validation*: Model and measured targets: Class CP 139 -> ~100 s, Class edit ~240 s, toolkit edit ~380 s. Statement green after every step.
- *est_effort*: open-ended, 1 day per split

### Quantified effects

Method. A session-level build simulator (scratchpad bf/sim2.py, layouts.py, phases.py) runs over the measured per-theory times from build.log, the theory import graph, and the named-fact/constant 'need' graph. Imports are modelled twice: 'cur' (today's imports, deleted theories bypassed, verified fixes applied) and 'need' (named-fact minimal imports). Ranges below are cur/need. Each session's elapsed time is estimated as max(0.4*W, 0.8*CP) + 30 s; the 30 s is the measured heap-load/save overhead, 27-46 s per session. Calibration: today's Statement path comes out at 1,119 s against 1,123 s measured (97+445+540+41). Per session: RA 491 vs 473, CPS 436 vs 401, CTM 68 vs 67. CPU is about 15% high in the model.

Clean builds:
- Statement-path CPU: 2,369 -> 1,919-1,934 s (-18%). All sessions including library heaps and leaves: 3,039 -> 2,597-2,613 s (-14%).
- Statement-path elapsed with cached distribution and AFP heaps: 1,119 -> 832-852 s (-24 to -26%). Phase 2 alone reaches 665-696 s, the best clean-build state; the later splits give back about 160 s of clean-build time for 2-4x faster iteration.
- Fully cold: 1,289-1,309 s (+15%), because the Levy_Prokhorov_Metric heap (620 s CPU, Riesz_Representation alone 243 s) is built once. Today this work cannot be cached at all, because it is re-checked inside CPS.

Rebuild after editing one theory (Statement path, estimated elapsed):
- value-function or uniqueness theory: 555 -> 134-141 s (-75%);
- operator or comparison theory: 555 -> 134-141 s;
- class or DPP theory: 555 -> 275-303 s (-48%);
- toolkit theory: 555 -> 440-458 s (-19%). With the AFP-honest toolkit parent it would be 621-707 s;
- Statement theory: 34 -> 32 s;
- CTM or CPS theory: 1,021-1,119 -> ~832 s;
- SMS, SOVA or WM theory: 555 -> ~684 s. This regression is accepted because library edits are rare after migration and are batched in phase 6.

PIDE startup with a requirements image (critical path / CPU):
- Value_Function_Supersolution_Case_2: 446/554 s -> 66/66 s;
- Value_Function_Uniqueness: 463/611 -> 73/81;
- Exit_Class_Marginals: 374/472 -> 118/118;
- Dynamic_Programming_Assembly: 355/451 -> 137/143;
- Comparison_Two_Domain: 84/110 -> 40/55, and Section 4 work needs no probability heap at all (cold start about 260 s instead of about 560 s);
- toolkit: 170 -> 154.

Re-checked lines:
- per clean Statement build today: 74,650 lines (CPS 34,334, RA 40,316), all inside sessions that rebuild on edits;
- after: about 13,400 in the cacheable AFP heap, about 10,900 in CPS and about 39,500 in Relative_Arbitrage_Base (both rarely rebuilt), and about 8,800 in paper sessions;
- per paper edit: 40,316 -> about 8,000 for value-function/PDE edits (the PDE re-check, about 55 s CPU, mostly parallel) and about 8,800 for Class edits.

Critical path:
- through user theories (theory level): 577 s over 35 theories -> 367 s over 26 with need-minimal imports, or 487 s with only the planned import fixes;
- paper-session critical path: today a single 614 s RA chain including the Disintegration and toolkit chains; after, Class 139 s, Relative_Arbitrage 89 s, PDE 40 s and toolkit 169 s, in separate sessions.

Lines: 120,625 -> about 99,000:
- SMS 8.3k, SemiC 1.45k, SOVA 14.3k, Crandall_Ishii 2.6k (leaf), CTM 9.45k, WM 4.1k, CPS 12.1k;
- Path_Space_Operations 12.2k (about 10.3k after the twin collapse);
- Relative_Arbitrage_PDE 8.1k, Relative_Arbitrage_Class 13.6k, Relative_Arbitrage 10.3k, Statement 0.75k, Extras 1.9k (leaf).
The paper sessions shrink from 65.6k to about 32.8k lines. Deleted outright: about 5,450 lines of whole theories (phase 1) and about 12,000 lines of in-theory dead code and clones (phases 5-6).

### Risks and open questions

- Simp-set hazard: VCI's global `declare transpose_matrix_vector [simp del]` reaches descendants through union-merged simpsets. Any import change, including the planned Exit_Class -> Ball_Solution removal, can flip simp behaviour in the whole class layer. Phase 1 must localise the declaration before touching imports.
- The need analysis sees only named facts and constants, not notation, abbreviations, instances or attributes. For example, `instance prod :: (polish_space, polish_space) polish_space` in Path_Space is invisible to it. The 'need' column of the model is therefore optimistic, and every import removal needs a build. Only the toolkit and PDE removals are covered by verified dry runs.
- Path_Space_Operations has the repo-local base as parent, so its ROOT is not AFP-submittable as is. Mitigations: a one-line parent swap at submission and a nightly CI job that builds the honest form. The honest form everywhere costs about +180 s per toolkit edit. If the project values ROOT honesty over toolkit iteration, use parent Continuous_Path_Spaces and put the base above the toolkit.
- Cold builds get about 15% slower unless CI caches the AFP heaps (Levy_Prokhorov_Metric, Martingales, Lower_Semicontinuous) together with the distribution heaps.
- Base-list drift: a new import of a library theory not listed in Relative_Arbitrage_Base silently becomes a re-check inside a paper session. The re-check whitelist check on build logs must be enforced in CI from phase 4 on.
- Each extra session costs about 30 s of overhead (measured 27-46 s). The model says further splits (Class into Class + DPP, or comparison after the value function) do not pay. Re-measure after phase 5 before splitting more.
- In-theory deletions are modelled as time proportional to deleted lines, which is unverified. Theories like Viscosity_Ball (27 s for 233 lines) show that time per line varies by 10x.
- Constant long names change when eigen_lb/eigen_ub move from Curvature_Operator to Constraint_Set. The Statement document's names_short output and @{const}/@{thm} antiquotations must be re-checked, and 40 @{theory Relative_Arbitrage.X} antiquotations in 19 files must be requalified.
- Rebuild semantics: from the Isabelle2026-RC3 sources, a session's sources digest covers only the files it loads, so Class should not rebuild when non-Constraint_Set PDE theories change. Verify this empirically in phase 4 by touching Comparison_Principle and checking which sessions say 'Building'.
- Open (content decision, build-neutral): keep Theorem 4.2(a) and the compact-uniqueness branch in the Extras leaf, or delete them; likewise Crandall_Ishii_Sums. The verification recommends against rebasing the comparison on Crandall-Ishii because the live path would grow.
- Open: whether the probability-free PDE session should become a real library (G-C abstract geometric operator) with a scope that does not name the paper. That would make its present paper-session status temporary.
- All timing estimates assume the measured 3 threads on a 4-core VM. With more cores the CP-bound paper sessions dominate and the advantage of the split grows, while the base heap's CPU-bound cost shrinks.

## Design: paper-first

### Summary

IDEA. Split the paper along its own seam, and order and name what is left the way the paper is ordered. That gives two paper sessions:
- Relative_Arbitrage_Equation: everything deterministic. The operator F of Eq. (1.9), Eqs. (1.4)-(1.5) with Lemma 2.1, Definition 3.1, Eqs. (3.4)-(3.6) with Lemma 3.1, and all of Section 4.
- Relative_Arbitrage: everything stochastic. P_x and v of Eqs. (1.6)-(1.7), Section 2, Example 3.1, Sections 3.1 and 3.2, and Theorem 1.1.

In both sessions the theories are listed in the paper's order. A theory is named after a paper result when it holds exactly that result (Example_3_1, Proposition_2_4, Theorem_1_1). A new last theory, Paper_Map, does two jobs:
- it is the reader's index: one `theorem` per numbered item of the paper, displayed in the paper's words and proved by `rule` from the working lemma, with the deviations written next to it;
- it is the root set that every dead-code pass must keep, so faithfulness evidence can never be deleted again (REVIEW_3 §1.2b).

Library sessions change only where the paper sessions need them:
- the path toolkit leaves the paper session (dry run checked);
- three parents are fixed;
- dead code, PIDE-verified clones and library re-proofs go.

Library-internal re-layering is deliberately left out: CTM/CPS theory moves, Dyadic_Grids, merging X/compensated twins, G-C. It costs risk and buys a paper reader nothing.

Mechanics. Moves and deletions only. The only proofs that change are PIDE-verified drop-ins with identical statements. New mathematics is confined to gated leaf theories.

STARTING POINT. The working tree, uncommitted, already contains PLAN_3 phase-1 work:
- Relative_Arbitrage/Theorem_1_1.thy, with theorem_1_1_assembled in the paper's hypothesis structure and example_3_1_xval;
- Statement_Auxiliary deleted;
- ell_op_sym_part;
- Paper_Readings extended.

P0 builds and commits it.

DECISIONS
- D1. The probability-free paper session gets parent Path_Space_Operations, not SOVA. Its theories keep exactly the imports the dry run checked, so there is zero proof-context change. The probability-free property is kept as an ML ancestor-check regression test. Why this parent:
  - the session is in Relative_Arbitrage's parent chain;
  - so Relative_Arbitrage re-checks only WM, KC and LPM: 7,150 lines and ≈140 s, against 40,344 lines and 560 s today;
  - a parallel parent (SOVA) would make every Relative_Arbitrage rebuild re-check the Equation session, SOVA, Lower_Semicontinuous and the SMS remainder (≈355-370 s);
  - cold-build cost is about the same either way;
  - switching back to SOVA is a one-line ROOT change.
- D2. Keep Theorem 4.2(a), labelled honestly. max_principle_boundary_holds (continuous u, w) is rooted as "Theorem 4.2(a), continuous data"; this keeps ≈1,600 lines alive. Delete only its corollaries that carry paper numbers they do not deserve:
  - OEC 562-655 (max_principle_le, comparison_from_max_principle, uniqueness_from_max_principle);
  - the VCI locale;
  - viscosity_uniqueness_compact and theorem_1_1_uniqueness_general.

  The faithful usc/lsc version is an optional gated leaf.
- D3. Crandall_Ishii_Sums stays in SOVA as a library root and is not rebased (verified: a rebase grows the live path). Paper_Map discloses that the formal Theorem 4.2 does not go through [CraIsh].
- D4. The market layer is deleted. It presents non-paper objects (val_fn, stopped markets) as the paper's, and its optimality results are vacuous.
- D5. Placement of the paper's objects:
  - sconstraint goes with xclass/xval into a new §1 theory, Control_Problem;
  - the tangential coefficient field stays in Relative_Arbitrage as Example 3.1 material;
  - expandable/convex_expandable (the T_ι hypothesis) move from SOVA.Test_Functions into the Equation session next to Theorem 4.3.
- D6. Proposition 2.4 is stated (gated, horizon-T form). Section 5 is recorded as not formalised in Paper_Map and root.tex.
- D7. One AFP entry for the paper: directory Relative_Arbitrage/ with two sessions; Relative_Arbitrage_Equation is declared `in "Equation"`.

PAPER MAP (where a reader finds each result after migration; RA = Relative_Arbitrage, EQ = Relative_Arbitrage_Equation)
- Eq. (1.9): EQ.Elliptic_Operator (ell_op, feasible, eigen_lb, eigen_ub, ell_op_sym_part).
- Eqs. (1.4)-(1.5) and Lemma 2.1: EQ.Constraint_Set_Convexity (suff_volatile, Pi_proj, Pi_constraint, lemma_2_1_exact).
- Eqs. (1.5)+cap, (1.6), (1.7): RA.Control_Problem (sconstraint, xclass, xval). The density reading is RA.Covariation_Density.dq_iff_density.
- Lemma 2.2: RA.Exit_Class_Tightness.tight_on_set_paper_pair_class. Stated for pair laws on [0,T] at S = sconstraint k L; the general S of G-B is a gated item.
- Lemma 2.3: RA.Exit_Class_Limits.exit_class_weak_closed and Exit_Class_Optimizer.exit_class_compactin_weak.
- Proposition 2.4:
  - usc: Exit_Class_Shift.exit_val_usc, giving Theorem_1_1.xval_usc;
  - DPP lower half: Dynamic_Programming_Assembly.exit_val_dpp_sup_ge_time;
  - DPP upper half: Dynamic_Programming_Conditioning.exit_val_cond_time;
  - attainment: Exit_Class_Optimizer.exit_val_measurable_selector;
  - the equality: RA.Proposition_2_4 (gated).
- Definition 3.1: EQ.Viscosity_Definitions (visc_subsol_env2, visc_supersol_env2).
- Eqs. (3.4)-(3.5): EQ.Operator_Formula.
- Lemma 3.1: EQ.Operator_Envelopes (ell_op_lsc_off_zero, ell_op_usc_off_zero, the p=0 clause, and eq36, which is dead today and rooted here).
- Example 3.1: RA.Example_3_1, giving example_3_1_xval.
- §3.1: RA.Value_Function_Subsolution.
- §3.2: RA.Value_Function_Supersolution_Case_1 and _Case_2.
- Proposition 4.1: EQ.Comparison_Two_Domain.uniqueness_expandable.
- Theorem 4.2(a): EQ.Maximum_Principle.max_principle_boundary_holds (continuous data).
- Theorem 4.2(b): EQ.Comparison_Two_Domain.comparison_two_domain, with supersol_bc_nonneg.
- Theorem 4.3: comparison_expandable.
- Eq. (4.4) and Remark 4.1: ell_op_conj_rot, ell_op_scale, convex_expandable.
- Theorem 1.1: RA.Theorem_1_1.theorem_1_1_assembled, restated in Statement.
- Section 5: not formalised.

SESSIONS (10; today 8)
- Libraries: SMS, SemiC (re-parented to HOL-Analysis), SOVA (parent SMS), CTM, WM (parent CTM), CPS, and Path_Space_Operations (new).
- Paper: Relative_Arbitrage_Equation (new) and Relative_Arbitrage (parent Relative_Arbitrage_Equation).
- Relative_Arbitrage_Statement, unchanged as the acceptance test.

If ten is judged too many, Path_Space_Operations can be appended to CPS. That costs ≈250-300 s more on every CPS rebuild (the SMS, Disintegration and S_Finite re-checks move there) and makes the CPS entry two-subject; nothing else changes.

### Sessions

| session | parent | sessions imports | scope |
|---|---|---|---|
| `Symmetric_Matrix_Spectra` | HOL-Analysis |  | The spectral theory of real symmetric matrices beyond HOL-Analysis: trace and transpose calculus, orthonormal families, Householder reflections and rotations, the spectral theorem, Ky Fan sums, ordered eigenvalues and their Lipschitz dependence, Courant-Fischer bounds and Poincare separation. |
| `Semicontinuous_Analysis` | HOL-Analysis | Lower_Semicontinuous | Upper and lower semicontinuity of real functions on metric spaces: the epsilon-delta calculus, attainment on compacta, bounded extension off a closed set, the semicontinuous envelopes globally and relative to a closed set, and Berge's maximum theorem. |
| `Second_Order_Viscosity_Analysis` | Symmetric_Matrix_Spectra |  | Second-order tools for viscosity solutions: convex subgradients and Moreau envelopes, Rademacher's and Alexandrov's theorems, Jensen's lemma, sup-convolution, the Crandall-Ishii theorem on sums, doubling-of-variables and penalty toolboxes, and the C2 test-function classes with their jet bridges. |
| `Continuous_Time_Martingales` | HOL-Probability | Martingales | Continuous-time martingale theory beyond the Martingales entry: Doob's maximal inequality, optional sampling and stopping at bounded stopping times, quadratic variation and its compensator, Vitali's theorem, exit times as stopping times, transport of the martingale property, power inequalities and the essential infimum. |
| `Wiener_Measure` | Continuous_Time_Martingales | Kolmogorov_Chentsov | Brownian motion as the projective limit of its Gaussian finite-dimensional distributions with a continuous modification, and the n-dimensional process with independent increments relative to its natural filtration, its martingale property and its compensated squares and cross-variations. |
| `Continuous_Path_Spaces` | Continuous_Time_Martingales | Kolmogorov_Chentsov, Levy_Prokhorov_Metric, Standard_Borel_Spaces, Semicontinuous_Analysis, HOL-Complex_Analysis (dropped if the optional local Arzela-Ascoli is taken) | The space of continuous paths as a Polish space: weak convergence with portmanteau and continuous mapping, tightness from increment moments, quadratic variation as an adapted path functional, exit times of closed sets and their semicontinuity along weak convergence, and measurable selection of an upper semicontinuous payoff. |
| `Path_Space_Operations` | Continuous_Path_Spaces | Symmetric_Matrix_Spectra, Semicontinuous_Analysis, Disintegration, Levy_Prokhorov_Metric | Cutting, stopping, restarting and gluing continuous paths and their laws (pasting at stopping times, kernel glues, conditional laws of the future), and the closure under weak limits and pasting of the laws of a continuous martingale paired with a covariation process whose difference quotients lie in a given set. |
| `Relative_Arbitrage_Equation` | Path_Space_Operations | Symmetric_Matrix_Spectra, Second_Order_Viscosity_Analysis, Semicontinuous_Analysis, Lower_Semicontinuous | Paper session (arXiv:2512.17702), the deterministic half, in paper order. The operator F of Eq. (1.9). The constraint sets of Eqs. (1.4)-(1.5) and Lemma 2.1. Definition 3.1. Eqs. (3.4)-(3.6) and Lemma 3.1. Section 4: Theorem 4.2 (maximum principle), Theorem 4.3 (comparison) and Proposition 4.1 (uniqueness). Its theories import nothing probabilistic, which a regression test checks. |
| `Relative_Arbitrage` | Relative_Arbitrage_Equation | Wiener_Measure, Kolmogorov_Chentsov, Levy_Prokhorov_Metric, Disintegration, Symmetric_Matrix_Spectra, Second_Order_Viscosity_Analysis, Semicontinuous_Analysis | Paper session (arXiv:2512.17702), the stochastic half and the theorem, in paper order. §1: the class P_x and value function v of Eqs. (1.6)-(1.7). §2: Lemmas 2.2-2.3 and Proposition 2.4. §3: Example 3.1 and the sub- and supersolution properties. Then Theorem 1.1 for xval/xclass, and Paper_Map, which is both the index and the root set. |
| `Relative_Arbitrage_Statement` | Relative_Arbitrage |  | Acceptance test: Theorem 1.1 and Example 3.1 for xval/xclass with every definition they mention, plus the checked readings of the paper's wording; for the authors, outside the AFP entry. |

### Deletions

- Market layer, 8 theories, 4,909 lines (zero facts used, measured): Volatile_Market, Ito_Market, Brownian_Market, Optimal_Exit_Time, Brownian_Optimal_Boundary, Value_Function_Market, Path_Tightness_Market, Exit_Time_Semicontinuity. First drop the imports in Exit_Class_Limits and Value_Function_Uniqueness and delete stopped_market_acov_leaves_sconstraint.
- Empty theories: Comparison_Jets (48 lines) and Dynamic_Programming_Optional_Sampling (33). Comparison_Strictness takes over Comparison_Jets' imports.
- Smooth ball strand, ≈880 lines: Viscosity_Ball (233), Viscosity_Comparison_Interface (195, including the locale with a refuted assumption) and Ball_Solution (516). Ball_Solution's two live facts move to Elliptic_Operator first. Before deleting VCI, an ML query lists the theories whose simpset really lacks transpose_matrix_vector, and the declaration is replicated exactly there; simpset merges are unions, so the inherited deletion may already be void in most of them.
- Dynamic_Programming_Kernels, ≈1,280 lines (13 facts, 1 used): exit_val_dpp_sup_ge_time_of_const moves to Dynamic_Programming_Pasting first.
- Value-function dead blocks, ≈3,100 lines (measured dead lines): the ball-version Euler chain (Value_Function_Euler_Construction 1,154), the plain Case 1 and the dead tanp/tanSF lemmas (Case_1 926), the deterministic-time quadratic subsolution chain (Value_Function_Subsolution 822), exit_val_case2_tilt_step, theorem_1_1_uniqueness_general and theorem_1_1_ball_fragment.
- Comparison dead code, about 2,470 dead lines minus ≈1,600 kept as Theorem 4.2(a). The quadratic route (comparison_supconv_doubling_complete 193, comparison_supconv_maximiser_complete 430, comparison_env_complete and comparison_supconv_complete) goes. So do the continuity-based corollaries labelled with the paper's numbers (OEC 562-655), viscosity_uniqueness_compact, max_principle_boundary_counterexample, Viscosity_Definitions' visc_sol_env with the five _eq_gen bridges, and Second_Order_Viscosity_Analysis.Viscosity_Solutions (108).
- Statement_Auxiliary (196 lines). Already deleted in the working tree, where Relative_Arbitrage.Theorem_1_1 replaces it.
- Laplace route of ess_inf_pexit_usc, 947 lines: Path_Exit_Times 193-1143 apart from weak_conv_open_liminf, Integrability_Criteria 346-396, and 105 lines saved in the proof body. The verified 69-line proof with an identical statement replaces it.
- Library re-proofs, verified 1-2 line derivations:
  - Covariation_Density.lipschitz_imp_absolutely_continuous_on (42 lines);
  - Exit_Class_Witness.bm_coordinates_indep (26 lines become 2);
  - Martingale_Algebra.martingale_add/diff (60);
  - Path_Tightness.continuous_map_real_diff (6);
  - Doubling_Of_Variables.norm_Pair_le (10; it shadows HOL's);
  - the matcher's EQUIV list: bm_prj_measurable, prob_space_pair_measure, integral_of_bounded_linear, trace_diff_matrix, inner_sum_scaleR_Basis, abs_norm_diff_le, norm_Pair_left/right_zero, and 8 Matrix_Algebra distributivity lemmas.
- Internal statement-level clones, verified, ≈750 lines:
  - exit_val_boundary_zero (100 lines become 5), diffquot_all_of_rational (85 become 1), exit_val_visc_subsol (95 become 1), exit_val_attained (66 become 5);
  - feasible_scaleR_p, plus the VCI twins, which go with VCI;
  - the Exit_Class copy of outerp_eq_outer_prod;
  - doubling_maximiser_exists and tilted_doubled_hessian_nonpositive (95 lines become 2);
  - the bmpair package (334 lines): bmpair stays a constant and gets the equation bmpair_eq_sbmpair. It does not become an abbreviation (the trap of PLAN_2 §10).
- Library dead code outside the declared roots, iterated to a fixpoint (estimates):
  - Continuous_Time_Martingales: Moment_Bounds (95) and Quadratic_Variation's stopped section (300), ≈1,000 in all;
  - Continuous_Path_Spaces: the Path_Tightness projective-limit, modification and scalar chains (≈2,350), plus Stopped_Localization and Pathwise_Quadratic_Variation remnants, ≈4,000;
  - Wiener_Measure: twins ≈800;
  - Symmetric_Matrix_Spectra ≈550, after rooting the evidence;
  - Semicontinuous_Analysis ≈300;
  - Second_Order_Viscosity_Analysis ≈2,900. With Crandall_Ishii_Sums rooted, ≈3,200 of the 6,323 dead lines stay live.
- Toolkit dead code, ≈1,900 lines: mainly the abandoned stopping-time kernel route (Path_Stopping_Times 785, Path_Law_Pasting 428) and Pair_Path_Laws/Pair_Path_Space leftovers (pairX, pairY, Yint, acont and so on).
- Repository hygiene: the tracked notes/restructuring_2/__pycache__/*.pyc. Notes naming theories that no longer exist are corrected, not deleted.
- Deliberately NOT deleted:
  - Theorem 4.2(a) for continuous data and its exclusive chain (≈1,600 lines);
  - Crandall_Ishii_Sums (library root);
  - the faithfulness evidence: lemma_2_1_exact chain, eigen_lb_iff_eigval_ge, poincare_separation, bracket_eq_sum, eq36, convex_expandable, paper_expandable_imp_expandable, dq_iff_density (≈1,100 lines outside today's closure).

### Phases

**P0 Baseline and guard-rails**

- Build the current working tree as is: Theorem_1_1.thy, Statement_Auxiliary removed, ell_op_sym_part, the Paper_Readings additions and the Matrix_Algebra/Envelopes edits. Use `isabelle build -b -d . -o timeout=900 Relative_Arbitrage_Statement` and `isabelle build -d . -D .`, then commit.
- Make Review_Analysis.thy's dead-code pass take roots.txt as input.
- Add a statement-fingerprint dump: an ML pass listing (base name, prop) for every fact in the closure of the roots, to diff before and after every move.
- Add a per-session re-check report from the build log, the critical-path script, and the ML ancestor check from the dry run as a regression test.
- *risk*: Low. The working-tree changes have not been built by this design; if they fail, they are fixed before anything else.
- *validation*: Both builds green. Thm_Deps.all_oracles = [] on theorem_1_1 and example_3_1_closed_form. Fingerprint baseline stored. Metrics baseline: 120,625 lines; RA build 626 s own + 560 s re-check; critical path 577 s.
- *est_effort*: 0.5 day, 1-2 commits

**P1 Paper_Map: the reader's index becomes the root set**

- New last theory Relative_Arbitrage.Paper_Map (imports Theorem_1_1). It has one `theorem` per numbered paper item (Eq. (1.9), Lemmas 2.1-2.3, Prop. 2.4 usc/halves/attainment, Def. 3.1, Eqs. (3.4)-(3.6), Lemma 3.1, Example 3.1, §3.1, §3.2, Prop. 4.1, Thm 4.2(a) continuous, Thm 4.2(b), Thm 4.3, Eq. (4.4), Remark 4.1, Theorem 1.1). Each is proved by `rule`/`OF` from the existing lemma, with a text noting every deviation: [0,T] pair laws, S = sconstraint, horizon-T DPP, the continuity hypothesis of 4.2(a), Section 5 not formalised.
- Move the numbered items lemma_2_1 and convex_sets_are_expandable from Paper_Readings to Paper_Map; Paper_Readings keeps the readings and imports Paper_Map.
- roots.txt gets every Paper_Map and Paper_Readings theorem, plus each library session's declared deliverables (including theorem_on_sums_quadratic_closed).
- Correct the false or stale prose of REVIEW_3 §1.2(f) inside the paper sessions and NOTES_FOR_AUTHORS:
  - 'k smallest eigenvalues';
  - the clause (0) comment;
  - 'proved here in full';
  - 'Eq. (1.10)';
  - 'mention nothing of this paper'.
- *risk*: Low: a new leaf theory and prose only.
- *validation*: Statement green. The dead-code script, re-run with the new roots, shows eq36, lemma_2_1_exact, poincare_separation and max_principle_boundary_holds inside the closure. Every Paper_Map statement is checked by eye against EM_final_paper.tex.
- *est_effort*: 1 day, 2-3 commits

**P2 Dead code by the roots protocol**

- (a) Drop the market imports from Exit_Class_Limits and Value_Function_Uniqueness, delete stopped_market_acov_leaves_sconstraint, then delete the 8 market theories.
- (b) ML query listing where transpose_matrix_vector is really not simp; replicate the declaration there. Move Ball_Solution's two live facts to Curvature_Operator. Delete Viscosity_Ball, Viscosity_Comparison_Interface, Ball_Solution, Comparison_Jets (Comparison_Strictness inherits its imports) and Dynamic_Programming_Optional_Sampling.
- (c) Move exit_val_dpp_sup_ge_time_of_const into Dynamic_Programming_Pasting; delete Dynamic_Programming_Kernels.
- (d) Delete the value-function dead blocks: ball Euler chain, plain Case 1, dead tanp/tanSF, deterministic-time quadratic chain, exit_val_case2_tilt_step, theorem_1_1_uniqueness_general, theorem_1_1_ball_fragment.
- (e) Delete the comparison dead blocks: the quadratic route, OEC 562-655, viscosity_uniqueness_compact, the counterexample, the dead Viscosity_Definitions variants, and SOVA.Viscosity_Solutions.
- (f) Library dead code outside the roots, session by session, iterated to a fixpoint (Moment_Bounds, the Quadratic_Variation stopped section, Path_Tightness chains, WM/SMS/SemiC unused, the toolkit's abandoned kernel route).
- *risk*: Medium-low. A deleted theory can carry declarations (simp del, unbundle inner_syntax) or notation that the fact-level analysis cannot see. Hence one deletion per commit with a build; a failing build is fixed by a local declaration or reverted.
- *validation*: Statement green and `-D .` green after each commit. Fingerprint diff on the roots shows identical statements. Dead-code script: outside-closure facts below 5%. Repository ≈ -21,000 lines.
- *est_effort*: 2-3 days, ≈15 commits

**P3 Verified drop-ins**

- Swap in the 69-line ess_inf_pexit_usc proof; delete the Laplace route and the exp_neg_time lemmas.
- Apply the 8 internal clone derivations, reordering where the special case currently precedes the general lemma.
- Move the sbmpair package (Euler 46-418) into Exit_Class_Witness and derive bmpair from it as a constant plus equation; this was checked with Exit_Class_Witness as the only import.
- Replace the library re-proofs by the library facts (Lipschitz_imp_absolutely_continuous, BMC.indep_vars_PiM_coordinate, martingale.add/diff, continuous_map_diff, Product_Vector.norm_Pair_le and the matcher's EQUIV list), correcting the three texts that claim the library lacks them.
- *risk*: Low: every replacement was checked in PIDE with an identical (aconv) statement, so no caller changes.
- *validation*: Fingerprint diff shows every replaced fact unchanged. Statement and `-D .` green. ≈ -1,900 lines.
- *est_effort*: 1-1.5 days, ≈10 commits

**P4 Import hygiene (critical path)**

- Pair_Path_Space drops Sup_Convolution, Doubling_Of_Variables, Vitali_Convergence and Brownian_FDD (verified), and the Pair_Path_Laws:203 antiquotation goes.
- Exit_Class_Infinite imports Exit_Class_Pasting instead of Dynamic_Programming_Assembly.
- Covariation_Density imports library theories only.
- Value_Function_Euler_Construction imports Exit_Class_Optimizer/Witness instead of Value_Function_Subsolution.
- Value_Function_Tangential_Field imports Case_1, not Case_2.
- Operator_Continuity imports Ky_Fan, not Eigenvalue_Bound_Exact.
- Library imports per actual_imports.txt: Optional_Sampling, Stopped_Adaptedness, Equicontinuity, Holder_Interpolation, Adapted_QV, Stopped_Localization, Jensen_Lemma, Rademacher, Theorem_On_Sums, Gaussian_Increments.
- *risk*: Low-medium: notation, abbreviations and instances are invisible to the named-fact analysis. One import change per commit, reverted individually.
- *validation*: Green. Critical-path script: ≤ 400 s on the current graph (the simulation on the used-fact DAG after P2 gives 327 s).
- *est_effort*: 1 day

**P5 Library parents**

- Second_Order_Viscosity_Analysis = Symmetric_Matrix_Spectra (drop `sessions`).
- Wiener_Measure = Continuous_Time_Martingales + sessions Kolmogorov_Chentsov.
- Move Semicontinuous_Selection to Continuous_Path_Spaces (requalify its 4 importers); Semicontinuous_Analysis = HOL-Analysis + Lower_Semicontinuous.
- Move cInf_mult_pos into Curvature_Operator; the two importers of Integrability_Criteria in the analytic layer drop that import. This keeps the layer probability-free.
- Optional: copy Arzela-Ascoli locally with attribution (≈180 lines) to drop HOL-Complex_Analysis: −226 s and −13,371 re-checked lines per CPS build.
- *risk*: Low: no proof changes; only qualified names and @{theory} antiquotations of the moved theory change.
- *validation*: All sessions green. The re-check report shows Semicontinuous_Analysis without HOL-Probability ancestors.
- *est_effort*: 1 day

**P6 Path_Space_Operations**

- New directory and ROOT (parent Continuous_Path_Spaces; sessions SMS, SemiC, Disintegration, LPM), with document and root.bib.
- git mv the six toolkit theories unchanged.
- Requalify the ≈25 Relative_Arbitrage importers and the @{theory Relative_Arbitrage.Pair_Path_Laws} antiquotation.
- Relative_Arbitrage's parent becomes Path_Space_Operations.
- *risk*: Low: dry run checked (0 errors, no SOVA ancestor).
- *validation*: Green. Fingerprint shows all moved facts identical modulo qualifier. In the re-check report, SMS, Disintegration and S_Finite move from the Relative_Arbitrage build to the PSO build.
- *est_effort*: 0.5-1 day

**P7 Relative_Arbitrage_Equation**

- Create Relative_Arbitrage/Equation with `session Relative_Arbitrage_Equation in "Equation" = Path_Space_Operations + sessions SMS SOVA SemiC Lower_Semicontinuous`.
- git mv the 12 surviving analytic theories: Curvature_Operator, Viscosity_Definitions, Constraint_Set_Convexity, Eigenvalue_Bound_Exact, Operator_Continuity, Operator_Formula, Operator_Envelopes, Operator_Envelope_Continuity, Comparison_Strictness, Comparison_Localisation, Comparison_Principle, Comparison_Two_Domain.
- Requalify importers and the ≈27 @{theory Relative_Arbitrage.<analytic>} antiquotations.
- Relative_Arbitrage = Relative_Arbitrage_Equation.
- *risk*: Low: the dry run checked these theories with only SMS/SOVA/SemiC ancestors, and the chosen parent does not change any theory's imports.
- *validation*: Green. The ancestor check reports no HOL-Probability, CTM, CPS or PSO ancestor in any Relative_Arbitrage_Equation theory. Re-check report: Relative_Arbitrage re-checks only WM, KC and LPM (≈140 s).
- *est_effort*: 0.5-1 day

**P8 Paper order inside both paper sessions (moves and renames only)**

- Relative_Arbitrage_Equation:
  - rename Curvature_Operator to Elliptic_Operator and Comparison_Principle to Maximum_Principle;
  - concatenate Eigenvalue_Bound_Exact into Constraint_Set_Convexity, Operator_Continuity into Operator_Formula, and Operator_Envelope_Continuity into Operator_Envelopes (no base-name clashes, checked on facts.tsv; both halves already carry unbundle inner_syntax);
  - move expandable/convex_expandable from SOVA.Test_Functions into Comparison_Two_Domain;
  - put the ROOT in paper order.
- Relative_Arbitrage, §1-§2:
  - M1-M3: create Control_Problem from the Exit_Class 23-209 sconstraint block, feasible_subset_sconstraint, and the xclass/xval block of Exit_Class_Marginals;
  - M4: exit_val_zero_outside into Exit_Class.
- Relative_Arbitrage, §3:
  - M5: the region chain (Case_1 1119-2065) to the end of Value_Function_Euler_Construction;
  - M6: the live tanp/uvec bricks into Tangential_Field (renamed);
  - M7-M10: Example_3_1 = Value_Function_Assembly renamed + Case_1 2065-2648 + subspace_tangential_exact_growth + Value_Function_Uniqueness 291-554 and example_3_1_uncapped;
  - M11: the envelope Case 1 (Case_2 15-583) into Case_1.
- Relative_Arbitrage, assembly:
  - M12: Value_Function_Uniqueness becomes Value_Function_Clauses;
  - ROOT in paper order (§1, §2, bridge, DPP, §3, clauses, Theorem_1_1, Paper_Map);
  - root.tex gets one part per paper section.
- Optional library returns:
  - Euler/Case-2 helpers (≈1,500 lines) from Path_Space_Operations.Pair_Path_Laws back to §3;
  - Brownian lemmas from Exit_Class_Witness to WM.Brownian_Coordinates;
  - outerp family, sconstraint_orth_feasible matrix toolkit, poincare_separation and eigval_ge_of_subspace to SMS (keep outerp a definition);
  - pball_exit to CPS.Path_Exit_Times.
- *risk*: Medium in aggregate: about 20 block moves, and the known traps are prose antiquotations, topological order inside the target file, and text blocks detached from their lemmas. Each move is mitigated by a dependency check on facts.tsv (done for M1-M12: no dependency on a later theory), one commit, one build, and a zero-diff fingerprint.
- *validation*: Green after each move. Fingerprint identical (moves may not change any statement). Paper_Map unchanged. A script checks that the ROOT order of both paper sessions matches the paper-section table.
- *est_effort*: 3-4 days, ≈20 commits

**P9 Paper results not yet stated (gated leaf additions)**

- (a) Proposition_2_4: the equality at deterministic and stopping times from exit_val_dpp_sup_ge_time and exit_val_cond_time (pathwise case split), with attainment by optimisers, in horizon-T form. Budget 150 lines; otherwise correct the prose and keep the halves in Paper_Map.
- (b) Optional: Theorem 4.2(a) for usc/lsc data with the Def. 3.1 predicates, reusing the two-domain engine. Budget 400 lines; otherwise keep the continuous version.
- (c) Optional G-B pilot: Lemma 2.2 for bounded S over covariation_class S (budget 300 lines); Lemma 2.3 for compact convex S only if the pilot passes.
- (d) Optional: Propositions 5.1-5.2 via dilation plus Theorem 4.2(b). Budget 400 lines.
- *risk*: Low for the development, because every item is a leaf and is reverted when it misses its budget. Medium for effort.
- *validation*: Green. The Paper_Map entry is upgraded from 'halves'/'continuous data' to the paper's form, and the new theorems are added to roots.txt.
- *est_effort*: 1 day for (a); 2-4 days for each optional item

**P10 Prose, scopes and notes**

- Remove the 119 lines of paper prose from 28 library theories and from the library ROOT descriptions; library ROOTs get the one-sentence scopes above.
- Repair the 168 'X lives in Y' pointer texts and the ≈60 detached text blocks.
- Paper root.tex files: abstract lists what is and is not formalised (Section 5).
- Notes: drop STATUS.md's eigen_lb_dim_obstruction claim, refresh UNUSED_THMS.md and OPEN_ITEMS.md, and fix the Statement ROOT's 'a single theory'.
- *risk*: Low: text only, and the build checks antiquotations.
- *validation*: grep for the paper's name, 'Eq. (', 'Lemma 2.', 'Theorem 1.1' and 'paper' over the seven library sessions returns 0. All sessions green.
- *est_effort*: 1-2 days

### Quantified effects

How these numbers were made. Lines come from the measured file lengths, minus the measured dead-line estimates and the verified simplifications, plus the evidence that is now rooted. CPU figures sum the measured per-theory times from build.log (3 threads); the time of a theory that loses dead code is scaled by its dead-line share. All results are estimates unless marked measured.

LINES
- Total: 120,625 → ≈94,500 (−26,000, −21%).
- Paper: Relative_Arbitrage (64,967 lines, 55 theories, measured) → Relative_Arbitrage_Equation ≈10,200 (9 theories) + Relative_Arbitrage ≈25,000 (27 theories), i.e. −46%. Statement 667 → ≈650.
- Libraries:
  - SMS 7,601 → ≈7,300
  - SemiC 2,318 → ≈1,300
  - SOVA 18,473 → ≈15,300
  - CTM 9,281 → ≈8,100
  - WM 3,801 → ≈3,500
  - CPS 13,517 → ≈9,300
  - Path_Space_Operations (new) ≈14,000, from 17,230 moved
- Kept on purpose though outside today's closure: Theorem 4.2(a) ≈1,600; Crandall_Ishii_Sums with its support ≈3,200; faithfulness evidence ≈1,100.
- Facts outside the closure of the roots: 2,371 of 4,793 (measured) → below 5%.
- Theories: 112 → ≈106.

RE-CHECKING (non-ancestor sessions re-checked inside a build)
- Relative_Arbitrage build: 40,344 re-checked lines and 560 s (measured) → 7,150 lines and ≈140 s (WM 40, KC 76, LPM 24).
- Relative_Arbitrage_Equation build: ≈16-21k lines, ≈160 s (SOVA ≈100, Lower_Semicontinuous 30, SMS remainder ≈24, SemiC ≈4).
- Path_Space_Operations build: ≈13-16k lines, ≈255-310 s (SMS subset ≈83, Disintegration 90, S_Finite 79, SemiC/Lower_Semicontinuous).
- CPS build: 33,845 lines and 881 s (measured) → ≈855 s, or ≈630 s and 20,500 lines with the optional Arzelà–Ascoli copy.
- The total re-checked by a cold Statement build barely moves (≈71-79k lines, from 77k). The design does not remove re-checking; it moves it out of the session that is rebuilt most often.

BUILD CPU AND WALL TIME
- Relative_Arbitrage: 1,186 s (626 own + 560 re-check, measured) → ≈385 s (≈245 own + ≈140).
- Relative_Arbitrage_Equation ≈230 s; Path_Space_Operations ≈430 s; CPS 1,010 → ≈960 s (≈735 s with the Arzelà–Ascoli copy); CTM 166 → ≈158 s.
- Edit loops (edit, then rebuild Relative_Arbitrage and the Statement):
  - after a Section 2-3 edit: ≈1,190 s → ≈390 s CPU; wall ≈9:40 → ≈3:45;
  - after a Section 4 edit: ≈1,190 s → ≈620 s (Relative_Arbitrage_Equation + Relative_Arbitrage).
- Cold Statement build, sum over user sessions: ≈2,370 s → ≈2,170 s CPU (≈1,945 s with the Arzelà–Ascoli copy). Wall ≈18:45 → ≈17:50 (≈16:10).
- Parallel alternative, with SOVA as the parent of the Equation session: every Relative_Arbitrage rebuild re-checks ≈370 s, so ≈615 s per §2-3 edit; cold-build cost is about equal. The chain saves ≈230 s CPU (≈1:45 wall) on every §2-3 rebuild.

CRITICAL PATH (sum of CPU along the longest import chain of user theories)
- Today: 577 s over 35 theories (measured).
- After: ≈330 s over ≈22 theories. Simulated on the used-fact DAG after P2/P4: 327 s. Drivers:
  - the toolkit no longer waits for Doubling_Of_Variables and Theorem_On_Sums (−38 s);
  - the class chain no longer waits for the market layer (−31 s);
  - Dynamic_Programming_Kernels is gone (−14 s);
  - Exit_Class_Infinite and Exit_Class_Marginals leave the DPP chain;
  - dead code inside the theories on the path is gone.
- Session serialisation in the chain adds the Equation session's internal path (≈125 s CPU) before Relative_Arbitrage can start.

PAPER COVERAGE
- Every numbered item of Sections 1-4 has a Paper_Map entry (Remark 1.1(b) is only a candidate, to be confirmed or marked not stated).
- Items stated in the paper's form today: Theorem 1.1, Example 3.1, Lemma 2.1, Lemma 3.1 (eq36 newly rooted), Proposition 4.1, Theorem 4.2(b) (with supersol_bc_nonneg) and Theorem 4.3.
- Items stated in a disclosed weaker or working form:
  - Lemmas 2.2 and 2.3 (pair laws on [0,T], S = sconstraint);
  - Proposition 2.4 (halves at horizon T, until P9a);
  - Theorem 4.2(a) (continuous data).
- Section 5 is declared not formalised.

### Risks and open questions

- D1 is a trade-off. With the chain, the Equation session's heap contains the probability stack. Anyone who wants only Section 4 must build CTM, CPS and Path_Space_Operations first, and Section 4 is still built after the probability stack, which REVIEW_3 §6.2 criticises. The content stays probability-free (checked by the ancestor regression test), and switching to `= Second_Order_Viscosity_Analysis` is a one-line ROOT change that costs ≈230 s on every Relative_Arbitrage rebuild. This should be confirmed by measurement after P7.
- D2 keeps ≈1,600 lines for a Theorem 4.2(a) weaker than the paper's. The alternative is PLAN_3's deletion, or the gated faithful version in P9b. Open question: does the author value 4.2(a) 'of independent interest' enough to keep it?
- VCI's global `declare transpose_matrix_vector [simp del]`. Simpset merges are unions, so the inherited deletion may already be void wherever another import carries the rule. Re-declaring it blindly at Exit_Class or Operator_Envelopes could therefore change behaviour, so P2b first measures, by ML, where the rule is really absent, and replicates the declaration exactly there.
- The fact-level analyses (placement, needed imports, the M1-M12 dependency checks) see named facts and constants. They do not see notation, abbreviations, type-class instances, bundles (unbundle inner_syntax) or simp declarations. Every move and import change therefore needs its own build, and P8 has ≈20 such steps.
- Prose antiquotations: 38 @{theory Relative_Arbitrage.X} occurrences in 19 files, plus @{thm}/@{const} references to facts declared later in a target file. These broke builds in PLAN_2's moves; each move requalifies them or turns them into plain cartouches.
- The Phase-1 changes in the working tree are uncommitted and their build status is unknown to this design. P0 must build them before anything else.
- Name changes caused by renames and moves (Curvature_Operator → Elliptic_Operator, Comparison_Principle → Maximum_Principle, xclass/xval → Control_Problem, Value_Function_* renames) break qualified references in notes/review_3/Review_Analysis.thy, Faithfulness_Checks.thy, theorem_1_1_unfolded.html and the notes. These are outside every session and must be updated by hand.
- Lemmas 2.2/2.3 remain stated for pair laws on C([0,T]) at S = sconstraint k L, not for P_x on C([0,∞)) for general S. G-B is gated (P9c), and the previous plan recorded four lemmas that resisted generalisation. Paper_Map states the gap; it does not hide it.
- Proposition 2.4 is formalised with the finite-horizon value v_{T-θ} in the integrand (a deliberate design). Even after P9a it is a horizon-T DPP, not the paper's infinite-horizon one.
- Ten sessions rather than eight. Folding Path_Space_Operations into Continuous_Path_Spaces gives nine, at ≈250-300 s per CPS rebuild and a two-subject CPS entry.
- The optional Arzelà–Ascoli copy is itself a library clone; it is preferable to ask upstream to move Arzela_Ascoli out of Great_Picard.
- Deferred on purpose, as re-proofs that a paper reader does not need:
  - the X-versus-compensated twins (≈2,450 lines), coordinate-versus-generic F-chain (≈1,260), ball-versus-region and quadratic-versus-general twins, and the dyadic-grid and optional-sampling twins in CTM/CPS;
  - G-C, the abstract geometric operator: the 23-fact interface is recorded in Paper_Map for a future library extraction;
  - G-G, one viscosity predicate family.
  Together they hold an estimated 8-10k further lines.
- Library deliverables (the roots of library sessions) need an explicit decision per session before P2f: for example, keep the dead C([0,∞)) projective limit in Path_Tightness, or the general path_rcd in Path_Law_Pasting? This design defaults to deleting what no declared deliverable reaches.
- Timings are 3-thread CPU sums on a 4-core VM; wall-clock values divide by the measured parallelism factor of about 2.1. Scaling a theory's time by its dead-line share is an approximation, so the estimates should be re-measured after P2, P7 and P8.

