# The one remaining construction

Everything of the bridge to the paper's uncapped Theorem 1.1 is proved except

    Q : exit_class k L T x
      ==> EX P : iexit_class k L x. pair_law_of T (pcut T) P = Q

stated verbatim as the `ext` hypothesis of
`Relative_Arbitrage.Exit_Class_Infinite.iexit_val_eq_of_extension`.  Discharging
it gives `v_infinity = v_T` wherever the horizon does not bind, and the five
clauses of Theorem 1.1 then transport to the paper's own value function by
rewriting -- no viscosity, comparison or DPP argument is touched.

## Route

It follows the construction of Wiener measure in
`Wiener_Measure.Brownian_Motion`, which is the same shape: a projective limit
on a product space, then a continuous modification.

1. **The compatible family.**  With `R n : exit_class k L (T*n) 0` from
   `exit_class_nonempty` (legitimate since `L >= 1`, via
   `mat_1_in_sconstraint`), set `Q 0 = Q` and
   `Q (n+1) = pglue_law (T*(n+1)) (T*(n+2)) (Q n) (R 1)`.
   Membership is `exit_class_pglue_law`.  Compatibility -- that each cut
   returns the previous law -- is `pcut_pglue` together with
   `pcut_id_on_mspace`, both proved.

2. **Finite-dimensional distributions.**  For finite `J <= {0..}` choose `n`
   with `Max J <= T*(n+1)` and put
   `ext_fdd J = distr (Q n) (PiM J (%_. borel)) (%w. restrict w J)`.
   Well-definedness is step 1's compatibility.

3. **The projective limit.**  `interpretation polish_projective "{0..}" ext_fdd`
   exactly as `Brownian_Motion.thy:863`; the limit is a measure on
   `PiM {0..} (%_. borel)` whose marginals are the `ext_fdd`
   (`wiener_pre_marginal` is the model).

4. **A continuous modification.**  The limit's paths are arbitrary functions.
   The fourth-moment bound of `Path_Space_Tightness.Increment_Moments` gives
   the Kolmogorov--Chentsov criterion for members of the class, so the AFP
   entry supplies a modification with continuous paths, as in
   `Wiener_Measure.Brownian_Motion_Continuity`.

5. **Into the half-line path space.**  Push the modification through
   `Path_Space_Tightness.Path_Space_Infinite.ipathify_measurable` to get a law
   on `ipath_space`.

6. **The four clauses.**  Transfer them from the `Q n` to the modification.
   `Relative_Arbitrage.Modification_Transfer` moves a martingale property to
   the natural filtration of a modification, which is the awkward one; the
   start and covariation clauses are almost-sure statements at countably many
   times and follow from the marginals.

## Where the cost is

Steps 1--3 are mechanical given what is proved.  Steps 4 and 6 are the bulk:
they amount to redoing `exit_class_nonempty` with a prescribed prefix, and the
martingale clause under a modification is the delicate part.
