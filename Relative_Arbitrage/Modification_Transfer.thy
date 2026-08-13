
(*<*)
theory Modification_Transfer
  imports Ito_Market
begin

(*>*)

text \<open>
  Transferring the vanishing of increment integrals to a modification,
             the resulting martingale transfer theorems, and the reduction of
             vector martingales to their components.  Together with
             \<open>martingale_of_set_integral_eq\<close> this gives the martingale property of
             a modification for its own natural filtration, which is what makes
             the continuous Kolmogorov-Chentsov modification usable as a market.\<close>
text \<open>A modification agrees with the process almost surely at each fixed
  time, but their natural filtrations agree only up to null sets, so
  adaptedness --- and with it the martingale property --- does not transfer
  for free.  What does transfer is

    \<open>int_A\<close> (\<open>X'_j\<close> - \<open>X'_i\<close>) = 0  for A in the natural filtration of X' at i,

  because a cylinder event of the modification has almost surely the same
  indicator as the corresponding cylinder event of the process, and cylinders
  form an intersection-stable generator, so a Dynkin induction extends the
  identity to the whole filtration.\<close>

section \<open>Cylinder events of a process\<close>

definition cylset ::
  "'a measure \<Rightarrow> (real \<Rightarrow> 'a \<Rightarrow> 'b :: topological_space) \<Rightarrow> real
     \<Rightarrow> 'a set set" where
  "cylset M X t = {space M \<inter> (\<Inter>p\<in>P. X (fst p) -` snd p) | P.
     finite P \<and> (\<forall>p\<in>P. fst p \<in> {0..t} \<and> snd p \<in> sets borel)}"

lemma cylset_single:
  assumes u: "u \<in> {0..t}" and B: "B \<in> sets borel"
  shows "X u -` B \<inter> space M \<in> cylset M X t"
proof -
  show ?thesis
    unfolding cylset_def
    using u B by (intro CollectI exI[of _ "{(u, B)}"]) auto
qed

lemma cylset_subset_Pow: "cylset M X t \<subseteq> Pow (space M)"
  unfolding cylset_def by auto

lemma Int_stable_cylset: "Int_stable (cylset M X t)"
proof (intro Int_stableI)
  fix A B assume AB: "A \<in> cylset M X t" "B \<in> cylset M X t"
  from AB(1) obtain P where
    P: "A = space M \<inter> (\<Inter>p\<in>P. X (fst p) -` snd p)" "finite P"
      "\<forall>p\<in>P. fst p \<in> {0..t} \<and> snd p \<in> sets borel"
    unfolding cylset_def by blast
  from AB(2) obtain Q where
    Q: "B = space M \<inter> (\<Inter>p\<in>Q. X (fst p) -` snd p)" "finite Q"
      "\<forall>p\<in>Q. fst p \<in> {0..t} \<and> snd p \<in> sets borel"
    unfolding cylset_def by blast
  have eq: "A \<inter> B = space M \<inter> (\<Inter>p\<in>P \<union> Q. X (fst p) -` snd p)"
    unfolding P(1) Q(1) by auto
  have fin: "finite (P \<union> Q)"
    using P(2) Q(2) by simp
  have all: "\<forall>p\<in>P \<union> Q. fst p \<in> {0..t} \<and> snd p \<in> sets borel"
    using P(3) Q(3) by auto
  show "A \<inter> B \<in> cylset M X t"
    unfolding cylset_def using eq fin all by blast
qed

lemma cylset_in_natural_filtration:
  assumes X: "\<And>u. 0 \<le> u \<Longrightarrow> X u \<in> borel_measurable M"
    and A: "A \<in> cylset M X t"
  shows "A \<in> sets (natural_filtration M 0 X t)"
proof -
  from A obtain P where
    P: "A = space M \<inter> (\<Inter>p\<in>P. X (fst p) -` snd p)" "finite P"
      "\<forall>p\<in>P. fst p \<in> {0..t} \<and> snd p \<in> sets borel"
    unfolding cylset_def by blast
  have gen: "X (fst p) -` snd p \<inter> space M
      \<in> sets (natural_filtration M 0 X t)" if p: "p \<in> P" for p
  proof -
    have "X (fst p) -` snd p \<inter> space M
        \<in> (\<Union>i\<in>{0..t}. {X i -` B \<inter> space M | B. B \<in> sets borel})"
      using P(3) p by blast
    then show ?thesis
      unfolding sets_natural_filtration by (intro sigma_sets.Basic) simp
  qed
  show ?thesis
  proof (cases "P = {}")
    case True
    have "space (natural_filtration M 0 X t)
        \<in> sets (natural_filtration M 0 X t)"
      by (rule sets.top)
    then show ?thesis
      unfolding P(1) True by simp
  next
    case False
    have "A = (\<Inter>p\<in>P. X (fst p) -` snd p \<inter> space M)"
      unfolding P(1) using False by auto
    also have "\<dots> \<in> sets (natural_filtration M 0 X t)"
      using P(2) False gen by (intro sets.finite_INT) auto
    finally show ?thesis .
  qed
qed

lemma sigma_sets_cylset:
  assumes X: "\<And>u. 0 \<le> u \<Longrightarrow> X u \<in> borel_measurable M"
  shows "sigma_sets (space M) (cylset M X t)
     = sets (natural_filtration M 0 X t)"
proof (rule antisym)
  show "sigma_sets (space M) (cylset M X t)
      \<subseteq> sets (natural_filtration M 0 X t)"
  proof (rule sigma_algebra.sigma_sets_subset)
    show "sigma_algebra (space M) (sets (natural_filtration M 0 X t))"
      using sets.sigma_algebra_axioms[of "natural_filtration M 0 X t"]
      by simp
    show "cylset M X t \<subseteq> sets (natural_filtration M 0 X t)"
      using X by (auto intro: cylset_in_natural_filtration)
  qed
  show "sets (natural_filtration M 0 X t)
      \<subseteq> sigma_sets (space M) (cylset M X t)"
    unfolding sets_natural_filtration
  proof (rule sigma_algebra.sigma_sets_subset)
    show "sigma_algebra (space M) (sigma_sets (space M) (cylset M X t))"
      using cylset_subset_Pow by (rule sigma_algebra_sigma_sets)
    show "(\<Union>i\<in>{0..t}. {X i -` A \<inter> space M | A. A \<in> sets borel})
        \<subseteq> sigma_sets (space M) (cylset M X t)"
      by (auto intro!: cylset_single)
  qed
qed

lemma cylset_indicator_AE_eq:
  assumes ae: "\<And>u. u \<in> {0..t} \<Longrightarrow> AE \<omega> in M. X' u \<omega> = X u \<omega>"
    and P: "finite P" and P2: "\<forall>p\<in>P. fst p \<in> {0..t} \<and> snd p \<in> sets borel"
  shows "AE \<omega> in M.
    indicat_real (space M \<inter> (\<Inter>p\<in>P. X' (fst p) -` snd p)) \<omega>
      = indicat_real (space M \<inter> (\<Inter>p\<in>P. X (fst p) -` snd p)) \<omega>"
proof -
  have "AE \<omega> in M. \<forall>p\<in>P. X' (fst p) \<omega> = X (fst p) \<omega>"
  proof (intro AE_finite_allI P)
    fix p assume "p \<in> P"
    then have "fst p \<in> {0..t}"
      using P2 by auto
    then show "AE \<omega> in M. X' (fst p) \<omega> = X (fst p) \<omega>"
      by (rule ae)
  qed
  then show ?thesis
  proof eventually_elim
    case (elim \<omega>)
    have "\<omega> \<in> space M \<inter> (\<Inter>p\<in>P. X' (fst p) -` snd p)
        \<longleftrightarrow> \<omega> \<in> space M \<inter> (\<Inter>p\<in>P. X (fst p) -` snd p)"
      using elim by auto
    then show ?case
      by (simp add: indicator_def)
  qed
qed

section \<open>Increments integrate to zero over the past of a modification\<close>

theorem set_integral_zero_transfer:
  fixes D D' :: "'a \<Rightarrow> real"
    and X X' :: "real \<Rightarrow> 'a \<Rightarrow> 'b :: {second_countable_topology, banach}"
  assumes X: "\<And>u. 0 \<le> u \<Longrightarrow> X u \<in> borel_measurable M"
    and X': "\<And>u. 0 \<le> u \<Longrightarrow> X' u \<in> borel_measurable M"
    and ae: "\<And>u. u \<in> {0..t} \<Longrightarrow> AE \<omega> in M. X' u \<omega> = X u \<omega>"
    and D_int: "integrable M D" and D'_int: "integrable M D'"
    and ae_D: "AE \<omega> in M. D' \<omega> = D \<omega>"
    and zero: "\<And>B. B \<in> sets (natural_filtration M 0 X t)
      \<Longrightarrow> (\<integral>\<omega>. indicat_real B \<omega> * D \<omega> \<partial>M) = 0"
    and A: "A \<in> sets (natural_filtration M 0 X' t)"
  shows "(\<integral>\<omega>. indicat_real A \<omega> * D' \<omega> \<partial>M) = 0"
proof -
  have subalg: "sets (natural_filtration M 0 Y t) \<subseteq> sets M"
    if Y: "\<And>u. 0 \<le> u \<Longrightarrow> Y u \<in> borel_measurable M"
    for Y :: "real \<Rightarrow> 'a \<Rightarrow> 'b"
  proof -
    interpret SP: stochastic_process M 0 Y
      by unfold_locales (auto intro: Y)
    show ?thesis
      using SP.subalgebra_natural_filtration by (simp add: subalgebra_def)
  qed
  have A_cyl: "A \<in> sigma_sets (space M) (cylset M X' t)"
    using A X' by (simp add: sigma_sets_cylset)
  have sets_M: "B \<in> sets M"
    if "B \<in> sigma_sets (space M) (cylset M X' t)" for B
  proof -
    have "B \<in> sets (natural_filtration M 0 X' t)"
      using that X' by (simp add: sigma_sets_cylset)
    then show ?thesis
      using subalg[OF X'] by (rule rev_subsetD)
  qed
  have int_ind: "integrable M (\<lambda>\<omega>. indicat_real C \<omega> * D' \<omega>)"
    if C: "C \<in> sets M" for C
  proof -
    have "integrable M (\<lambda>\<omega>. indicat_real C \<omega> *\<^sub>R D' \<omega>)"
      by (intro integrable_mult_indicator C D'_int)
    then show ?thesis by simp
  qed
  have int_ind0: "integrable M (\<lambda>\<omega>. indicat_real C \<omega> * D \<omega>)"
    if C: "C \<in> sets M" for C
  proof -
    have "integrable M (\<lambda>\<omega>. indicat_real C \<omega> *\<^sub>R D \<omega>)"
      by (intro integrable_mult_indicator C D_int)
    then show ?thesis by simp
  qed
  have space_nf: "space M \<in> sets (natural_filtration M 0 X t)"
    using sets.top[of "natural_filtration M 0 X t"] by simp
  show ?thesis
    using Int_stable_cylset cylset_subset_Pow A_cyl
  proof (induct rule: sigma_sets_induct_disjoint)
    case (basic B)
    then obtain P where
      P: "B = space M \<inter> (\<Inter>p\<in>P. X' (fst p) -` snd p)" "finite P"
        "\<forall>p\<in>P. fst p \<in> {0..t} \<and> snd p \<in> sets borel"
      unfolding cylset_def by blast
    define B0 where "B0 = space M \<inter> (\<Inter>p\<in>P. X (fst p) -` snd p)"
    have B0_cyl: "B0 \<in> cylset M X t"
      unfolding B0_def cylset_def using P(2,3) by blast
    have B0_sets: "B0 \<in> sets (natural_filtration M 0 X t)"
      using X B0_cyl by (rule cylset_in_natural_filtration)
    have B0_M: "B0 \<in> sets M"
      by (rule subsetD[OF subalg[OF X] B0_sets])
    have B_M: "B \<in> sets M"
    proof (rule sets_M)
      show "B \<in> sigma_sets (space M) (cylset M X' t)"
        using basic by (rule sigma_sets.Basic)
    qed
    have ae_ind: "AE \<omega> in M. indicat_real B \<omega> * D' \<omega>
        = indicat_real B0 \<omega> * D \<omega>"
    proof -
      have "AE \<omega> in M. indicat_real B \<omega> = indicat_real B0 \<omega>"
        unfolding P(1) B0_def
        by (rule cylset_indicator_AE_eq[where t = t, OF ae P(2) P(3)])
      with ae_D show ?thesis
        by eventually_elim simp
    qed
    have m1: "(\<lambda>\<omega>. indicat_real B \<omega> * D' \<omega>) \<in> borel_measurable M"
      using int_ind[OF B_M] by (rule borel_measurable_integrable)
    have m2: "(\<lambda>\<omega>. indicat_real B0 \<omega> * D \<omega>) \<in> borel_measurable M"
      using int_ind0[OF B0_M] by (rule borel_measurable_integrable)
    have "(\<integral>\<omega>. indicat_real B \<omega> * D' \<omega> \<partial>M)
        = (\<integral>\<omega>. indicat_real B0 \<omega> * D \<omega> \<partial>M)"
      by (rule integral_cong_AE[OF m1 m2 ae_ind])
    also have "\<dots> = 0"
      by (rule zero[OF B0_sets])
    finally show ?case .
  next
    case empty
    show ?case by simp
  next
    case (compl B)
    have B_M: "B \<in> sets M"
      using compl(1) by (rule sets_M)
    have space_M: "space M \<in> sets M"
      by (rule sets.top)
    have space_zero: "(\<integral>\<omega>. indicat_real (space M) \<omega> * D' \<omega> \<partial>M) = 0"
    proof -
      have ae_sp: "AE \<omega> in M. indicat_real (space M) \<omega> * D' \<omega>
          = indicat_real (space M) \<omega> * D \<omega>"
        using ae_D by eventually_elim simp
      have s1: "(\<lambda>\<omega>. indicat_real (space M) \<omega> * D' \<omega>)
          \<in> borel_measurable M"
        using int_ind[OF space_M] by (rule borel_measurable_integrable)
      have s2: "(\<lambda>\<omega>. indicat_real (space M) \<omega> * D \<omega>)
          \<in> borel_measurable M"
        using int_ind0[OF space_M] by (rule borel_measurable_integrable)
      have "(\<integral>\<omega>. indicat_real (space M) \<omega> * D' \<omega> \<partial>M)
          = (\<integral>\<omega>. indicat_real (space M) \<omega> * D \<omega> \<partial>M)"
        by (rule integral_cong_AE[OF s1 s2 ae_sp])
      also have "\<dots> = 0"
        by (rule zero[OF space_nf])
      finally show ?thesis .
    qed
    have "(\<integral>\<omega>. indicat_real (space M - B) \<omega> * D' \<omega> \<partial>M)
        = (\<integral>\<omega>. indicat_real (space M) \<omega> * D' \<omega>
            - indicat_real B \<omega> * D' \<omega> \<partial>M)"
      by (intro Bochner_Integration.integral_cong refl)
        (simp add: indicator_def)
    also have "\<dots> = (\<integral>\<omega>. indicat_real (space M) \<omega> * D' \<omega> \<partial>M)
        - (\<integral>\<omega>. indicat_real B \<omega> * D' \<omega> \<partial>M)"
      by (intro Bochner_Integration.integral_diff int_ind space_M B_M)
    also have "\<dots> = 0"
      using space_zero compl(2) by simp
    finally show ?case .
  next
    case (union Bs)
    have Bs_M: "Bs i \<in> sets M" for i
      by (rule sets_M[OF subsetD[OF union(2) rangeI]])
    have partial: "(\<integral>\<omega>. indicat_real (\<Union>i<n. Bs i) \<omega> * D' \<omega> \<partial>M) = 0"
      for n
    proof -
      have dfn: "disjoint_family_on Bs {..<n}"
        using union(1) unfolding disjoint_family_on_def by auto
      have ind_sum: "indicat_real (\<Union>i<n. Bs i) \<omega>
          = (\<Sum>i<n. indicat_real (Bs i) \<omega>)" for \<omega>
        by (intro indicator_UN_disjoint finite_lessThan dfn)
      have "(\<integral>\<omega>. indicat_real (\<Union>i<n. Bs i) \<omega> * D' \<omega> \<partial>M)
          = (\<integral>\<omega>. (\<Sum>i<n. indicat_real (Bs i) \<omega> * D' \<omega>) \<partial>M)"
        by (intro Bochner_Integration.integral_cong refl)
          (simp add: ind_sum sum_distrib_right)
      also have "\<dots> = (\<Sum>i<n. (\<integral>\<omega>. indicat_real (Bs i) \<omega> * D' \<omega> \<partial>M))"
        by (intro Bochner_Integration.integral_sum int_ind Bs_M)
      also have "\<dots> = 0"
        using union(3) by simp
      finally show ?thesis .
    qed
    have UN_M: "(\<Union>i. Bs i) \<in> sets M"
      by (rule sets.countable_UN) (intro image_subsetI Bs_M)
    have finUN_M: "(\<Union>i<n. Bs i) \<in> sets M" for n
      by (rule sets.finite_UN[OF finite_lessThan]) (rule Bs_M)
    have "(\<lambda>n. (\<integral>\<omega>. indicat_real (\<Union>i<n. Bs i) \<omega> * D' \<omega> \<partial>M))
        \<longlonglongrightarrow> (\<integral>\<omega>. indicat_real (\<Union>i. Bs i) \<omega> * D' \<omega> \<partial>M)"
    proof (rule integral_dominated_convergence
        [where w = "\<lambda>\<omega>. \<bar>D' \<omega>\<bar>"])
      show "integrable M (\<lambda>\<omega>. \<bar>D' \<omega>\<bar>)"
        by (intro integrable_abs D'_int)
      show "(\<lambda>\<omega>. indicat_real (\<Union>i. Bs i) \<omega> * D' \<omega>) \<in> borel_measurable M"
        using int_ind[OF UN_M] by (rule borel_measurable_integrable)
      show "(\<lambda>\<omega>. indicat_real (\<Union>i<n. Bs i) \<omega> * D' \<omega>)
          \<in> borel_measurable M" for n
        using int_ind[OF finUN_M] by (rule borel_measurable_integrable)
      show "AE \<omega> in M. (\<lambda>n. indicat_real (\<Union>i<n. Bs i) \<omega> * D' \<omega>)
          \<longlonglongrightarrow> indicat_real (\<Union>i. Bs i) \<omega> * D' \<omega>"
      proof (intro AE_I2)
        fix \<omega>
        show "(\<lambda>n. indicat_real (\<Union>i<n. Bs i) \<omega> * D' \<omega>)
            \<longlonglongrightarrow> indicat_real (\<Union>i. Bs i) \<omega> * D' \<omega>"
        proof (cases "\<omega> \<in> (\<Union>i. Bs i)")
          case True
          then obtain i0 where i0: "\<omega> \<in> Bs i0" by blast
          have ev: "\<forall>\<^sub>F n in sequentially.
              indicat_real (\<Union>i<n. Bs i) \<omega> * D' \<omega>
                = indicat_real (\<Union>i. Bs i) \<omega> * D' \<omega>"
          proof (intro eventually_sequentiallyI[of "Suc i0"])
            fix n assume "Suc i0 \<le> n"
            then have "\<omega> \<in> (\<Union>i<n. Bs i)"
              using i0 by auto
            moreover have "\<omega> \<in> (\<Union>i. Bs i)"
              using i0 by blast
            ultimately show "indicat_real (\<Union>i<n. Bs i) \<omega> * D' \<omega>
                = indicat_real (\<Union>i. Bs i) \<omega> * D' \<omega>"
              by simp
          qed
          show ?thesis
            by (rule tendsto_eventually[OF ev])
        next
          case False
          have z1: "indicat_real (\<Union>i<n. Bs i) \<omega> = 0" for n
            using False by auto
          have z2: "indicat_real (\<Union>i. Bs i) \<omega> = 0"
            using False by simp
          show ?thesis
            by (simp add: z1 z2)
        qed
      qed
      show "AE \<omega> in M. norm (indicat_real (\<Union>i<n. Bs i) \<omega> * D' \<omega>)
          \<le> \<bar>D' \<omega>\<bar>" for n
        by (intro AE_I2) (simp add: indicator_def)
    qed
    then have "(\<lambda>n. 0 :: real)
        \<longlonglongrightarrow> (\<integral>\<omega>. indicat_real (\<Union>i. Bs i) \<omega> * D' \<omega> \<partial>M)"
      unfolding partial .
    then show ?case
      by (simp add: LIMSEQ_const_iff)
  qed
qed

section \<open>The martingale property transfers to the modification\<close>

text \<open>Real-valued case, which is what the process form of the martingale
  problem needs.  For a vector-valued process the set-integral identity is
  obtained componentwise from this one.\<close>

section \<open>The vector-valued case, componentwise\<close>

text \<open>The market processes of @{theory Relative_Arbitrage.Ito_Market} take values in \<open>real^'n\<close>, so the
  transfer is needed there too.  The increments in
  \<open>set\_integral\_zero\_transfer\<close> are real-valued and independent of the value
  type of the process, so the vector case follows componentwise.\<close>

theorem martingale_of_modification_vec:
  fixes X X' :: "real \<Rightarrow> 'a \<Rightarrow> real^'n::finite"
  assumes PS: "prob_space M"
    and mg: "martingale M (natural_filtration M 0 X) 0 X"
    and meas': "\<And>u. 0 \<le> u \<Longrightarrow> X' u \<in> borel_measurable M"
    and ae: "\<And>u. 0 \<le> u \<Longrightarrow> AE \<omega> in M. X' u \<omega> = X u \<omega>"
  shows "martingale M (natural_filtration M 0 X') 0 X'"
proof -
  interpret Mg: martingale M "natural_filtration M 0 X" 0 X
    by (rule mg)
  interpret SP': stochastic_process M 0 X'
    by unfold_locales (auto intro: meas')
  have fm: "finite_measure M"
    by (rule finite_measureI) (simp add: prob_space.emeasure_space_1[OF PS])
  have sfs: "sigma_finite_subalgebra M (natural_filtration M 0 X' i)" for i
    by (intro finite_measure_subalgebra_is_sigma_finite
        finite_measure_subalgebra.intro finite_measure_subalgebra_axioms.intro
        fm SP'.subalgebra_natural_filtration)
  have sff: "sigma_finite_filtered_measure M (natural_filtration M 0 X') 0"
    by (intro sigma_finite_filtered_measure.intro
        sigma_finite_filtered_measure_axioms.intro
        SP'.filtered_measure_natural_filtration sfs)
  interpret SFF: sigma_finite_filtered_measure M "natural_filtration M 0 X'" 0
    by (rule sff)
  have int': "integrable M (X' i)" if i: "0 \<le> i" for i
  proof -
    have "integrable M (X' i) \<longleftrightarrow> integrable M (X i)"
      by (intro integrable_cong_AE meas'[OF i] Mg.random_variable[OF i] ae[OF i])
    then show ?thesis
      using Mg.integrable[OF i] by simp
  qed
  have split_diff: "(\<integral>\<omega>. indicat_real C \<omega> *\<^sub>R (Y \<omega> - Z \<omega>) \<partial>M)
      = set_lebesgue_integral M C Y - set_lebesgue_integral M C Z"
    if YZ: "set_integrable M C Y" "set_integrable M C Z" for C and Y :: "'a \<Rightarrow> real^'n" and Z :: "'a \<Rightarrow> real^'n"
  proof -
    have "(\<integral>\<omega>. indicat_real C \<omega> *\<^sub>R (Y \<omega> - Z \<omega>) \<partial>M)
        = (\<integral>\<omega>. indicat_real C \<omega> *\<^sub>R Y \<omega>
              - indicat_real C \<omega> *\<^sub>R Z \<omega> \<partial>M)"
      by (intro Bochner_Integration.integral_cong refl)
        (simp add: scaleR_right_diff_distrib)
    also have "\<dots> = set_lebesgue_integral M C Y - set_lebesgue_integral M C Z"
      unfolding set_lebesgue_integral_def
      using YZ by (intro Bochner_Integration.integral_diff)
        (simp_all add: set_integrable_def)
    finally show ?thesis .
  qed
  show ?thesis
  proof (rule SFF.martingale_of_set_integral_eq)
    show "adapted_process M (natural_filtration M 0 X') 0 X'"
      by (rule SP'.adapted_process_natural_filtration)
    show "\<And>i. 0 \<le> i \<Longrightarrow> integrable M (X' i)"
      by (rule int')
    fix A and i j :: real
    assume i: "0 \<le> i" and ij: "i \<le> j"
      and A: "A \<in> sets (natural_filtration M 0 X' i)"
    have j: "0 \<le> j" using i ij by simp
    have A_M: "A \<in> sets M"
    proof -
      have "sets (natural_filtration M 0 X' i) \<subseteq> sets M"
        using SP'.subalgebra_natural_filtration by (simp add: subalgebra_def)
      then show ?thesis using A by blast
    qed
    have si: "set_integrable M A (X' u)" if u: "0 \<le> u" for u
      unfolding set_integrable_def
      by (intro integrable_mult_indicator A_M int' u)
    have dA: "integrable M (\<lambda>\<omega>. indicat_real A \<omega> *\<^sub>R (X' j \<omega> - X' i \<omega>))"
      using si[OF j] si[OF i] unfolding set_integrable_def
      by (subst scaleR_right_diff_distrib) (rule Bochner_Integration.integrable_diff)
    have comp_zero: "(\<integral>\<omega>. indicat_real A \<omega>
        * ((X' j \<omega> - X' i \<omega>) $ k) \<partial>M) = 0" for k
    proof (rule set_integral_zero_transfer
        [where X = X and X' = X' and t = i
          and D = "\<lambda>\<omega>. (X j \<omega> - X i \<omega>) $ k"])
      show "\<And>u. 0 \<le> u \<Longrightarrow> X u \<in> borel_measurable M"
        by (rule Mg.random_variable)
      show "\<And>u. 0 \<le> u \<Longrightarrow> X' u \<in> borel_measurable M"
        by (rule meas')
      show "\<And>u. u \<in> {0..i} \<Longrightarrow> AE \<omega> in M. X' u \<omega> = X u \<omega>"
        by (intro ae) auto
      show "integrable M (\<lambda>\<omega>. (X j \<omega> - X i \<omega>) $ k)"
        by (intro integrable_bounded_linear[OF bounded_linear_vec_nth]
            Bochner_Integration.integrable_diff Mg.integrable i j)
      show "integrable M (\<lambda>\<omega>. (X' j \<omega> - X' i \<omega>) $ k)"
        by (intro integrable_bounded_linear[OF bounded_linear_vec_nth]
            Bochner_Integration.integrable_diff int' i j)
      show "AE \<omega> in M. (X' j \<omega> - X' i \<omega>) $ k = (X j \<omega> - X i \<omega>) $ k"
        using ae[OF i] ae[OF j] by eventually_elim simp
      show "A \<in> sets (natural_filtration M 0 X' i)"
        by (rule A)
      fix B assume B: "B \<in> sets (natural_filtration M 0 X i)"
      have B_M: "B \<in> sets M"
      proof -
        have "sets (natural_filtration M 0 X i) \<subseteq> sets M"
          using Mg.subalgebra_natural_filtration by (simp add: subalgebra_def)
        then show ?thesis using B by blast
      qed
      have sB: "set_integrable M B (X u)" if u: "0 \<le> u" for u
        unfolding set_integrable_def
        by (intro integrable_mult_indicator B_M Mg.integrable u)
      have dB: "integrable M (\<lambda>\<omega>. indicat_real B \<omega> *\<^sub>R (X j \<omega> - X i \<omega>))"
        using sB[OF j] sB[OF i] unfolding set_integrable_def
        by (subst scaleR_right_diff_distrib) (rule Bochner_Integration.integrable_diff)
      have "(\<integral>\<omega>. indicat_real B \<omega> * ((X j \<omega> - X i \<omega>) $ k) \<partial>M)
          = (\<integral>\<omega>. (indicat_real B \<omega> *\<^sub>R (X j \<omega> - X i \<omega>)) $ k \<partial>M)"
        by (intro Bochner_Integration.integral_cong refl) simp
      also have "\<dots> = (\<integral>\<omega>. indicat_real B \<omega>
            *\<^sub>R (X j \<omega> - X i \<omega>) \<partial>M) $ k"
        by (rule integral_bounded_linear[OF bounded_linear_vec_nth dB])
      also have "\<dots> = 0"
        using split_diff[OF sB[OF j] sB[OF i]] Mg.set_integral_eq[OF B i ij]
        by simp
      finally show "(\<integral>\<omega>. indicat_real B \<omega>
          * ((X j \<omega> - X i \<omega>) $ k) \<partial>M) = 0" .
    qed
    have key: "(\<integral>\<omega>. indicat_real A \<omega> *\<^sub>R (X' j \<omega> - X' i \<omega>) \<partial>M) = 0"
    proof -
      have "(\<integral>\<omega>. indicat_real A \<omega> *\<^sub>R (X' j \<omega> - X' i \<omega>) \<partial>M) $ k = 0"
        for k
      proof -
        have "(\<integral>\<omega>. indicat_real A \<omega> *\<^sub>R (X' j \<omega> - X' i \<omega>) \<partial>M) $ k
            = (\<integral>\<omega>. (indicat_real A \<omega> *\<^sub>R (X' j \<omega> - X' i \<omega>)) $ k \<partial>M)"
          by (rule integral_bounded_linear
              [OF bounded_linear_vec_nth dA, symmetric])
        also have "\<dots> = (\<integral>\<omega>. indicat_real A \<omega>
              * ((X' j \<omega> - X' i \<omega>) $ k) \<partial>M)"
          by (intro Bochner_Integration.integral_cong refl) simp
        also have "\<dots> = 0"
          by (rule comp_zero)
        finally show ?thesis .
      qed
      then show ?thesis
        by (simp add: vec_eq_iff)
    qed
    show "set_lebesgue_integral M A (X' i) = set_lebesgue_integral M A (X' j)"
      using split_diff[OF si[OF j] si[OF i]] key by simp
  qed
qed

section \<open>Separating the filtration from the martingale\<close>

text \<open>The market locales require a single filtration for both the state
  process and its compensated square, so here the process generating the
  filtration (\<open>X\<close> to \<open>X'\<close>) and the martingale (\<open>Y\<close> to \<open>Y'\<close>) are transferred
  separately.  Adaptedness of the new martingale to the new filtration is
  assumed, since it does not transfer for free; in the applications \<open>Y'\<close> is a
  continuous function of \<open>X'\<close>.\<close>

theorem martingale_of_modification_gen:
  fixes X X' :: "real \<Rightarrow> 'a \<Rightarrow> 'b :: {second_countable_topology, banach}"
    and Y Y' :: "real \<Rightarrow> 'a \<Rightarrow> real"
  assumes PS: "prob_space M"
    and mg: "martingale M (natural_filtration M 0 X) 0 Y"
    and measX: "\<And>u. 0 \<le> u \<Longrightarrow> X u \<in> borel_measurable M"
    and meas': "\<And>u. 0 \<le> u \<Longrightarrow> X' u \<in> borel_measurable M"
    and aeX: "\<And>u. 0 \<le> u \<Longrightarrow> AE \<omega> in M. X' u \<omega> = X u \<omega>"
    and measY': "\<And>u. 0 \<le> u \<Longrightarrow> Y' u \<in> borel_measurable M"
    and aeY: "\<And>u. 0 \<le> u \<Longrightarrow> AE \<omega> in M. Y' u \<omega> = Y u \<omega>"
    and adaptedY': "adapted_process M (natural_filtration M 0 X') 0 Y'"
  shows "martingale M (natural_filtration M 0 X') 0 Y'"
proof -
  interpret Mg: martingale M "natural_filtration M 0 X" 0 Y
    by (rule mg)
  interpret SP: stochastic_process M 0 X
    by unfold_locales (auto intro: measX)
  interpret SP': stochastic_process M 0 X'
    by unfold_locales (auto intro: meas')
  have fm: "finite_measure M"
    by (rule finite_measureI) (simp add: prob_space.emeasure_space_1[OF PS])
  have sfs: "sigma_finite_subalgebra M (natural_filtration M 0 X' i)" for i
    by (intro finite_measure_subalgebra_is_sigma_finite
        finite_measure_subalgebra.intro finite_measure_subalgebra_axioms.intro
        fm SP'.subalgebra_natural_filtration)
  have sff: "sigma_finite_filtered_measure M (natural_filtration M 0 X') 0"
    by (intro sigma_finite_filtered_measure.intro
        sigma_finite_filtered_measure_axioms.intro
        SP'.filtered_measure_natural_filtration sfs)
  interpret SFF: sigma_finite_filtered_measure M "natural_filtration M 0 X'" 0
    by (rule sff)
  have int': "integrable M (Y' i)" if i: "0 \<le> i" for i
  proof -
    have "integrable M (Y' i) \<longleftrightarrow> integrable M (Y i)"
      by (intro integrable_cong_AE measY'[OF i] Mg.random_variable[OF i] aeY[OF i])
    then show ?thesis
      using Mg.integrable[OF i] by simp
  qed
  have gconv: "set_lebesgue_integral M C V = (\<integral>\<omega>. indicat_real C \<omega> * V \<omega> \<partial>M)"
    for C and V :: "'a \<Rightarrow> real"
    unfolding set_lebesgue_integral_def by simp
  have iV: "integrable M (\<lambda>\<omega>. indicat_real C \<omega> * V \<omega>)"
    if "set_integrable M C V" for C and V :: "'a \<Rightarrow> real"
    using that[unfolded set_integrable_def] by simp
  have split_diff: "(\<integral>\<omega>. indicat_real C \<omega> * (V \<omega> - W \<omega>) \<partial>M)
      = set_lebesgue_integral M C V - set_lebesgue_integral M C W"
    if V: "set_integrable M C V" and W: "set_integrable M C W"
    for C and V W :: "'a \<Rightarrow> real"
  proof -
    have "(\<integral>\<omega>. indicat_real C \<omega> * (V \<omega> - W \<omega>) \<partial>M)
        = (\<integral>\<omega>. indicat_real C \<omega> * V \<omega>
              - indicat_real C \<omega> * W \<omega> \<partial>M)"
      by (intro Bochner_Integration.integral_cong refl) (simp add: algebra_simps)
    also have "\<dots> = (\<integral>\<omega>. indicat_real C \<omega> * V \<omega> \<partial>M)
        - (\<integral>\<omega>. indicat_real C \<omega> * W \<omega> \<partial>M)"
      by (intro Bochner_Integration.integral_diff iV V W)
    finally show ?thesis unfolding gconv .
  qed
  show ?thesis
  proof (rule SFF.martingale_of_set_integral_eq)
    show "adapted_process M (natural_filtration M 0 X') 0 Y'"
      by (rule adaptedY')
    show "\<And>i. 0 \<le> i \<Longrightarrow> integrable M (Y' i)"
      by (rule int')
    fix A and i j :: real
    assume i: "0 \<le> i" and ij: "i \<le> j"
      and A: "A \<in> sets (natural_filtration M 0 X' i)"
    have j: "0 \<le> j" using i ij by simp
    have A_M: "A \<in> sets M"
    proof -
      have "sets (natural_filtration M 0 X' i) \<subseteq> sets M"
        using SP'.subalgebra_natural_filtration by (simp add: subalgebra_def)
      then show ?thesis using A by blast
    qed
    have si: "set_integrable M A (Y' u)" if u: "0 \<le> u" for u
      unfolding set_integrable_def
      by (intro integrable_mult_indicator A_M int' u)
    have key: "(\<integral>\<omega>. indicat_real A \<omega> * (Y' j \<omega> - Y' i \<omega>) \<partial>M) = 0"
    proof (rule set_integral_zero_transfer
        [where X = X and X' = X' and t = i
          and D = "\<lambda>\<omega>. Y j \<omega> - Y i \<omega>"])
      show "\<And>u. 0 \<le> u \<Longrightarrow> X u \<in> borel_measurable M"
        by (rule measX)
      show "\<And>u. 0 \<le> u \<Longrightarrow> X' u \<in> borel_measurable M"
        by (rule meas')
      show "\<And>u. u \<in> {0..i} \<Longrightarrow> AE \<omega> in M. X' u \<omega> = X u \<omega>"
        by (intro aeX) auto
      show "integrable M (\<lambda>\<omega>. Y j \<omega> - Y i \<omega>)"
        by (intro Bochner_Integration.integrable_diff Mg.integrable i j)
      show "integrable M (\<lambda>\<omega>. Y' j \<omega> - Y' i \<omega>)"
        by (intro Bochner_Integration.integrable_diff int' i j)
      show "AE \<omega> in M. Y' j \<omega> - Y' i \<omega> = Y j \<omega> - Y i \<omega>"
        using aeY[OF i] aeY[OF j] by eventually_elim simp
      show "A \<in> sets (natural_filtration M 0 X' i)"
        by (rule A)
      fix B assume B: "B \<in> sets (natural_filtration M 0 X i)"
      have B_M: "B \<in> sets M"
      proof -
        have "sets (natural_filtration M 0 X i) \<subseteq> sets M"
          using SP.subalgebra_natural_filtration by (simp add: subalgebra_def)
        then show ?thesis using B by blast
      qed
      have sB: "set_integrable M B (Y u)" if u: "0 \<le> u" for u
        unfolding set_integrable_def
        by (intro integrable_mult_indicator B_M Mg.integrable u)
      show "(\<integral>\<omega>. indicat_real B \<omega> * (Y j \<omega> - Y i \<omega>) \<partial>M) = 0"
        using split_diff[OF sB[OF j] sB[OF i]] Mg.set_integral_eq[OF B i ij]
        by simp
    qed
    show "set_lebesgue_integral M A (Y' i) = set_lebesgue_integral M A (Y' j)"
      using split_diff[OF si[OF j] si[OF i]] key by simp
  qed
qed

text \<open>Adaptedness of a measurable function of the state to the state's own
  natural filtration.  This is stated here rather than at the point of use
  because the Kolmogorov-Chentsov entry has a type of the same name as the
  locale \<open>stochastic\_process,\<close> so the locale cannot be interpreted in a
  theory that imports both.\<close>

lemma adapted_of_natural_filtration:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> 'b :: {second_countable_topology, banach}"
    and f :: "real \<Rightarrow> 'b \<Rightarrow> real"
  assumes measX: "\<And>u. 0 \<le> u \<Longrightarrow> X u \<in> borel_measurable M"
    and measf: "\<And>u. f u \<in> borel_measurable borel"
  shows "adapted_process M (natural_filtration M 0 X) 0 (\<lambda>u \<omega>. f u (X u \<omega>))"
proof -
  interpret SP: stochastic_process M 0 X
    by unfold_locales (auto intro: measX)
  interpret AP: adapted_process M "natural_filtration M 0 X" 0 X
    by (rule SP.adapted_process_natural_filtration)
  show ?thesis
  proof (intro adapted_process.intro adapted_process_axioms.intro
      SP.filtered_measure_natural_filtration)
    fix i :: real assume i: "0 \<le> i"
    show "(\<lambda>\<omega>. f i (X i \<omega>))
        \<in> borel_measurable (natural_filtration M 0 X i)"
      by (rule measurable_compose[OF AP.adapted[OF i] measf])
  qed
qed

text \<open>Two more facts that need the locale \<open>stochastic\_process\<close> and therefore
  have to live in a theory that does not import Kolmogorov-Chentsov.\<close>

lemma sets_natural_filtration_subset:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> 'b :: {second_countable_topology, banach}"
  assumes measX: "\<And>u. 0 \<le> u \<Longrightarrow> X u \<in> borel_measurable M"
  shows "sets (natural_filtration M 0 X i) \<subseteq> sets M"
proof -
  interpret SP: stochastic_process M 0 X
    by unfold_locales (auto intro: measX)
  show ?thesis
    using SP.subalgebra_natural_filtration by (simp add: subalgebra_def)
qed

(*<*)
end
(*>*)
