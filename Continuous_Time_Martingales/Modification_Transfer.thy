
(*<*)
theory Modification_Transfer
  imports Natural_Filtration
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

text \<open>The natural filtration of a measurable process consists of events.  This
  needs the locale \<open>stochastic\_process,\<close> so it has to live in a theory that
  does not import Kolmogorov-Chentsov.\<close>

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
  interpret SP': stochastic_process M 0 X'
    by unfold_locales (auto intro: X')
  have [measurable]: "D \<in> borel_measurable M" "D' \<in> borel_measurable M"
    using D_int D'_int by (simp_all add: borel_measurable_integrable)
  have conv: "set_lebesgue_integral M C D' = (\<integral>\<omega>. indicat_real C \<omega> * D' \<omega> \<partial>M)"
    for C
    unfolding set_lebesgue_integral_def by simp
  have "set_lebesgue_integral M A D' = 0"
  proof (rule set_integral_zero_of_generator[OF SP'.subalgebra_natural_filtration D'_int
        Int_stable_cylset cylset_subset_Pow sigma_sets_cylset[OF X', symmetric] _ _ A])
    show "space M \<in> cylset M X' t"
      unfolding cylset_def by (intro CollectI exI[of _ "{}"]) auto
    fix B assume B: "B \<in> cylset M X' t"
    then obtain P where
      P: "B = space M \<inter> (\<Inter>p\<in>P. X' (fst p) -` snd p)" "finite P"
        "\<forall>p\<in>P. fst p \<in> {0..t} \<and> snd p \<in> sets borel"
      unfolding cylset_def by blast
    define B0 where "B0 = space M \<inter> (\<Inter>p\<in>P. X (fst p) -` snd p)"
    have B0_cyl: "B0 \<in> cylset M X t"
      unfolding B0_def cylset_def using P(2,3) by blast
    have B0_sets: "B0 \<in> sets (natural_filtration M 0 X t)"
      using X B0_cyl by (rule cylset_in_natural_filtration)
    have B_sets: "B \<in> sets (natural_filtration M 0 X' t)"
      by (rule cylset_in_natural_filtration[OF X' B])
    have [measurable]: "B \<in> sets M"
      by (rule subsetD[OF sets_natural_filtration_subset[OF X'] B_sets])
    have [measurable]: "B0 \<in> sets M"
      by (rule subsetD[OF sets_natural_filtration_subset[OF X] B0_sets])
    have "AE \<omega> in M. indicat_real B \<omega> = indicat_real B0 \<omega>"
      unfolding P(1) B0_def
      by (rule cylset_indicator_AE_eq[where t = t, OF ae P(2) P(3)])
    with ae_D have "AE \<omega> in M. indicat_real B \<omega> * D' \<omega> = indicat_real B0 \<omega> * D \<omega>"
      by eventually_elim simp
    then have "(\<integral>\<omega>. indicat_real B \<omega> * D' \<omega> \<partial>M)
        = (\<integral>\<omega>. indicat_real B0 \<omega> * D \<omega> \<partial>M)"
      by (intro integral_cong_AE) measurable
    then show "set_lebesgue_integral M B D' = 0"
      unfolding conv using zero[OF B0_sets] by simp
  qed
  then show ?thesis
    unfolding conv .
qed

section \<open>The martingale property transfers to the modification\<close>

text \<open>The market locales require a single filtration for both the state
  process and its compensated square, so here the process generating the
  filtration (\<open>X\<close> to \<open>X'\<close>) and the martingale (\<open>Y\<close> to \<open>Y'\<close>) are transferred
  separately.  Adaptedness of the new martingale to the new filtration is
  assumed, since it does not transfer for free; in the applications \<open>Y'\<close> is a
  continuous function of \<open>X'\<close>.  The martingale takes values in any Euclidean
  space: the increments in \<open>set_integral_zero_transfer\<close> are real-valued, so
  the transfer is done for the inner product of the increment with each vector.\<close>

theorem martingale_of_modification_gen:
  fixes X X' :: "real \<Rightarrow> 'a \<Rightarrow> 'b :: {second_countable_topology, banach}"
    and Y Y' :: "real \<Rightarrow> 'a \<Rightarrow> 'c :: euclidean_space"
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
  interpret SP': stochastic_process M 0 X'
    by unfold_locales (auto intro: meas')
  have fm: "finite_measure M"
    by (rule finite_measureI) (simp add: prob_space.emeasure_space_1[OF PS])
  interpret SFF: finite_filtered_measure M "natural_filtration M 0 X'" 0
    by (rule SP'.finite_filtered_measure_natural_filtration[OF fm])
  have int': "integrable M (Y' i)" if i: "0 \<le> i" for i
  proof -
    have "integrable M (Y' i) \<longleftrightarrow> integrable M (Y i)"
      by (intro integrable_cong_AE measY'[OF i] Mg.random_variable[OF i] aeY[OF i])
    then show ?thesis
      using Mg.integrable[OF i] by simp
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
    have sdiff: "(\<integral>\<omega>. indicat_real C \<omega> * ((V j \<omega> - V i \<omega>) \<bullet> b) \<partial>M)
        = (set_lebesgue_integral M C (V j) - set_lebesgue_integral M C (V i)) \<bullet> b"
      if Vj: "set_integrable M C (V j)" and Vi: "set_integrable M C (V i)"
      for C b and V :: "real \<Rightarrow> 'a \<Rightarrow> 'c"
    proof -
      have "(\<integral>\<omega>. indicat_real C \<omega> * ((V j \<omega> - V i \<omega>) \<bullet> b) \<partial>M)
          = (\<integral>\<omega>. (indicat_real C \<omega> *\<^sub>R (V j \<omega> - V i \<omega>)) \<bullet> b \<partial>M)"
        by (intro Bochner_Integration.integral_cong refl) simp
      also have "\<dots> = set_lebesgue_integral M C (\<lambda>\<omega>. V j \<omega> - V i \<omega>) \<bullet> b"
        unfolding set_lebesgue_integral_def
        by (rule integral_inner_left)
          (use set_integral_diff(1)[OF Vj Vi] in \<open>simp add: set_integrable_def\<close>)
      finally show ?thesis
        using set_integral_diff(2)[OF Vj Vi] by simp
    qed
    have A_M: "A \<in> sets M"
      by (rule subsetD[OF sets_natural_filtration_subset[OF meas'] A])
    have si: "set_integrable M A (Y' u)" if u: "0 \<le> u" for u
      unfolding set_integrable_def by (intro integrable_mult_indicator A_M int' u)
    have comp_zero: "(\<integral>\<omega>. indicat_real A \<omega> * ((Y' j \<omega> - Y' i \<omega>) \<bullet> b) \<partial>M) = 0"
      for b
    proof (rule set_integral_zero_transfer
        [where X = X and X' = X' and t = i
          and D = "\<lambda>\<omega>. (Y j \<omega> - Y i \<omega>) \<bullet> b"])
      show "\<And>u. 0 \<le> u \<Longrightarrow> X u \<in> borel_measurable M"
        by (rule measX)
      show "\<And>u. 0 \<le> u \<Longrightarrow> X' u \<in> borel_measurable M"
        by (rule meas')
      show "\<And>u. u \<in> {0..i} \<Longrightarrow> AE \<omega> in M. X' u \<omega> = X u \<omega>"
        by (intro aeX) auto
      show "integrable M (\<lambda>\<omega>. (Y j \<omega> - Y i \<omega>) \<bullet> b)"
        by (intro integrable_inner_left Bochner_Integration.integrable_diff
            Mg.integrable i j)
      show "integrable M (\<lambda>\<omega>. (Y' j \<omega> - Y' i \<omega>) \<bullet> b)"
        by (intro integrable_inner_left Bochner_Integration.integrable_diff int' i j)
      show "AE \<omega> in M. (Y' j \<omega> - Y' i \<omega>) \<bullet> b = (Y j \<omega> - Y i \<omega>) \<bullet> b"
        using aeY[OF i] aeY[OF j] by eventually_elim simp
      show "A \<in> sets (natural_filtration M 0 X' i)"
        by (rule A)
      fix B assume B: "B \<in> sets (natural_filtration M 0 X i)"
      have B_M: "B \<in> sets M"
        by (rule subsetD[OF sets_natural_filtration_subset[OF measX] B])
      have sB: "set_integrable M B (Y u)" if u: "0 \<le> u" for u
        unfolding set_integrable_def by (intro integrable_mult_indicator B_M Mg.integrable u)
      show "(\<integral>\<omega>. indicat_real B \<omega> * ((Y j \<omega> - Y i \<omega>) \<bullet> b) \<partial>M) = 0"
        using sdiff[OF sB[OF j] sB[OF i]] Mg.set_integral_eq[OF B i ij] by simp
    qed
    have "(set_lebesgue_integral M A (Y' j) - set_lebesgue_integral M A (Y' i))
        \<bullet> (set_lebesgue_integral M A (Y' j) - set_lebesgue_integral M A (Y' i)) = 0"
      using sdiff[OF si[OF j] si[OF i]] comp_zero by simp
    then show "set_lebesgue_integral M A (Y' i) = set_lebesgue_integral M A (Y' j)"
      by simp
  qed
qed

text \<open>State processes commonly take values in \<open>real^'n\<close>, so the
  transfer is needed there too, with the process as its own martingale.\<close>

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
  show ?thesis
    by (rule martingale_of_modification_gen[OF PS mg Mg.random_variable meas' ae
          meas' ae SP'.adapted_process_natural_filtration])
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

(*<*)
end
(*>*)
