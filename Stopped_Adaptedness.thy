(*
  Title:   Stopped_Adaptedness.thy
  Content: A continuous adapted process stopped at a stopping time is adapted.

  This discharges the hypothesis stopped_adapted of theorem optional_stopping
  (Optional_Sampling.thy), which that theorem leaves to the caller.

  The proof is the usual dyadic approximation.  The stopped time
  rho = min v tau is measurable at the horizon v, because {rho <= a} is
  either the whole space (a >= v), or {tau <= a} in F a and hence in F v
  (0 <= a < v), or empty (a < 0).  The dyadic index
  idx n = min (nat ceiling(2^n rho)) (nat ceiling(2^n v)) has all its level
  sets in F v, since {idx n <= i} is again a sublevel set of rho, and the
  process evaluated at the corresponding grid time is a finite sum of
  F v-measurable terms.  Finally the grid times are within 2^-n of rho, so
  path continuity gives convergence and the limit is F v-measurable.
*)

theory Stopped_Adaptedness
  imports Optional_Sampling
begin


section \<open>The stopped process is adapted\<close>

text \<open>This is the hypothesis stopped\_adapted of the optional stopping
  theorem above.  The proof is the usual dyadic approximation: the stopped
  time is approximated from above by grid times, at which the process is a
  finite sum of terms measurable with respect to the filtration at the
  horizon, and the approximations converge by path continuity.\<close>

lemma stopped_adapted_of_cont:
  fixes Z :: "real \<Rightarrow> 'a \<Rightarrow> real" and tau :: "'a \<Rightarrow> real"
    and v :: real
  assumes ap: "adapted_process M F 0 Z"
    and tau_nonneg: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> 0 \<le> tau \<omega>"
    and tau_stop: "\<And>s. 0 \<le> s \<Longrightarrow> {\<omega> \<in> space M. tau \<omega> \<le> s} \<in> sets (F s)"
    and cont: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> continuous_on {0..} (\<lambda>s. Z s \<omega>)"
    and v: "0 \<le> v"
  shows "(\<lambda>\<omega>. Z (min v (tau \<omega>)) \<omega>) \<in> borel_measurable (F v)"
proof -
  interpret AP: adapted_process M F 0 Z
    by (rule ap)
  have spaceF: "space (F v) = space M"
    using AP.subalgebras[OF v] by (simp add: subalgebra_def)
  define rho where "rho \<omega> = min v (tau \<omega>)" for \<omega>
  define N where "N n = nat \<lceil>2 ^ n * v\<rceil>" for n :: nat
  define dg where "dg n i = min v (real i / 2 ^ n)" for n i :: nat
  define idx where
    "idx n \<omega> = min (nat \<lceil>2 ^ n * rho \<omega>\<rceil>) (N n)" for n :: nat and \<omega>
  have rho_nonneg: "0 \<le> rho \<omega>" if "\<omega> \<in> space M" for \<omega>
    unfolding rho_def using tau_nonneg[OF that] v by simp
  have rho_le: "rho \<omega> \<le> v" for \<omega>
    unfolding rho_def by simp

  text \<open>The stopped time is measurable at the horizon.\<close>
  have rho_meas: "rho \<in> borel_measurable (F v)"
  proof (rule borel_measurable_iff_le[THEN iffD2], intro allI)
    fix a :: real
    show "{\<omega> \<in> space (F v). rho \<omega> \<le> a} \<in> sets (F v)"
    proof (cases "v \<le> a")
      case True
      then have "{\<omega> \<in> space (F v). rho \<omega> \<le> a} = space (F v)"
        unfolding rho_def by auto
      then show ?thesis
        by simp
    next
      case False
      then have a: "a < v" by simp
      show ?thesis
      proof (cases "0 \<le> a")
        case True
        have "{\<omega> \<in> space (F v). rho \<omega> \<le> a} = {\<omega> \<in> space M. tau \<omega> \<le> a}"
          unfolding rho_def using a spaceF by auto
        moreover have "{\<omega> \<in> space M. tau \<omega> \<le> a} \<in> sets (F a)"
          by (rule tau_stop[OF True])
        moreover have "sets (F a) \<subseteq> sets (F v)"
          using True a by (intro AP.sets_F_mono) auto
        ultimately show ?thesis
          by auto
      next
        case False
        have empty: "{\<omega> \<in> space (F v). rho \<omega> \<le> a} = {}"
          using False rho_nonneg spaceF by force
        show ?thesis
          unfolding empty by simp
      qed
    qed
  qed
  have rho_le_sets: "{\<omega> \<in> space M. rho \<omega> \<le> c} \<in> sets (F v)"
    for c
  proof -
    have "{\<omega> \<in> space (F v). rho \<omega> \<le> c} \<in> sets (F v)"
      using rho_meas unfolding borel_measurable_iff_le by blast
    then show ?thesis
      using spaceF by simp
  qed
  have kn_le: "(nat \<lceil>2 ^ n * rho \<omega>\<rceil> \<le> i)
      \<longleftrightarrow> rho \<omega> \<le> real i / 2 ^ n" for n i \<omega>
  proof -
    have "(nat \<lceil>2 ^ n * rho \<omega>\<rceil> \<le> i)
        \<longleftrightarrow> \<lceil>2 ^ n * rho \<omega>\<rceil> \<le> int i"
      by (simp add: nat_le_iff)
    also have "\<dots> \<longleftrightarrow> 2 ^ n * rho \<omega> \<le> real i"
      by (simp add: ceiling_le_iff)
    also have "\<dots> \<longleftrightarrow> rho \<omega> \<le> real i / 2 ^ n"
      by (simp add: field_simps)
    finally show ?thesis .
  qed
  have idx_le_sets: "{\<omega> \<in> space M. idx n \<omega> \<le> i} \<in> sets (F v)"
    for n i
  proof (cases "N n \<le> i")
    case True
    then have eq: "{\<omega> \<in> space M. idx n \<omega> \<le> i} = space (F v)"
      unfolding idx_def using spaceF by auto
    show ?thesis
      unfolding eq by (rule sets.top)
  next
    case False
    have "{\<omega> \<in> space M. idx n \<omega> \<le> i}
        = {\<omega> \<in> space M. rho \<omega> \<le> real i / 2 ^ n}"
    proof (intro set_eqI)
      fix \<omega>
      have "(idx n \<omega> \<le> i)
          \<longleftrightarrow> (nat \<lceil>2 ^ n * rho \<omega>\<rceil> \<le> i)"
        unfolding idx_def using False by (simp add: min_le_iff_disj)
      also have "\<dots> \<longleftrightarrow> rho \<omega> \<le> real i / 2 ^ n"
        by (rule kn_le)
      finally show "(\<omega> \<in> {\<omega> \<in> space M. idx n \<omega> \<le> i})
          = (\<omega> \<in> {\<omega> \<in> space M. rho \<omega> \<le> real i / 2 ^ n})"
        by simp
    qed
    then show ?thesis
      using rho_le_sets by simp
  qed
  have sets_i: "{\<xi> \<in> space M. idx n \<xi> = i} \<in> sets (F v)"
    for n i
  proof (cases i)
    case 0
    have "{\<xi> \<in> space M. idx n \<xi> = i}
        = {\<xi> \<in> space M. idx n \<xi> \<le> i}"
      unfolding 0 by auto
    then show ?thesis
      using idx_le_sets by simp
  next
    case (Suc j)
    have "{\<xi> \<in> space M. idx n \<xi> = i}
        = {\<xi> \<in> space M. idx n \<xi> \<le> i}
          - {\<xi> \<in> space M. idx n \<xi> \<le> j}"
      unfolding Suc by auto
    then show ?thesis
      using sets.Diff[OF idx_le_sets[of n i] idx_le_sets[of n j]] by simp
  qed

  text \<open>On the grid the stopped process is a finite sum.\<close>
  have idx_le: "idx n \<omega> \<le> N n" for n \<omega>
    unfolding idx_def by simp
  have sum_eq: "Z (dg n (idx n \<omega>)) \<omega>
      = (\<Sum>i\<le>N n. indicat_real {\<xi> \<in> space M. idx n \<xi> = i} \<omega>
           * Z (dg n i) \<omega>)"
    if w: "\<omega> \<in> space M" for n \<omega>
  proof -
    have "(\<Sum>i\<le>N n. indicat_real {\<xi> \<in> space M. idx n \<xi> = i} \<omega>
             * Z (dg n i) \<omega>)
        = (\<Sum>i\<le>N n. if i = idx n \<omega> then Z (dg n i) \<omega> else 0)"
      using w by (intro sum.cong refl) auto
    also have "\<dots> = Z (dg n (idx n \<omega>)) \<omega>"
      using idx_le[of n \<omega>] by (simp cong: if_cong)
    finally show ?thesis ..
  qed
  have grid_meas: "(\<lambda>\<omega>. Z (dg n (idx n \<omega>)) \<omega>) \<in> borel_measurable (F v)"
    for n
  proof -
    have dg_meas: "(\<lambda>\<omega>. Z (dg n i) \<omega>) \<in> borel_measurable (F v)"
      for i
    proof -
      have dg0: "0 \<le> dg n i" and dgv: "dg n i \<le> v"
        unfolding dg_def using v by auto
      have sp: "space (F (dg n i)) = space M"
        using AP.subalgebras[OF dg0] by (simp add: subalgebra_def)
      have "subalgebra (F v) (F (dg n i))"
        unfolding subalgebra_def
        using sp spaceF AP.sets_F_mono[OF dg0 dgv] by simp
      then show ?thesis
        using AP.adapted[OF dg0] by (rule measurable_from_subalg)
    qed
    have "(\<lambda>\<omega>. \<Sum>i\<le>N n. indicat_real {\<xi> \<in> space M. idx n \<xi> = i} \<omega>
        * Z (dg n i) \<omega>) \<in> borel_measurable (F v)"
      by (intro borel_measurable_sum borel_measurable_times
          borel_measurable_indicator sets_i dg_meas)
    then show ?thesis
      by (rule measurable_cong[THEN iffD1, rotated])
        (use sum_eq spaceF in simp)
  qed

  text \<open>The grid times converge to the stopped time.\<close>
  have dg_idx_close: "\<bar>dg n (idx n \<omega>) - rho \<omega>\<bar> \<le> 1 / 2 ^ n"
    if w: "\<omega> \<in> space M" for n \<omega>
  proof -
    have rn: "0 \<le> rho \<omega>" by (rule rho_nonneg[OF w])
    have pos: "(0 :: real) < 2 ^ n" by simp
    define c where "c = real (nat \<lceil>2 ^ n * rho \<omega>\<rceil>) / 2 ^ n"
    have c_lb: "rho \<omega> \<le> c"
      unfolding c_def using rn pos
      by (simp add: field_simps)
    have c_ub: "c \<le> rho \<omega> + 1 / 2 ^ n"
      unfolding c_def using rn pos
      by (simp add: field_simps)
        (smt (verit) ceiling_correct nat_0_le of_int_of_nat_eq
          zero_le_ceiling zero_le_mult_iff zero_le_power)
    have big: "v \<le> real (N n) / 2 ^ n"
      unfolding N_def using v pos
      by (simp add: field_simps)
    have "dg n (idx n \<omega>) = min v c"
    proof (cases "nat \<lceil>2 ^ n * rho \<omega>\<rceil> \<le> N n")
      case True
      then have "idx n \<omega> = nat \<lceil>2 ^ n * rho \<omega>\<rceil>"
        unfolding idx_def by simp
      then show ?thesis
        unfolding dg_def c_def by simp
    next
      case False
      then have "N n < nat \<lceil>2 ^ n * rho \<omega>\<rceil>"
        by (rule not_le[THEN iffD1])
      then have kge: "N n \<le> nat \<lceil>2 ^ n * rho \<omega>\<rceil>"
        by (rule less_imp_le)
      have idxN: "idx n \<omega> = N n"
        unfolding idx_def using kge by (rule min_absorb2)
      have vc: "v \<le> c"
      proof -
        have "real (N n) \<le> real (nat \<lceil>2 ^ n * rho \<omega>\<rceil>)"
          using kge by (rule of_nat_mono)
        then have "real (N n) / 2 ^ n \<le> c"
          unfolding c_def by (simp add: divide_right_mono)
        then show ?thesis
          using big by simp
      qed
      have "min v c = v"
        using vc by (rule min_absorb1)
      moreover have "dg n (idx n \<omega>) = v"
        unfolding idxN dg_def using big by (rule min_absorb1)
      ultimately show ?thesis
        by simp
    qed
    then show ?thesis
      using c_lb c_ub rho_le[of \<omega>] by simp
  qed
  have conv: "(\<lambda>n. Z (dg n (idx n \<omega>)) \<omega>) \<longlonglongrightarrow> Z (rho \<omega>) \<omega>"
    if w: "\<omega> \<in> space M" for \<omega>
  proof -
    have zero: "(\<lambda>n. 1 / 2 ^ n :: real) \<longlonglongrightarrow> 0"
      by (rule LIMSEQ_divide_realpow_zero) simp
    have diff0: "(\<lambda>n. dg n (idx n \<omega>) - rho \<omega>) \<longlonglongrightarrow> 0"
    proof (rule Lim_null_comparison[OF _ zero])
      show "\<forall>\<^sub>F n in sequentially.
          norm (dg n (idx n \<omega>) - rho \<omega>) \<le> 1 / 2 ^ n"
        using dg_idx_close[OF w] by simp
    qed
    have tt: "(\<lambda>n. dg n (idx n \<omega>)) \<longlonglongrightarrow> rho \<omega>"
      using tendsto_add[OF diff0 tendsto_const[of "rho \<omega>"]] by simp
    have mem: "dg n (idx n \<omega>) \<in> {0..}" for n
      unfolding dg_def using v by simp
    have rho0: "rho \<omega> \<in> {0..}"
      using rho_nonneg[OF w] by simp
    show ?thesis
    proof (rule continuous_on_tendsto_compose[OF cont[OF w] tt rho0])
      show "\<forall>\<^sub>F n in sequentially. dg n (idx n \<omega>) \<in> {0..}"
        by (intro always_eventually allI mem)
    qed
  qed
  show ?thesis
  proof (rule borel_measurable_LIMSEQ_metric[OF grid_meas])
    fix \<omega> assume "\<omega> \<in> space (F v)"
    then have "\<omega> \<in> space M" using spaceF by simp
    then show "(\<lambda>n. Z (dg n (idx n \<omega>)) \<omega>) \<longlonglongrightarrow> Z (min v (tau \<omega>)) \<omega>"
      using conv unfolding rho_def by simp
  qed
qed

end
