section \<open>Clause (2): the subsolution half\<close>

(*<*)
theory Value_Function_Subsolution
  imports Dynamic_Programming_Assembly Curvature_Operator Operator_Envelopes
    "Continuous_Time_Martingales.Quadratic_Variation"
    "Continuous_Time_Martingales.Integrability_Criteria"
    "Symmetric_Matrix_Spectra.Matrix_Algebra"
    "Symmetric_Matrix_Spectra.Ky_Fan"
begin

(*>*)

text \<open>
  Towards clause (2) of Theorem 1.1 of \<^cite>\<open>LaiShkolnikovSoner\<close> --- the two
             viscosity inequalities for `\<open>exit_val\<close>`.  PLAN section 2.1.

    Two facts shape everything here.

    (a) The operator of Eq. (1.9) is an INFIMUM,

          \<open>ell_op\<close> k L p M = Inf ((\<open>\<lambda>\<close>a. - trace (M ** a) / 2) ` feasible k L p),

        so a subsolution inequality needs only ONE witness, while a
        supersolution inequality needs the whole family.

    (b) The two halves of the DPP are not interchangeable.  The `<=` half is an
        ALMOST SURE bound, and a.s. bounds survive integration; the `>=` half
        bounds an essential infimum from below, which no mean can do.  So the
        SUBSOLUTION half is the one an expectation argument reaches.

    The class of (1.7) is a martingale-problem class, not an SDE class, so Ito's
    formula is unavailable.  For QUADRATIC test functions it is also unnecessary:
    z . (M *v z) = trace (M ** outerp z) is a linear functional of the
    compensated clause, so the expansion is exact and elementary.  That is
    \<open>exit_class_quadratic_mean\<close>, and \<open>exit_val_subsol_quadratic_global\<close> is the
    subsolution inequality it yields, for the relaxed operator \<open>ell_op_s\<close> and a
    globally touching quadratic.

    The final section states precisely what separates that from \<open>visc_subsol\<close>,
    including two localisation routes that were checked and provably do not work.\<close>
section \<open>One witness suffices for the subsolution inequality\<close>

text \<open>\<^const>\<open>ell_op\<close> is an infimum over the feasible set, and
  @{thm [source] ell_op_bdd_below} says that infimum is over a set bounded
  below.  So a single feasible matrix beating the threshold settles the
  inequality --- there is no need to control the whole family.\<close>

lemma ell_op_le_of_witness:
  fixes M :: "real^'n::finite^'n" and p :: "real^'n"
  assumes a: "a \<in> feasible k L p" and le: "- trace (M ** a) / 2 \<le> c"
  shows "ell_op k L p M \<le> c"
proof -
  have mem: "- trace (M ** a) / 2 \<in> (\<lambda>a. - trace (M ** a) / 2) ` feasible k L p"
    using a by blast
  have "ell_op k L p M \<le> - trace (M ** a) / 2"
    unfolding ell_op_def by (rule cInf_lower[OF mem ell_op_bdd_below])
  also have "\<dots> \<le> c" by (rule le)
  finally show ?thesis .
qed

section \<open>The DPP at the exit time of a ball\<close>

text \<open>The \<open>\<le>\<close> half of the DPP, @{thm [source] exit_val_cond_time}, needs its
  random time only to lie in \<open>[0,T]\<close>, so the subsolution argument can use
  the exit time of a ball directly.

  The supersolution half needs @{thm [source] exit_val_dpp_sup_ge_time},
  whose \<open>\<theta>\<close> must be a \<^const>\<open>path_stopping_time\<close> --- true of the ball's
  exit time only on continuous paths, since the stopping-time predicate
  quantifies over all functions.

  Combined with @{thm [source] enn2real_paper_v_horizon_cap}, the
  conclusion has no varying horizon: the value at the reduced horizon is
  the value at \<open>T\<close>, capped.\<close>

definition pball_exit :: "real \<Rightarrow> real^'n::finite \<Rightarrow> real \<Rightarrow> 'n pairpath \<Rightarrow> real"
  where "pball_exit T x \<epsilon> \<omega> = pexit T (ball x \<epsilon>) (\<lambda>t. fst (\<omega> t))"

lemma pball_exit_nonneg:
  assumes T0: "0 \<le> T" shows "0 \<le> pball_exit T x \<epsilon> \<omega>"
  unfolding pball_exit_def by (rule pexit_nonneg[OF T0])

lemma pball_exit_le:
  assumes T0: "0 \<le> T" shows "pball_exit T x \<epsilon> \<omega> \<le> T"
  unfolding pball_exit_def by (rule pexit_le_T[OF T0])

theorem exit_val_cond_ball:
  fixes P :: "('n::finite pairpath) measure" and K :: "(real^'n) set"
    and x y :: "real^'n"
  assumes T0: "0 \<le> T" and L1: "1 \<le> L" and Kc: "closed K"
    and P: "P \<in> exit_class k L T y"
    and c: "AE \<omega> in P. c \<le> pexit T K (\<lambda>t. fst (\<omega> t))"
  shows "AE \<omega> in P. c \<le> pball_exit T x \<epsilon> \<omega>
      + min (enn2real (exit_val k L T K (fst (\<omega> (pball_exit T x \<epsilon> \<omega>)))))
            (T - pball_exit T x \<epsilon> \<omega>)"
proof -
  have th0: "0 \<le> pball_exit T x \<epsilon> \<omega>" for \<omega> :: "'n pairpath"
    by (rule pball_exit_nonneg[OF T0])
  have thT: "pball_exit T x \<epsilon> \<omega> \<le> T" for \<omega> :: "'n pairpath"
    by (rule pball_exit_le[OF T0])
  have "AE \<omega> in P. c \<le> pball_exit T x \<epsilon> \<omega>
      + enn2real (exit_val k L (T - pball_exit T x \<epsilon> \<omega>) K
          (fst (\<omega> (pball_exit T x \<epsilon> \<omega>))))"
    by (rule exit_val_cond_time[OF T0 L1 Kc P c th0 thT])
  then show ?thesis
  proof (rule eventually_mono)
    fix \<omega> :: "'n pairpath"
    assume h: "c \<le> pball_exit T x \<epsilon> \<omega>
        + enn2real (exit_val k L (T - pball_exit T x \<epsilon> \<omega>) K
            (fst (\<omega> (pball_exit T x \<epsilon> \<omega>))))"
    have a: "0 \<le> T - pball_exit T x \<epsilon> \<omega>" using thT[of \<omega>] by simp
    have b: "T - pball_exit T x \<epsilon> \<omega> \<le> T" using th0[of \<omega>] by simp
    have "enn2real (exit_val k L (T - pball_exit T x \<epsilon> \<omega>) K
          (fst (\<omega> (pball_exit T x \<epsilon> \<omega>))))
        = min (enn2real (exit_val k L T K (fst (\<omega> (pball_exit T x \<epsilon> \<omega>)))))
              (T - pball_exit T x \<epsilon> \<omega>)"
      by (rule enn2real_paper_v_horizon_cap[OF a b L1 Kc])
    with h show "c \<le> pball_exit T x \<epsilon> \<omega>
        + min (enn2real (exit_val k L T K (fst (\<omega> (pball_exit T x \<epsilon> \<omega>)))))
              (T - pball_exit T x \<epsilon> \<omega>)" by simp
  qed
qed

section \<open>Ito for quadratic test functions, from the martingale clauses\<close>

text \<open>The class of (1.7) is defined by martingale properties, not by an SDE,
  so Ito's formula is not available.  For a quadratic test function the
  expansion is exact and needs no stochastic integration:

    \<open>\<phi> z = c + p \<bullet> z + (z \<bullet> (M *v z))/2\<close>,

  and \<open>z \<bullet> (M *v z) = trace (M ** outerp z)\<close>, so the second-order term is a
  linear functional of the compensated clause (iv) of (1.7).  Its mean is
  therefore pinned by that clause alone, and the first-order term by the
  martingale clause (iii).  What comes out is

    \<open>E[\<phi>(X\<^sub>t)] - \<phi>(x) = (t/2) \<sqdot> trace (M ** b)\<close>,  \<open>b \<in> sconstraint k L\<close>,

  which is exactly the shape the viscosity argument consumes, with \<open>b\<close> the
  averaged covariation direction.\<close>

subsection \<open>Matrix functionals that are bounded linear\<close>

lemma outerp_eq_outer_prod:
  fixes v :: "real^'n::finite"
  shows "outerp v = outer_prod v v"
  by (simp add: outerp_def outer_prod_def)

lemma trace_mult_outerp:
  fixes M :: "real^'n::finite^'n" and v :: "real^'n"
  shows "trace (M ** outerp v) = v \<bullet> (M *v v)"
  by (simp add: outerp_eq_outer_prod mult_outer_prod inner_commute)

text \<open>\<open>trace_mult_sum\<close>, \<open>bounded_linear_trace_mult_left\<close>, \<open>bounded_linear_trace_mult_right\<close>, \<open>bounded_linear_quadform\<close>, \<open>trace_mult_diff\<close>, \<open>trace_mult_scaleR\<close>, \<open>bounded_linear_transpose\<close> live in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


subsection \<open>The averaged covariation stays in the constraint set\<close>

text \<open>Every condition defining \<^const>\<open>sconstraint\<close> is a linear (in)equality in
  the matrix: \<^const>\<open>psd\<close> and \<^const>\<open>eigen_ub\<close> are conditions on the
  quadratic form \<open>z \<bullet> (a *v z)\<close>, linear in \<open>a\<close>, and \<open>c \<le> Pi_proj a m\<close> is by
  @{thm [source] Pi_proj_ge} an intersection of the half-spaces
  \<open>c \<le> trace (a ** P)\<close>, again linear in \<open>a\<close>.  The set is an intersection of
  closed half-spaces and passes through the integral.\<close>

lemma exit_class_Y_integrable:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> exit_class k L T x" and t: "t \<in> {0..T}"
  shows "integrable Q (\<lambda>\<omega>. snd (\<omega> t))"
proof -
  interpret P: prob_space Q by (rule exit_class_prob[OF Q])
  have meas: "(\<lambda>\<omega>. snd (\<omega> t)) \<in> borel_measurable Q"
  proof (rule measurable_compose[OF exit_class_eval_measurable[OF Q t]])
    show "(snd :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n^'n)
        \<in> borel_measurable borel"
      by (intro borel_measurable_continuous_onI continuous_intros)
  qed
  have bd: "AE \<omega> in Q. norm (snd (\<omega> t)) \<le> real CARD('n) * L * T"
    using exit_class_Y_bounded_ae[OF T L Q]
  proof (rule eventually_mono)
    fix \<omega> :: "'n pairpath"
    assume "\<forall>u\<in>{0..T}. norm (snd (\<omega> u)) \<le> real CARD('n) * L * T"
    then show "norm (snd (\<omega> t)) \<le> real CARD('n) * L * T" using t by blast
  qed
  show ?thesis by (rule P.integrable_const_bound[OF bd meas])
qed

theorem exit_class_Y_mean_sconstraint:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> exit_class k L T x"
    and t: "0 < t" and tT: "t \<le> T"
  shows "(1 / t) *\<^sub>R (\<integral>\<omega>. snd (\<omega> t) \<partial>Q) \<in> sconstraint k L"
proof -
  interpret P: prob_space Q by (rule exit_class_prob[OF Q])
  have tI: "t \<in> {0..T}" using t tT by simp
  have iY: "integrable Q (\<lambda>\<omega>. snd (\<omega> t))"
    by (rule exit_class_Y_integrable[OF T L Q tI])
  have i1: "integrable Q (\<lambda>\<omega>. (1 / t) *\<^sub>R snd (\<omega> t))"
    using iY by simp
  define b where "b = (1 / t) *\<^sub>R (\<integral>\<omega>. snd (\<omega> t) \<partial>Q)"
  have bint: "b = (\<integral>\<omega>. (1 / t) *\<^sub>R snd (\<omega> t) \<partial>Q)"
    unfolding b_def by simp
  text \<open>the constraint of clause (iii), read between \<open>0\<close> and \<open>t\<close>\<close>
  have st: "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    using Q unfolding exit_class_def by blast
  have dq: "AE \<omega> in Q. \<forall>s u. 0 \<le> s \<longrightarrow> s < u \<longrightarrow> u \<le> T \<longrightarrow>
      (1 / (u - s)) *\<^sub>R (snd (\<omega> u) - snd (\<omega> s)) \<in> sconstraint k L"
    using Q unfolding exit_class_def by blast
  have mem: "AE \<omega> in Q. (1 / t) *\<^sub>R snd (\<omega> t) \<in> sconstraint k L"
    using st dq
  proof eventually_elim
    case (elim \<omega>)
    have "(1 / (t - 0)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> 0)) \<in> sconstraint k L"
      using elim t tT by blast
    then show ?case using elim by simp
  qed
  have memP: "AE \<omega> in Q. psd ((1 / t) *\<^sub>R snd (\<omega> t))"
    using mem by eventually_elim (simp add: sconstraint_def Pi_constraint_def)
  have memU: "AE \<omega> in Q. eigen_ub ((1 / t) *\<^sub>R snd (\<omega> t)) L"
    using mem by eventually_elim (simp add: sconstraint_def)
  have memI: "AE \<omega> in Q. \<forall>m. k < m \<longrightarrow> m \<le> CARD('n) \<longrightarrow>
      real (m - k) \<le> Pi_proj ((1 / t) *\<^sub>R snd (\<omega> t)) m"
    using mem by eventually_elim (simp add: sconstraint_def Pi_constraint_def)
  text \<open>a real-valued bounded linear functional passes through the integral\<close>
  have lin: "(\<integral>\<omega>. F ((1 / t) *\<^sub>R snd (\<omega> t)) \<partial>Q) = F b"
    if F: "bounded_linear (F :: real^'n^'n \<Rightarrow> real)" for F
    unfolding bint by (rule integral_of_bounded_linear[OF F i1])
  have linI: "integrable Q (\<lambda>\<omega>. F ((1 / t) *\<^sub>R snd (\<omega> t)))"
    if F: "bounded_linear (F :: real^'n^'n \<Rightarrow> real)" for F
    by (rule integrable_bounded_linear[OF F i1])
  text \<open>symmetry\<close>
  have trb: "transpose b = b"
  proof -
    have "transpose b = (\<integral>\<omega>. transpose ((1 / t) *\<^sub>R snd (\<omega> t)) \<partial>Q)"
      unfolding bint
      by (rule integral_of_bounded_linear
          [OF bounded_linear_transpose i1, symmetric])
    also have "\<dots> = (\<integral>\<omega>. (1 / t) *\<^sub>R snd (\<omega> t) \<partial>Q)"
    proof (rule integral_cong_AE)
      show "(\<lambda>\<omega>. transpose ((1 / t) *\<^sub>R snd (\<omega> t))) \<in> borel_measurable Q"
        by (rule borel_measurable_integrable
            [OF integrable_bounded_linear[OF bounded_linear_transpose i1]])
      show "(\<lambda>\<omega>. (1 / t) *\<^sub>R snd (\<omega> t)) \<in> borel_measurable Q"
        by (rule borel_measurable_integrable[OF i1])
      show "AE \<omega> in Q. transpose ((1 / t) *\<^sub>R snd (\<omega> t))
          = (1 / t) *\<^sub>R snd (\<omega> t)"
        using memP by eventually_elim (simp add: psd_def)
    qed
    finally show ?thesis unfolding bint .
  qed
  text \<open>the quadratic form, both bounds\<close>
  have quad_lo: "0 \<le> z \<bullet> (b *v z)" for z :: "real^'n"
  proof -
    have "0 \<le> (\<integral>\<omega>. z \<bullet> (((1 / t) *\<^sub>R snd (\<omega> t)) *v z) \<partial>Q)"
      by (rule integral_nonneg_AE)
        (use memP in \<open>eventually_elim, simp add: psd_def\<close>)
    then show ?thesis using lin[OF bounded_linear_quadform] by simp
  qed
  have quad_hi: "z \<bullet> (b *v z) \<le> L * (z \<bullet> z)" for z :: "real^'n"
  proof -
    have "(\<integral>\<omega>. z \<bullet> (((1 / t) *\<^sub>R snd (\<omega> t)) *v z) \<partial>Q)
        \<le> (\<integral>\<omega>. L * (z \<bullet> z) \<partial>Q)"
      by (rule integral_mono_AE)
        (use linI[OF bounded_linear_quadform] memU
          in \<open>auto elim!: eventually_mono simp: eigen_ub_def\<close>)
    then show ?thesis
      using lin[OF bounded_linear_quadform] by (simp add: P.prob_space)
  qed
  have psdb: "psd b" unfolding psd_def using trb quad_lo by blast
  text \<open>the projection bounds\<close>
  have proj: "real (m - k) \<le> Pi_proj b m"
    if m: "k < m" "m \<le> CARD('n)" for m
  proof (rule Pi_proj_ge[OF m(2)])
    fix P :: "real^'n^'n"
    assume P: "is_proj P" and trP: "trace P = real m"
    have ae: "AE \<omega> in Q.
        real (m - k) \<le> trace (((1 / t) *\<^sub>R snd (\<omega> t)) ** P)"
      using memP memI
    proof eventually_elim
      case (elim \<omega>)
      have "real (m - k) \<le> Pi_proj ((1 / t) *\<^sub>R snd (\<omega> t)) m"
        using elim(2) m by blast
      also have "\<dots> \<le> trace (((1 / t) *\<^sub>R snd (\<omega> t)) ** P)"
        by (rule Pi_proj_le[OF elim(1) P trP])
      finally show ?case .
    qed
    have "real (m - k) = (\<integral>\<omega>. real (m - k) \<partial>Q)"
      by (simp add: P.prob_space)
    also have "\<dots> \<le> (\<integral>\<omega>. trace (((1 / t) *\<^sub>R snd (\<omega> t)) ** P) \<partial>Q)"
      by (rule integral_mono_AE)
        (use linI[OF bounded_linear_trace_mult_right] ae in auto)
    also have "\<dots> = trace (b ** P)"
      by (rule lin[OF bounded_linear_trace_mult_right])
    finally show "real (m - k) \<le> trace (b ** P)" .
  qed
  have pic: "b \<in> Pi_constraint k"
    unfolding Pi_constraint_def
  proof (intro CollectI conjI allI impI)
    show "psd b" by (rule psdb)
  next
    fix m assume "k < m" and "m \<le> CARD('n)"
    then show "real (m - k) \<le> Pi_proj b m" by (rule proj)
  qed
  have eub: "b \<in> {a :: real^'n^'n. eigen_ub a L}"
    using quad_hi by (simp add: eigen_ub_def)
  have "b \<in> sconstraint k L"
    unfolding sconstraint_def using pic eub by blast
  then show ?thesis unfolding b_def[symmetric] .
qed

subsection \<open>The exact expansion of a quadratic test function\<close>

lemma exit_class_X_integrable:
  fixes Q :: "('n::finite pairpath) measure"
  assumes Q: "Q \<in> exit_class k L T x" and t: "t \<in> {0..T}"
  shows "integrable Q (\<lambda>\<omega>. fst (\<omega> t) :: real^'n)"
proof -
  interpret MG: martingale Q "natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)" 0
      "\<lambda>u \<omega>. fst (\<omega> (min u T)) :: real^'n"
    by (rule exit_class_X_martingale[OF Q])
  have "integrable Q (\<lambda>\<omega>. fst (\<omega> (min t T)) :: real^'n)"
    using t by (intro MG.integrable) simp
  then show ?thesis using t by simp
qed

theorem exit_class_X_mean:
  fixes Q :: "('n::finite pairpath) measure"
  assumes Q: "Q \<in> exit_class k L T x" and t: "t \<in> {0..T}"
  shows "(\<integral>\<omega>. fst (\<omega> t) \<partial>Q) = x"
proof -
  interpret P: prob_space Q by (rule exit_class_prob[OF Q])
  interpret MG: martingale Q "natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)" 0
      "\<lambda>u \<omega>. fst (\<omega> (min u T)) :: real^'n"
    by (rule exit_class_X_martingale[OF Q])
  have t0: "0 \<le> t" and tT: "t \<le> T" using t by simp_all
  have z: "(0::real) \<in> {0..T}" using t by simp
  have i0: "integrable Q (\<lambda>\<omega>. fst (\<omega> 0) :: real^'n)"
    by (rule exit_class_X_integrable[OF Q z])
  have it: "integrable Q (\<lambda>\<omega>. fst (\<omega> t) :: real^'n)"
    by (rule exit_class_X_integrable[OF Q t])
  have top: "space Q \<in> sets (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u) 0)"
    using sets.top[of "natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u) 0"] by simp
  have const: "(\<integral>\<omega>. fst (\<omega> 0) \<partial>Q) = (\<integral>\<omega>. fst (\<omega> t) \<partial>Q)"
    using MG.set_integral_eq[OF top order.refl t0] t0 tT
    by (simp add: set_integral_space[OF i0] set_integral_space[OF it])
  have start: "(\<integral>\<omega>. fst (\<omega> 0) \<partial>Q) = x"
  proof -
    have ae: "AE \<omega> in Q. fst (\<omega> 0) = x"
    proof -
      have "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
        using Q unfolding exit_class_def by blast
      then show ?thesis by (rule eventually_mono) simp
    qed
    have "(\<integral>\<omega>. fst (\<omega> 0) \<partial>Q) = (\<integral>\<omega>. x \<partial>Q)"
      by (rule integral_cong_AE[OF borel_measurable_integrable[OF i0] _ ae])
        measurable
    then show ?thesis by (simp add: P.prob_space)
  qed
  from const start show ?thesis by simp
qed

text \<open>The second-order identity holds with no symmetry hypothesis on \<open>M\<close> and
  no stopping: clause (iv) is used at the fixed time \<open>t\<close>, exactly as in
  @{thm [source] exit_class_sq_norm_mean_ge}, of which this is the
  \<open>M = 1\<close> case with the inequality replaced by an identity.\<close>

theorem exit_class_quadform_mean:
  fixes Q :: "('n::finite pairpath) measure" and M :: "real^'n^'n"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> exit_class k L T x" and t: "t \<in> {0..T}"
  shows "(\<integral>\<omega>. fst (\<omega> t) \<bullet> (M *v fst (\<omega> t)) \<partial>Q)
       = x \<bullet> (M *v x) + trace (M ** (\<integral>\<omega>. snd (\<omega> t) \<partial>Q))"
proof -
  have ci: "integrable Q (\<lambda>\<omega>. outerp (fst (\<omega> t)) - snd (\<omega> t))"
    by (rule exit_class_compensated_integrable[OF Q t])
  have iY: "integrable Q (\<lambda>\<omega>. snd (\<omega> t))"
    by (rule exit_class_Y_integrable[OF T L Q t])
  have iA: "integrable Q
      (\<lambda>\<omega>. trace (M ** (outerp (fst (\<omega> t)) - snd (\<omega> t))))"
    by (rule integrable_bounded_linear[OF bounded_linear_trace_mult_left ci])
  have iB: "integrable Q (\<lambda>\<omega>. trace (M ** snd (\<omega> t)))"
    by (rule integrable_bounded_linear[OF bounded_linear_trace_mult_left iY])
  have tdiff: "trace (M ** (A - B)) = trace (M ** A) - trace (M ** B)"
    for A B :: "real^'n^'n"
    by (rule trace_mult_diff)
  have eqf: "(\<lambda>\<omega>. trace (M ** outerp (fst (\<omega> t))))
      = (\<lambda>\<omega>. trace (M ** (outerp (fst (\<omega> t)) - snd (\<omega> t)))
             + trace (M ** snd (\<omega> t)))"
    by (rule ext) (simp add: tdiff)
  have e1: "(\<integral>\<omega>. trace (M ** (outerp (fst (\<omega> t)) - snd (\<omega> t))) \<partial>Q)
      = trace (M ** outerp x)"
  proof -
    have "(\<integral>\<omega>. trace (M ** (outerp (fst (\<omega> t)) - snd (\<omega> t))) \<partial>Q)
        = trace (M ** (\<integral>\<omega>. outerp (fst (\<omega> t)) - snd (\<omega> t) \<partial>Q))"
      by (rule integral_of_bounded_linear[OF bounded_linear_trace_mult_left ci])
    also have "\<dots> = trace (M ** outerp x)"
      by (simp add: exit_class_compensated_mean[OF Q t])
    finally show ?thesis .
  qed
  have e2: "(\<integral>\<omega>. trace (M ** snd (\<omega> t)) \<partial>Q)
      = trace (M ** (\<integral>\<omega>. snd (\<omega> t) \<partial>Q))"
    by (rule integral_of_bounded_linear[OF bounded_linear_trace_mult_left iY])
  have "(\<integral>\<omega>. fst (\<omega> t) \<bullet> (M *v fst (\<omega> t)) \<partial>Q)
      = (\<integral>\<omega>. trace (M ** outerp (fst (\<omega> t))) \<partial>Q)"
    by (simp add: trace_mult_outerp)
  also have "\<dots> = (\<integral>\<omega>. trace (M ** (outerp (fst (\<omega> t)) - snd (\<omega> t))) \<partial>Q)
      + (\<integral>\<omega>. trace (M ** snd (\<omega> t)) \<partial>Q)"
    unfolding eqf by (rule Bochner_Integration.integral_add[OF iA iB])
  also have "\<dots> = x \<bullet> (M *v x) + trace (M ** (\<integral>\<omega>. snd (\<omega> t) \<partial>Q))"
    unfolding e1 e2 by (simp add: trace_mult_outerp)
  finally show ?thesis .
qed

lemma exit_class_quadform_integrable:
  fixes Q :: "('n::finite pairpath) measure" and M :: "real^'n^'n"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> exit_class k L T x" and t: "t \<in> {0..T}"
  shows "integrable Q (\<lambda>\<omega>. fst (\<omega> t) \<bullet> (M *v fst (\<omega> t)))"
proof -
  have ci: "integrable Q (\<lambda>\<omega>. outerp (fst (\<omega> t)) - snd (\<omega> t))"
    by (rule exit_class_compensated_integrable[OF Q t])
  have iY: "integrable Q (\<lambda>\<omega>. snd (\<omega> t))"
    by (rule exit_class_Y_integrable[OF T L Q t])
  have iA: "integrable Q
      (\<lambda>\<omega>. trace (M ** (outerp (fst (\<omega> t)) - snd (\<omega> t))))"
    by (rule integrable_bounded_linear[OF bounded_linear_trace_mult_left ci])
  have iB: "integrable Q (\<lambda>\<omega>. trace (M ** snd (\<omega> t)))"
    by (rule integrable_bounded_linear[OF bounded_linear_trace_mult_left iY])
  have tdiff: "trace (M ** (A - B)) = trace (M ** A) - trace (M ** B)"
    for A B :: "real^'n^'n"
    by (rule trace_mult_diff)
  have eqf: "(\<lambda>\<omega>. fst (\<omega> t) \<bullet> (M *v fst (\<omega> t)))
      = (\<lambda>\<omega>. trace (M ** (outerp (fst (\<omega> t)) - snd (\<omega> t)))
             + trace (M ** snd (\<omega> t)))"
    by (rule ext) (simp add: tdiff trace_mult_outerp[symmetric])
  show ?thesis
    unfolding eqf by (rule Bochner_Integration.integrable_add[OF iA iB])
qed

text \<open>The mean increment of a quadratic test function along any class member
  is \<open>(t/2) \<sqdot> trace (M ** b)\<close> for a single averaged direction \<open>b\<close> of the
  constraint set: the substitute for Ito's formula that the viscosity
  argument needs.\<close>

theorem exit_class_quadratic_mean:
  fixes Q :: "('n::finite pairpath) measure" and M :: "real^'n^'n"
    and p :: "real^'n" and c :: real
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> exit_class k L T x"
    and t: "0 < t" and tT: "t \<le> T"
  obtains b where "b \<in> sconstraint k L"
    and "(\<integral>\<omega>. c + p \<bullet> fst (\<omega> t) + (fst (\<omega> t) \<bullet> (M *v fst (\<omega> t))) / 2 \<partial>Q)
       = c + p \<bullet> x + (x \<bullet> (M *v x)) / 2 + (t / 2) * trace (M ** b)"
proof -
  interpret P: prob_space Q by (rule exit_class_prob[OF Q])
  have tI: "t \<in> {0..T}" using t tT by simp
  define b where "b = (1 / t) *\<^sub>R (\<integral>\<omega>. snd (\<omega> t) \<partial>Q)"
  have bmem: "b \<in> sconstraint k L"
    unfolding b_def by (rule exit_class_Y_mean_sconstraint[OF T L Q t tT])
  have bY: "(\<integral>\<omega>. snd (\<omega> t) \<partial>Q) = t *\<^sub>R b"
    unfolding b_def using t by simp
  have iX: "integrable Q (\<lambda>\<omega>. fst (\<omega> t) :: real^'n)"
    by (rule exit_class_X_integrable[OF Q tI])
  have iP: "integrable Q (\<lambda>\<omega>. p \<bullet> fst (\<omega> t))"
    by (rule integrable_bounded_linear[OF bounded_linear_inner_right iX])
  have iM: "integrable Q (\<lambda>\<omega>. fst (\<omega> t) \<bullet> (M *v fst (\<omega> t)))"
    by (rule exit_class_quadform_integrable[OF T L Q tI])
  have mP: "(\<integral>\<omega>. p \<bullet> fst (\<omega> t) \<partial>Q) = p \<bullet> x"
    using integral_of_bounded_linear[OF bounded_linear_inner_right iX]
      exit_class_X_mean[OF Q tI] by simp
  have mM: "(\<integral>\<omega>. fst (\<omega> t) \<bullet> (M *v fst (\<omega> t)) \<partial>Q)
      = x \<bullet> (M *v x) + t * trace (M ** b)"
  proof -
    have "(\<integral>\<omega>. fst (\<omega> t) \<bullet> (M *v fst (\<omega> t)) \<partial>Q)
        = x \<bullet> (M *v x) + trace (M ** (\<integral>\<omega>. snd (\<omega> t) \<partial>Q))"
      by (rule exit_class_quadform_mean[OF T L Q tI])
    also have "trace (M ** (\<integral>\<omega>. snd (\<omega> t) \<partial>Q)) = t * trace (M ** b)"
      unfolding bY by (rule trace_mult_scaleR)
    finally show ?thesis .
  qed
  have "(\<integral>\<omega>. c + p \<bullet> fst (\<omega> t)
        + (fst (\<omega> t) \<bullet> (M *v fst (\<omega> t))) / 2 \<partial>Q)
      = c + (\<integral>\<omega>. p \<bullet> fst (\<omega> t) \<partial>Q)
        + (\<integral>\<omega>. fst (\<omega> t) \<bullet> (M *v fst (\<omega> t)) \<partial>Q) / 2"
    using iP iM by (simp add: P.prob_space)
  also have "\<dots> = c + p \<bullet> x + (x \<bullet> (M *v x)) / 2 + (t / 2) * trace (M ** b)"
    unfolding mP mM by (simp add: field_simps)
  finally show ?thesis using that[OF bmem] by blast
qed

subsection \<open>What the orthogonality constraint of Eq. (1.9) does\<close>

text \<open>A direction annihilated by the averaged covariation is frozen: the
  process does not move along it, almost surely.  The proof is the
  quadratic identity at \<open>M = outerp q\<close>, which turns the second moment of
  \<open>q \<bullet> X\<^sub>t\<close> into \<open>q \<bullet> (E[Y\<^sub>t] *v q)\<close>, so the variance vanishes exactly when
  that number does.

  This is the mechanism behind the constraint \<open>a *v p = 0\<close> of Eq. (1.9).
  For a quadratic test function with gradient \<open>q = p + M *v x\<close> at \<open>x\<close>,

    \<open>\<phi>(X\<^sub>t) - \<phi>(x) = q \<bullet> (X\<^sub>t - x) + (X\<^sub>t - x) \<bullet> (M *v (X\<^sub>t - x)) / 2\<close>

  when \<open>M\<close> is symmetric, and feasibility of the covariation direction
  kills the first-order term identically, not just in mean: an a.s.
  statement, obtained from a mean-zero variance, that the supersolution
  argument needs and the subsolution argument does not.\<close>

text \<open>\<open>trace_mult_commute\<close> is \<open>trace_matrix_commute\<close> from
  @{theory Relative_Arbitrage.Operator_Envelopes}.\<close>

lemma trace_outerp_mult:
  fixes B :: "real^'n::finite^'n" and v :: "real^'n"
  shows "trace (outerp v ** B) = v \<bullet> (B *v v)"
  by (subst trace_matrix_commute) (rule trace_mult_outerp)

lemma quadform_outerp:
  fixes q z :: "real^'n::finite"
  shows "z \<bullet> (outerp q *v z) = (q \<bullet> z)\<^sup>2"
  by (simp add: outerp_eq_outer_prod power2_eq_square inner_commute)

section \<open>The relaxed operator, and the inequality the class really gives\<close>

text \<open>Eq. (1.9) takes its infimum over \<^const>\<open>feasible\<close>, which carries the
  orthogonality constraint \<open>a *v p = 0\<close> on top of the spectral bounds; the
  class of (1.7) carries no such constraint, its covariation directions
  living in \<^const>\<open>sconstraint\<close>.  The two are related in one direction,

    \<^const>\<open>feasible\<close> \<open>k L p\<close> \<open>\<subseteq>\<close> \<^const>\<open>sconstraint\<close> \<open>k L\<close>

  (@{thm [source] suff_volatile_cap_in_sconstraint}), so the infimum over
  the larger set is smaller: \<open>ell_op_s \<le> ell_op\<close>.  Naming the relaxed
  operator keeps the missing ingredient --- orthogonality of the optimal
  direction to the gradient --- visible instead of buried.\<close>

definition ell_op_s :: "nat \<Rightarrow> real \<Rightarrow> real^'n::finite^'n \<Rightarrow> real" where
  "ell_op_s k L M = Inf ((\<lambda>a. - trace (M ** a) / 2) ` sconstraint k L)"

lemma ell_op_s_bdd_below:
  fixes M :: "real^'n::finite^'n"
  assumes L: "0 \<le> L"
  shows "bdd_below ((\<lambda>a. - trace (M ** a) / 2) ` sconstraint k L)"
proof (rule bdd_belowI[of _
      "- ((\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>) * (real CARD('n) * L)) / 2"])
  fix v assume "v \<in> (\<lambda>a. - trace (M ** a) / 2) ` sconstraint k L"
  then obtain a where a: "a \<in> sconstraint k L"
    and v: "v = - trace (M ** a) / 2" by auto
  have eb: "\<bar>a $ j $ i\<bar> \<le> real CARD('n) * L" for i j
  proof -
    have "\<bar>a $ j $ i\<bar> = norm (a $ j $ i)" by simp
    also have "\<dots> \<le> norm (a $ j)" by (rule Finite_Cartesian_Product.norm_nth_le)
    also have "\<dots> \<le> norm a" by (rule Finite_Cartesian_Product.norm_nth_le)
    also have "\<dots> \<le> real CARD('n) * L" by (rule sconstraint_norm_le[OF L a])
    finally show ?thesis .
  qed
  have "trace (M ** a) \<le> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j * a $ j $ i\<bar>)"
    unfolding trace_mult_sum by (intro sum_mono order_trans[OF _ sum_abs]) auto
  also have "\<dots> \<le> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar> * (real CARD('n) * L))"
    by (intro sum_mono) (simp add: abs_mult mult_left_mono eb)
  also have "\<dots> = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>) * (real CARD('n) * L)"
    by (simp add: sum_distrib_right)
  finally show
    "- ((\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>) * (real CARD('n) * L)) / 2 \<le> v"
    by (simp add: v)
qed

lemma ell_op_s_le_of_witness:
  fixes M :: "real^'n::finite^'n"
  assumes L: "0 \<le> L" and a: "a \<in> sconstraint k L"
    and le: "- trace (M ** a) / 2 \<le> c"
  shows "ell_op_s k L M \<le> c"
proof -
  have mem: "- trace (M ** a) / 2
      \<in> (\<lambda>a. - trace (M ** a) / 2) ` sconstraint k L"
    using a by blast
  have "ell_op_s k L M \<le> - trace (M ** a) / 2"
    unfolding ell_op_s_def by (rule cInf_lower[OF mem ell_op_s_bdd_below[OF L]])
  also have "\<dots> \<le> c" by (rule le)
  finally show ?thesis .
qed

lemma feasible_subset_sconstraint:
  fixes p :: "real^'n::finite"
  shows "feasible k L p \<subseteq> sconstraint k L"
proof
  fix a :: "real^'n^'n"
  assume a: "a \<in> feasible k L p"
  have sv: "a \<in> suff_volatile k"
    using a unfolding feasible_def suff_volatile_def by blast
  have ub: "eigen_ub a L" using a unfolding feasible_def by blast
  show "a \<in> sconstraint k L"
    by (rule suff_volatile_cap_in_sconstraint[OF sv ub])
qed

text \<open>@{thm [source] exit_val_attained} supplies the optimizer, at which the
  exit time dominates the value almost surely --- the reason the
  subsolution half is reachable by expectations: the DPP bound it
  consumes is an a.s. bound, and a.s. bounds survive integration, whereas
  the supersolution half needs a lower bound on an essential infimum,
  which a mean cannot give.

  The test function here is quadratic and touches globally; turning a
  local touching into a global one is the Crandall--Ishii localisation
  step, not used here, so \<open>ell_op_s\<close> rather than \<^const>\<open>ell_op\<close> is what
  comes out.\<close>

theorem exit_val_subsol_quadratic_global:
  fixes K :: "(real^'n::finite) set" and M :: "real^'n^'n"
    and p :: "real^'n" and x :: "real^'n" and c :: real
  assumes T: "0 < T" and L1: "1 \<le> L" and Kc: "closed K"
    and touch: "\<And>z. enn2real (exit_val k L T K z)
          - (c + p \<bullet> z + (z \<bullet> (M *v z)) / 2)
        \<le> enn2real (exit_val k L T K x)
          - (c + p \<bullet> x + (x \<bullet> (M *v x)) / 2)"
  shows "ell_op_s k L M \<le> 1"
proof -
  have L0: "0 \<le> L" using L1 by simp
  have T0: "0 \<le> T" using T by simp
  define u where "u = (\<lambda>z :: real^'n. enn2real (exit_val k L T K z))"
  define \<phi> where "\<phi> = (\<lambda>z :: real^'n. c + p \<bullet> z + (z \<bullet> (M *v z)) / 2)"
  define h where "h = T / 2"
  have h0: "0 < h" and hT: "h \<le> T" using T by (simp_all add: h_def)
  have hI: "h \<in> {0..T}" using h0 hT by simp
  obtain P where P: "P \<in> exit_class k L T x"
    and Pv: "ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))
        = exit_val k L T K x"
    using exit_val_attained[OF T L1 Kc] by blast
  interpret PP: prob_space P by (rule exit_class_prob[OF P])
  text \<open>at the optimizer the exit time dominates the value almost surely\<close>
  have cAE: "AE \<omega> in P. u x \<le> pexit T K (\<lambda>t. fst (\<omega> t))"
  proof (rule eventually_mono
      [OF ess_inf_time_AE[of P "\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))"]])
    fix \<omega> :: "'n pairpath"
    assume "ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))
        \<le> ennreal (pexit T K (\<lambda>t. fst (\<omega> t)))"
    then have le: "exit_val k L T K x \<le> ennreal (pexit T K (\<lambda>t. fst (\<omega> t)))"
      using Pv by simp
    have "enn2real (exit_val k L T K x)
        \<le> enn2real (ennreal (pexit T K (\<lambda>t. fst (\<omega> t))))"
      by (rule enn2real_mono[OF le ennreal_less_top])
    then show "u x \<le> pexit T K (\<lambda>t. fst (\<omega> t))"
      unfolding u_def
      using pexit_nonneg[OF T0, of K "\<lambda>t. fst (\<omega> t)"] by simp
  qed
  text \<open>the DPP at the constant time \<open>h\<close>, then the horizon cap\<close>
  have dpp: "AE \<omega> in P. u x \<le> h + enn2real (exit_val k L (T - h) K (fst (\<omega> h)))"
    by (rule exit_val_cond_time[OF T0 L1 Kc P cAE]) (use h0 hT in auto)
  have low: "AE \<omega> in P. u x - h \<le> u (fst (\<omega> h))"
  proof (rule eventually_mono[OF dpp])
    fix \<omega> :: "'n pairpath"
    assume d: "u x \<le> h + enn2real (exit_val k L (T - h) K (fst (\<omega> h)))"
    have a: "0 \<le> T - h" using hT by simp
    have b: "T - h \<le> T" using h0 by simp
    have "enn2real (exit_val k L (T - h) K (fst (\<omega> h)))
        = min (u (fst (\<omega> h))) (T - h)"
      unfolding u_def by (rule enn2real_paper_v_horizon_cap[OF a b L1 Kc])
    with d show "u x - h \<le> u (fst (\<omega> h))" by simp
  qed
  text \<open>the touching hypothesis transports it to the test function\<close>
  have phiAE: "AE \<omega> in P. \<phi> x - h \<le> \<phi> (fst (\<omega> h))"
  proof (rule eventually_mono[OF low])
    fix \<omega> :: "'n pairpath"
    assume lo: "u x - h \<le> u (fst (\<omega> h))"
    have "u (fst (\<omega> h)) - \<phi> (fst (\<omega> h)) \<le> u x - \<phi> x"
      unfolding u_def \<phi>_def by (rule touch)
    with lo show "\<phi> x - h \<le> \<phi> (fst (\<omega> h))" by simp
  qed
  text \<open>integrate, and read off the exact expansion\<close>
  obtain b where b: "b \<in> sconstraint k L"
    and mean: "(\<integral>\<omega>. c + p \<bullet> fst (\<omega> h)
          + (fst (\<omega> h) \<bullet> (M *v fst (\<omega> h))) / 2 \<partial>P)
        = c + p \<bullet> x + (x \<bullet> (M *v x)) / 2 + (h / 2) * trace (M ** b)"
    by (rule exit_class_quadratic_mean[OF T0 L0 P h0 hT])
  have i1: "integrable P (\<lambda>\<omega>. p \<bullet> fst (\<omega> h))"
    by (rule integrable_bounded_linear[OF bounded_linear_inner_right
        exit_class_X_integrable[OF P hI]])
  have i2: "integrable P (\<lambda>\<omega>. fst (\<omega> h) \<bullet> (M *v fst (\<omega> h)))"
    by (rule exit_class_quadform_integrable[OF T0 L0 P hI])
  have bl2: "bounded_linear (\<lambda>r :: real. r / 2)"
    unfolding linear_conv_bounded_linear[symmetric]
    by (intro linearI) (simp_all add: field_simps)
  have i3: "integrable P (\<lambda>\<omega>. (fst (\<omega> h) \<bullet> (M *v fst (\<omega> h))) / 2)"
    by (rule integrable_bounded_linear[OF bl2 i2])
  have iphi: "integrable P (\<lambda>\<omega>. \<phi> (fst (\<omega> h)))"
    unfolding \<phi>_def
    by (intro Bochner_Integration.integrable_add i1 i3 PP.integrable_const)
  have mean': "(\<integral>\<omega>. \<phi> (fst (\<omega> h)) \<partial>P) = \<phi> x + (h / 2) * trace (M ** b)"
    unfolding \<phi>_def using mean by simp
  have "\<phi> x - h = (\<integral>\<omega>. \<phi> x - h \<partial>P)" by (simp add: PP.prob_space)
  also have "\<dots> \<le> (\<integral>\<omega>. \<phi> (fst (\<omega> h)) \<partial>P)"
    by (rule integral_mono_AE) (use iphi phiAE in auto)
  finally have "\<phi> x - h \<le> \<phi> x + (h / 2) * trace (M ** b)"
    unfolding mean' .
  then have "- h \<le> (h / 2) * trace (M ** b)" by simp
  then have le2: "(- 2) * (h / 2) \<le> trace (M ** b) * (h / 2)"
    by (simp add: field_simps)
  have hp: "0 < h / 2" using h0 by simp
  have "- 2 \<le> trace (M ** b)" by (rule mult_right_le_imp_le[OF le2 hp])
  then have w: "- trace (M ** b) / 2 \<le> 1" by simp
  show ?thesis by (rule ell_op_s_le_of_witness[OF L0 b w])
qed

subsection \<open>Quadratics are test functions, and the relaxed predicates\<close>

lemma test_fun_at_quadratic:
  fixes M :: "real^'n::finite^'n" and p x :: "real^'n" and c :: real
  assumes sym: "transpose M = M"
  shows "test_fun_at (\<lambda>z. c + p \<bullet> z + (z \<bullet> (M *v z)) / 2)
      (\<lambda>z. p + M *v z) M x"
  unfolding test_fun_at_def
proof (intro conjI)
  show "transpose M = M" by (rule sym)
next
  have bl: "bounded_linear (\<lambda>z :: real^'n. M *v z)"
    unfolding linear_conv_bounded_linear[symmetric]
    by (rule matrix_vector_mul_linear)
  have dM: "((\<lambda>z :: real^'n. M *v z) has_derivative (\<lambda>h. M *v h)) (at y)"
    for y :: "real^'n"
    by (rule bounded_linear.has_derivative[OF bl has_derivative_ident])
  have d: "((\<lambda>z :: real^'n. c + p \<bullet> z + (z \<bullet> (M *v z)) / 2)
      has_derivative (\<lambda>h. (p + M *v y) \<bullet> h)) (at y)" for y :: "real^'n"
  proof -
    have "((\<lambda>z :: real^'n. c + p \<bullet> z + (z \<bullet> (M *v z)) / 2)
        has_derivative (\<lambda>h. p \<bullet> h + (h \<bullet> (M *v y) + y \<bullet> (M *v h)) / 2))
        (at y)"
      by (auto intro!: derivative_eq_intros dM)
    moreover have "(\<lambda>h :: real^'n. p \<bullet> h + (h \<bullet> (M *v y) + y \<bullet> (M *v h)) / 2)
        = (\<lambda>h. (p + M *v y) \<bullet> h)"
    proof (rule ext)
      fix h :: "real^'n"
      have "y \<bullet> (M *v h) = (transpose M *v y) \<bullet> h"
        by (rule inner_transpose_matrix)
      then have "y \<bullet> (M *v h) = (M *v y) \<bullet> h" using sym by simp
      then show "p \<bullet> h + (h \<bullet> (M *v y) + y \<bullet> (M *v h)) / 2
          = (p + M *v y) \<bullet> h"
        by (simp add: inner_commute inner_add_right)
    qed
    ultimately show ?thesis by simp
  qed
  show "\<exists>e>0. \<forall>y \<in> ball x e.
      ((\<lambda>z. c + p \<bullet> z + (z \<bullet> (M *v z)) / 2) has_derivative
        (\<lambda>h. (p + M *v y) \<bullet> h)) (at y)"
    using d by (intro exI[of _ 1]) auto
next
  have bl: "bounded_linear (\<lambda>z :: real^'n. M *v z)"
    unfolding linear_conv_bounded_linear[symmetric]
    by (rule matrix_vector_mul_linear)
  show "((\<lambda>z. p + M *v z) has_derivative (\<lambda>h. M *v h)) (at x)"
    using bounded_linear.has_derivative[OF bl has_derivative_ident]
    by (auto intro!: derivative_eq_intros)
qed

section \<open>The ball exit time along a continuous path\<close>

text \<open>Three pathwise facts about \<^const>\<open>pball_exit\<close>, all consumed by an
  Ito-side supplier and none needing a law: they are statements about a
  single continuous path.

  The first is attainment.  With \<open>K\<close> open the target \<open>-K\<close> is closed, so
  along a continuous path the infimum defining \<^const>\<open>pexit\<close> is a minimum
  whenever it is below the horizon: the path really is outside \<open>K\<close> at the
  exit time.  This is the single fact that fails for a general
  discontinuous function, and every other clause below is a consequence
  of it.\<close>

lemma pexit_le_of_mem:
  fixes f :: "real \<Rightarrow> 'b::polish_space"
  assumes T0: "0 \<le> T" and r: "0 \<le> r" "r \<le> T" and mem: "f r \<notin> K"
  shows "pexit T K f \<le> r"
  unfolding pexit_def using T0 r mem by (intro etime_le_of_mem) auto

lemma pexit_mem_of_less_T:
  fixes f :: "real \<Rightarrow> 'b::polish_space"
  assumes T0: "0 \<le> T" and Kop: "open K"
    and cont: "continuous_on {0..T} f"
    and lt: "pexit T K f < T"
  shows "f (pexit T K f) \<notin> K"
proof -
  let ?S = "{r. 0 \<le> r \<and> r \<le> T \<and> f r \<in> - K}"
  have cK: "closed (- K)" unfolding closed_def using Kop by simp
  have Sclosed: "closed ?S"
  proof -
    have "?S = f -` (- K) \<inter> {0..T}" by auto
    then show ?thesis using cont cK by (simp add: continuous_on_closed_vimage)
  qed
  have Sbdd: "bdd_below ?S" by (intro bdd_belowI[of _ 0]) auto
  have pe: "pexit T K f = Inf (?S \<union> {T})"
    unfolding pexit_def etime_def by simp
  have Sne: "?S \<noteq> {}"
  proof (rule ccontr)
    assume "\<not> ?S \<noteq> {}"
    then have e: "?S = {}" by simp
    have "pexit T K f = Inf ({} \<union> {T})" unfolding pe e ..
    then have "pexit T K f = T" by simp
    with lt show False by simp
  qed
  have SleT: "Inf ?S \<le> T"
  proof -
    from Sne obtain s where s: "s \<in> ?S" by blast
    then have "Inf ?S \<le> s" using Sbdd by (intro cInf_lower)
    also have "s \<le> T" using s by simp
    finally show ?thesis .
  qed
  have "Inf (?S \<union> {T}) = inf (Inf ?S) (Inf {T})"
    by (rule cInf_union_distrib[OF Sne Sbdd]) auto
  then have "pexit T K f = Inf ?S" using pe SleT by (simp add: inf_min)
  moreover have "Inf ?S \<in> ?S"
    using Sne Sbdd Sclosed by (intro closed_contains_Inf) auto
  ultimately show ?thesis by simp
qed

text \<open>The second is the congruence clause of a stopping time, restricted to
  continuous paths.  The asymmetry: the \<open>\<ge>\<close> direction is unconditional (a
  witness for \<open>g\<close> strictly below the exit time of \<open>f\<close> is a witness for \<open>f\<close>
  too), and only the \<open>\<le>\<close> direction needs attainment.\<close>

lemma pexit_cong_stopping:
  fixes f g :: "real \<Rightarrow> 'b::polish_space"
  assumes T0: "0 \<le> T" and Kop: "open K"
    and cont: "continuous_on {0..T} f"
    and eq: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> pexit T K f \<Longrightarrow> f t = g t"
  shows "pexit T K g = pexit T K f"
proof -
  have th0: "0 \<le> pexit T K f" by (rule pexit_nonneg[OF T0])
  have thT: "pexit T K f \<le> T" by (rule pexit_le_T[OF T0])
  have le: "pexit T K g \<le> pexit T K f"
  proof (cases "pexit T K f < T")
    case True
    have "f (pexit T K f) \<notin> K"
      by (rule pexit_mem_of_less_T[OF T0 Kop cont True])
    then have m: "g (pexit T K f) \<notin> K"
      using eq[OF th0 order_refl] by simp
    show ?thesis
      by (rule pexit_le_of_mem[of T "pexit T K f" g K, OF T0 th0 thT m])
  next
    case False
    with thT have "pexit T K f = T" by simp
    then show ?thesis using pexit_le_T[OF T0, of K g] by simp
  qed
  have ge: "pexit T K f \<le> pexit T K g"
  proof (rule ccontr)
    assume "\<not> pexit T K f \<le> pexit T K g"
    then have lt: "pexit T K g < pexit T K f" by simp
    have "(\<exists>r. 0 \<le> r \<and> r \<le> T \<and> g r \<in> - K \<and> r < pexit T K f)
        \<or> T < pexit T K f"
      using lt pexit_less_iff[OF T0] by blast
    with thT obtain r where r: "0 \<le> r" "r \<le> T" "g r \<notin> K"
      "r < pexit T K f" by auto
    have "f r \<notin> K" using eq[OF r(1)] r(4) r(3) by simp
    then have "pexit T K f \<le> r"
      by (rule pexit_le_of_mem[OF T0 r(1) r(2)])
    with r(4) show False by simp
  qed
  from le ge show ?thesis by simp
qed

lemma pball_exit_cong:
  fixes \<omega> \<omega>' :: "'n::finite pairpath"
  assumes T0: "0 \<le> T"
    and cont: "continuous_on {0..T} (\<lambda>t. fst (\<omega> t))"
    and eq: "\<And>t. t \<in> {0..pball_exit T x \<epsilon> \<omega>} \<Longrightarrow> \<omega> t = \<omega>' t"
  shows "pball_exit T x \<epsilon> \<omega>' = pball_exit T x \<epsilon> \<omega>"
  unfolding pball_exit_def
proof (rule pexit_cong_stopping[OF T0 open_ball cont])
  fix t :: real
  assume t: "0 \<le> t" "t \<le> pexit T (ball x \<epsilon>) (\<lambda>t. fst (\<omega> t))"
  then have "t \<in> {0..pball_exit T x \<epsilon> \<omega>}" by (simp add: pball_exit_def)
  from eq[OF this] show "fst (\<omega> t) = fst (\<omega>' t)" by simp
qed

text \<open>The third is what makes the exit time useful to the expansion: below
  the horizon the path has actually travelled the full distance \<open>\<epsilon>\<close>.\<close>

lemma pball_exit_outside:
  fixes \<omega> :: "'n::finite pairpath"
  assumes T0: "0 \<le> T"
    and cont: "continuous_on {0..T} (\<lambda>t. fst (\<omega> t))"
    and lt: "pball_exit T x \<epsilon> \<omega> < T"
  shows "\<epsilon> \<le> dist (fst (\<omega> (pball_exit T x \<epsilon> \<omega>))) x"
proof -
  have "fst (\<omega> (pexit T (ball x \<epsilon>) (\<lambda>t. fst (\<omega> t)))) \<notin> ball x \<epsilon>"
    using lt unfolding pball_exit_def
    by (intro pexit_mem_of_less_T[OF T0 open_ball cont]) simp
  then show ?thesis
    unfolding pball_exit_def by (simp add: dist_commute)
qed

text \<open>And it is strictly positive when the path starts strictly inside the
  ball --- exactly the situation of the subsolution argument, where the
  starting point is the touching point \<open>x\<close> itself.  Without this the DPP
  bound of @{thm [source] exit_val_cond_ball} would be vacuous.\<close>

lemma pball_exit_pos:
  fixes \<omega> :: "'n::finite pairpath"
  assumes T0: "0 < T"
    and start: "dist (fst (\<omega> 0)) x < \<epsilon>"
    and cont: "continuous_on {0..T} (\<lambda>t. fst (\<omega> t))"
  shows "0 < pball_exit T x \<epsilon> \<omega>"
proof -
  have T0': "0 \<le> T" using T0 by simp
  have z: "(0::real) \<in> {0..T}" using T0 by simp
  have e0: "0 < \<epsilon> - dist (fst (\<omega> 0)) x" using start by simp
  from cont[unfolded continuous_on_iff] z e0
  obtain \<delta> where d0: "0 < \<delta>"
    and dd: "\<And>t. t \<in> {0..T} \<Longrightarrow> dist t 0 < \<delta>
        \<Longrightarrow> dist (fst (\<omega> t)) (fst (\<omega> 0)) < \<epsilon> - dist (fst (\<omega> 0)) x"
    by blast
  have mle: "min \<delta> T \<le> pball_exit T x \<epsilon> \<omega>"
  proof (rule ccontr)
    assume "\<not> min \<delta> T \<le> pball_exit T x \<epsilon> \<omega>"
    then have lt0: "pball_exit T x \<epsilon> \<omega> < min \<delta> T" by (rule not_le_imp_less)
    then have lt: "pexit T (ball x \<epsilon>) (\<lambda>t. fst (\<omega> t)) < min \<delta> T"
      by (simp add: pball_exit_def)
    have "(\<exists>r. 0 \<le> r \<and> r \<le> T \<and> fst (\<omega> r) \<in> - ball x \<epsilon> \<and> r < min \<delta> T)
        \<or> T < min \<delta> T"
      using lt[unfolded pexit_less_iff[OF T0']] .
    then obtain r where r: "0 \<le> r" "r \<le> T" "fst (\<omega> r) \<notin> ball x \<epsilon>"
      "r < min \<delta> T" by auto
    have dr: "dist (fst (\<omega> r)) (fst (\<omega> 0)) < \<epsilon> - dist (fst (\<omega> 0)) x"
      using r by (intro dd) (auto simp: dist_real_def)
    have "dist (fst (\<omega> r)) x
        \<le> dist (fst (\<omega> r)) (fst (\<omega> 0)) + dist (fst (\<omega> 0)) x"
      by (rule dist_triangle)
    also have "\<dots> < \<epsilon>" using dr by simp
    finally have "fst (\<omega> r) \<in> ball x \<epsilon>" by (simp add: dist_commute)
    with r(3) show False by simp
  qed
  have m0: "0 < min \<delta> T" using d0 T0 by simp
  show ?thesis by (rule order_less_le_trans[OF m0 mle])
qed

section \<open>The ball exit time is a stopping time\<close>

text \<open>\<^const>\<open>path_stopping_time\<close> restricts its congruence clause to
  continuous paths, which is exactly what @{thm [source] pexit_mem_of_less_T}
  shows is forced: attainment of the infimum genuinely fails off the path
  space, so no redefinition of the exit time could have avoided it.  The
  restriction costs nothing, because \<open>space Q = mspace (path_metric T)\<close> is
  the set of continuous paths, and it buys this:\<close>

theorem pball_exit_path_stopping_time:
  fixes x :: "real^'n::finite"
  assumes T0: "0 \<le> T"
  shows "path_stopping_time T (pball_exit T x \<epsilon>)"
  unfolding path_stopping_time_def
proof (intro conjI)
  show "\<forall>\<omega> :: 'n pairpath.
      0 \<le> pball_exit T x \<epsilon> \<omega> \<and> pball_exit T x \<epsilon> \<omega> \<le> T"
    using pball_exit_nonneg[OF T0] pball_exit_le[OF T0] by blast
next
  show "\<forall>\<omega> \<omega>' :: 'n pairpath.
      continuous_on {0..T} (\<lambda>t. fst (\<omega> t)) \<longrightarrow>
      continuous_on {0..T} (\<lambda>t. fst (\<omega>' t)) \<longrightarrow>
      (\<forall>t \<in> {0..pball_exit T x \<epsilon> \<omega>}. \<omega> t = \<omega>' t) \<longrightarrow>
      pball_exit T x \<epsilon> \<omega>' = pball_exit T x \<epsilon> \<omega>"
  proof (intro allI impI)
    fix \<omega> \<omega>' :: "'n pairpath"
    assume c: "continuous_on {0..T} (\<lambda>t. fst (\<omega> t))"
      and c': "continuous_on {0..T} (\<lambda>t. fst (\<omega>' t))"
      and e: "\<forall>t \<in> {0..pball_exit T x \<epsilon> \<omega>}. \<omega> t = \<omega>' t"
    show "pball_exit T x \<epsilon> \<omega>' = pball_exit T x \<epsilon> \<omega>"
      by (rule pball_exit_cong[OF T0 c]) (use e in blast)
  qed
qed

text \<open>So @{thm [source] exit_val_dpp_sup_ge_time} applies at the exit time of
  a ball, and optional sampling at \<open>\<tau> \<and> h\<close> is available for stochastic
  localisation.\<close>

section \<open>Scalar multiples through the Bochner integral\<close>

text \<open>\<open>integrable_cmult\<close>, \<open>integral_cmult\<close>, \<open>integral_pos_of_AE_pos\<close> live in @{theory Continuous_Time_Martingales.Integrability_Criteria}.\<close>


section \<open>Measurability of the ball exit time\<close>

text \<open>\<open>pexit_path_measurable\<close> covers closed targets and the ball is open, so
  this cannot be inherited directly.  With the closed set \<open>- ball x \<epsilon>\<close> as
  the hitting target, along a continuous path the sublevel event
  \<open>{\<tau> \<le> t}\<close> is (by @{thm [source] etime_le_iff}, using attainment) the
  event that the path reaches distance \<open>\<ge> \<epsilon>\<close> somewhere on \<open>[0,t]\<close>, and by
  continuity that is decided by countably many times: the rationals of
  \<open>[0,t]\<close> and \<open>t\<close> itself.  A countable intersection of countable unions of
  evaluation events remains measurable.\<close>

lemma dist_eval_measurable:
  fixes x :: "real^'n::finite"
  shows "(\<lambda>\<omega> :: 'n pairpath. dist (fst (\<omega> r)) x)
      \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
proof -
  have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> r) \<in> borel_measurable
      (borel_of (mtopology_of (path_metric T :: ('n pairpath) metric)))"
    by (rule pair_law_eval_measurable[OF refl])
  have c: "(\<lambda>pr :: (real^'n) \<times> (real^'n^'n). dist (fst pr) x)
      \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  show ?thesis by (rule measurable_compose[OF ev c])
qed

lemma pball_exit_le_iff_dense:
  fixes \<omega> :: "'n::finite pairpath"
  assumes T0: "0 \<le> T" and t: "0 \<le> t" and tT: "t < T"
    and cont: "continuous_on {0..T} (\<lambda>s. fst (\<omega> s))"
  shows "pball_exit T x \<epsilon> \<omega> \<le> t \<longleftrightarrow>
     (\<forall>n :: nat. \<exists>r \<in> insert t ({0..t} \<inter> \<rat>).
        \<epsilon> - 1 / real (Suc n) < dist (fst (\<omega> r)) x)"
proof -
  have Ac: "closed (- ball x \<epsilon> :: (real^'n) set)"
    by (simp add: closed_Compl)
  have hc: "continuous_on {0..T} (\<lambda>s. dist (fst (\<omega> s)) x)"
    by (intro continuous_on_dist cont continuous_on_const)
  show ?thesis
  proof
    assume le: "pball_exit T x \<epsilon> \<omega> \<le> t"
    then have "etime T (- ball x \<epsilon>) (\<lambda>r g. g r) (\<lambda>s. fst (\<omega> s)) \<le> t"
      by (simp add: pball_exit_def pexit_def)
    then have "\<exists>r\<in>{0..t}. fst (\<omega> r) \<in> - ball x \<epsilon>"
      using etime_le_iff[where X = "\<lambda>r g. g r" and \<omega> = "\<lambda>s. fst (\<omega> s)",
          OF T0 t tT Ac cont] by simp
    then obtain r0 where r0: "r0 \<in> {0..t}" and m0: "fst (\<omega> r0) \<notin> ball x \<epsilon>"
      by auto
    have d0: "\<epsilon> \<le> dist (fst (\<omega> r0)) x"
      using m0 by (simp add: dist_commute)
    show "\<forall>n :: nat. \<exists>r \<in> insert t ({0..t} \<inter> \<rat>).
        \<epsilon> - 1 / real (Suc n) < dist (fst (\<omega> r)) x"
    proof
      fix n :: nat
      show "\<exists>r \<in> insert t ({0..t} \<inter> \<rat>).
          \<epsilon> - 1 / real (Suc n) < dist (fst (\<omega> r)) x"
      proof (cases "r0 = 0 \<or> r0 = t")
        case True
        have mem: "r0 \<in> insert t ({0..t} \<inter> \<rat>)"
          using True r0 t by auto
        have p1: "0 < 1 / real (Suc n)" by simp
        with d0 have "\<epsilon> - 1 / real (Suc n) < dist (fst (\<omega> r0)) x" by linarith
        with mem show ?thesis by blast
      next
        case False
        then have r00: "0 < r0" and r0t: "r0 < t" using r0 by auto
        have r0T: "r0 \<in> {0..T}" using r0 tT by auto
        have cw: "continuous (at r0 within {0..T}) (\<lambda>s. dist (fst (\<omega> s)) x)"
          using hc r0T by (simp add: continuous_on_eq_continuous_within)
        have e1: "0 < 1 / real (Suc n)" by simp
        obtain d where dd: "0 < d"
          and near: "\<And>s. s \<in> {0..T} \<Longrightarrow> dist s r0 < d \<Longrightarrow>
              dist (dist (fst (\<omega> s)) x) (dist (fst (\<omega> r0)) x) < 1 / real (Suc n)"
          using cw[unfolded continuous_within_eps_delta, rule_format, OF e1]
          by blast
        obtain q where q: "q \<in> \<rat>" and ql: "r0 - min d r0 < q" and qu: "q < r0"
          using Rats_dense_in_real[of "r0 - min d r0" r0] dd r00 by auto
        have q0: "0 \<le> q" using ql dd r00 by simp
        have qt: "q \<le> t" using qu r0t by simp
        have qT: "q \<in> {0..T}" using q0 qt tT by auto
        have "dist q r0 < d" using ql qu dd by (simp add: dist_real_def)
        then have "dist (dist (fst (\<omega> q)) x) (dist (fst (\<omega> r0)) x)
            < 1 / real (Suc n)"
          by (rule near[OF qT])
        then have "dist (fst (\<omega> r0)) x - 1 / real (Suc n) < dist (fst (\<omega> q)) x"
          by (simp add: dist_real_def abs_diff_less_iff)
        with d0 have "\<epsilon> - 1 / real (Suc n) < dist (fst (\<omega> q)) x" by simp
        moreover have "q \<in> insert t ({0..t} \<inter> \<rat>)" using q q0 qt by auto
        ultimately show ?thesis by blast
      qed
    qed
  next
    assume H: "\<forall>n :: nat. \<exists>r \<in> insert t ({0..t} \<inter> \<rat>).
        \<epsilon> - 1 / real (Suc n) < dist (fst (\<omega> r)) x"
    have "\<exists>r \<in> {0..t}. \<epsilon> \<le> dist (fst (\<omega> r)) x"
    proof -
      obtain rs where rs: "\<And>n :: nat. rs n \<in> insert t ({0..t} \<inter> \<rat>)
          \<and> \<epsilon> - 1 / real (Suc n) < dist (fst (\<omega> (rs n))) x"
        using H by metis
      have rng: "rs n \<in> {0..t}" for n using rs[of n] t by auto
      have bdd: "bounded (range rs)"
      proof (rule boundedI[of _ t])
        fix w assume "w \<in> range rs"
        then obtain n where "w = rs n" by blast
        then show "norm w \<le> t" using rng[of n] t by auto
      qed
      obtain l \<sigma> where sm: "strict_mono \<sigma>" and lim: "(rs \<circ> \<sigma>) \<longlonglongrightarrow> l"
        using bounded_imp_convergent_subsequence[OF bdd] by blast
      have inI: "(rs \<circ> \<sigma>) n \<in> {0..t}" for n using rng[of "\<sigma> n"] by simp
      have lI: "l \<in> {0..t}"
        by (rule closed_sequentially[OF closed_atLeastAtMost _ lim])
          (use inI in blast)
      have lT: "l \<in> {0..T}" using lI tT by auto
      have cl: "continuous (at l within {0..T}) (\<lambda>s. dist (fst (\<omega> s)) x)"
        using hc lT by (simp add: continuous_on_eq_continuous_within)
      have inT: "(rs \<circ> \<sigma>) n \<in> {0..T}" for n using inI[of n] tT by auto
      have tends: "(\<lambda>n. dist (fst (\<omega> ((rs \<circ> \<sigma>) n))) x)
          \<longlonglongrightarrow> dist (fst (\<omega> l)) x"
        using cl[unfolded continuous_within_sequentially, rule_format,
            of "rs \<circ> \<sigma>"] inT lim by (simp add: o_def)
      have low: "\<epsilon> - 1 / real (Suc n) \<le> dist (fst (\<omega> ((rs \<circ> \<sigma>) n))) x" for n
      proof -
        have "\<epsilon> - 1 / real (Suc (\<sigma> n)) < dist (fst (\<omega> (rs (\<sigma> n)))) x"
          using rs[of "\<sigma> n"] by blast
        moreover have "\<epsilon> - 1 / real (Suc n) \<le> \<epsilon> - 1 / real (Suc (\<sigma> n))"
          using seq_suble[OF sm, of n] by (simp add: frac_le)
        ultimately show ?thesis by (simp add: o_def)
      qed
      have lima: "(\<lambda>n. \<epsilon> - 1 / real (Suc n)) \<longlonglongrightarrow> \<epsilon>"
      proof -
        have "(\<lambda>n. 1 / real (Suc n)) \<longlonglongrightarrow> 0"
          using LIMSEQ_inverse_real_of_nat by (simp add: inverse_eq_divide)
        then have "(\<lambda>n. \<epsilon> - 1 / real (Suc n)) \<longlonglongrightarrow> \<epsilon> - 0"
          by (intro tendsto_diff tendsto_const)
        then show ?thesis by simp
      qed
      have "\<epsilon> \<le> dist (fst (\<omega> l)) x"
        by (rule LIMSEQ_le[OF lima tends]) (use low in blast)
      then show ?thesis using lI by blast
    qed
    then obtain r where r: "r \<in> {0..t}" and rd: "\<epsilon> \<le> dist (fst (\<omega> r)) x"
      by blast
    have "fst (\<omega> r) \<notin> ball x \<epsilon>" using rd by (simp add: dist_commute)
    then have "pexit T (ball x \<epsilon>) (\<lambda>s. fst (\<omega> s)) \<le> r"
      using r tT by (intro pexit_le_of_mem[OF T0]) auto
    then have "pball_exit T x \<epsilon> \<omega> \<le> r" by (simp add: pball_exit_def)
    then show "pball_exit T x \<epsilon> \<omega> \<le> t"
      using r by (auto intro: order_trans)
  qed
qed

theorem pball_exit_measurable:
  fixes x :: "real^'n::finite"
  assumes T0: "0 \<le> T"
  shows "pball_exit T x \<epsilon> \<in> borel_measurable (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
proof (rule borel_measurableI_le)
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  fix a :: real
  show "{\<omega> \<in> space ?B. pball_exit T x \<epsilon> \<omega> \<le> a} \<in> sets ?B"
  proof (cases "a < 0")
    case True
    have empty: "{\<omega> \<in> space ?B. pball_exit T x \<epsilon> \<omega> \<le> a} = {}"
    proof (rule set_eqI)
      fix \<omega> :: "'n pairpath"
      have "\<not> pball_exit T x \<epsilon> \<omega> \<le> a"
        using pball_exit_nonneg[OF T0, of x \<epsilon> \<omega>] True by linarith
      then show "\<omega> \<in> {\<omega> \<in> space ?B. pball_exit T x \<epsilon> \<omega> \<le> a}
          \<longleftrightarrow> \<omega> \<in> {}" by simp
    qed
    show ?thesis unfolding empty by simp
  next
    case False
    then have a0: "0 \<le> a" by simp
    show ?thesis
    proof (cases "T \<le> a")
      case True
      have ya: "pball_exit T x \<epsilon> \<omega> \<le> a" for \<omega> :: "'n pairpath"
        using pball_exit_le[OF T0, of x \<epsilon> \<omega>] True by linarith
      then have "{\<omega> \<in> space ?B. pball_exit T x \<epsilon> \<omega> \<le> a} = space ?B" by auto
      then show ?thesis by simp
    next
      case False
      then have aT: "a < T" by simp
      let ?D = "insert a ({0..a} \<inter> \<rat>)"
      let ?S = "\<lambda>n r. {\<omega> \<in> space ?B. \<epsilon> - 1 / real (Suc n) < dist (fst (\<omega> r)) x}"
      have cntD: "countable ?D"
        by (intro countable_insert countable_Int2 countable_rat)
      have atom: "?S n r \<in> sets ?B" for n r
      proof -
        have "(\<lambda>\<omega> :: 'n pairpath. dist (fst (\<omega> r)) x) \<in> borel_measurable ?B"
          by (rule dist_eval_measurable)
        then have "(\<lambda>\<omega> :: 'n pairpath. dist (fst (\<omega> r)) x) -` {\<epsilon> - 1 / real (Suc n) <..}
            \<inter> space ?B \<in> sets ?B"
          by (rule measurable_sets) simp
        moreover have "?S n r = (\<lambda>\<omega> :: 'n pairpath. dist (fst (\<omega> r)) x)
            -` {\<epsilon> - 1 / real (Suc n) <..} \<inter> space ?B"
          by auto
        ultimately show ?thesis by simp
      qed
      have eq: "{\<omega> \<in> space ?B. pball_exit T x \<epsilon> \<omega> \<le> a}
          = (\<Inter>n. \<Union>r \<in> ?D. ?S n r)"
      proof (rule set_eqI)
        fix \<omega> :: "'n pairpath"
        show "\<omega> \<in> {\<omega> \<in> space ?B. pball_exit T x \<epsilon> \<omega> \<le> a}
            \<longleftrightarrow> \<omega> \<in> (\<Inter>n. \<Union>r \<in> ?D. ?S n r)"
        proof (cases "\<omega> \<in> space ?B")
          case True
          have cw: "continuous_on {0..T} (\<lambda>s. fst (\<omega> s))"
            by (rule path_sets_fst_continuous[OF refl True])
          show ?thesis
            using pball_exit_le_iff_dense[OF T0 a0 aT cw, of x \<epsilon>] True
            by auto
        next
          case False
          then show ?thesis by auto
        qed
      qed
      have un_m: "(\<Union>r \<in> ?D. ?S n r) \<in> sets ?B" for n
        by (rule sets.countable_UN'[OF cntD]) (use atom in blast)
      have "(\<Inter>n. \<Union>r \<in> ?D. ?S n r) \<in> sets ?B"
        using un_m by blast
      with eq show ?thesis by metis
    qed
  qed
qed

section \<open>Up to the exit time the path stays in the closed ball\<close>

lemma pball_exit_stays_cball:
  fixes \<omega> :: "'n::finite pairpath"
  assumes T0: "0 \<le> T"
    and start: "dist (fst (\<omega> 0)) x < \<epsilon>"
    and cont: "continuous_on {0..T} (\<lambda>s. fst (\<omega> s))"
    and s: "0 \<le> s" and sle: "s \<le> pball_exit T x \<epsilon> \<omega>"
  shows "dist (fst (\<omega> s)) x \<le> \<epsilon>"
proof (rule ccontr)
  assume "\<not> dist (fst (\<omega> s)) x \<le> \<epsilon>"
  then have gt: "\<epsilon> < dist (fst (\<omega> s)) x" by simp
  have sT: "s \<le> T" using sle pball_exit_le[OF T0] order_trans by blast
  have notin: "fst (\<omega> s) \<notin> ball x \<epsilon>"
    using gt by (simp add: dist_commute)
  have le1: "pball_exit T x \<epsilon> \<omega> \<le> s"
    unfolding pball_exit_def
    by (rule pexit_le_of_mem[where f = "\<lambda>s. fst (\<omega> s)" and r = s
          and K = "ball x \<epsilon>", OF T0 s sT notin])
  with sle have seq: "s = pball_exit T x \<epsilon> \<omega>" by simp
  have h0: "dist (fst (\<omega> 0)) x \<le> \<epsilon>" using start by simp
  have hc: "continuous_on {0..s} (\<lambda>r. dist (fst (\<omega> r)) x)"
    by (rule continuous_on_subset[of "{0..T}"])
      (use sT in \<open>auto intro!: continuous_on_dist cont continuous_on_const\<close>)
  obtain r where r0: "0 \<le> r" and rs: "r \<le> s" and rd: "dist (fst (\<omega> r)) x = \<epsilon>"
    using IVT'[of "\<lambda>r. dist (fst (\<omega> r)) x" 0 \<epsilon> s] h0 gt s hc by auto
  have rlt: "r < s" using rd gt rs by (cases "r = s") auto
  have "fst (\<omega> r) \<notin> ball x \<epsilon>" using rd by (simp add: dist_commute)
  then have "pball_exit T x \<epsilon> \<omega> \<le> r"
    unfolding pball_exit_def
    by (intro pexit_le_of_mem[OF T0 r0]) (use rs sT in auto)
  with rlt seq show False by simp
qed

section \<open>Optional sampling at a stopping time, via the stopped law\<close>

text \<open>The optional-sampling content follows from the DPP:
  @{thm [source] pstopped_law_horizon_component} and
  @{thm [source] pstopped_law_horizon_compensated} say the two martingale
  clauses of (1.7) survive stopping.  Reading those martingales' means at
  the horizon \<open>T\<close>, where the stopped path is the path at \<open>\<theta>\<close>, and
  transporting along \<open>pair_law_of\<close> (a \<open>distr\<close>) yields the sampled means.\<close>

lemma X_eval_entry_measurable:
  "(\<lambda>p' :: 'n::finite pairpath. fst (p' u) $ c) \<in> borel_measurable
     (borel_of (mtopology_of (path_metric T :: ('n pairpath) metric)))"
proof (rule measurable_compose[OF pair_law_eval_measurable[OF refl]])
  have f: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n) \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  show "(\<lambda>pr :: (real^'n) \<times> (real^'n^'n). fst pr $ c) \<in> borel_measurable borel"
    by (rule measurable_compose[OF f borel_measurable_nth])
qed

lemma comp_eval_entry_measurable:
  "(\<lambda>p' :: 'n::finite pairpath. (outerp (fst (p' u)) - snd (p' u)) $ cc $ dd)
     \<in> borel_measurable
       (borel_of (mtopology_of (path_metric T :: ('n pairpath) metric)))"
proof (rule measurable_compose[OF pair_law_eval_measurable[OF refl]])
  have f: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n) \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  have s: "(snd :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n^'n) \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  have o: "(\<lambda>pr :: (real^'n) \<times> (real^'n^'n). outerp (fst pr))
      \<in> borel_measurable borel"
    by (rule measurable_compose[OF f outerp_borel])
  have dm: "(\<lambda>pr :: (real^'n) \<times> (real^'n^'n). outerp (fst pr) - snd pr)
      \<in> borel_measurable borel"
    by (rule borel_measurable_diff[OF o s])
  have n1: "(\<lambda>v :: real^'n^'n. v $ cc) \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI)
      (rule linear_continuous_on[OF bounded_linear_vec_nth])
  have n2: "(\<lambda>v :: real^'n. v $ dd) \<in> borel_measurable borel"
    by (rule borel_measurable_nth)
  show "(\<lambda>pr :: (real^'n) \<times> (real^'n^'n). (outerp (fst pr) - snd pr) $ cc $ dd)
      \<in> borel_measurable borel"
    by (rule measurable_compose[OF measurable_compose[OF dm n1] n2])
qed

lemma exit_class_X_entry_stopped:
  fixes P :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T: "0 < T" and L0: "0 \<le> L" and P: "P \<in> exit_class k L T x"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "integrable P (\<lambda>\<omega>. fst (\<omega> (\<theta> \<omega>)) $ c)"
    and "(\<integral>\<omega>. fst (\<omega> (\<theta> \<omega>)) $ c \<partial>P) = x $ c"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?Q = "pair_law_of T (pstopped T \<theta>) P"
  let ?G = "natural_filtration ?Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  have T0: "0 \<le> T" using T by simp
  have PS: "prob_space P" by (rule exit_class_prob[OF P])
  have setsP: "sets P = sets ?B" by (rule exit_class_sets[OF P])
  have P0: "AE \<omega> in P. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    using P unfolding exit_class_def by blast
  have th0: "0 \<le> \<theta> \<omega>" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF st])
  have thT: "\<theta> \<omega> \<le> T" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_le[OF st])
  interpret H: horizon_sq_int_martingale ?Q ?G
      "\<lambda>u p'. fst (p' (min u T)) $ c" T
    by (rule pstopped_law_horizon_component[OF T L0 P st thM])
  have m1: "pstopped T \<theta> \<in> P \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsP refl]
    by (rule pstopped_measurable[OF T0 thM th0 thT])
  have fm: "(\<lambda>p' :: 'n pairpath. fst (p' T) $ c) \<in> borel_measurable ?B"
    by (rule X_eval_entry_measurable)
  have iT: "integrable ?Q (\<lambda>p'. fst (p' (min T T)) $ c)"
    by (intro H.integrable) (rule T0)
  then have iT': "integrable ?Q (\<lambda>p'. fst (p' T) $ c)" by simp
  have i0: "integrable ?Q (\<lambda>p'. fst (p' (min 0 T)) $ c)"
    by (intro H.integrable) simp
  then have i0': "integrable ?Q (\<lambda>p'. fst (p' 0) $ c)" using T0 by simp
  have top: "space ?Q \<in> sets (?G 0)"
    using sets.top[of "?G 0"] by simp
  have const': "(\<integral>p'. fst (p' 0) $ c \<partial>?Q) = (\<integral>p'. fst (p' T) $ c \<partial>?Q)"
  proof -
    have s: "(\<integral>p'\<in>space ?Q. fst (p' (min 0 T)) $ c \<partial>?Q)
        = (\<integral>p'\<in>space ?Q. fst (p' (min T T)) $ c \<partial>?Q)"
      by (rule H.set_integral_eq[OF top order.refl T0])
    have e0: "(\<integral>p'\<in>space ?Q. fst (p' (min 0 T)) $ c \<partial>?Q)
        = (\<integral>p'. fst (p' (min 0 T)) $ c \<partial>?Q)"
      by (rule set_integral_space[OF i0])
    have eT: "(\<integral>p'\<in>space ?Q. fst (p' (min T T)) $ c \<partial>?Q)
        = (\<integral>p'. fst (p' (min T T)) $ c \<partial>?Q)"
      by (rule set_integral_space[OF iT])
    from s e0 eT show ?thesis using T0 by simp
  qed
  have Qst: "AE p' in ?Q. fst (p' 0) = x \<and> snd (p' 0) = 0"
    by (rule pstopped_law_start[OF T0 setsP st thM P0])
  have PQ1: "measure ?Q (space ?Q) = 1"
    using prob_space.prob_space[OF pstopped_law_prob[OF T0 PS setsP st thM]]
    by simp
  have start: "(\<integral>p'. fst (p' 0) $ c \<partial>?Q) = x $ c"
  proof -
    have "(\<integral>p'. fst (p' 0) $ c \<partial>?Q) = (\<integral>p'. x $ c \<partial>?Q)"
      by (rule integral_cong_AE[OF borel_measurable_integrable[OF i0'] _])
        (use Qst in \<open>auto elim: eventually_mono\<close>)
    also have "\<dots> = measure ?Q (space ?Q) *\<^sub>R (x $ c)"
      by (rule lebesgue_integral_const)
    finally show ?thesis by (simp add: PQ1)
  qed
  have peq: "(\<lambda>\<omega> :: 'n pairpath. fst (pstopped T \<theta> \<omega> T) $ c)
      = (\<lambda>\<omega>. fst (\<omega> (\<theta> \<omega>)) $ c)"
  proof (rule ext)
    fix \<omega> :: "'n pairpath"
    have "pstopped T \<theta> \<omega> T = \<omega> (min T (\<theta> \<omega>))"
      by (rule pstopped_apply) (use T0 in simp)
    also have "min T (\<theta> \<omega>) = \<theta> \<omega>" using thT[of \<omega>] by simp
    finally show "fst (pstopped T \<theta> \<omega> T) $ c = fst (\<omega> (\<theta> \<omega>)) $ c" by simp
  qed
  have QT: "(\<integral>p'. fst (p' T) $ c \<partial>?Q) = (\<integral>\<omega>. fst (\<omega> (\<theta> \<omega>)) $ c \<partial>P)"
  proof -
    have "(\<integral>p'. fst (p' T) $ c \<partial>?Q)
        = (\<integral>\<omega>. fst (pstopped T \<theta> \<omega> T) $ c \<partial>P)"
      unfolding pair_law_of_def by (rule integral_distr[OF m1 fm])
    then show ?thesis unfolding peq .
  qed
  show "integrable P (\<lambda>\<omega>. fst (\<omega> (\<theta> \<omega>)) $ c)"
  proof -
    have "integrable P (\<lambda>\<omega>. fst (pstopped T \<theta> \<omega> T) $ c)"
      using iT' unfolding pair_law_of_def integrable_distr_eq[OF m1 fm] .
    then show ?thesis unfolding peq .
  qed
  show "(\<integral>\<omega>. fst (\<omega> (\<theta> \<omega>)) $ c \<partial>P) = x $ c"
    using const' start QT by simp
qed

lemma exit_class_comp_entry_stopped:
  fixes P :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T: "0 < T" and L0: "0 \<le> L" and P: "P \<in> exit_class k L T x"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "integrable P (\<lambda>\<omega>. (outerp (fst (\<omega> (\<theta> \<omega>))) - snd (\<omega> (\<theta> \<omega>))) $ cc $ dd)"
    and "(\<integral>\<omega>. (outerp (fst (\<omega> (\<theta> \<omega>))) - snd (\<omega> (\<theta> \<omega>))) $ cc $ dd \<partial>P)
        = outerp x $ cc $ dd"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?Q = "pair_law_of T (pstopped T \<theta>) P"
  let ?G = "natural_filtration ?Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  have T0: "0 \<le> T" using T by simp
  have PS: "prob_space P" by (rule exit_class_prob[OF P])
  have setsP: "sets P = sets ?B" by (rule exit_class_sets[OF P])
  have P0: "AE \<omega> in P. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    using P unfolding exit_class_def by blast
  have th0: "0 \<le> \<theta> \<omega>" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF st])
  have thT: "\<theta> \<omega> \<le> T" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_le[OF st])
  interpret H: horizon_sq_int_martingale ?Q ?G
      "\<lambda>u p'. (outerp (fst (p' (min u T))) - snd (p' (min u T))) $ cc $ dd" T
    by (rule pstopped_law_horizon_compensated[OF T L0 P st thM])
  have m1: "pstopped T \<theta> \<in> P \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsP refl]
    by (rule pstopped_measurable[OF T0 thM th0 thT])
  have fm: "(\<lambda>p' :: 'n pairpath. (outerp (fst (p' T)) - snd (p' T)) $ cc $ dd)
      \<in> borel_measurable ?B"
    by (rule comp_eval_entry_measurable)
  have iT: "integrable ?Q
      (\<lambda>p'. (outerp (fst (p' (min T T))) - snd (p' (min T T))) $ cc $ dd)"
    by (intro H.integrable) (rule T0)
  then have iT': "integrable ?Q
      (\<lambda>p'. (outerp (fst (p' T)) - snd (p' T)) $ cc $ dd)" by simp
  have i0: "integrable ?Q
      (\<lambda>p'. (outerp (fst (p' (min 0 T))) - snd (p' (min 0 T))) $ cc $ dd)"
    by (intro H.integrable) simp
  then have i0': "integrable ?Q
      (\<lambda>p'. (outerp (fst (p' 0)) - snd (p' 0)) $ cc $ dd)" using T0 by simp
  have top: "space ?Q \<in> sets (?G 0)"
    using sets.top[of "?G 0"] by simp
  have const': "(\<integral>p'. (outerp (fst (p' 0)) - snd (p' 0)) $ cc $ dd \<partial>?Q)
      = (\<integral>p'. (outerp (fst (p' T)) - snd (p' T)) $ cc $ dd \<partial>?Q)"
  proof -
    have s: "(\<integral>p'\<in>space ?Q.
          (outerp (fst (p' (min 0 T))) - snd (p' (min 0 T))) $ cc $ dd \<partial>?Q)
        = (\<integral>p'\<in>space ?Q.
          (outerp (fst (p' (min T T))) - snd (p' (min T T))) $ cc $ dd \<partial>?Q)"
      by (rule H.set_integral_eq[OF top order.refl T0])
    have e0: "(\<integral>p'\<in>space ?Q.
          (outerp (fst (p' (min 0 T))) - snd (p' (min 0 T))) $ cc $ dd \<partial>?Q)
        = (\<integral>p'. (outerp (fst (p' (min 0 T))) - snd (p' (min 0 T))) $ cc $ dd \<partial>?Q)"
      by (rule set_integral_space[OF i0])
    have eT: "(\<integral>p'\<in>space ?Q.
          (outerp (fst (p' (min T T))) - snd (p' (min T T))) $ cc $ dd \<partial>?Q)
        = (\<integral>p'. (outerp (fst (p' (min T T))) - snd (p' (min T T))) $ cc $ dd \<partial>?Q)"
      by (rule set_integral_space[OF iT])
    from s e0 eT show ?thesis using T0 by simp
  qed
  have Qst: "AE p' in ?Q. fst (p' 0) = x \<and> snd (p' 0) = 0"
    by (rule pstopped_law_start[OF T0 setsP st thM P0])
  have PQ1: "measure ?Q (space ?Q) = 1"
    using prob_space.prob_space[OF pstopped_law_prob[OF T0 PS setsP st thM]]
    by simp
  have start: "(\<integral>p'. (outerp (fst (p' 0)) - snd (p' 0)) $ cc $ dd \<partial>?Q)
      = outerp x $ cc $ dd"
  proof -
    have "(\<integral>p'. (outerp (fst (p' 0)) - snd (p' 0)) $ cc $ dd \<partial>?Q)
        = (\<integral>p'. outerp x $ cc $ dd \<partial>?Q)"
      by (rule integral_cong_AE[OF borel_measurable_integrable[OF i0'] _])
        (use Qst in \<open>auto elim: eventually_mono\<close>)
    also have "\<dots> = measure ?Q (space ?Q) *\<^sub>R (outerp x $ cc $ dd)"
      by (rule lebesgue_integral_const)
    finally show ?thesis by (simp add: PQ1)
  qed
  have peq: "(\<lambda>\<omega> :: 'n pairpath.
        (outerp (fst (pstopped T \<theta> \<omega> T)) - snd (pstopped T \<theta> \<omega> T)) $ cc $ dd)
      = (\<lambda>\<omega>. (outerp (fst (\<omega> (\<theta> \<omega>))) - snd (\<omega> (\<theta> \<omega>))) $ cc $ dd)"
  proof (rule ext)
    fix \<omega> :: "'n pairpath"
    have "pstopped T \<theta> \<omega> T = \<omega> (min T (\<theta> \<omega>))"
      by (rule pstopped_apply) (use T0 in simp)
    also have "min T (\<theta> \<omega>) = \<theta> \<omega>" using thT[of \<omega>] by simp
    finally show "(outerp (fst (pstopped T \<theta> \<omega> T)) - snd (pstopped T \<theta> \<omega> T)) $ cc $ dd
        = (outerp (fst (\<omega> (\<theta> \<omega>))) - snd (\<omega> (\<theta> \<omega>))) $ cc $ dd" by simp
  qed
  have QT: "(\<integral>p'. (outerp (fst (p' T)) - snd (p' T)) $ cc $ dd \<partial>?Q)
      = (\<integral>\<omega>. (outerp (fst (\<omega> (\<theta> \<omega>))) - snd (\<omega> (\<theta> \<omega>))) $ cc $ dd \<partial>P)"
  proof -
    have "(\<integral>p'. (outerp (fst (p' T)) - snd (p' T)) $ cc $ dd \<partial>?Q)
        = (\<integral>\<omega>. (outerp (fst (pstopped T \<theta> \<omega> T)) - snd (pstopped T \<theta> \<omega> T)) $ cc $ dd \<partial>P)"
      unfolding pair_law_of_def by (rule integral_distr[OF m1 fm])
    then show ?thesis unfolding peq .
  qed
  show "integrable P (\<lambda>\<omega>. (outerp (fst (\<omega> (\<theta> \<omega>))) - snd (\<omega> (\<theta> \<omega>))) $ cc $ dd)"
  proof -
    have "integrable P (\<lambda>\<omega>.
        (outerp (fst (pstopped T \<theta> \<omega> T)) - snd (pstopped T \<theta> \<omega> T)) $ cc $ dd)"
      using iT' unfolding pair_law_of_def integrable_distr_eq[OF m1 fm] .
    then show ?thesis unfolding peq .
  qed
  show "(\<integral>\<omega>. (outerp (fst (\<omega> (\<theta> \<omega>))) - snd (\<omega> (\<theta> \<omega>))) $ cc $ dd \<partial>P)
      = outerp x $ cc $ dd"
    using const' start QT by simp
qed

lemma exit_class_Y_stopped_integrable:
  fixes P :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T0: "0 \<le> T" and L0: "0 \<le> L" and P: "P \<in> exit_class k L T x"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "integrable P (\<lambda>\<omega>. snd (\<omega> (\<theta> \<omega>)))"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  interpret PP: prob_space P by (rule exit_class_prob[OF P])
  have setsP: "sets P = sets ?B" by (rule exit_class_sets[OF P])
  have idm: "(\<lambda>\<omega> :: 'n pairpath. \<omega>) \<in> P \<rightarrow>\<^sub>M ?B"
    by (rule measurable_ident_sets[OF setsP])
  have thP: "\<theta> \<in> borel_measurable P"
    unfolding measurable_cong_sets[OF setsP refl] by (rule thM)
  have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (\<theta> \<omega>)) \<in> borel_measurable P"
    by (rule path_eval_at_measurable_time[OF T0 idm thP])
      (simp_all add: path_stopping_time_nonneg[OF st] path_stopping_time_le[OF st])
  have sm: "(snd :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n^'n) \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  have m: "(\<lambda>\<omega>. snd (\<omega> (\<theta> \<omega>))) \<in> borel_measurable P"
    by (rule measurable_compose[OF ev sm])
  have bd: "AE \<omega> in P. norm (snd (\<omega> (\<theta> \<omega>))) \<le> real CARD('n) * L * T"
    using exit_class_Y_bounded_ae[OF T0 L0 P]
    by (rule eventually_mono)
      (use path_stopping_time_nonneg[OF st] path_stopping_time_le[OF st] in auto)
  show ?thesis by (rule PP.integrable_const_bound[OF bd m])
qed

section \<open>The averaged covariation at a stopping time\<close>

text \<open>The weighted analogue of @{thm [source] exit_class_Y_mean_sconstraint}:
  \<open>E[Y\<^sub>\<theta>] / E[\<theta>]\<close> lies in the constraint set.  Pathwise, \<open>(1/\<theta>) Y\<^sub>\<theta>\<close> is in
  the set (the diffquot clause at \<open>(0, \<theta>]\<close>); every defining condition is a
  linear inequality in the matrix, so it integrates against the weight
  \<open>\<theta>\<close> and divides by \<open>E[\<theta>] > 0\<close>.\<close>

theorem exit_class_Y_stopped_mean_sconstraint:
  fixes P :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T: "0 < T" and L0: "0 \<le> L" and P: "P \<in> exit_class k L T x"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and pos: "AE \<omega> in P. 0 < \<theta> \<omega>"
  shows "(1 / (\<integral>\<omega>. \<theta> \<omega> \<partial>P)) *\<^sub>R (\<integral>\<omega>. snd (\<omega> (\<theta> \<omega>)) \<partial>P) \<in> sconstraint k L"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?Y = "\<lambda>\<omega> :: 'n pairpath. snd (\<omega> (\<theta> \<omega>))"
  have T0: "0 \<le> T" using T by simp
  interpret PP: prob_space P by (rule exit_class_prob[OF P])
  have setsP: "sets P = sets ?B" by (rule exit_class_sets[OF P])
  have thP: "\<theta> \<in> borel_measurable P"
    unfolding measurable_cong_sets[OF setsP refl] by (rule thM)
  have th0: "0 \<le> \<theta> \<omega>" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF st])
  have thT: "\<theta> \<omega> \<le> T" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_le[OF st])
  have ith: "integrable P \<theta>"
    by (rule PP.integrable_const_bound[of _ T])
      (auto simp: thP th0 thT)
  define et where "et = (\<integral>\<omega>. \<theta> \<omega> \<partial>P)"
  have et0: "0 < et"
    unfolding et_def
    by (rule integral_pos_of_AE_pos[OF PP.prob_space_axioms ith pos])
  have iY: "integrable P ?Y"
    by (rule exit_class_Y_stopped_integrable[OF T0 L0 P st thM])
  define EY where "EY = (\<integral>\<omega>. ?Y \<omega> \<partial>P)"
  define b where "b = (1 / et) *\<^sub>R EY"
  have stc: "AE \<omega> in P. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    using P unfolding exit_class_def by blast
  have dq: "AE \<omega> in P. \<forall>s t'. 0 \<le> s \<longrightarrow> s < t' \<longrightarrow> t' \<le> T \<longrightarrow>
      (1 / (t' - s)) *\<^sub>R (snd (\<omega> t') - snd (\<omega> s)) \<in> sconstraint k L"
    using P unfolding exit_class_def by blast
  have mem: "AE \<omega> in P. (1 / \<theta> \<omega>) *\<^sub>R ?Y \<omega> \<in> sconstraint k L \<and> 0 < \<theta> \<omega>"
    using stc dq pos
  proof eventually_elim
    case (elim \<omega>)
    have "(1 / (\<theta> \<omega> - 0)) *\<^sub>R (snd (\<omega> (\<theta> \<omega>)) - snd (\<omega> 0)) \<in> sconstraint k L"
      using elim thT[of \<omega>] by blast
    then show ?case using elim by simp
  qed
  \<comment> \<open>the four weighted pathwise facts\<close>
  have memQ: "AE \<omega> in P. \<forall>z :: real^'n.
      0 \<le> z \<bullet> (?Y \<omega> *v z) \<and> z \<bullet> (?Y \<omega> *v z) \<le> \<theta> \<omega> * (L * (z \<bullet> z))"
    using mem
  proof (rule eventually_mono)
    fix \<omega> :: "'n pairpath"
    assume h: "(1 / \<theta> \<omega>) *\<^sub>R ?Y \<omega> \<in> sconstraint k L \<and> 0 < \<theta> \<omega>"
    then have hp: "psd ((1 / \<theta> \<omega>) *\<^sub>R ?Y \<omega>)"
      and hu: "eigen_ub ((1 / \<theta> \<omega>) *\<^sub>R ?Y \<omega>) L"
      unfolding sconstraint_def Pi_constraint_def by auto
    have t0: "0 < \<theta> \<omega>" using h by simp
    show "\<forall>z :: real^'n.
        0 \<le> z \<bullet> (?Y \<omega> *v z) \<and> z \<bullet> (?Y \<omega> *v z) \<le> \<theta> \<omega> * (L * (z \<bullet> z))"
    proof
      fix z :: "real^'n"
      have e: "z \<bullet> (((1 / \<theta> \<omega>) *\<^sub>R ?Y \<omega>) *v z) = (1 / \<theta> \<omega>) * (z \<bullet> (?Y \<omega> *v z))"
        by (simp add: scaleR_matrix_vector)
      have lo: "0 \<le> (1 / \<theta> \<omega>) * (z \<bullet> (?Y \<omega> *v z))"
        using hp unfolding psd_def e[symmetric] by blast
      have hi: "(1 / \<theta> \<omega>) * (z \<bullet> (?Y \<omega> *v z)) \<le> L * (z \<bullet> z)"
        using hu unfolding eigen_ub_def e[symmetric] by blast
      have lo': "0 \<le> z \<bullet> (?Y \<omega> *v z)"
      proof -
        have "0 \<le> \<theta> \<omega> * ((1 / \<theta> \<omega>) * (z \<bullet> (?Y \<omega> *v z)))"
          by (rule mult_nonneg_nonneg[OF less_imp_le[OF t0] lo])
        then show ?thesis using t0 by (simp add: field_simps)
      qed
      have hi': "z \<bullet> (?Y \<omega> *v z) \<le> \<theta> \<omega> * (L * (z \<bullet> z))"
        using hi t0 by (simp add: field_simps)
      from lo' hi' show "0 \<le> z \<bullet> (?Y \<omega> *v z)
          \<and> z \<bullet> (?Y \<omega> *v z) \<le> \<theta> \<omega> * (L * (z \<bullet> z))" by blast
    qed
  qed
  have memT: "AE \<omega> in P. transpose (?Y \<omega>) = ?Y \<omega>"
    using mem
  proof (rule eventually_mono)
    fix \<omega> :: "'n pairpath"
    assume h: "(1 / \<theta> \<omega>) *\<^sub>R ?Y \<omega> \<in> sconstraint k L \<and> 0 < \<theta> \<omega>"
    then have tr2: "transpose ((1 / \<theta> \<omega>) *\<^sub>R ?Y \<omega>) = (1 / \<theta> \<omega>) *\<^sub>R ?Y \<omega>"
      unfolding sconstraint_def Pi_constraint_def psd_def by auto
    have tr1: "transpose ((1 / \<theta> \<omega>) *\<^sub>R ?Y \<omega>)
        = (1 / \<theta> \<omega>) *\<^sub>R transpose (?Y \<omega>)"
      by (simp add: transpose_def vec_eq_iff)
    have eqs: "(1 / \<theta> \<omega>) *\<^sub>R transpose (?Y \<omega>) = (1 / \<theta> \<omega>) *\<^sub>R ?Y \<omega>"
      unfolding tr1[symmetric] by (rule tr2)
    have t0: "0 < \<theta> \<omega>" using h by simp
    have nz: "1 / \<theta> \<omega> \<noteq> 0" using t0 by simp
    have entry: "transpose (?Y \<omega>) $ i $ j = ?Y \<omega> $ i $ j" for i j
    proof -
      have "((1 / \<theta> \<omega>) *\<^sub>R transpose (?Y \<omega>)) $ i $ j
          = ((1 / \<theta> \<omega>) *\<^sub>R ?Y \<omega>) $ i $ j"
        by (rule arg_cong[where f = "\<lambda>A. A $ i $ j", OF eqs])
      then have "(1 / \<theta> \<omega>) * transpose (?Y \<omega>) $ i $ j
          = (1 / \<theta> \<omega>) * ?Y \<omega> $ i $ j"
        by simp
      then show ?thesis using mult_left_cancel[OF nz] by blast
    qed
    show "transpose (?Y \<omega>) = ?Y \<omega>" using entry by (simp add: vec_eq_iff)
  qed
  have memPi: "AE \<omega> in P. \<forall>m Pm. k < m \<longrightarrow> m \<le> CARD('n) \<longrightarrow>
      is_proj Pm \<longrightarrow> trace Pm = real m \<longrightarrow>
      real (m - k) * \<theta> \<omega> \<le> trace (?Y \<omega> ** Pm)"
    using mem
  proof (rule eventually_mono)
    fix \<omega> :: "'n pairpath"
    assume h: "(1 / \<theta> \<omega>) *\<^sub>R ?Y \<omega> \<in> sconstraint k L \<and> 0 < \<theta> \<omega>"
    then have hp: "psd ((1 / \<theta> \<omega>) *\<^sub>R ?Y \<omega>)"
      and hpi: "\<And>m. k < m \<Longrightarrow> m \<le> CARD('n) \<Longrightarrow>
          real (m - k) \<le> Pi_proj ((1 / \<theta> \<omega>) *\<^sub>R ?Y \<omega>) m"
      unfolding sconstraint_def Pi_constraint_def by auto
    have t0: "0 < \<theta> \<omega>" using h by simp
    show "\<forall>m Pm. k < m \<longrightarrow> m \<le> CARD('n) \<longrightarrow>
        is_proj Pm \<longrightarrow> trace Pm = real m \<longrightarrow>
        real (m - k) * \<theta> \<omega> \<le> trace (?Y \<omega> ** Pm)"
    proof (intro allI impI)
      fix m and Pm :: "real^'n^'n"
      assume m: "k < m" "m \<le> CARD('n)"
        and pj: "is_proj Pm" and tp: "trace Pm = real m"
      have "real (m - k) \<le> Pi_proj ((1 / \<theta> \<omega>) *\<^sub>R ?Y \<omega>) m"
        by (rule hpi[OF m])
      also have "\<dots> \<le> trace (((1 / \<theta> \<omega>) *\<^sub>R ?Y \<omega>) ** Pm)"
        by (rule Pi_proj_le[OF hp pj tp])
      also have "\<dots> = (1 / \<theta> \<omega>) * trace (?Y \<omega> ** Pm)"
        by (simp add: scaleR_matrix_mult trace_scaleR)
      finally have "real (m - k) \<le> (1 / \<theta> \<omega>) * trace (?Y \<omega> ** Pm)" .
      then show "real (m - k) * \<theta> \<omega> \<le> trace (?Y \<omega> ** Pm)"
        using t0 by (simp add: field_simps)
    qed
  qed
  \<comment> \<open>integrate the four facts\<close>
  have lin: "(\<integral>\<omega>. F (?Y \<omega>) \<partial>P) = F EY"
    if F: "bounded_linear (F :: real^'n^'n \<Rightarrow> real)" for F
    unfolding EY_def by (rule integral_of_bounded_linear[OF F iY])
  have linI: "integrable P (\<lambda>\<omega>. F (?Y \<omega>))"
    if F: "bounded_linear (F :: real^'n^'n \<Rightarrow> real)" for F
    by (rule integrable_bounded_linear[OF F iY])
  have qlo: "0 \<le> z \<bullet> (EY *v z)" for z :: "real^'n"
  proof -
    have "0 \<le> (\<integral>\<omega>. z \<bullet> (?Y \<omega> *v z) \<partial>P)"
      by (rule integral_nonneg_AE)
        (use memQ in \<open>auto elim: eventually_mono\<close>)
    then show ?thesis using lin[OF bounded_linear_quadform] by simp
  qed
  have qhi: "z \<bullet> (EY *v z) \<le> et * (L * (z \<bullet> z))" for z :: "real^'n"
  proof -
    have blc: "bounded_linear (\<lambda>r :: real. r * (L * (z \<bullet> z)))"
      unfolding linear_conv_bounded_linear[symmetric]
      by (intro linearI) (auto simp: algebra_simps)
    have "z \<bullet> (EY *v z) = (\<integral>\<omega>. z \<bullet> (?Y \<omega> *v z) \<partial>P)"
      using lin[OF bounded_linear_quadform] by simp
    also have "\<dots> \<le> (\<integral>\<omega>. \<theta> \<omega> * (L * (z \<bullet> z)) \<partial>P)"
      by (rule integral_mono_AE[OF linI[OF bounded_linear_quadform]
            integrable_bounded_linear[OF blc ith]])
        (use memQ in \<open>auto elim: eventually_mono\<close>)
    also have "\<dots> = (\<integral>\<omega>. \<theta> \<omega> \<partial>P) * (L * (z \<bullet> z))"
      by (rule integral_of_bounded_linear[OF blc ith])
    also have "\<dots> = et * (L * (z \<bullet> z))" by (simp add: et_def)
    finally show ?thesis .
  qed
  have trE: "transpose EY = EY"
  proof -
    have "transpose EY = (\<integral>\<omega>. transpose (?Y \<omega>) \<partial>P)"
      unfolding EY_def
      by (rule integral_of_bounded_linear[OF bounded_linear_transpose iY, symmetric])
    also have "\<dots> = (\<integral>\<omega>. ?Y \<omega> \<partial>P)"
    proof (rule integral_cong_AE[OF _ _ memT])
      show "(\<lambda>\<omega>. transpose (?Y \<omega>)) \<in> borel_measurable P"
        by (rule borel_measurable_integrable
            [OF integrable_bounded_linear[OF bounded_linear_transpose iY]])
      show "?Y \<in> borel_measurable P"
        by (rule borel_measurable_integrable[OF iY])
    qed
    finally show ?thesis by (simp add: EY_def)
  qed
  have piE: "real (m - k) * et \<le> trace (EY ** Pm)"
    if m: "k < m" "m \<le> CARD('n)" and pj: "is_proj Pm" and tp: "trace Pm = real m"
    for m and Pm :: "real^'n^'n"
  proof -
    have blc: "bounded_linear (\<lambda>r :: real. real (m - k) * r)"
      unfolding linear_conv_bounded_linear[symmetric]
      by (intro linearI) (auto simp: algebra_simps)
    have "real (m - k) * et = (\<integral>\<omega>. real (m - k) * \<theta> \<omega> \<partial>P)"
      using integral_of_bounded_linear[OF blc ith] by (simp add: et_def)
    also have "\<dots> \<le> (\<integral>\<omega>. trace (?Y \<omega> ** Pm) \<partial>P)"
      by (rule integral_mono_AE[OF integrable_bounded_linear[OF blc ith]
            linI[OF bounded_linear_trace_mult_right]])
        (use memPi m pj tp in \<open>auto elim: eventually_mono\<close>)
    also have "\<dots> = trace (EY ** Pm)"
      by (rule lin[OF bounded_linear_trace_mult_right])
    finally show ?thesis .
  qed
  \<comment> \<open>assemble the membership of \<open>b\<close>\<close>
  have psdb: "psd b"
  proof -
    have "transpose b = b"
      unfolding b_def using trE by (simp add: transpose_def vec_eq_iff)
    moreover have "0 \<le> z \<bullet> (b *v z)" for z :: "real^'n"
    proof -
      have "z \<bullet> (b *v z) = (1 / et) * (z \<bullet> (EY *v z))"
        unfolding b_def by (simp add: scaleR_matrix_vector)
      then show ?thesis using qlo[of z] et0 by simp
    qed
    ultimately show ?thesis unfolding psd_def by blast
  qed
  have eubb: "eigen_ub b L"
  proof -
    have "z \<bullet> (b *v z) \<le> L * (z \<bullet> z)" for z :: "real^'n"
    proof -
      have "z \<bullet> (b *v z) = (1 / et) * (z \<bullet> (EY *v z))"
        unfolding b_def by (simp add: scaleR_matrix_vector)
      also have "\<dots> \<le> (1 / et) * (et * (L * (z \<bullet> z)))"
        using qhi[of z] et0 by (intro mult_left_mono) auto
      also have "\<dots> = L * (z \<bullet> z)" using et0 by simp
      finally show ?thesis .
    qed
    then show ?thesis unfolding eigen_ub_def by blast
  qed
  have pib: "real (m - k) \<le> Pi_proj b m"
    if m: "k < m" "m \<le> CARD('n)" for m
  proof (rule Pi_proj_ge[OF m(2)])
    fix Pm :: "real^'n^'n"
    assume pj: "is_proj Pm" and tp: "trace Pm = real m"
    have e1: "trace (b ** Pm) = (1 / et) * trace (EY ** Pm)"
      unfolding b_def by (simp add: scaleR_matrix_mult trace_scaleR)
    then have e2: "et * trace (b ** Pm) = trace (EY ** Pm)"
      using et0 by (simp add: field_simps)
    have "et * real (m - k) \<le> et * trace (b ** Pm)"
      using piE[OF m pj tp] e2 by (simp add: ac_simps)
    then show "real (m - k) \<le> trace (b ** Pm)"
      using et0 by (simp add: mult_le_cancel_left)
  qed
  have pic: "b \<in> Pi_constraint k"
    unfolding Pi_constraint_def
  proof (intro CollectI conjI allI impI)
    show "psd b" by (rule psdb)
  next
    fix m assume "k < m" and "m \<le> CARD('n)"
    then show "real (m - k) \<le> Pi_proj b m" by (rule pib)
  qed
  have "b \<in> sconstraint k L"
    unfolding sconstraint_def using pic eubb by blast
  then show ?thesis unfolding b_def EY_def et_def .
qed

section \<open>The localised subsolution inequality\<close>

text \<open>The DPP at the ball exit time, the touching used only on the closed
  ball, and the exact quadratic expansion at the stopping time give the
  stochastic localisation of the subsolution inequality, with no
  remainder estimate: for a quadratic the expansion is exact at any
  bounded stopping time.\<close>

theorem exit_val_subsol_quadratic_ball:
  fixes K :: "(real^'n::finite) set" and x q :: "real^'n" and M :: "real^'n^'n"
  assumes T: "0 < T" and L1: "1 \<le> L" and Kc: "closed K" and e0: "0 < \<epsilon>"
    and touch: "\<And>z. dist z x \<le> \<epsilon> \<Longrightarrow>
        enn2real (exit_val k L T K z)
          \<le> enn2real (exit_val k L T K x) + q \<bullet> (z - x)
            + ((z - x) \<bullet> (M *v (z - x))) / 2"
  obtains b where "b \<in> sconstraint k L" and "- trace (M ** b) / 2 \<le> 1"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have T0: "0 \<le> T" using T by simp
  have L0: "0 \<le> L" using L1 by simp
  define u where "u = (\<lambda>z :: real^'n. enn2real (exit_val k L T K z))"
  obtain P where P: "P \<in> exit_class k L T x"
    and Pv: "ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))
        = exit_val k L T K x"
    using exit_val_attained[OF T L1 Kc] by blast
  interpret PP: prob_space P by (rule exit_class_prob[OF P])
  have setsP: "sets P = sets ?B" by (rule exit_class_sets[OF P])
  let ?th = "pball_exit T x \<epsilon>"
  let ?Xf = "\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (?th \<omega>))"
  let ?Yf = "\<lambda>\<omega> :: 'n pairpath. snd (\<omega> (?th \<omega>))"
  have st: "path_stopping_time T ?th"
    by (rule pball_exit_path_stopping_time[OF T0])
  have thM: "?th \<in> borel_measurable ?B"
    by (rule pball_exit_measurable[OF T0])
  have thP: "?th \<in> borel_measurable P"
    unfolding measurable_cong_sets[OF setsP refl] by (rule thM)
  have th0: "0 \<le> ?th \<omega>" for \<omega> :: "'n pairpath"
    by (rule pball_exit_nonneg[OF T0])
  have thT: "?th \<omega> \<le> T" for \<omega> :: "'n pairpath"
    by (rule pball_exit_le[OF T0])
  \<comment> \<open>the almost-sure facts\<close>
  have cAE: "AE \<omega> in P. u x \<le> pexit T K (\<lambda>t. fst (\<omega> t))"
  proof (rule eventually_mono
      [OF ess_inf_time_AE[of P "\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))"]])
    fix \<omega> :: "'n pairpath"
    assume "ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))
        \<le> ennreal (pexit T K (\<lambda>t. fst (\<omega> t)))"
    then have le: "exit_val k L T K x \<le> ennreal (pexit T K (\<lambda>t. fst (\<omega> t)))"
      using Pv by simp
    have "enn2real (exit_val k L T K x)
        \<le> enn2real (ennreal (pexit T K (\<lambda>t. fst (\<omega> t))))"
      by (rule enn2real_mono[OF le ennreal_less_top])
    then show "u x \<le> pexit T K (\<lambda>t. fst (\<omega> t))"
      unfolding u_def
      using pexit_nonneg[OF T0, of K "\<lambda>t. fst (\<omega> t)"] by simp
  qed
  have dpp: "AE \<omega> in P. u x \<le> ?th \<omega> + u (?Xf \<omega>)"
  proof (rule eventually_mono[OF exit_val_cond_ball
      [OF T0 L1 Kc P cAE, where x = x and \<epsilon> = \<epsilon>]])
    fix \<omega> :: "'n pairpath"
    assume "u x \<le> ?th \<omega> + min (enn2real (exit_val k L T K (?Xf \<omega>))) (T - ?th \<omega>)"
    moreover have "min (enn2real (exit_val k L T K (?Xf \<omega>))) (T - ?th \<omega>)
        \<le> enn2real (exit_val k L T K (?Xf \<omega>))"
      by (rule min.cobounded1)
    ultimately show "u x \<le> ?th \<omega> + u (?Xf \<omega>)" unfolding u_def by linarith
  qed
  have stc: "AE \<omega> in P. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    using P unfolding exit_class_def by blast
  have cwAE: "AE \<omega> in P. continuous_on {0..T} (\<lambda>t. fst (\<omega> t))"
  proof -
    have "AE \<omega> in P. \<omega> \<in> space P" by (rule AE_space)
    then show ?thesis
    proof (rule eventually_mono)
      fix \<omega> :: "'n pairpath" assume "\<omega> \<in> space P"
      then show "continuous_on {0..T} (\<lambda>t. fst (\<omega> t))"
        by (rule path_sets_fst_continuous[OF setsP])
    qed
  qed
  have posAE: "AE \<omega> in P. 0 < ?th \<omega>"
    using stc cwAE
  proof eventually_elim
    case (elim \<omega>)
    have "dist (fst (\<omega> 0)) x < \<epsilon>" using elim e0 by simp
    then show ?case using elim by (intro pball_exit_pos[OF T]) auto
  qed
  have inball: "AE \<omega> in P. dist (?Xf \<omega>) x \<le> \<epsilon>"
    using stc cwAE
  proof eventually_elim
    case (elim \<omega>)
    have "dist (fst (\<omega> 0)) x < \<epsilon>" using elim e0 by simp
    then show ?case
      using elim by (intro pball_exit_stays_cball[OF T0 _ _ th0 order.refl]) auto
  qed
  have key: "AE \<omega> in P. 0 \<le> ?th \<omega> + q \<bullet> (?Xf \<omega> - x)
      + ((?Xf \<omega> - x) \<bullet> (M *v (?Xf \<omega> - x))) / 2"
    using dpp inball
  proof eventually_elim
    case (elim \<omega>)
    have "u (?Xf \<omega>) \<le> u x + q \<bullet> (?Xf \<omega> - x)
        + ((?Xf \<omega> - x) \<bullet> (M *v (?Xf \<omega> - x))) / 2"
      unfolding u_def by (rule touch[OF elim(2)])
    with elim(1) show ?case by linarith
  qed
  \<comment> \<open>the integrable pieces and their means\<close>
  have ith: "integrable P ?th"
    by (rule PP.integrable_const_bound[of _ T])
      (auto simp: thP th0 thT)
  define et where "et = (\<integral>\<omega>. ?th \<omega> \<partial>P)"
  have et0: "0 < et"
    unfolding et_def
    by (rule integral_pos_of_AE_pos[OF PP.prob_space_axioms ith posAE])
  have iXc: "integrable P (\<lambda>\<omega>. ?Xf \<omega> $ c)" for c
    using exit_class_X_entry_stopped(1)[OF T L0 P st thM] .
  have EXc: "(\<integral>\<omega>. ?Xf \<omega> $ c \<partial>P) = x $ c" for c
    using exit_class_X_entry_stopped(2)[OF T L0 P st thM] .
  have iCc: "integrable P (\<lambda>\<omega>. (outerp (?Xf \<omega>) - ?Yf \<omega>) $ cc $ dd)" for cc dd
    using exit_class_comp_entry_stopped(1)[OF T L0 P st thM] .
  have ECc: "(\<integral>\<omega>. (outerp (?Xf \<omega>) - ?Yf \<omega>) $ cc $ dd \<partial>P) = outerp x $ cc $ dd"
    for cc dd
    using exit_class_comp_entry_stopped(2)[OF T L0 P st thM] .
  have iY: "integrable P ?Yf"
    by (rule exit_class_Y_stopped_integrable[OF T0 L0 P st thM])
  define EY where "EY = (\<integral>\<omega>. ?Yf \<omega> \<partial>P)"
  have iX: "integrable P ?Xf"
  proof -
    have "integrable P (\<lambda>\<omega>. \<chi> c. ?Xf \<omega> $ c)"
      by (intro integrable_vec_components iXc)
    then show ?thesis by simp
  qed
  have EX: "(\<integral>\<omega>. ?Xf \<omega> \<partial>P) = x"
  proof -
    have "(\<integral>\<omega>. ?Xf \<omega> \<partial>P) $ c = x $ c" for c
      using integral_of_bounded_linear[OF bounded_linear_vec_nth iX] EXc[of c]
      by simp
    then show ?thesis by (simp add: vec_eq_iff)
  qed
  \<comment> \<open>means of the four scalar pieces\<close>
  have ig1: "integrable P (\<lambda>\<omega>. q \<bullet> ?Xf \<omega>)"
    by (rule integrable_bounded_linear[OF bounded_linear_inner_right iX])
  have Eg1: "(\<integral>\<omega>. q \<bullet> ?Xf \<omega> \<partial>P) = q \<bullet> x"
    using integral_of_bounded_linear[OF bounded_linear_inner_right iX] EX by simp
  have blM: "bounded_linear (\<lambda>w :: real^'n. M *v w)"
    unfolding linear_conv_bounded_linear[symmetric]
    by (rule matrix_vector_mul_linear)
  have ig2: "integrable P (\<lambda>\<omega>. x \<bullet> (M *v ?Xf \<omega>))"
    by (rule integrable_bounded_linear[OF bounded_linear_compose
          [OF bounded_linear_inner_right blM] iX])
  have Eg2: "(\<integral>\<omega>. x \<bullet> (M *v ?Xf \<omega>) \<partial>P) = x \<bullet> (M *v x)"
    using integral_of_bounded_linear[OF bounded_linear_compose
        [OF bounded_linear_inner_right blM] iX] EX by simp
  have ig3: "integrable P (\<lambda>\<omega>. ?Xf \<omega> \<bullet> (M *v x))"
    by (rule integrable_bounded_linear[OF bounded_linear_inner_left iX])
  have Eg3: "(\<integral>\<omega>. ?Xf \<omega> \<bullet> (M *v x) \<partial>P) = x \<bullet> (M *v x)"
    using integral_of_bounded_linear[OF bounded_linear_inner_left iX] EX by simp
  \<comment> \<open>the quadratic term, through the compensated entries\<close>
  have icomp: "integrable P (\<lambda>\<omega>. trace (M ** (outerp (?Xf \<omega>) - ?Yf \<omega>)))"
    unfolding trace_mult_sum
    by (intro Bochner_Integration.integrable_sum integrable_cmult iCc)
  have Ecomp: "(\<integral>\<omega>. trace (M ** (outerp (?Xf \<omega>) - ?Yf \<omega>)) \<partial>P)
      = trace (M ** outerp x)"
  proof -
    have "(\<integral>\<omega>. (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. M $ i $ j * (outerp (?Xf \<omega>) - ?Yf \<omega>) $ j $ i) \<partial>P)
        = (\<Sum>i\<in>UNIV. (\<integral>\<omega>. (\<Sum>j\<in>UNIV. M $ i $ j * (outerp (?Xf \<omega>) - ?Yf \<omega>) $ j $ i) \<partial>P))"
      by (rule Bochner_Integration.integral_sum)
        (intro Bochner_Integration.integrable_sum integrable_cmult iCc)
    also have "\<dots> = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV.
        (\<integral>\<omega>. M $ i $ j * (outerp (?Xf \<omega>) - ?Yf \<omega>) $ j $ i \<partial>P))"
      by (intro sum.cong refl Bochner_Integration.integral_sum
          integrable_cmult iCc)
    also have "\<dots> = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. M $ i $ j * outerp x $ j $ i)"
    proof -
      have iCc': "integrable P (\<lambda>\<omega>. outerp (?Xf \<omega>) $ cc $ dd - ?Yf \<omega> $ cc $ dd)"
        for cc dd
      proof -
        have e: "(\<lambda>\<omega>. outerp (?Xf \<omega>) $ cc $ dd - ?Yf \<omega> $ cc $ dd)
            = (\<lambda>\<omega>. (outerp (?Xf \<omega>) - ?Yf \<omega>) $ cc $ dd)" by simp
        show ?thesis unfolding e by (rule iCc)
      qed
      have ECc': "(\<integral>\<omega>. outerp (?Xf \<omega>) $ cc $ dd - ?Yf \<omega> $ cc $ dd \<partial>P)
          = outerp x $ cc $ dd" for cc dd
      proof -
        have e: "(\<lambda>\<omega>. outerp (?Xf \<omega>) $ cc $ dd - ?Yf \<omega> $ cc $ dd)
            = (\<lambda>\<omega>. (outerp (?Xf \<omega>) - ?Yf \<omega>) $ cc $ dd)" by simp
        show ?thesis unfolding e by (rule ECc)
      qed
      show ?thesis
        by (intro sum.cong refl)
          (simp add: integral_cmult[OF iCc'] ECc')
    qed    finally show ?thesis unfolding trace_mult_sum .
  qed
  have itrY: "integrable P (\<lambda>\<omega>. trace (M ** ?Yf \<omega>))"
    by (rule integrable_bounded_linear[OF bounded_linear_trace_mult_left iY])
  have EtrY: "(\<integral>\<omega>. trace (M ** ?Yf \<omega>) \<partial>P) = trace (M ** EY)"
    unfolding EY_def
    by (rule integral_of_bounded_linear[OF bounded_linear_trace_mult_left iY])
  have g4eq: "(\<lambda>\<omega>. ?Xf \<omega> \<bullet> (M *v ?Xf \<omega>))
      = (\<lambda>\<omega>. trace (M ** (outerp (?Xf \<omega>) - ?Yf \<omega>)) + trace (M ** ?Yf \<omega>))"
    by (rule ext) (simp add: trace_mult_diff trace_mult_outerp)
  have ig4: "integrable P (\<lambda>\<omega>. ?Xf \<omega> \<bullet> (M *v ?Xf \<omega>))"
    unfolding g4eq by (intro Bochner_Integration.integrable_add icomp itrY)
  have Eg4: "(\<integral>\<omega>. ?Xf \<omega> \<bullet> (M *v ?Xf \<omega>) \<partial>P)
      = x \<bullet> (M *v x) + trace (M ** EY)"
    unfolding g4eq
    using Bochner_Integration.integral_add[OF icomp itrY] Ecomp EtrY
    by (simp add: trace_mult_outerp)
  \<comment> \<open>assemble the integrand\<close>
  define F where "F = (\<lambda>\<omega>. ?th \<omega> + q \<bullet> (?Xf \<omega> - x)
      + ((?Xf \<omega> - x) \<bullet> (M *v (?Xf \<omega> - x))) / 2)"
  have Fexp: "F = (\<lambda>\<omega>. ?th \<omega> + (q \<bullet> ?Xf \<omega> - q \<bullet> x)
      + (?Xf \<omega> \<bullet> (M *v ?Xf \<omega>) - x \<bullet> (M *v ?Xf \<omega>) - ?Xf \<omega> \<bullet> (M *v x)
         + x \<bullet> (M *v x)) / 2)"
  proof (rule ext)
    fix \<omega> :: "'n pairpath"
    have lind: "M *v (a - b) = M *v a - M *v b" for a b :: "real^'n"
      using linear_diff[OF matrix_vector_mul_linear, of M] by simp
    show "F \<omega> = ?th \<omega> + (q \<bullet> ?Xf \<omega> - q \<bullet> x)
        + (?Xf \<omega> \<bullet> (M *v ?Xf \<omega>) - x \<bullet> (M *v ?Xf \<omega>) - ?Xf \<omega> \<bullet> (M *v x)
           + x \<bullet> (M *v x)) / 2"
      unfolding F_def
      by (simp add: lind algebra_simps)
  qed
  have iq2: "integrable P (\<lambda>\<omega>. ?Xf \<omega> \<bullet> (M *v ?Xf \<omega>) - x \<bullet> (M *v ?Xf \<omega>)
      - ?Xf \<omega> \<bullet> (M *v x) + x \<bullet> (M *v x))"
    by (intro Bochner_Integration.integrable_add
        Bochner_Integration.integrable_diff ig4 ig2 ig3 PP.integrable_const)
  have bl2: "bounded_linear (\<lambda>r :: real. r / 2)"
    unfolding linear_conv_bounded_linear[symmetric]
    by (intro linearI) (simp_all add: field_simps)
  have ihalf: "integrable P (\<lambda>\<omega>. (?Xf \<omega> \<bullet> (M *v ?Xf \<omega>) - x \<bullet> (M *v ?Xf \<omega>)
      - ?Xf \<omega> \<bullet> (M *v x) + x \<bullet> (M *v x)) / 2)"
    by (rule integrable_bounded_linear[OF bl2 iq2])
  have EF: "(\<integral>\<omega>. F \<omega> \<partial>P) = et + trace (M ** EY) / 2"
  proof -
    have Eq2: "(\<integral>\<omega>. ?Xf \<omega> \<bullet> (M *v ?Xf \<omega>) - x \<bullet> (M *v ?Xf \<omega>)
        - ?Xf \<omega> \<bullet> (M *v x) + x \<bullet> (M *v x) \<partial>P) = trace (M ** EY)"
      using Bochner_Integration.integral_add[OF
          Bochner_Integration.integrable_diff[OF
            Bochner_Integration.integrable_diff[OF ig4 ig2] ig3]
          PP.integrable_const]
        Bochner_Integration.integral_diff[OF
          Bochner_Integration.integrable_diff[OF ig4 ig2] ig3]
        Bochner_Integration.integral_diff[OF ig4 ig2]
        Eg4 Eg2 Eg3 by (simp add: PP.prob_space)
    have E1: "(\<integral>\<omega>. q \<bullet> ?Xf \<omega> - q \<bullet> x \<partial>P) = 0"
      using Bochner_Integration.integral_diff[OF ig1 PP.integrable_const]
        Eg1 by (simp add: PP.prob_space)
    have iA: "integrable P (\<lambda>\<omega>. ?th \<omega> + (q \<bullet> ?Xf \<omega> - q \<bullet> x))"
      by (intro Bochner_Integration.integrable_add
          Bochner_Integration.integrable_diff ith ig1 PP.integrable_const)
    have "(\<integral>\<omega>. F \<omega> \<partial>P)
        = (\<integral>\<omega>. ?th \<omega> + (q \<bullet> ?Xf \<omega> - q \<bullet> x) \<partial>P)
          + (\<integral>\<omega>. (?Xf \<omega> \<bullet> (M *v ?Xf \<omega>) - x \<bullet> (M *v ?Xf \<omega>)
             - ?Xf \<omega> \<bullet> (M *v x) + x \<bullet> (M *v x)) / 2 \<partial>P)"
      unfolding Fexp by (rule Bochner_Integration.integral_add[OF iA ihalf])
    also have "(\<integral>\<omega>. ?th \<omega> + (q \<bullet> ?Xf \<omega> - q \<bullet> x) \<partial>P) = et"
      using Bochner_Integration.integral_add[OF ith
          Bochner_Integration.integrable_diff[OF ig1 PP.integrable_const]]
        E1 by (simp add: et_def)
    also have "(\<integral>\<omega>. (?Xf \<omega> \<bullet> (M *v ?Xf \<omega>) - x \<bullet> (M *v ?Xf \<omega>)
        - ?Xf \<omega> \<bullet> (M *v x) + x \<bullet> (M *v x)) / 2 \<partial>P) = trace (M ** EY) / 2"
    proof -
      have "(\<integral>\<omega>. (?Xf \<omega> \<bullet> (M *v ?Xf \<omega>) - x \<bullet> (M *v ?Xf \<omega>)
          - ?Xf \<omega> \<bullet> (M *v x) + x \<bullet> (M *v x)) / 2 \<partial>P)
          = (\<integral>\<omega>. ?Xf \<omega> \<bullet> (M *v ?Xf \<omega>) - x \<bullet> (M *v ?Xf \<omega>)
            - ?Xf \<omega> \<bullet> (M *v x) + x \<bullet> (M *v x) \<partial>P) / 2"
        by (rule integral_of_bounded_linear[OF bl2 iq2])
      then show ?thesis using Eq2 by simp
    qed
    finally show ?thesis .
  qed
  have "0 \<le> (\<integral>\<omega>. F \<omega> \<partial>P)"
    by (rule integral_nonneg_AE) (use key in \<open>auto simp: F_def elim: eventually_mono\<close>)
  then have ge: "0 \<le> et + trace (M ** EY) / 2" unfolding EF .
  \<comment> \<open>the averaged direction\<close>
  have bmem: "(1 / et) *\<^sub>R EY \<in> sconstraint k L"
    unfolding et_def EY_def
    by (rule exit_class_Y_stopped_mean_sconstraint[OF T L0 P st thM posAE])
  have EYb: "EY = et *\<^sub>R ((1 / et) *\<^sub>R EY)"
    using et0 by simp
  have trb: "trace (M ** EY) = et * trace (M ** ((1 / et) *\<^sub>R EY))"
    by (subst EYb) (rule trace_mult_scaleR)
  have "0 \<le> et * (1 + trace (M ** ((1 / et) *\<^sub>R EY)) / 2)"
    using ge trb by (simp add: field_simps)
  then have "0 \<le> 1 + trace (M ** ((1 / et) *\<^sub>R EY)) / 2"
    using et0 by (simp add: zero_le_mult_iff)
  then have w: "- trace (M ** ((1 / et) *\<^sub>R EY)) / 2 \<le> 1" by simp
  show ?thesis by (rule that[OF bmem w])
qed

section \<open>From quadratics to arbitrary test functions\<close>

text \<open>The classical reduction: a \<open>C\<^sup>1\<close> function whose gradient is
  differentiable at \<open>x\<close> is dominated, near \<open>x\<close>, by its second-order
  expansion with the Hessian bumped by \<open>\<delta>\<close>.  One-dimensional along each
  ray: the difference has nonpositive derivative, by the \<open>\<epsilon>\<close>-\<open>\<delta>\<close> form of
  differentiability of the gradient with \<open>\<epsilon> := \<delta>/2\<close>.\<close>

lemma sconstraint_trace_le:
  fixes b :: "real^'n::finite^'n"
  assumes L0: "0 \<le> L" and b: "b \<in> sconstraint k L"
  shows "trace b \<le> real CARD('n) * (real CARD('n) * L)"
proof -
  have entry: "b $ i $ i \<le> real CARD('n) * L" for i
  proof -
    have "b $ i $ i \<le> \<bar>b $ i $ i\<bar>" by simp
    also have "\<bar>b $ i $ i\<bar> = norm (b $ i $ i)" by simp
    also have "\<dots> \<le> norm (b $ i)"
      by (rule Finite_Cartesian_Product.norm_nth_le)
    also have "\<dots> \<le> norm b"
      by (rule Finite_Cartesian_Product.norm_nth_le)
    also have "\<dots> \<le> real CARD('n) * L"
      by (rule sconstraint_norm_le[OF L0 b])
    finally show ?thesis .
  qed
  have "trace b = (\<Sum>i\<in>UNIV. b $ i $ i)" by (simp add: trace_def)
  also have "\<dots> \<le> (\<Sum>i\<in>(UNIV :: 'n set). real CARD('n) * L)"
    by (rule sum_mono) (rule entry)
  also have "\<dots> = real CARD('n) * (real CARD('n) * L)"
    by simp
  finally show ?thesis .
qed

section \<open>Positive semidefinite forms kill their null directions\<close>

text \<open>The Cauchy--Schwarz inequality for a psd form, in the shape needed
  later: if the form vanishes at \<open>q\<close> then \<open>q\<close> is in the kernel.\<close>

lemma psd_kernel_eq:
  fixes a :: "real^'n::finite^'n" and q :: "real^'n"
  assumes a: "psd a" and z: "q \<bullet> (a *v q) = 0"
  shows "a *v q = 0"
proof -
  have sym: "transpose a = a" using a by (simp add: psd_def)
  have nn: "0 \<le> y \<bullet> (a *v y)" for y using a by (simp add: psd_def)
  have cross: "z \<bullet> (a *v q) = 0" for z
  proof (rule ccontr)
    assume ne: "z \<bullet> (a *v q) \<noteq> 0"
    define Bc where "Bc = z \<bullet> (a *v q)"
    define Ac where "Ac = z \<bullet> (a *v z)"
    have Bc0: "Bc \<noteq> 0" using ne by (simp add: Bc_def)
    have Ac0: "0 \<le> Ac" by (simp add: Ac_def nn)
    have qa: "q \<bullet> (a *v z) = Bc"
    proof -
      have "q \<bullet> (a *v z) = (transpose a *v q) \<bullet> z"
        by (rule inner_transpose_matrix)
      also have "\<dots> = (a *v q) \<bullet> z" using sym by simp
      also have "\<dots> = z \<bullet> (a *v q)" by (rule inner_commute)
      finally show ?thesis by (simp add: Bc_def)
    qed
    have expand: "(q + r *\<^sub>R z) \<bullet> (a *v (q + r *\<^sub>R z))
        = 2 * r * Bc + r\<^sup>2 * Ac" for r
    proof -
      have lin: "a *v (q + r *\<^sub>R z) = a *v q + r *\<^sub>R (a *v z)"
        by (simp add: matrix_vector_mult_def vec_eq_iff sum.distrib
            sum_distrib_left algebra_simps)
      show ?thesis
        unfolding lin
        by (simp add: z qa Bc_def Ac_def power2_eq_square
            algebra_simps)
    qed
    show False
    proof (cases "Ac = 0")
      case True
      have "0 \<le> 2 * (- Bc) * Bc + (- Bc)\<^sup>2 * Ac"
        using nn[of "q + (- Bc) *\<^sub>R z"] expand[of "- Bc"] by simp
      then have "Bc * Bc \<le> 0" using True by (simp add: power2_eq_square)
      moreover have "0 < Bc * Bc"
        using Bc0 by (cases "0 < Bc") (auto intro: mult_pos_pos mult_neg_neg
            simp: not_less le_less)
      ultimately show False by linarith
    next
      case False
      then have AcP: "0 < Ac" using Ac0 by simp
      define r where "r = - Bc / Ac"
      have "0 \<le> 2 * r * Bc + r\<^sup>2 * Ac"
        using nn[of "q + r *\<^sub>R z"] expand[of r] by simp
      also have "2 * r * Bc + r\<^sup>2 * Ac = - (Bc\<^sup>2 / Ac)"
        unfolding r_def using AcP by (simp add: power2_eq_square field_simps)
      finally have h: "Bc\<^sup>2 / Ac \<le> 0" by simp
      have "0 < Bc * Bc"
        using Bc0 by (cases "0 < Bc") (auto intro: mult_pos_pos mult_neg_neg
            simp: not_less le_less)
      then have "0 < Bc\<^sup>2 / Ac"
        using AcP by (simp add: power2_eq_square)
      with h show False by linarith
    qed
  qed
  have "(a *v q) \<bullet> (a *v q) = 0" using cross[of "a *v q"] by simp
  then show ?thesis by simp
qed

section \<open>Sums of outer products: the toolkit\<close>

text \<open>\<open>onormal_subset\<close> lives in
  @{theory Symmetric_Matrix_Spectra.Orthonormal_Families}.\<close>

lemma matvec_sum_outer:
  fixes S :: "(real^'n::finite) set" and c :: "real^'n \<Rightarrow> real"
  assumes finS: "finite S"
  shows "(\<Sum>u\<in>S. c u *\<^sub>R outer_prod u u) *v z = (\<Sum>u\<in>S. (c u * (u \<bullet> z)) *\<^sub>R u)"
proof -
  have "(\<Sum>u\<in>S. c u *\<^sub>R outer_prod u u) *v z
      = (\<Sum>u\<in>S. (c u *\<^sub>R outer_prod u u) *v z)"
    by (rule matrix_vector_mult_sum)
  also have "\<dots> = (\<Sum>u\<in>S. (c u * (u \<bullet> z)) *\<^sub>R u)"
    by (rule sum.cong[OF refl])
      (simp add: scaleR_matrix_vector)
  finally show ?thesis .
qed

lemma quadform_sum_outer:
  fixes S :: "(real^'n::finite) set" and c :: "real^'n \<Rightarrow> real"
  assumes finS: "finite S"
  shows "z \<bullet> ((\<Sum>u\<in>S. c u *\<^sub>R outer_prod u u) *v z) = (\<Sum>u\<in>S. c u * (u \<bullet> z)\<^sup>2)"
proof -
  have "z \<bullet> ((\<Sum>u\<in>S. c u *\<^sub>R outer_prod u u) *v z)
      = z \<bullet> (\<Sum>u\<in>S. (c u * (u \<bullet> z)) *\<^sub>R u)"
    by (simp add: matvec_sum_outer[OF finS])
  also have "\<dots> = (\<Sum>u\<in>S. z \<bullet> ((c u * (u \<bullet> z)) *\<^sub>R u))"
    by (rule inner_sum_right)
  also have "\<dots> = (\<Sum>u\<in>S. c u * (u \<bullet> z)\<^sup>2)"
    by (rule sum.cong[OF refl])
      (simp add: inner_commute power2_eq_square
        algebra_simps)
  finally show ?thesis .
qed

lemma traceM_sum_outer:
  fixes S :: "(real^'n::finite) set" and c :: "real^'n \<Rightarrow> real"
    and M :: "real^'n^'n"
  shows "trace (M ** (\<Sum>u\<in>S. c u *\<^sub>R outer_prod u u))
      = (\<Sum>u\<in>S. c u * (u \<bullet> (M *v u)))"
proof -
  have "M ** (\<Sum>u\<in>S. c u *\<^sub>R outer_prod u u)
      = (\<Sum>u\<in>S. M ** (c u *\<^sub>R outer_prod u u))"
    by (rule matrix_mult_sum_right)
  then have "trace (M ** (\<Sum>u\<in>S. c u *\<^sub>R outer_prod u u))
      = (\<Sum>u\<in>S. trace (M ** (c u *\<^sub>R outer_prod u u)))"
    by (simp add: trace_matrix_sum)
  also have "\<dots> = (\<Sum>u\<in>S. c u * (u \<bullet> (M *v u)))"
  proof (rule sum.cong[OF refl])
    fix u assume "u \<in> S"
    have "trace (M ** (c u *\<^sub>R outer_prod u u))
        = c u * trace (M ** outer_prod u u)"
      by (rule trace_mult_scaleR)
    also have "trace (M ** outer_prod u u) = u \<bullet> (M *v u)"
      using trace_mult_outerp[of M u] by (simp add: outerp_eq_outer_prod)
    finally show "trace (M ** (c u *\<^sub>R outer_prod u u))
        = c u * (u \<bullet> (M *v u))" .
  qed
  finally show ?thesis .
qed

text \<open>\<open>trace_mult_add\<close> lives in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


lemma onormal_parseval:
  fixes B :: "(real^'n::finite) set"
  assumes B: "onormal B" and sp: "span B = UNIV"
  shows "(\<Sum>u\<in>B. (u \<bullet> z)\<^sup>2) = z \<bullet> z"
proof -
  have finB: "finite B" by (rule onormal_finite[OF B])
  have "(\<Sum>u\<in>B. (u \<bullet> z)\<^sup>2) = (\<Sum>u\<in>B. 1 * (u \<bullet> z)\<^sup>2)" by simp
  also have "\<dots> = z \<bullet> ((\<Sum>u\<in>B. 1 *\<^sub>R outer_prod u u) *v z)"
    by (rule quadform_sum_outer[OF finB, symmetric])
  also have "(\<Sum>u\<in>B. (1::real) *\<^sub>R outer_prod u u) = (\<Sum>u\<in>B. outer_prod u u)"
    by simp
  also have "\<dots> = mat 1" by (rule onormal_complete[OF B sp])
  also have "z \<bullet> (mat 1 *v z) = z \<bullet> z" by simp
  finally show ?thesis .
qed

lemma onormal_span_parseval:
  fixes S :: "(real^'n::finite) set"
  assumes S: "onormal S" and x: "x \<in> span S"
  shows "(\<Sum>u\<in>S. (u \<bullet> x)\<^sup>2) = x \<bullet> x"
proof -
  have finS: "finite S" by (rule onormal_finite[OF S])
  have "x \<bullet> x = x \<bullet> (\<Sum>u\<in>S. (u \<bullet> x) *\<^sub>R u)"
    by (simp add: onormal_expand[OF S x])
  also have "\<dots> = (\<Sum>u\<in>S. x \<bullet> ((u \<bullet> x) *\<^sub>R u))"
    by (rule inner_sum_right)
  also have "\<dots> = (\<Sum>u\<in>S. (u \<bullet> x)\<^sup>2)"
    by (rule sum.cong[OF refl])
      (simp add: inner_commute power2_eq_square)
  finally show ?thesis by simp
qed

section \<open>Selecting a value-minimal index set: the threshold argument\<close>

text \<open>\<open>exists_min_subset\<close> lives in @{theory Symmetric_Matrix_Spectra.Ky_Fan}.\<close>


lemma weighted_min_value:
  fixes w c :: "'a \<Rightarrow> real"
  assumes finB: "finite B" and m1: "1 \<le> m" and mB: "m \<le> card B"
    and c0: "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> c u" and c1: "\<And>u. u \<in> B \<Longrightarrow> c u \<le> 1"
    and csum: "real m \<le> (\<Sum>u\<in>B. c u)"
  obtains S where "S \<subseteq> B" and "m \<le> card S"
    and "(\<Sum>u\<in>S. w u) \<le> (\<Sum>u\<in>B. c u * w u)"
proof -
  obtain S0 where S0: "S0 \<subseteq> B" and cS0: "card S0 = m"
    and least: "\<forall>u\<in>S0. \<forall>v\<in>B - S0. w u \<le> w v"
    using exists_min_subset[OF finB mB] by blast
  have finS0: "finite S0" using S0 finB by (rule finite_subset)
  have neS0: "S0 \<noteq> {}" using cS0 m1 by auto
  define Neg where "Neg = {u \<in> B. w u < 0}"
  have finNeg: "finite Neg" unfolding Neg_def using finB by simp
  define \<tau> where "\<tau> = Max (w ` S0)"
  have tauS0: "\<And>u. u \<in> S0 \<Longrightarrow> w u \<le> \<tau>"
    unfolding \<tau>_def by (intro Max_ge finite_imageI finS0) blast
  have tauout: "\<And>v. v \<in> B - S0 \<Longrightarrow> \<tau> \<le> w v"
    unfolding \<tau>_def
    by (intro Max.boundedI finite_imageI finS0)
      (use neS0 least in blast)+
  show ?thesis
  proof (cases "Neg \<subseteq> S0")
    case True
    \<comment> \<open>the threshold is \<open>max \<tau> 0\<close>; every term is compared against it\<close>
    define tp where "tp = max \<tau> 0"
    have tp0: "0 \<le> tp" by (simp add: tp_def)
    have key: "0 \<le> (\<Sum>u\<in>B. c u * w u) - (\<Sum>u\<in>S0. w u)"
    proof -
      have split: "(\<Sum>u\<in>B. c u * w u)
          = (\<Sum>u\<in>S0. c u * w u) + (\<Sum>u\<in>B - S0. c u * w u)"
        using sum.subset_diff[OF S0 finB, of "\<lambda>u. c u * w u"] by simp
      have inS: "\<And>u. u \<in> S0 \<Longrightarrow> (c u - 1) * tp \<le> (c u - 1) * w u"
      proof -
        fix u assume u: "u \<in> S0"
        have wle: "w u \<le> tp" using tauS0[OF u] by (simp add: tp_def)
        have cle: "c u - 1 \<le> 0" using c1 S0 u by auto
        show "(c u - 1) * tp \<le> (c u - 1) * w u"
          using mult_left_mono_neg[OF wle cle] by simp
      qed
      have outS: "\<And>u. u \<in> B - S0 \<Longrightarrow> c u * tp \<le> c u * w u"
      proof -
        fix u assume u: "u \<in> B - S0"
        have w0: "0 \<le> w u" using True u unfolding Neg_def by auto
        have wge: "tp \<le> w u"
          using tauout[OF u] w0 by (simp add: tp_def)
        have c0': "0 \<le> c u" using c0 u by auto
        show "c u * tp \<le> c u * w u"
          by (rule mult_left_mono[OF wge c0'])
      qed
      have "(\<Sum>u\<in>B. c u * w u) - (\<Sum>u\<in>S0. w u)
          = (\<Sum>u\<in>S0. (c u - 1) * w u) + (\<Sum>u\<in>B - S0. c u * w u)"
        unfolding split by (simp add: sum_subtractf algebra_simps)
      moreover have "(\<Sum>u\<in>S0. (c u - 1) * tp) + (\<Sum>u\<in>B - S0. c u * tp)
          \<le> (\<Sum>u\<in>S0. (c u - 1) * w u) + (\<Sum>u\<in>B - S0. c u * w u)"
        by (intro add_mono sum_mono inS outS)
      moreover have "(\<Sum>u\<in>S0. (c u - 1) * tp) + (\<Sum>u\<in>B - S0. c u * tp)
          = tp * ((\<Sum>u\<in>B. c u) - real m)"
      proof -
        have h1: "(\<Sum>u\<in>S0. (c u - 1) * tp)
            = (\<Sum>u\<in>S0. c u * tp) - real m * tp"
          by (simp add: sum_subtractf cS0 algebra_simps)
        have h2: "(\<Sum>u\<in>S0. c u * tp) + (\<Sum>u\<in>B - S0. c u * tp)
            = (\<Sum>u\<in>B. c u * tp)"
          using sum.subset_diff[OF S0 finB, of "\<lambda>u. c u * tp"] by simp
        have h3: "(\<Sum>u\<in>B. c u * tp) = (\<Sum>u\<in>B. c u) * tp"
          by (simp add: sum_distrib_right)
        show ?thesis using h1 h2 h3 by (simp add: algebra_simps)
      qed
      moreover have "0 \<le> tp * ((\<Sum>u\<in>B. c u) - real m)"
        using tp0 csum by simp
      ultimately show ?thesis by linarith
    qed
    show ?thesis
      by (rule that[of S0]) (use S0 cS0 key in auto)
  next
    case False
    \<comment> \<open>a negative weight escaped the minimal set, so \<open>\<tau> < 0\<close> and taking all
      negatives on top of \<open>S0\<close> costs nothing\<close>
    obtain vn where vn: "vn \<in> Neg" "vn \<notin> S0" using False by blast
    have tneg: "\<tau> < 0"
    proof -
      have "\<tau> \<le> w vn"
        using tauout vn unfolding Neg_def by auto
      also have "w vn < 0" using vn unfolding Neg_def by auto
      finally show ?thesis .
    qed
    define S where "S = S0 \<union> Neg"
    have SB: "S \<subseteq> B" unfolding S_def Neg_def using S0 by auto
    have finS: "finite S" using SB finB by (rule finite_subset)
    have cardS: "m \<le> card S"
      unfolding S_def using cS0 card_mono[OF finS[unfolded S_def], of S0]
      by simp
    have inS: "\<And>u. u \<in> S \<Longrightarrow> w u \<le> 0"
    proof -
      fix u assume "u \<in> S"
      then consider "u \<in> S0" | "u \<in> Neg" unfolding S_def by blast
      then show "w u \<le> 0"
      proof cases
        case 1 then show ?thesis using tauS0 tneg by fastforce
      next
        case 2 then show ?thesis unfolding Neg_def by auto
      qed
    qed
    have key: "0 \<le> (\<Sum>u\<in>B. c u * w u) - (\<Sum>u\<in>S. w u)"
    proof -
      have split: "(\<Sum>u\<in>B. c u * w u)
          = (\<Sum>u\<in>S. c u * w u) + (\<Sum>u\<in>B - S. c u * w u)"
        using sum.subset_diff[OF SB finB, of "\<lambda>u. c u * w u"] by simp
      have t1: "0 \<le> (\<Sum>u\<in>S. (c u - 1) * w u)"
      proof (rule sum_nonneg)
        fix u assume u: "u \<in> S"
        have c1': "c u - 1 \<le> 0" using c1 SB u by auto
        have w0: "w u \<le> 0" by (rule inS[OF u])
        show "0 \<le> (c u - 1) * w u" by (rule mult_nonpos_nonpos[OF c1' w0])
      qed
      have t2: "0 \<le> (\<Sum>u\<in>B - S. c u * w u)"
      proof (rule sum_nonneg)
        fix u assume u: "u \<in> B - S"
        have "0 \<le> w u" using u unfolding S_def Neg_def by auto
        then show "0 \<le> c u * w u" using c0 u by auto
      qed
      have "(\<Sum>u\<in>B. c u * w u) - (\<Sum>u\<in>S. w u)
          = (\<Sum>u\<in>S. (c u - 1) * w u) + (\<Sum>u\<in>B - S. c u * w u)"
        unfolding split by (simp add: sum_subtractf algebra_simps)
      with t1 t2 show ?thesis by linarith
    qed
    show ?thesis
      by (rule that[of S]) (use SB cardS key in auto)
  qed
qed

section \<open>From the convexified constraint to a feasible witness\<close>

text \<open>The step the paper never needs to make explicit: a matrix of the
  convexified constraint set that kills \<open>q\<close> dominates, in any linear
  value, a matrix of the original feasible set of Eq. (1.9).  The
  construction is a capped spectral split: write \<open>b\<close> in its eigenbasis,
  cut the eigenvalues at \<open>1\<close>, decompose the capped part by the threshold
  selection --- its atoms are projections, so they carry eigenvalue cap
  \<open>1\<close> --- and hand the excess, bounded by \<open>L - 1\<close>, to the chosen atom.
  The cap closes at \<open>1 + (L-1) = L\<close>, exactly why the split must happen at
  level \<open>1\<close> and nowhere else.  Orthogonality to \<open>q\<close> survives because every
  eigendirection that carries weight is orthogonal to \<open>q\<close> already.\<close>

theorem sconstraint_orth_feasible:
  fixes b M :: "real^'n::finite^'n" and q :: "real^'n"
  assumes kn: "k < CARD('n)" and L1: "1 \<le> L"
    and b: "b \<in> sconstraint k L" and orth: "b *v q = 0"
  obtains a where "a \<in> feasible k L q"
    and "- trace (M ** a) / 2 \<le> - trace (M ** b) / 2"
proof -
  have psd_b: "psd b" and Pi_b: "b \<in> Pi_constraint k" and ub_b: "eigen_ub b L"
    using b unfolding sconstraint_def Pi_constraint_def by auto
  have sym_b: "transpose b = b" using psd_b by (simp add: psd_def)
  obtain B :: "(real^'n) set" where B: "onormal B" "span B = UNIV"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> b *v u = (u \<bullet> (b *v u)) *\<^sub>R u"
    using symmetric_eigenbasis[OF sym_b] by blast
  have cardB: "card B = CARD('n)" by (rule onormal_span_card[OF B])
  have finB: "finite B" by (rule onormal_finite[OF B(1)])
  define lam where "lam = (\<lambda>u :: real^'n. u \<bullet> (b *v u))"
  have lam_nn: "0 \<le> lam u" for u
    using psd_b by (simp add: lam_def psd_def)
  have lam_le: "\<And>u. u \<in> B \<Longrightarrow> lam u \<le> L"
  proof -
    fix u assume u: "u \<in> B"
    have "u \<bullet> (b *v u) \<le> L * (u \<bullet> u)"
      using ub_b unfolding eigen_ub_def by blast
    then show "lam u \<le> L"
      using onormal_inner_self[OF B(1) u] by (simp add: lam_def)
  qed
  have bdecomp: "b = (\<Sum>u\<in>B. lam u *\<^sub>R outer_prod u u)"
    unfolding lam_def by (rule spectral_decomposition[OF B eig])
  \<comment> \<open>every eigendirection with weight is orthogonal to \<open>q\<close>\<close>
  have orthu: "\<And>u. u \<in> B \<Longrightarrow> lam u * (u \<bullet> q) = 0"
  proof -
    fix u assume u: "u \<in> B"
    have "u \<bullet> (b *v q) = 0" using orth by simp
    moreover have "u \<bullet> (b *v q) = (b *v u) \<bullet> q"
    proof -
      have "u \<bullet> (b *v q) = (transpose b *v u) \<bullet> q"
        by (rule inner_transpose_matrix)
      then show ?thesis using sym_b by simp
    qed
    moreover have "(b *v u) \<bullet> q = lam u * (u \<bullet> q)"
    proof -
      have "(b *v u) \<bullet> q = ((u \<bullet> (b *v u)) *\<^sub>R u) \<bullet> q"
        by (rule arg_cong[where f = "\<lambda>v. v \<bullet> q", OF eig[OF u]])
      then show ?thesis by (simp add: lam_def)
    qed
    ultimately show "lam u * (u \<bullet> q) = 0" by simp
  qed
  define cap where "cap = (\<lambda>u :: real^'n. min (lam u) 1)"
  have cap_nn: "0 \<le> cap u" for u using lam_nn by (simp add: cap_def)
  have cap_le1: "cap u \<le> 1" for u by (simp add: cap_def)
  have cap_le_lam: "cap u \<le> lam u" for u by (simp add: cap_def)
  define m where "m = CARD('n) - k"
  have m1: "1 \<le> m" using kn by (simp add: m_def)
  have capsum: "real m \<le> (\<Sum>u\<in>B. cap u)"
    unfolding cap_def lam_def m_def
    by (rule Pi_constraint_capped_trace[OF Pi_b kn B(1) cardB eig])
  define B' where "B' = {u \<in> B. 0 < lam u}"
  have B'B: "B' \<subseteq> B" unfolding B'_def by blast
  have finB': "finite B'" using B'B finB by (rule finite_subset)
  have cap0: "\<And>u. u \<in> B - B' \<Longrightarrow> cap u = 0"
  proof -
    fix u assume "u \<in> B - B'"
    then have "lam u \<le> 0" unfolding B'_def by auto
    then have "lam u = 0" using lam_nn[of u] by simp
    then show "cap u = 0" by (simp add: cap_def)
  qed
  have capsum': "real m \<le> (\<Sum>u\<in>B'. cap u)"
  proof -
    have "(\<Sum>u\<in>B. cap u) = (\<Sum>u\<in>B'. cap u)"
      by (rule sum.mono_neutral_right[OF finB B'B]) (use cap0 in auto)
    then show ?thesis using capsum by simp
  qed
  have mB': "m \<le> card B'"
  proof -
    have "(\<Sum>u\<in>B'. cap u) \<le> (\<Sum>u\<in>B'. 1)"
      by (rule sum_mono) (rule cap_le1)
    then have "real m \<le> real (card B')" using capsum' by simp
    then show ?thesis by simp
  qed
  have orthB': "\<And>u. u \<in> B' \<Longrightarrow> u \<bullet> q = 0"
  proof -
    fix u assume u: "u \<in> B'"
    have "lam u * (u \<bullet> q) = 0" using orthu B'B u by blast
    moreover have "lam u \<noteq> 0" using u unfolding B'_def by auto
    ultimately show "u \<bullet> q = 0" by simp
  qed
  \<comment> \<open>select the value-minimal index set with the weights \<open>- u \<bullet> (M *v u)\<close>\<close>
  obtain S where SB': "S \<subseteq> B'" and cardS: "m \<le> card S"
    and Sval: "(\<Sum>u\<in>S. - (u \<bullet> (M *v u)))
        \<le> (\<Sum>u\<in>B'. cap u * - (u \<bullet> (M *v u)))"
    by (rule weighted_min_value[OF finB' m1 mB' cap_nn cap_le1 capsum'])
  have SB: "S \<subseteq> B" using SB' B'B by blast
  have finS: "finite S" using SB finB by (rule finite_subset)
  define rho where "rho = (\<lambda>u :: real^'n. lam u - cap u)"
  have rho_nn: "0 \<le> rho u" for u
    by (simp add: rho_def cap_le_lam)
  have rho_le: "\<And>u. u \<in> B \<Longrightarrow> rho u \<le> L - 1"
  proof -
    fix u assume u: "u \<in> B"
    show "rho u \<le> L - 1"
    proof (cases "lam u \<le> 1")
      case True
      then have "rho u = 0" by (simp add: rho_def cap_def)
      then show ?thesis using L1 by simp
    next
      case False
      then have "rho u = lam u - 1" by (simp add: rho_def cap_def)
      then show ?thesis using lam_le[OF u] by simp
    qed
  qed
  have rho_orth: "\<And>u. u \<in> B \<Longrightarrow> rho u * (u \<bullet> q) = 0"
  proof -
    fix u assume u: "u \<in> B"
    show "rho u * (u \<bullet> q) = 0"
    proof (cases "rho u = 0")
      case True then show ?thesis by simp
    next
      case False
      then have "lam u \<noteq> 0" by (simp add: rho_def cap_def min_def split: if_splits)
      then have "0 < lam u" using lam_nn[of u] by simp
      then have "u \<in> B'" using u unfolding B'_def by simp
      then show ?thesis using orthB' by simp
    qed
  qed
  define R where "R = (\<Sum>u\<in>B. rho u *\<^sub>R outer_prod u u)"
  define a where "a = (\<Sum>u\<in>S. outer_prod u u) + R"
  \<comment> \<open>the quadratic form of \<open>a\<close>\<close>
  have quad_a: "z \<bullet> (a *v z)
      = (\<Sum>u\<in>S. (u \<bullet> z)\<^sup>2) + (\<Sum>u\<in>B. rho u * (u \<bullet> z)\<^sup>2)" for z
  proof -
    have "a *v z = (\<Sum>u\<in>S. outer_prod u u) *v z + R *v z"
      unfolding a_def by (simp add: matrix_vector_mult_add_rdistrib)
    then have "z \<bullet> (a *v z)
        = z \<bullet> ((\<Sum>u\<in>S. outer_prod u u) *v z) + z \<bullet> (R *v z)"
      by (simp add: inner_add_right)
    moreover have "z \<bullet> ((\<Sum>u\<in>S. outer_prod u u) *v z) = (\<Sum>u\<in>S. (u \<bullet> z)\<^sup>2)"
      using quadform_sum_outer[OF finS, where c = "\<lambda>_. 1" and z = z] by simp
    moreover have "z \<bullet> (R *v z) = (\<Sum>u\<in>B. rho u * (u \<bullet> z)\<^sup>2)"
      unfolding R_def by (rule quadform_sum_outer[OF finB])
    ultimately show ?thesis by simp
  qed
  have quad_a_nn: "0 \<le> z \<bullet> (a *v z)" for z
    unfolding quad_a
    by (intro add_nonneg_nonneg sum_nonneg)
      (auto intro: mult_nonneg_nonneg rho_nn)
  have sym_a: "transpose a = a"
  proof -
    have t1: "transpose (\<Sum>u\<in>S. outer_prod u u) = (\<Sum>u\<in>S. outer_prod u u)"
      by (simp add: transpose_matrix_sum)
    have t2: "transpose R = R"
    proof -
      have "transpose R = (\<Sum>u\<in>B. transpose (rho u *\<^sub>R outer_prod u u))"
        unfolding R_def by (rule transpose_matrix_sum)
      also have "\<dots> = (\<Sum>u\<in>B. rho u *\<^sub>R outer_prod u u)"
        by (rule sum.cong[OF refl])
          (simp add: transpose_def vec_eq_iff outer_prod_def mult.commute)
      finally show ?thesis unfolding R_def .
    qed
    have "transpose a = transpose (\<Sum>u\<in>S. outer_prod u u) + transpose R"
      unfolding a_def by (simp add: transpose_def vec_eq_iff)
    then show ?thesis unfolding a_def using t1 t2 by simp
  qed
  have psd_a: "psd a"
    unfolding psd_def using sym_a quad_a_nn by blast
  have aq: "a *v q = 0"
  proof -
    have "(\<Sum>u\<in>S. outer_prod u u) *v q = (\<Sum>u\<in>S. (1 * (u \<bullet> q)) *\<^sub>R u)"
      using matvec_sum_outer[OF finS, of "\<lambda>_. 1" q] by simp
    also have "\<dots> = 0"
      by (rule sum.neutral) (use orthB' SB' in auto)
    finally have z1: "(\<Sum>u\<in>S. outer_prod u u) *v q = 0" .
    have "R *v q = (\<Sum>u\<in>B. (rho u * (u \<bullet> q)) *\<^sub>R u)"
      unfolding R_def by (rule matvec_sum_outer[OF finB])
    also have "\<dots> = 0"
      by (rule sum.neutral) (use rho_orth in auto)
    finally have z2: "R *v q = 0" .
    show ?thesis
      unfolding a_def by (simp add: matrix_vector_mult_add_rdistrib z1 z2)
  qed
  have lb_a: "eigen_lb a (CARD('n) - k)"
    unfolding eigen_lb_def
  proof (intro exI[of _ "span S"] conjI)
    show "subspace (span S)" by (rule subspace_span)
    have "card S = dim (span S)"
      by (rule onormal_card_dim_span[OF onormal_subset[OF B(1) SB]])
    then show "CARD('n) - k \<le> dim (span S)"
      using cardS m_def by simp
    show "\<forall>x\<in>span S. x \<bullet> x \<le> x \<bullet> (a *v x)"
    proof
      fix x assume x: "x \<in> span S"
      have "x \<bullet> x = (\<Sum>u\<in>S. (u \<bullet> x)\<^sup>2)"
        by (rule onormal_span_parseval[OF onormal_subset[OF B(1) SB] x,
              symmetric])
      also have "\<dots> \<le> (\<Sum>u\<in>S. (u \<bullet> x)\<^sup>2) + (\<Sum>u\<in>B. rho u * (u \<bullet> x)\<^sup>2)"
        by (simp add: sum_nonneg rho_nn)
      finally show "x \<bullet> x \<le> x \<bullet> (a *v x)" unfolding quad_a .
    qed
  qed
  have ub_a: "eigen_ub a L"
    unfolding eigen_ub_def
  proof
    fix z :: "real^'n"
    have "(\<Sum>u\<in>S. (u \<bullet> z)\<^sup>2) \<le> (\<Sum>u\<in>B. (u \<bullet> z)\<^sup>2)"
      by (rule sum_mono2[OF finB SB]) auto
    moreover have "(\<Sum>u\<in>B. rho u * (u \<bullet> z)\<^sup>2)
        \<le> (\<Sum>u\<in>B. (L - 1) * (u \<bullet> z)\<^sup>2)"
      by (rule sum_mono) (auto intro: mult_right_mono rho_le)
    ultimately have "z \<bullet> (a *v z)
        \<le> (\<Sum>u\<in>B. (u \<bullet> z)\<^sup>2) + (L - 1) * (\<Sum>u\<in>B. (u \<bullet> z)\<^sup>2)"
      unfolding quad_a by (simp add: sum_distrib_left)
    also have "\<dots> = L * (\<Sum>u\<in>B. (u \<bullet> z)\<^sup>2)" by (simp add: algebra_simps)
    also have "\<dots> = L * (z \<bullet> z)" by (simp add: onormal_parseval[OF B])
    finally show "z \<bullet> (a *v z) \<le> L * (z \<bullet> z)" .
  qed
  have feas: "a \<in> feasible k L q"
    unfolding feasible_def using psd_a aq lb_a ub_a by blast
  \<comment> \<open>the value comparison\<close>
  have val: "trace (M ** b) \<le> trace (M ** a)"
  proof -
    have capdec: "b = (\<Sum>u\<in>B. cap u *\<^sub>R outer_prod u u) + R"
    proof -
      have "(\<Sum>u\<in>B. cap u *\<^sub>R outer_prod u u) + R
          = (\<Sum>u\<in>B. cap u *\<^sub>R outer_prod u u + rho u *\<^sub>R outer_prod u u)"
        unfolding R_def by (rule sum.distrib[symmetric])
      also have "\<dots> = (\<Sum>u\<in>B. lam u *\<^sub>R outer_prod u u)"
        by (rule sum.cong[OF refl])
          (simp add: rho_def scaleR_add_left[symmetric])
      finally show ?thesis using bdecomp by simp
    qed
    have vb: "trace (M ** b)
        = (\<Sum>u\<in>B. cap u * (u \<bullet> (M *v u))) + trace (M ** R)"
      by (subst capdec) (simp add: trace_mult_add traceM_sum_outer)
    have va: "trace (M ** a)
        = (\<Sum>u\<in>S. u \<bullet> (M *v u)) + trace (M ** R)"
    proof -
      have "trace (M ** (\<Sum>u\<in>S. outer_prod u u)) = (\<Sum>u\<in>S. u \<bullet> (M *v u))"
        using traceM_sum_outer[where M = M and S = S and c = "\<lambda>_. 1"] by simp
      then show ?thesis
        unfolding a_def by (simp add: trace_mult_add)
    qed
    have capval: "(\<Sum>u\<in>B. cap u * (u \<bullet> (M *v u)))
        = (\<Sum>u\<in>B'. cap u * (u \<bullet> (M *v u)))"
      by (rule sum.mono_neutral_right[OF finB B'B]) (use cap0 in auto)
    have "(\<Sum>u\<in>B'. cap u * (u \<bullet> (M *v u))) \<le> (\<Sum>u\<in>S. u \<bullet> (M *v u))"
    proof -
      have "- (\<Sum>u\<in>S. u \<bullet> (M *v u)) \<le> - (\<Sum>u\<in>B'. cap u * (u \<bullet> (M *v u)))"
        using Sval by (simp add: sum_negf)
      then show ?thesis by simp
    qed
    then show ?thesis using vb va capval by simp
  qed
  have "- trace (M ** a) / 2 \<le> - trace (M ** b) / 2"
    using val by simp
  then show ?thesis using that feas by blast
qed

section \<open>The DPP capped at an arbitrary \<open>[0,T]\<close>-valued time\<close>

theorem exit_val_cond_at_time:
  fixes P :: "('n::finite pairpath) measure" and K :: "(real^'n) set"
    and y :: "real^'n" and \<theta> :: "'n pairpath \<Rightarrow> real"
  assumes T0: "0 \<le> T" and L1: "1 \<le> L" and Kc: "closed K"
    and P: "P \<in> exit_class k L T y"
    and c: "AE \<omega> in P. c \<le> pexit T K (\<lambda>t. fst (\<omega> t))"
    and th0: "\<And>\<omega>. 0 \<le> \<theta> \<omega>" and thT: "\<And>\<omega>. \<theta> \<omega> \<le> T"
  shows "AE \<omega> in P. c \<le> \<theta> \<omega>
      + min (enn2real (exit_val k L T K (fst (\<omega> (\<theta> \<omega>))))) (T - \<theta> \<omega>)"
proof -
  have "AE \<omega> in P. c \<le> \<theta> \<omega>
      + enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>))))"
    by (rule exit_val_cond_time[OF T0 L1 Kc P c th0 thT])
  then show ?thesis
  proof (rule eventually_mono)
    fix \<omega> :: "'n pairpath"
    assume h: "c \<le> \<theta> \<omega>
        + enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>))))"
    have a: "0 \<le> T - \<theta> \<omega>" using thT[of \<omega>] by simp
    have b: "T - \<theta> \<omega> \<le> T" using th0[of \<omega>] by simp
    have "enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>))))
        = min (enn2real (exit_val k L T K (fst (\<omega> (\<theta> \<omega>))))) (T - \<theta> \<omega>)"
      by (rule enn2real_paper_v_horizon_cap[OF a b L1 Kc])
    with h show "c \<le> \<theta> \<omega>
        + min (enn2real (exit_val k L T K (fst (\<omega> (\<theta> \<omega>))))) (T - \<theta> \<omega>)"
      by simp
  qed
qed

section \<open>Small pointwise bounds\<close>

text \<open>\<open>quadform_abs_le\<close>, \<open>axis1_inner\<close>, \<open>axis1_self\<close>, \<open>matvec_axis1\<close> live in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


section \<open>Moments at a stopping time, assembled\<close>

lemma exit_class_stopped_moments:
  fixes P :: "('n::finite pairpath) measure" and x q :: "real^'n"
    and M :: "real^'n^'n"
  assumes T: "0 < T" and L0: "0 \<le> L" and P: "P \<in> exit_class k L T x"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows stopped_X_int: "integrable P (\<lambda>\<omega>. fst (\<omega> (\<theta> \<omega>)))"
    and stopped_X_mean: "(\<integral>\<omega>. fst (\<omega> (\<theta> \<omega>)) \<partial>P) = x"
    and stopped_lin_int: "integrable P (\<lambda>\<omega>. q \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x))"
    and stopped_lin_mean: "(\<integral>\<omega>. q \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x) \<partial>P) = 0"
    and stopped_quad_int: "integrable P
      (\<lambda>\<omega>. (fst (\<omega> (\<theta> \<omega>)) - x) \<bullet> (M *v (fst (\<omega> (\<theta> \<omega>)) - x)))"
    and stopped_quad_mean: "(\<integral>\<omega>. (fst (\<omega> (\<theta> \<omega>)) - x)
        \<bullet> (M *v (fst (\<omega> (\<theta> \<omega>)) - x)) \<partial>P)
      = trace (M ** (\<integral>\<omega>. snd (\<omega> (\<theta> \<omega>)) \<partial>P))"
proof -
  let ?Xf = "\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (\<theta> \<omega>))"
  let ?Yf = "\<lambda>\<omega> :: 'n pairpath. snd (\<omega> (\<theta> \<omega>))"
  have T0: "0 \<le> T" using T by simp
  interpret PP: prob_space P by (rule exit_class_prob[OF P])
  have iXc: "integrable P (\<lambda>\<omega>. ?Xf \<omega> $ c)" for c
    using exit_class_X_entry_stopped(1)[OF T L0 P st thM] .
  have EXc: "(\<integral>\<omega>. ?Xf \<omega> $ c \<partial>P) = x $ c" for c
    using exit_class_X_entry_stopped(2)[OF T L0 P st thM] .
  have iCc: "integrable P (\<lambda>\<omega>. (outerp (?Xf \<omega>) - ?Yf \<omega>) $ cc $ dd)" for cc dd
    using exit_class_comp_entry_stopped(1)[OF T L0 P st thM] .
  have ECc: "(\<integral>\<omega>. (outerp (?Xf \<omega>) - ?Yf \<omega>) $ cc $ dd \<partial>P) = outerp x $ cc $ dd"
    for cc dd
    using exit_class_comp_entry_stopped(2)[OF T L0 P st thM] .
  have iY: "integrable P ?Yf"
    by (rule exit_class_Y_stopped_integrable[OF T0 L0 P st thM])
  show iX: "integrable P ?Xf"
  proof -
    have "integrable P (\<lambda>\<omega>. \<chi> c. ?Xf \<omega> $ c)"
      by (intro integrable_vec_components iXc)
    then show ?thesis by simp
  qed
  show EX: "(\<integral>\<omega>. ?Xf \<omega> \<partial>P) = x"
  proof -
    have "(\<integral>\<omega>. ?Xf \<omega> \<partial>P) $ c = x $ c" for c
      using integral_of_bounded_linear[OF bounded_linear_vec_nth iX] EXc[of c]
      by simp
    then show ?thesis by (simp add: vec_eq_iff)
  qed
  have ig1: "integrable P (\<lambda>\<omega>. q \<bullet> ?Xf \<omega>)"
    by (rule integrable_bounded_linear[OF bounded_linear_inner_right iX])
  have Eg1: "(\<integral>\<omega>. q \<bullet> ?Xf \<omega> \<partial>P) = q \<bullet> x"
    using integral_of_bounded_linear[OF bounded_linear_inner_right iX] EX
    by simp
  have lin_eq: "(\<lambda>\<omega>. q \<bullet> (?Xf \<omega> - x)) = (\<lambda>\<omega>. q \<bullet> ?Xf \<omega> - q \<bullet> x)"
    by (simp add: fun_eq_iff inner_diff_right)
  show "integrable P (\<lambda>\<omega>. q \<bullet> (?Xf \<omega> - x))"
    unfolding lin_eq
    by (intro Bochner_Integration.integrable_diff ig1 PP.integrable_const)
  show "(\<integral>\<omega>. q \<bullet> (?Xf \<omega> - x) \<partial>P) = 0"
    unfolding lin_eq
    using Bochner_Integration.integral_diff[OF ig1 PP.integrable_const] Eg1
    by (simp add: PP.prob_space)
  \<comment> \<open>the quadratic part, through the compensated entries\<close>
  have blM: "bounded_linear (\<lambda>w :: real^'n. M *v w)"
    unfolding linear_conv_bounded_linear[symmetric]
    by (rule matrix_vector_mul_linear)
  have ig2: "integrable P (\<lambda>\<omega>. x \<bullet> (M *v ?Xf \<omega>))"
    by (rule integrable_bounded_linear[OF bounded_linear_compose
          [OF bounded_linear_inner_right blM] iX])
  have Eg2: "(\<integral>\<omega>. x \<bullet> (M *v ?Xf \<omega>) \<partial>P) = x \<bullet> (M *v x)"
    using integral_of_bounded_linear[OF bounded_linear_compose
        [OF bounded_linear_inner_right blM] iX] EX by simp
  have ig3: "integrable P (\<lambda>\<omega>. ?Xf \<omega> \<bullet> (M *v x))"
    by (rule integrable_bounded_linear[OF bounded_linear_inner_left iX])
  have Eg3: "(\<integral>\<omega>. ?Xf \<omega> \<bullet> (M *v x) \<partial>P) = x \<bullet> (M *v x)"
    using integral_of_bounded_linear[OF bounded_linear_inner_left iX] EX
    by simp
  have icomp: "integrable P (\<lambda>\<omega>. trace (M ** (outerp (?Xf \<omega>) - ?Yf \<omega>)))"
    unfolding trace_mult_sum
    by (intro Bochner_Integration.integrable_sum integrable_cmult iCc)
  have Ecomp: "(\<integral>\<omega>. trace (M ** (outerp (?Xf \<omega>) - ?Yf \<omega>)) \<partial>P)
      = trace (M ** outerp x)"
  proof -
    have "(\<integral>\<omega>. (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV.
          M $ i $ j * (outerp (?Xf \<omega>) - ?Yf \<omega>) $ j $ i) \<partial>P)
        = (\<Sum>i\<in>UNIV. (\<integral>\<omega>. (\<Sum>j\<in>UNIV.
            M $ i $ j * (outerp (?Xf \<omega>) - ?Yf \<omega>) $ j $ i) \<partial>P))"
      by (rule Bochner_Integration.integral_sum)
        (intro Bochner_Integration.integrable_sum integrable_cmult iCc)
    also have "\<dots> = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV.
        (\<integral>\<omega>. M $ i $ j * (outerp (?Xf \<omega>) - ?Yf \<omega>) $ j $ i \<partial>P))"
      by (intro sum.cong refl Bochner_Integration.integral_sum
          integrable_cmult iCc)
    also have "\<dots> = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. M $ i $ j * outerp x $ j $ i)"
    proof -
      have iCc': "integrable P
          (\<lambda>\<omega>. outerp (?Xf \<omega>) $ cc $ dd - ?Yf \<omega> $ cc $ dd)" for cc dd
      proof -
        have e: "(\<lambda>\<omega>. outerp (?Xf \<omega>) $ cc $ dd - ?Yf \<omega> $ cc $ dd)
            = (\<lambda>\<omega>. (outerp (?Xf \<omega>) - ?Yf \<omega>) $ cc $ dd)" by simp
        show ?thesis unfolding e by (rule iCc)
      qed
      have ECc': "(\<integral>\<omega>. outerp (?Xf \<omega>) $ cc $ dd - ?Yf \<omega> $ cc $ dd \<partial>P)
          = outerp x $ cc $ dd" for cc dd
      proof -
        have e: "(\<lambda>\<omega>. outerp (?Xf \<omega>) $ cc $ dd - ?Yf \<omega> $ cc $ dd)
            = (\<lambda>\<omega>. (outerp (?Xf \<omega>) - ?Yf \<omega>) $ cc $ dd)" by simp
        show ?thesis unfolding e by (rule ECc)
      qed
      show ?thesis
        by (intro sum.cong refl)
          (simp add: integral_cmult[OF iCc'] ECc')
    qed
    finally show ?thesis unfolding trace_mult_sum .
  qed
  have itrY: "integrable P (\<lambda>\<omega>. trace (M ** ?Yf \<omega>))"
    by (rule integrable_bounded_linear[OF bounded_linear_trace_mult_left iY])
  have EtrY: "(\<integral>\<omega>. trace (M ** ?Yf \<omega>) \<partial>P)
      = trace (M ** (\<integral>\<omega>. ?Yf \<omega> \<partial>P))"
    by (rule integral_of_bounded_linear[OF bounded_linear_trace_mult_left iY])
  have g4eq: "(\<lambda>\<omega>. ?Xf \<omega> \<bullet> (M *v ?Xf \<omega>))
      = (\<lambda>\<omega>. trace (M ** (outerp (?Xf \<omega>) - ?Yf \<omega>)) + trace (M ** ?Yf \<omega>))"
    by (rule ext) (simp add: trace_mult_diff trace_mult_outerp)
  have ig4: "integrable P (\<lambda>\<omega>. ?Xf \<omega> \<bullet> (M *v ?Xf \<omega>))"
    unfolding g4eq by (intro Bochner_Integration.integrable_add icomp itrY)
  have Eg4: "(\<integral>\<omega>. ?Xf \<omega> \<bullet> (M *v ?Xf \<omega>) \<partial>P)
      = x \<bullet> (M *v x) + trace (M ** (\<integral>\<omega>. ?Yf \<omega> \<partial>P))"
    unfolding g4eq
    using Bochner_Integration.integral_add[OF icomp itrY] Ecomp EtrY
    by (simp add: trace_mult_outerp)
  have quad_eq: "(\<lambda>\<omega>. (?Xf \<omega> - x) \<bullet> (M *v (?Xf \<omega> - x)))
      = (\<lambda>\<omega>. ?Xf \<omega> \<bullet> (M *v ?Xf \<omega>) - x \<bullet> (M *v ?Xf \<omega>)
          - ?Xf \<omega> \<bullet> (M *v x) + x \<bullet> (M *v x))"
  proof (rule ext)
    fix \<omega> :: "'n pairpath"
    have lind: "M *v (a - b) = M *v a - M *v b" for a b :: "real^'n"
      using linear_diff[OF matrix_vector_mul_linear, of M] by simp
    show "(?Xf \<omega> - x) \<bullet> (M *v (?Xf \<omega> - x))
        = ?Xf \<omega> \<bullet> (M *v ?Xf \<omega>) - x \<bullet> (M *v ?Xf \<omega>)
          - ?Xf \<omega> \<bullet> (M *v x) + x \<bullet> (M *v x)"
      by (simp add: lind algebra_simps)
  qed
  show "integrable P (\<lambda>\<omega>. (?Xf \<omega> - x) \<bullet> (M *v (?Xf \<omega> - x)))"
    unfolding quad_eq
    by (intro Bochner_Integration.integrable_add
        Bochner_Integration.integrable_diff ig4 ig2 ig3 PP.integrable_const)
  show "(\<integral>\<omega>. (?Xf \<omega> - x) \<bullet> (M *v (?Xf \<omega> - x)) \<partial>P)
      = trace (M ** (\<integral>\<omega>. ?Yf \<omega> \<partial>P))"
    unfolding quad_eq
    using Bochner_Integration.integral_add[OF
        Bochner_Integration.integrable_diff[OF
          Bochner_Integration.integrable_diff[OF ig4 ig2] ig3]
        PP.integrable_const]
      Bochner_Integration.integral_diff[OF
        Bochner_Integration.integrable_diff[OF ig4 ig2] ig3]
      Bochner_Integration.integral_diff[OF ig4 ig2]
      Eg4 Eg2 Eg3 by (simp add: PP.prob_space)
qed

lemma exit_class_stopped_var:
  fixes P :: "('n::finite pairpath) measure" and x q :: "real^'n"
  assumes T: "0 < T" and L0: "0 \<le> L" and P: "P \<in> exit_class k L T x"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "integrable P (\<lambda>\<omega>. (q \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x))\<^sup>2)"
    and "(\<integral>\<omega>. (q \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x))\<^sup>2 \<partial>P)
      = q \<bullet> ((\<integral>\<omega>. snd (\<omega> (\<theta> \<omega>)) \<partial>P) *v q)"
proof -
  have e: "(\<lambda>\<omega> :: 'n pairpath. (q \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x))\<^sup>2)
      = (\<lambda>\<omega>. (fst (\<omega> (\<theta> \<omega>)) - x) \<bullet> (outerp q *v (fst (\<omega> (\<theta> \<omega>)) - x)))"
    by (rule ext) (simp add: quadform_outerp)
  show "integrable P (\<lambda>\<omega>. (q \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x))\<^sup>2)"
    unfolding e
    by (rule exit_class_stopped_moments(5)[OF T L0 P st thM])
  have "(\<integral>\<omega>. (q \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x))\<^sup>2 \<partial>P)
      = trace (outerp q ** (\<integral>\<omega>. snd (\<omega> (\<theta> \<omega>)) \<partial>P))"
    unfolding e
    by (rule exit_class_stopped_moments(6)[OF T L0 P st thM])
  then show "(\<integral>\<omega>. (q \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x))\<^sup>2 \<partial>P)
      = q \<bullet> ((\<integral>\<omega>. snd (\<omega> (\<theta> \<omega>)) \<partial>P) *v q)"
    by (simp add: trace_outerp_mult)
qed

lemma exit_class_stopped_normsq:
  fixes P :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T: "0 < T" and L0: "0 \<le> L" and P: "P \<in> exit_class k L T x"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "(\<integral>\<omega>. (fst (\<omega> (\<theta> \<omega>)) - x) \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x) \<partial>P)
      = trace (\<integral>\<omega>. snd (\<omega> (\<theta> \<omega>)) \<partial>P)"
proof -
  have e: "(\<lambda>\<omega> :: 'n pairpath.
      (fst (\<omega> (\<theta> \<omega>)) - x) \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x))
      = (\<lambda>\<omega>. (fst (\<omega> (\<theta> \<omega>)) - x) \<bullet> (mat 1 *v (fst (\<omega> (\<theta> \<omega>)) - x)))"
    by (simp add: fun_eq_iff)
  have "(\<integral>\<omega>. (fst (\<omega> (\<theta> \<omega>)) - x) \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x) \<partial>P)
      = trace (mat 1 ** (\<integral>\<omega>. snd (\<omega> (\<theta> \<omega>)) \<partial>P))"
    unfolding e
    by (rule exit_class_stopped_moments(6)[OF T L0 P st thM])
  then show ?thesis by simp
qed

section \<open>The near-orthogonal direction: the anti-concentration dichotomy\<close>

text \<open>The Girsanov-free replacement for the paper's exponential martingale
  ((3.18)--(3.19)).  The DPP and touching inequality hold almost surely,
  so if the averaged covariation kept variance \<open>\<ge> \<epsilon>\<^sub>0\<close> in the gradient
  direction, the martingale \<open>q \<bullet> X\<close> would take a negative value larger
  than the entire drift-plus-curvature budget \<open>t + C\<epsilon>\<^sup>2/2\<close> on a set of
  positive measure, a contradiction.  The quantitative form needs no
  fourth moment: the stopped increment is bounded by \<open>\<bar>q\<bar>\<epsilon>\<close>, so a bare
  indicator split gives the anti-concentration, and the scaling
  \<open>t := \<epsilon>\<^sup>2/(2nL)\<close> closes the loop.\<close>

theorem exit_val_touch_near_orth:
  fixes K :: "(real^'n::finite) set" and x q :: "real^'n" and M :: "real^'n^'n"
  assumes T: "0 < T" and L1: "1 \<le> L" and Kc: "closed K" and eb: "0 < ebar"
    and touch: "\<And>z. dist z x \<le> ebar \<Longrightarrow>
        enn2real (exit_val k L T K z)
          \<le> enn2real (exit_val k L T K x) + q \<bullet> (z - x)
            + ((z - x) \<bullet> (M *v (z - x))) / 2"
    and e0: "0 < \<epsilon>\<^sub>0"
  obtains b where "b \<in> sconstraint k L" and "- trace (M ** b) / 2 \<le> 1"
    and "q \<bullet> (b *v q) < \<epsilon>\<^sub>0"
proof (cases "q = 0")
  case True
  obtain b where bmem: "b \<in> sconstraint k L"
    and w: "- trace (M ** b) / 2 \<le> 1"
    by (rule exit_val_subsol_quadratic_ball[OF T L1 Kc eb touch])
  have "q \<bullet> (b *v q) < \<epsilon>\<^sub>0" using True e0 by simp
  then show ?thesis using that bmem w by blast
next
  case False
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have T0: "0 \<le> T" using T by simp
  have L0: "0 \<le> L" using L1 by simp
  define nq where "nq = norm q"
  have nq0: "0 < nq" using False by (simp add: nq_def)
  define n' where "n' = real CARD('n)"
  have n'1: "1 \<le> n'" unfolding n'_def
    using zero_less_card_finite[where 'a = 'n]
    by (simp add: Suc_leI of_nat_le_iff [symmetric])
  define Cm where "Cm = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>)"
  have Cm0: "0 \<le> Cm" unfolding Cm_def by (intro sum_nonneg) auto
  define \<beta> where "\<beta> = 1 / (2 * n' * n' * L)"
  have b0: "0 < \<beta>" unfolding \<beta>_def using n'1 L1 by simp
  define \<epsilon>K where "\<epsilon>K = sqrt \<epsilon>\<^sub>0 * sqrt \<beta> * \<epsilon>\<^sub>0 * \<beta>
      / (16 * nq\<^sup>2 * (\<beta> + Cm / 2))"
  have den0: "0 < 16 * nq\<^sup>2 * (\<beta> + Cm / 2)"
    using nq0 b0 Cm0 by (simp add: power2_eq_square)
  have eK0: "0 < \<epsilon>K"
    unfolding \<epsilon>K_def using e0 b0 den0 by simp
  define \<epsilon> where "\<epsilon> = min ebar (min (sqrt (T / \<beta>)) (\<epsilon>K / 2))"
  have eps0: "0 < \<epsilon>"
    unfolding \<epsilon>_def using eb T b0 eK0 by simp
  have epseb: "\<epsilon> \<le> ebar" unfolding \<epsilon>_def by simp
  have epsK: "\<epsilon> \<le> \<epsilon>K / 2" unfolding \<epsilon>_def by simp
  define t where "t = \<beta> * \<epsilon>\<^sup>2"
  have t0: "0 < t" unfolding t_def using b0 eps0 by simp
  have tT: "t \<le> T"
  proof -
    have "\<epsilon> \<le> sqrt (T / \<beta>)" unfolding \<epsilon>_def by simp
    then have "\<epsilon>\<^sup>2 \<le> (sqrt (T / \<beta>))\<^sup>2"
      using eps0 by (intro power_mono) auto
    also have "\<dots> = T / \<beta>" using T b0 by simp
    finally show ?thesis unfolding t_def using b0 by (simp add: field_simps)
  qed
  define \<theta>' where "\<theta>' = (\<lambda>\<omega> :: 'n pairpath. min t (pball_exit T x \<epsilon> \<omega>))"
  have st': "path_stopping_time T \<theta>'"
    unfolding \<theta>'_def
    by (rule path_stopping_time_min[OF pball_exit_path_stopping_time[OF T0]])
      (use t0 tT in auto)
  have thM': "\<theta>' \<in> borel_measurable ?B"
    unfolding \<theta>'_def
    by (intro borel_measurable_min borel_measurable_const
        pball_exit_measurable[OF T0])
  have th0': "0 \<le> \<theta>' \<omega>" for \<omega> :: "'n pairpath"
    unfolding \<theta>'_def using t0 pball_exit_nonneg[OF T0, of x \<epsilon> \<omega>] by simp
  have thT': "\<theta>' \<omega> \<le> T" for \<omega> :: "'n pairpath"
    unfolding \<theta>'_def using tT by simp
  have thle: "\<theta>' \<omega> \<le> pball_exit T x \<epsilon> \<omega>" for \<omega> :: "'n pairpath"
    unfolding \<theta>'_def by (rule min.cobounded2)
  have tht: "\<theta>' \<omega> \<le> t" for \<omega> :: "'n pairpath"
    unfolding \<theta>'_def by (rule min.cobounded1)
  define u where "u = (\<lambda>z :: real^'n. enn2real (exit_val k L T K z))"
  obtain P where P: "P \<in> exit_class k L T x"
    and Pv: "ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))
        = exit_val k L T K x"
    using exit_val_attained[OF T L1 Kc] by blast
  interpret PP: prob_space P by (rule exit_class_prob[OF P])
  have setsP: "sets P = sets ?B" by (rule exit_class_sets[OF P])
  have thP': "\<theta>' \<in> borel_measurable P"
    unfolding measurable_cong_sets[OF setsP refl] by (rule thM')
  let ?Xf = "\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (\<theta>' \<omega>))"
  let ?Yf = "\<lambda>\<omega> :: 'n pairpath. snd (\<omega> (\<theta>' \<omega>))"
  let ?V = "\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (\<theta>' \<omega>)) - x"
  \<comment> \<open>the almost-sure facts\<close>
  have cAE: "AE \<omega> in P. u x \<le> pexit T K (\<lambda>t. fst (\<omega> t))"
  proof (rule eventually_mono
      [OF ess_inf_time_AE[of P "\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))"]])
    fix \<omega> :: "'n pairpath"
    assume "ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))
        \<le> ennreal (pexit T K (\<lambda>t. fst (\<omega> t)))"
    then have le: "exit_val k L T K x \<le> ennreal (pexit T K (\<lambda>t. fst (\<omega> t)))"
      using Pv by simp
    have "enn2real (exit_val k L T K x)
        \<le> enn2real (ennreal (pexit T K (\<lambda>t. fst (\<omega> t))))"
      by (rule enn2real_mono[OF le ennreal_less_top])
    then show "u x \<le> pexit T K (\<lambda>t. fst (\<omega> t))"
      unfolding u_def
      using pexit_nonneg[OF T0, of K "\<lambda>t. fst (\<omega> t)"] by simp
  qed
  have dpp: "AE \<omega> in P. u x \<le> \<theta>' \<omega> + u (?Xf \<omega>)"
  proof (rule eventually_mono
      [OF exit_val_cond_at_time[OF T0 L1 Kc P cAE th0' thT']])
    fix \<omega> :: "'n pairpath"
    assume "u x \<le> \<theta>' \<omega>
        + min (enn2real (exit_val k L T K (?Xf \<omega>))) (T - \<theta>' \<omega>)"
    moreover have "min (enn2real (exit_val k L T K (?Xf \<omega>))) (T - \<theta>' \<omega>)
        \<le> enn2real (exit_val k L T K (?Xf \<omega>))"
      by (rule min.cobounded1)
    ultimately show "u x \<le> \<theta>' \<omega> + u (?Xf \<omega>)"
      unfolding u_def by linarith
  qed
  have stc: "AE \<omega> in P. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    using P unfolding exit_class_def by blast
  have cwAE: "AE \<omega> in P. continuous_on {0..T} (\<lambda>s. fst (\<omega> s))"
  proof -
    have "AE \<omega> in P. \<omega> \<in> space P" by (rule AE_space)
    then show ?thesis
    proof (rule eventually_mono)
      fix \<omega> :: "'n pairpath" assume "\<omega> \<in> space P"
      then show "continuous_on {0..T} (\<lambda>s. fst (\<omega> s))"
        by (rule path_sets_fst_continuous[OF setsP])
    qed
  qed
  have posAE: "AE \<omega> in P. 0 < \<theta>' \<omega>"
    using stc cwAE
  proof eventually_elim
    case (elim \<omega>)
    have "dist (fst (\<omega> 0)) x < \<epsilon>" using elim eps0 by simp
    then have "0 < pball_exit T x \<epsilon> \<omega>"
      using elim by (intro pball_exit_pos[OF T]) auto
    then show ?case unfolding \<theta>'_def using t0 by simp
  qed
  have inball: "AE \<omega> in P. dist (?Xf \<omega>) x \<le> \<epsilon>"
    using stc cwAE
  proof eventually_elim
    case (elim \<omega>)
    have "dist (fst (\<omega> 0)) x < \<epsilon>" using elim eps0 by simp
    then show ?case
      using elim
      by (intro pball_exit_stays_cball[OF T0 _ _ th0' thle]) auto
  qed
  have key: "AE \<omega> in P. 0 \<le> \<theta>' \<omega> + q \<bullet> (?V \<omega>)
      + ((?V \<omega>) \<bullet> (M *v (?V \<omega>))) / 2"
    using dpp inball
  proof eventually_elim
    case (elim \<omega>)
    have "dist (?Xf \<omega>) x \<le> ebar" using elim(2) epseb by simp
    then have "u (?Xf \<omega>) \<le> u x + q \<bullet> (?V \<omega>)
        + ((?V \<omega>) \<bullet> (M *v (?V \<omega>))) / 2"
      unfolding u_def by (rule touch)
    with elim(1) show ?case by linarith
  qed
  \<comment> \<open>moments at the stopping time\<close>
  define EY where "EY = (\<integral>\<omega>. ?Yf \<omega> \<partial>P)"
  define et where "et = (\<integral>\<omega>. \<theta>' \<omega> \<partial>P)"
  have ith: "integrable P \<theta>'"
    by (rule PP.integrable_const_bound[of _ T])
      (auto simp: thP' th0' thT')
  have et0: "0 < et"
    unfolding et_def
    by (rule integral_pos_of_AE_pos[OF PP.prob_space_axioms ith posAE])
  have ett: "et \<le> t"
    unfolding et_def
    using integral_mono_AE[OF ith PP.integrable_const, of t] tht
    by (simp add: PP.prob_space)
  have iY: "integrable P ?Yf"
    by (rule exit_class_Y_stopped_integrable[OF T0 L0 P st' thM'])
  have bmem: "(1 / et) *\<^sub>R EY \<in> sconstraint k L"
    unfolding et_def EY_def
    by (rule exit_class_Y_stopped_mean_sconstraint
        [OF T L0 P st' thM' posAE])
  define b where "b = (1 / et) *\<^sub>R EY"
  have EYb: "EY = et *\<^sub>R b" unfolding b_def using et0 by simp
  \<comment> \<open>the value inequality\<close>
  have ilin: "integrable P (\<lambda>\<omega>. q \<bullet> (?V \<omega>))"
    by (rule exit_class_stopped_moments(3)[OF T L0 P st' thM'])
  have Elin: "(\<integral>\<omega>. q \<bullet> (?V \<omega>) \<partial>P) = 0"
    by (rule exit_class_stopped_moments(4)[OF T L0 P st' thM'])
  have iquad: "integrable P (\<lambda>\<omega>. (?V \<omega>) \<bullet> (M *v (?V \<omega>)))"
    by (rule exit_class_stopped_moments(5)[OF T L0 P st' thM'])
  have Equad: "(\<integral>\<omega>. (?V \<omega>) \<bullet> (M *v (?V \<omega>)) \<partial>P) = trace (M ** EY)"
    unfolding EY_def
    by (rule exit_class_stopped_moments(6)[OF T L0 P st' thM'])
  have bl2: "bounded_linear (\<lambda>r :: real. r / 2)"
    unfolding linear_conv_bounded_linear[symmetric]
    by (intro linearI) (simp_all add: field_simps)
  have ihalf: "integrable P (\<lambda>\<omega>. ((?V \<omega>) \<bullet> (M *v (?V \<omega>))) / 2)"
    by (rule integrable_bounded_linear[OF bl2 iquad])
  have Ehalf: "(\<integral>\<omega>. ((?V \<omega>) \<bullet> (M *v (?V \<omega>))) / 2 \<partial>P)
      = trace (M ** EY) / 2"
    using integral_of_bounded_linear[OF bl2 iquad] Equad by simp
  have w: "- trace (M ** b) / 2 \<le> 1"
  proof -
    have iA: "integrable P (\<lambda>\<omega>. \<theta>' \<omega> + q \<bullet> (?V \<omega>))"
      by (intro Bochner_Integration.integrable_add ith ilin)
    have "0 \<le> (\<integral>\<omega>. \<theta>' \<omega> + q \<bullet> (?V \<omega>)
        + ((?V \<omega>) \<bullet> (M *v (?V \<omega>))) / 2 \<partial>P)"
      by (rule integral_nonneg_AE) (use key in \<open>auto elim: eventually_mono\<close>)
    also have "(\<integral>\<omega>. \<theta>' \<omega> + q \<bullet> (?V \<omega>)
        + ((?V \<omega>) \<bullet> (M *v (?V \<omega>))) / 2 \<partial>P)
        = et + trace (M ** EY) / 2"
      using Bochner_Integration.integral_add[OF iA ihalf]
        Bochner_Integration.integral_add[OF ith ilin] Elin Ehalf
      by (simp add: et_def)
    finally have ge: "0 \<le> et + trace (M ** EY) / 2" .
    have trb: "trace (M ** EY) = et * trace (M ** b)"
      by (subst EYb) (rule trace_mult_scaleR)
    have "0 \<le> et * (1 + trace (M ** b) / 2)"
      using ge trb by (simp add: field_simps)
    then have "0 \<le> 1 + trace (M ** b) / 2"
      using et0 by (simp add: zero_le_mult_iff)
    then show ?thesis by simp
  qed
  \<comment> \<open>the martingale increment and its moments\<close>
  define W where "W = (\<lambda>\<omega> :: 'n pairpath. q \<bullet> (?V \<omega>))"
  have Wint: "integrable P W" unfolding W_def by (rule ilin)
  have Wmean: "(\<integral>\<omega>. W \<omega> \<partial>P) = 0" unfolding W_def by (rule Elin)
  have Wm: "W \<in> borel_measurable P"
    by (rule borel_measurable_integrable[OF Wint])
  have W2int: "integrable P (\<lambda>\<omega>. (W \<omega>)\<^sup>2)"
    unfolding W_def
    by (rule exit_class_stopped_var(1)[OF T L0 P st' thM'])
  define s where "s = (\<integral>\<omega>. (W \<omega>)\<^sup>2 \<partial>P)"
  have svar: "s = q \<bullet> (EY *v q)"
    unfolding s_def W_def EY_def
    by (rule exit_class_stopped_var(2)[OF T L0 P st' thM'])
  have s0: "0 \<le> s"
    unfolding s_def by (rule integral_nonneg_AE) auto
  have Wabs: "AE \<omega> in P. \<bar>W \<omega>\<bar> \<le> nq * \<epsilon>"
    using inball
  proof (rule eventually_mono)
    fix \<omega> :: "'n pairpath"
    assume h: "dist (?Xf \<omega>) x \<le> \<epsilon>"
    have "\<bar>W \<omega>\<bar> \<le> norm q * norm (?V \<omega>)"
      unfolding W_def by (rule Cauchy_Schwarz_ineq2)
    also have "norm (?V \<omega>) = dist (?Xf \<omega>) x" by (simp add: dist_norm)
    also have "norm q * dist (?Xf \<omega>) x \<le> norm q * \<epsilon>"
      by (rule mult_left_mono[OF h norm_ge_zero])
    finally show "\<bar>W \<omega>\<bar> \<le> nq * \<epsilon>" unfolding nq_def .
  qed
  \<comment> \<open>the negative part is small\<close>
  have negbnd: "AE \<omega> in P. max (- W \<omega>) 0 \<le> t + Cm * \<epsilon>\<^sup>2 / 2"
    using key inball
  proof eventually_elim
    case (elim \<omega>)
    have q1: "\<bar>(?V \<omega>) \<bullet> (M *v (?V \<omega>))\<bar> \<le> Cm * \<epsilon>\<^sup>2"
    proof -
      have nv2: "(norm (?V \<omega>))\<^sup>2 \<le> \<epsilon>\<^sup>2"
        using elim(2) by (intro power_mono) (auto simp: dist_norm)
      have "\<bar>(?V \<omega>) \<bullet> (M *v (?V \<omega>))\<bar> \<le> Cm * (norm (?V \<omega>))\<^sup>2"
        unfolding Cm_def by (rule quadform_abs_le)
      also have "\<dots> \<le> Cm * \<epsilon>\<^sup>2"
        by (rule mult_left_mono[OF nv2 Cm0])
      finally show ?thesis .
    qed
    have "- W \<omega> \<le> \<theta>' \<omega> + ((?V \<omega>) \<bullet> (M *v (?V \<omega>))) / 2"
      using elim(1) unfolding W_def by linarith
    also have "\<dots> \<le> t + Cm * \<epsilon>\<^sup>2 / 2"
      using tht[of \<omega>] q1 by linarith
    finally have h: "- W \<omega> \<le> t + Cm * \<epsilon>\<^sup>2 / 2" .
    have "0 \<le> t + Cm * \<epsilon>\<^sup>2 / 2" using t0 Cm0 by simp
    with h show ?case by simp
  qed
  have nqe0: "0 \<le> nq * \<epsilon>" using nq0 eps0 by simp
  have inegint: "integrable P (\<lambda>\<omega>. max (- W \<omega>) 0)"
    by (rule PP.integrable_const_bound[of _ "nq * \<epsilon>"])
      (use Wabs Wm nqe0 in \<open>auto elim: eventually_mono\<close>)
  have iposint: "integrable P (\<lambda>\<omega>. max (W \<omega>) 0)"
    by (rule PP.integrable_const_bound[of _ "nq * \<epsilon>"])
      (use Wabs Wm nqe0 in \<open>auto elim: eventually_mono\<close>)
  have iabs: "integrable P (\<lambda>\<omega>. \<bar>W \<omega>\<bar>)"
    by (rule integrable_abs[OF Wint])
  have negE: "(\<integral>\<omega>. max (- W \<omega>) 0 \<partial>P) \<le> t + Cm * \<epsilon>\<^sup>2 / 2"
    using integral_mono_AE[OF inegint PP.integrable_const negbnd]
    by (simp add: PP.prob_space)
  have halfabs: "(\<integral>\<omega>. \<bar>W \<omega>\<bar> \<partial>P) = 2 * (\<integral>\<omega>. max (- W \<omega>) 0 \<partial>P)"
  proof -
    have d1: "(\<lambda>\<omega>. W \<omega>) = (\<lambda>\<omega>. max (W \<omega>) 0 - max (- W \<omega>) 0)"
      by (rule ext) (simp add: max_def)
    have d2: "(\<lambda>\<omega>. \<bar>W \<omega>\<bar>) = (\<lambda>\<omega>. max (W \<omega>) 0 + max (- W \<omega>) 0)"
      by (rule ext) (simp add: max_def abs_if)
    have "(\<integral>\<omega>. W \<omega> \<partial>P)
        = (\<integral>\<omega>. max (W \<omega>) 0 \<partial>P) - (\<integral>\<omega>. max (- W \<omega>) 0 \<partial>P)"
      by (subst d1) (rule Bochner_Integration.integral_diff[OF iposint inegint])
    with Wmean have posneg:
      "(\<integral>\<omega>. max (W \<omega>) 0 \<partial>P) = (\<integral>\<omega>. max (- W \<omega>) 0 \<partial>P)"
      by simp
    have "(\<integral>\<omega>. \<bar>W \<omega>\<bar> \<partial>P)
        = (\<integral>\<omega>. max (W \<omega>) 0 \<partial>P) + (\<integral>\<omega>. max (- W \<omega>) 0 \<partial>P)"
      unfolding d2 by (rule Bochner_Integration.integral_add[OF iposint inegint])
    then show ?thesis using posneg by simp
  qed
  \<comment> \<open>anti-concentration from boundedness\<close>
  define A where "A = {\<omega> \<in> space P. sqrt (s / 2) \<le> \<bar>W \<omega>\<bar>}"
  have Am: "A \<in> sets P" unfolding A_def using Wm by measurable
  have W2b: "AE \<omega> in P. (W \<omega>)\<^sup>2 \<le> (nq * \<epsilon>)\<^sup>2"
    using Wabs
  proof (rule eventually_mono)
    fix \<omega> assume h: "\<bar>W \<omega>\<bar> \<le> nq * \<epsilon>"
    have "\<bar>W \<omega>\<bar>\<^sup>2 \<le> (nq * \<epsilon>)\<^sup>2" by (rule power_mono[OF h abs_ge_zero])
    then show "(W \<omega>)\<^sup>2 \<le> (nq * \<epsilon>)\<^sup>2" by simp
  qed
  have W2A_int: "integrable P (\<lambda>\<omega>. (W \<omega>)\<^sup>2 * indicat_real A \<omega>)"
  proof (rule PP.integrable_const_bound[of _ "(nq * \<epsilon>)\<^sup>2"])
    show "AE \<omega> in P. norm ((W \<omega>)\<^sup>2 * indicat_real A \<omega>) \<le> (nq * \<epsilon>)\<^sup>2"
      using W2b
    proof (rule eventually_mono)
      fix \<omega> assume h: "(W \<omega>)\<^sup>2 \<le> (nq * \<epsilon>)\<^sup>2"
      have "(W \<omega>)\<^sup>2 * indicat_real A \<omega> \<le> (W \<omega>)\<^sup>2 * 1"
        by (intro mult_left_mono) (auto simp: indicator_def)
      then show "norm ((W \<omega>)\<^sup>2 * indicat_real A \<omega>) \<le> (nq * \<epsilon>)\<^sup>2"
        using h by (auto simp: abs_mult indicator_def)
    qed
    show "(\<lambda>\<omega>. (W \<omega>)\<^sup>2 * indicat_real A \<omega>) \<in> borel_measurable P"
      using Wm Am by measurable
  qed
  have W2Ac_int: "integrable P
      (\<lambda>\<omega>. (W \<omega>)\<^sup>2 * indicat_real (space P - A) \<omega>)"
  proof (rule PP.integrable_const_bound[of _ "(nq * \<epsilon>)\<^sup>2"])
    show "AE \<omega> in P. norm ((W \<omega>)\<^sup>2 * indicat_real (space P - A) \<omega>)
        \<le> (nq * \<epsilon>)\<^sup>2"
      using W2b
    proof (rule eventually_mono)
      fix \<omega> assume h: "(W \<omega>)\<^sup>2 \<le> (nq * \<epsilon>)\<^sup>2"
      have "(W \<omega>)\<^sup>2 * indicat_real (space P - A) \<omega> \<le> (W \<omega>)\<^sup>2 * 1"
        by (intro mult_left_mono) (auto simp: indicator_def)
      then show "norm ((W \<omega>)\<^sup>2 * indicat_real (space P - A) \<omega>) \<le> (nq * \<epsilon>)\<^sup>2"
        using h by (auto simp: abs_mult indicator_def)
    qed
    show "(\<lambda>\<omega>. (W \<omega>)\<^sup>2 * indicat_real (space P - A) \<omega>) \<in> borel_measurable P"
      using Wm Am by measurable
  qed
  have s_split: "s = (\<integral>\<omega>. (W \<omega>)\<^sup>2 * indicat_real A \<omega> \<partial>P)
      + (\<integral>\<omega>. (W \<omega>)\<^sup>2 * indicat_real (space P - A) \<omega> \<partial>P)"
  proof -
    have "s = (\<integral>\<omega>. (W \<omega>)\<^sup>2 * indicat_real A \<omega>
        + (W \<omega>)\<^sup>2 * indicat_real (space P - A) \<omega> \<partial>P)"
      unfolding s_def
      by (rule Bochner_Integration.integral_cong[OF refl])
        (auto simp: indicator_def)
    also have "\<dots> = (\<integral>\<omega>. (W \<omega>)\<^sup>2 * indicat_real A \<omega> \<partial>P)
        + (\<integral>\<omega>. (W \<omega>)\<^sup>2 * indicat_real (space P - A) \<omega> \<partial>P)"
      by (rule Bochner_Integration.integral_add[OF W2A_int W2Ac_int])
    finally show ?thesis .
  qed
  have EAc_le: "(\<integral>\<omega>. (W \<omega>)\<^sup>2 * indicat_real (space P - A) \<omega> \<partial>P) \<le> s / 2"
  proof -
    have ptw: "AE \<omega> in P. (W \<omega>)\<^sup>2 * indicat_real (space P - A) \<omega> \<le> s / 2"
    proof (rule eventually_mono[OF AE_space])
      fix \<omega> assume sp: "\<omega> \<in> space P"
      show "(W \<omega>)\<^sup>2 * indicat_real (space P - A) \<omega> \<le> s / 2"
      proof (cases "\<omega> \<in> A")
        case True
        then show ?thesis using s0 by (simp add: indicator_def)
      next
        case False
        then have "\<bar>W \<omega>\<bar> \<le> sqrt (s / 2)"
          using sp unfolding A_def by auto
        then have "\<bar>W \<omega>\<bar>\<^sup>2 \<le> (sqrt (s / 2))\<^sup>2"
          by (rule power_mono[OF _ abs_ge_zero])
        then have "(W \<omega>)\<^sup>2 \<le> s / 2" using s0 by simp
        then show ?thesis
          using sp False by (simp add: indicator_def)
      qed
    qed
    have "(\<integral>\<omega>. (W \<omega>)\<^sup>2 * indicat_real (space P - A) \<omega> \<partial>P)
        \<le> (\<integral>\<omega>. s / 2 \<partial>P)"
      by (rule integral_mono_AE[OF W2Ac_int PP.integrable_const ptw])
    then show ?thesis by (simp add: PP.prob_space)
  qed
  have indA_int: "integrable P (indicat_real A)"
    by (rule integrable_real_indicator[OF Am]) (simp add: PP.emeasure_eq_measure)
  have indA_E: "(\<integral>\<omega>. indicat_real A \<omega> \<partial>P) = PP.prob A"
    using Am by simp
  have EA_le: "(\<integral>\<omega>. (W \<omega>)\<^sup>2 * indicat_real A \<omega> \<partial>P)
      \<le> (nq * \<epsilon>)\<^sup>2 * PP.prob A"
  proof -
    have ptw: "AE \<omega> in P. (W \<omega>)\<^sup>2 * indicat_real A \<omega>
        \<le> (nq * \<epsilon>)\<^sup>2 * indicat_real A \<omega>"
      using W2b
      by (rule eventually_mono) (auto intro: mult_right_mono simp: indicator_def)
    have "(\<integral>\<omega>. (W \<omega>)\<^sup>2 * indicat_real A \<omega> \<partial>P)
        \<le> (\<integral>\<omega>. (nq * \<epsilon>)\<^sup>2 * indicat_real A \<omega> \<partial>P)"
      by (rule integral_mono_AE[OF W2A_int integrable_cmult[OF indA_int] ptw])
    also have "\<dots> = (nq * \<epsilon>)\<^sup>2 * PP.prob A"
      using integral_cmult[OF indA_int] indA_E by simp
    finally show ?thesis .
  qed
  have probA: "s / 2 \<le> (nq * \<epsilon>)\<^sup>2 * PP.prob A"
    using s_split EAc_le EA_le by linarith
  have EabsA: "sqrt (s / 2) * PP.prob A \<le> (\<integral>\<omega>. \<bar>W \<omega>\<bar> \<partial>P)"
  proof -
    have ptw: "AE \<omega> in P. sqrt (s / 2) * indicat_real A \<omega> \<le> \<bar>W \<omega>\<bar>"
    proof (rule eventually_mono[OF AE_space])
      fix \<omega> assume "\<omega> \<in> space P"
      show "sqrt (s / 2) * indicat_real A \<omega> \<le> \<bar>W \<omega>\<bar>"
        unfolding A_def by (auto simp: indicator_def)
    qed
    have "sqrt (s / 2) * PP.prob A
        = (\<integral>\<omega>. sqrt (s / 2) * indicat_real A \<omega> \<partial>P)"
      using integral_cmult[OF indA_int] indA_E by simp
    also have "\<dots> \<le> (\<integral>\<omega>. \<bar>W \<omega>\<bar> \<partial>P)"
      by (rule integral_mono_AE[OF integrable_cmult[OF indA_int] iabs ptw])
    finally show ?thesis .
  qed
  \<comment> \<open>the contradiction\<close>
  have concl: "q \<bullet> (b *v q) < \<epsilon>\<^sub>0"
  proof (rule ccontr)
    assume "\<not> q \<bullet> (b *v q) < \<epsilon>\<^sub>0"
    then have con: "\<epsilon>\<^sub>0 \<le> q \<bullet> (b *v q)" by simp
    have sEq: "s = et * (q \<bullet> (b *v q))"
    proof -
      have "EY *v q = et *\<^sub>R (b *v q)"
        by (subst EYb) (simp add: scaleR_matrix_vector)
      then have "q \<bullet> (EY *v q) = et * (q \<bullet> (b *v q))"
        by simp
      then show ?thesis using svar by simp
    qed
    \<comment> \<open>the exit before \<open>t\<close> has probability at most \<open>1/2\<close>\<close>
    have dq: "AE \<omega> in P. \<forall>s' t'. 0 \<le> s' \<longrightarrow> s' < t' \<longrightarrow> t' \<le> T \<longrightarrow>
        (1 / (t' - s')) *\<^sub>R (snd (\<omega> t') - snd (\<omega> s')) \<in> sconstraint k L"
      using P unfolding exit_class_def by blast
    have trYbnd: "AE \<omega> in P. trace (?Yf \<omega>) \<le> n' * n' * L * \<theta>' \<omega>"
      using stc dq posAE
    proof eventually_elim
      case (elim \<omega>)
      have mem: "(1 / \<theta>' \<omega>) *\<^sub>R ?Yf \<omega> \<in> sconstraint k L"
      proof -
        have "(1 / (\<theta>' \<omega> - 0)) *\<^sub>R (snd (\<omega> (\<theta>' \<omega>)) - snd (\<omega> 0))
            \<in> sconstraint k L"
          using elim thT'[of \<omega>] by blast
        then show ?thesis using elim by simp
      qed
      have trsc: "trace ((1 / \<theta>' \<omega>) *\<^sub>R ?Yf \<omega>) \<le> n' * (n' * L)"
        using sconstraint_trace_le[OF L0 mem] by (simp add: n'_def)
      have t0': "0 < \<theta>' \<omega>" using elim by simp
      have "trace (?Yf \<omega>) = \<theta>' \<omega> * trace ((1 / \<theta>' \<omega>) *\<^sub>R ?Yf \<omega>)"
      proof -
        have "?Yf \<omega> = \<theta>' \<omega> *\<^sub>R ((1 / \<theta>' \<omega>) *\<^sub>R ?Yf \<omega>)"
          using t0' by simp
        then show ?thesis
          by (metis trace_scaleR)
      qed
      also have "\<dots> \<le> \<theta>' \<omega> * (n' * (n' * L))"
        using trsc t0' by (intro mult_left_mono) auto
      finally show ?case by (simp add: algebra_simps)
    qed
    have itrY: "integrable P (\<lambda>\<omega>. trace (?Yf \<omega>))"
      by (rule integrable_bounded_linear[OF bounded_linear_trace iY])
    have EtrY: "trace EY \<le> n' * n' * L * et"
    proof -
      have "trace EY = (\<integral>\<omega>. trace (?Yf \<omega>) \<partial>P)"
        unfolding EY_def
        by (rule integral_of_bounded_linear[OF bounded_linear_trace iY,
              symmetric])
      also have "\<dots> \<le> (\<integral>\<omega>. n' * n' * L * \<theta>' \<omega> \<partial>P)"
        by (rule integral_mono_AE[OF itrY integrable_cmult[OF ith] trYbnd])
      also have "\<dots> = n' * n' * L * et"
        using integral_cmult[OF ith] by (simp add: et_def)
      finally show ?thesis .
    qed
    have normsqE: "(\<integral>\<omega>. (?V \<omega>) \<bullet> (?V \<omega>) \<partial>P) = trace EY"
      unfolding EY_def
      by (rule exit_class_stopped_normsq[OF T L0 P st' thM'])
    have inormsq: "integrable P (\<lambda>\<omega>. (?V \<omega>) \<bullet> (?V \<omega>))"
    proof -
      have e: "(\<lambda>\<omega> :: 'n pairpath. (?V \<omega>) \<bullet> (?V \<omega>))
          = (\<lambda>\<omega>. (?V \<omega>) \<bullet> (mat 1 *v (?V \<omega>)))"
        by (simp add: fun_eq_iff)
      show ?thesis
        unfolding e
        by (rule exit_class_stopped_moments(5)[OF T L0 P st' thM'])
    qed
    define Ev where "Ev = {\<omega> \<in> space P. pball_exit T x \<epsilon> \<omega> < t}"
    have tauP: "pball_exit T x \<epsilon> \<in> borel_measurable P"
      unfolding measurable_cong_sets[OF setsP refl]
      by (rule pball_exit_measurable[OF T0])
    have Evm: "Ev \<in> sets P"
      unfolding Ev_def using tauP by measurable
    have chexit: "\<epsilon>\<^sup>2 * PP.prob Ev \<le> trace EY"
    proof -
      have ptw: "AE \<omega> in P. \<epsilon>\<^sup>2 * indicat_real Ev \<omega> \<le> (?V \<omega>) \<bullet> (?V \<omega>)"
        using cwAE AE_space
      proof eventually_elim
        case (elim \<omega>)
        show ?case
        proof (cases "\<omega> \<in> Ev")
          case True
          then have lt: "pball_exit T x \<epsilon> \<omega> < t" unfolding Ev_def by simp
          have th_eq: "\<theta>' \<omega> = pball_exit T x \<epsilon> \<omega>"
            unfolding \<theta>'_def using lt by (simp add: min_def)
          have ltT: "pball_exit T x \<epsilon> \<omega> < T" using lt tT by linarith
          have "fst (\<omega> (pexit T (ball x \<epsilon>) (\<lambda>s. fst (\<omega> s)))) \<notin> ball x \<epsilon>"
            by (rule pexit_mem_of_less_T[OF T0 open_ball elim(1)])
              (use ltT in \<open>simp add: pball_exit_def\<close>)
          then have "\<epsilon> \<le> dist (?Xf \<omega>) x"
            unfolding th_eq pball_exit_def
            by (simp add: dist_commute)
          then have "\<epsilon>\<^sup>2 \<le> (dist (?Xf \<omega>) x)\<^sup>2"
            using eps0 by (intro power_mono) auto
          moreover have "(?V \<omega>) \<bullet> (?V \<omega>) = (dist (?Xf \<omega>) x)\<^sup>2"
            by (simp add: dot_square_norm dist_norm)
          ultimately show ?thesis using True by (simp add: indicator_def)
        next
          case False
          have "0 \<le> (?V \<omega>) \<bullet> (?V \<omega>)" by (rule inner_ge_zero)
          then show ?thesis using False by (simp add: indicator_def)
        qed
      qed
      have indEv_int: "integrable P (indicat_real Ev)"
        by (rule integrable_real_indicator[OF Evm])
          (simp add: PP.emeasure_eq_measure)
      have "\<epsilon>\<^sup>2 * PP.prob Ev = (\<integral>\<omega>. \<epsilon>\<^sup>2 * indicat_real Ev \<omega> \<partial>P)"
        using integral_cmult[OF indEv_int] Evm by simp
      also have "\<dots> \<le> (\<integral>\<omega>. (?V \<omega>) \<bullet> (?V \<omega>) \<partial>P)"
        by (rule integral_mono_AE[OF integrable_cmult[OF indEv_int]
              inormsq ptw])
      finally show ?thesis using normsqE by simp
    qed
    have probEv: "PP.prob Ev \<le> 1 / 2"
    proof -
      have nL0: "0 < n' * n' * L" using n'1 L1 by simp
      have "n' * n' * L * et \<le> n' * n' * L * t"
        using ett nL0 by (intro mult_left_mono) auto
      with EtrY have h1: "trace EY \<le> n' * n' * L * t" by linarith
      have n'ne: "n' \<noteq> 0" using n'1 by simp
      have Lne: "L \<noteq> 0" using L1 by simp
      have "n' * n' * L * t = \<epsilon>\<^sup>2 / 2"
        unfolding t_def \<beta>_def using n'ne Lne by (simp add: field_simps)
      with h1 chexit have h2: "\<epsilon>\<^sup>2 * PP.prob Ev \<le> \<epsilon>\<^sup>2 * (1 / 2)" by linarith
      have e20: "0 < \<epsilon>\<^sup>2" using eps0 by simp
      show ?thesis using h2 e20 by (simp add: mult_le_cancel_left)
    qed
    have etlow: "t / 2 \<le> et"
    proof -
      have ptw: "AE \<omega> in P. t * indicat_real (space P - Ev) \<omega> \<le> \<theta>' \<omega>"
      proof (rule eventually_mono[OF AE_space])
        fix \<omega> assume sp: "\<omega> \<in> space P"
        show "t * indicat_real (space P - Ev) \<omega> \<le> \<theta>' \<omega>"
        proof (cases "\<omega> \<in> Ev")
          case True
          then show ?thesis using th0'[of \<omega>] by (simp add: indicator_def)
        next
          case False
          then have "t \<le> pball_exit T x \<epsilon> \<omega>"
            using sp unfolding Ev_def by auto
          then have "\<theta>' \<omega> = t" unfolding \<theta>'_def by (simp add: min_def)
          then show ?thesis using sp False by (simp add: indicator_def)
        qed
      qed
      have indC_int: "integrable P (indicat_real (space P - Ev))"
        by (rule integrable_real_indicator)
          (auto simp: PP.emeasure_eq_measure sets.compl_sets Evm)
      have "t * PP.prob (space P - Ev)
          = (\<integral>\<omega>. t * indicat_real (space P - Ev) \<omega> \<partial>P)"
        using integral_cmult[OF indC_int] sets.compl_sets[OF Evm] by simp
      also have "\<dots> \<le> et"
        unfolding et_def
        by (rule integral_mono_AE[OF integrable_cmult[OF indC_int] ith ptw])
      finally have h: "t * PP.prob (space P - Ev) \<le> et" .
      have "PP.prob (space P - Ev) = 1 - PP.prob Ev"
        by (rule PP.prob_compl[OF Evm])
      then have "1 / 2 \<le> PP.prob (space P - Ev)" using probEv by simp
      then have "t * (1 / 2) \<le> t * PP.prob (space P - Ev)"
        using t0 by (intro mult_left_mono) auto
      then show ?thesis using h by simp
    qed
    have slow: "\<epsilon>\<^sub>0 * (t / 2) \<le> s"
    proof -
      have "\<epsilon>\<^sub>0 * (t / 2) \<le> (q \<bullet> (b *v q)) * et"
        using con etlow e0 t0 et0 by (intro mult_mono) auto
      then show ?thesis using sEq by (simp add: algebra_simps)
    qed
    \<comment> \<open>assemble the numeric contradiction\<close>
    have EnegLow: "sqrt (s / 2) * s / (4 * nq\<^sup>2 * \<epsilon>\<^sup>2)
        \<le> (\<integral>\<omega>. max (- W \<omega>) 0 \<partial>P)"
    proof -
      have pA: "s / 2 / (nq * \<epsilon>)\<^sup>2 \<le> PP.prob A"
        using probA nq0 eps0 by (simp add: field_simps power2_eq_square)
      have sq0: "0 \<le> sqrt (s / 2)"
        using s0 by (simp add: real_sqrt_ge_zero)
      have "sqrt (s / 2) * (s / 2 / (nq * \<epsilon>)\<^sup>2)
          \<le> sqrt (s / 2) * PP.prob A"
        by (intro mult_left_mono pA sq0)
      also have "\<dots> \<le> (\<integral>\<omega>. \<bar>W \<omega>\<bar> \<partial>P)" by (rule EabsA)
      also have "\<dots> = 2 * (\<integral>\<omega>. max (- W \<omega>) 0 \<partial>P)" by (rule halfabs)
      finally have "sqrt (s / 2) * (s / 2 / (nq * \<epsilon>)\<^sup>2)
          \<le> 2 * (\<integral>\<omega>. max (- W \<omega>) 0 \<partial>P)" .
      then show ?thesis
        using nq0 eps0 by (simp add: field_simps
            power2_eq_square)
    qed
    have upper: "sqrt (s / 2) * s \<le> 4 * nq\<^sup>2 * \<epsilon>\<^sup>2 * (\<beta> + Cm / 2) * \<epsilon>\<^sup>2"
    proof -
      have "sqrt (s / 2) * s / (4 * nq\<^sup>2 * \<epsilon>\<^sup>2) \<le> t + Cm * \<epsilon>\<^sup>2 / 2"
        using EnegLow negE by linarith
      also have "t + Cm * \<epsilon>\<^sup>2 / 2 = (\<beta> + Cm / 2) * \<epsilon>\<^sup>2"
        unfolding t_def by (simp add: algebra_simps)
      finally have h: "sqrt (s / 2) * s / (4 * nq\<^sup>2 * \<epsilon>\<^sup>2)
          \<le> (\<beta> + Cm / 2) * \<epsilon>\<^sup>2" .
      have d0: "0 < 4 * nq\<^sup>2 * \<epsilon>\<^sup>2"
        using nq0 eps0 by (simp add: power2_eq_square)
      show ?thesis
        using h d0 by (simp add: pos_divide_le_eq algebra_simps)
    qed
    have lower: "sqrt \<epsilon>\<^sub>0 * sqrt \<beta> * \<epsilon>\<^sub>0 * \<beta> * \<epsilon> ^ 3 / 4 \<le> sqrt (s / 2) * s"
    proof -
      have s0': "\<epsilon>\<^sub>0 * t / 2 \<le> s" using slow by simp
      have st0: "0 \<le> \<epsilon>\<^sub>0 * t / 2" using e0 t0 by simp
      have r1: "sqrt (\<epsilon>\<^sub>0 * t / 4) \<le> sqrt (s / 2)"
        by (rule real_sqrt_le_mono) (use s0' in simp)
      have r2: "sqrt (\<epsilon>\<^sub>0 * t / 4) = sqrt (\<epsilon>\<^sub>0 * t) / 2"
        by (simp add: real_sqrt_divide)
      have r3: "sqrt (\<epsilon>\<^sub>0 * t) = sqrt \<epsilon>\<^sub>0 * sqrt \<beta> * \<epsilon>"
      proof -
        have st: "sqrt t = sqrt \<beta> * \<epsilon>"
        proof -
          have "sqrt t = sqrt \<beta> * sqrt (\<epsilon>\<^sup>2)"
            unfolding t_def by (simp add: real_sqrt_mult)
          also have "sqrt (\<epsilon>\<^sup>2) = \<bar>\<epsilon>\<bar>" by (rule real_sqrt_abs)
          also have "\<bar>\<epsilon>\<bar> = \<epsilon>" using eps0 by simp
          finally show ?thesis .
        qed
        have "sqrt (\<epsilon>\<^sub>0 * t) = sqrt \<epsilon>\<^sub>0 * sqrt t"
          by (simp add: real_sqrt_mult)
        then show ?thesis using st by simp
      qed
      have f1: "sqrt (\<epsilon>\<^sub>0 * t) / 2 \<le> sqrt (s / 2)"
        using r1 r2 by simp
      have flip: "(sqrt (\<epsilon>\<^sub>0 * t) / 2) * (\<epsilon>\<^sub>0 * t / 2)
          = sqrt \<epsilon>\<^sub>0 * sqrt \<beta> * \<epsilon>\<^sub>0 * \<beta> * \<epsilon> ^ 3 / 4"
      proof -
        have e2: "\<epsilon>\<^sub>0 * t = \<epsilon>\<^sub>0 * \<beta> * \<epsilon>\<^sup>2"
          unfolding t_def by simp
        have "(sqrt (\<epsilon>\<^sub>0 * t) / 2) * (\<epsilon>\<^sub>0 * t / 2)
            = (sqrt \<epsilon>\<^sub>0 * sqrt \<beta> * \<epsilon>) * (\<epsilon>\<^sub>0 * t) / 4"
          unfolding r3 by (simp add: field_simps)
        also have "\<dots> = (sqrt \<epsilon>\<^sub>0 * sqrt \<beta> * \<epsilon>) * (\<epsilon>\<^sub>0 * \<beta> * \<epsilon>\<^sup>2) / 4"
          by (simp only: e2)
        also have "\<dots> = sqrt \<epsilon>\<^sub>0 * sqrt \<beta> * \<epsilon>\<^sub>0 * \<beta> * \<epsilon> ^ 3 / 4"
          by (simp add: power2_eq_square power3_eq_cube algebra_simps)
        finally show ?thesis .
      qed
      have "sqrt \<epsilon>\<^sub>0 * sqrt \<beta> * \<epsilon>\<^sub>0 * \<beta> * \<epsilon> ^ 3 / 4
          = (sqrt (\<epsilon>\<^sub>0 * t) / 2) * (\<epsilon>\<^sub>0 * t / 2)"
        by (rule flip[symmetric])
      also have "\<dots> \<le> sqrt (s / 2) * s"
      proof -
        have sq0: "0 \<le> sqrt (s / 2)"
          using s0 by (simp add: real_sqrt_ge_zero)
        show ?thesis by (rule mult_mono[OF f1 s0' sq0 st0])
      qed
      finally show ?thesis .
    qed
    have final: "\<epsilon>K \<le> \<epsilon>"
    proof -
      have LU: "sqrt \<epsilon>\<^sub>0 * sqrt \<beta> * \<epsilon>\<^sub>0 * \<beta> * \<epsilon> ^ 3 / 4
          \<le> 4 * nq\<^sup>2 * \<epsilon>\<^sup>2 * (\<beta> + Cm / 2) * \<epsilon>\<^sup>2"
        using lower upper by linarith
      have e30: "0 < \<epsilon> ^ 3" using eps0 by simp
      have ll: "sqrt \<epsilon>\<^sub>0 * sqrt \<beta> * \<epsilon>\<^sub>0 * \<beta> * \<epsilon> ^ 3 / 4
          = \<epsilon> ^ 3 * (sqrt \<epsilon>\<^sub>0 * sqrt \<beta> * \<epsilon>\<^sub>0 * \<beta> / 4)"
        by (simp add: algebra_simps)
      have rr: "4 * nq\<^sup>2 * \<epsilon>\<^sup>2 * (\<beta> + Cm / 2) * \<epsilon>\<^sup>2
          = \<epsilon> ^ 3 * (4 * nq\<^sup>2 * (\<beta> + Cm / 2) * \<epsilon>)"
        by (simp add: power2_eq_square power3_eq_cube algebra_simps)
      have "\<epsilon> ^ 3 * (sqrt \<epsilon>\<^sub>0 * sqrt \<beta> * \<epsilon>\<^sub>0 * \<beta> / 4)
          \<le> \<epsilon> ^ 3 * (4 * nq\<^sup>2 * (\<beta> + Cm / 2) * \<epsilon>)"
        using LU unfolding ll rr .
      then have h3: "sqrt \<epsilon>\<^sub>0 * sqrt \<beta> * \<epsilon>\<^sub>0 * \<beta> / 4
          \<le> 4 * nq\<^sup>2 * (\<beta> + Cm / 2) * \<epsilon>"
        using e30 by (simp add: mult_le_cancel_left)
      have "sqrt \<epsilon>\<^sub>0 * sqrt \<beta> * \<epsilon>\<^sub>0 * \<beta>
          \<le> 4 * (4 * nq\<^sup>2 * (\<beta> + Cm / 2) * \<epsilon>)"
        using h3 by linarith
      then have h4: "sqrt \<epsilon>\<^sub>0 * sqrt \<beta> * \<epsilon>\<^sub>0 * \<beta>
          \<le> \<epsilon> * (16 * nq\<^sup>2 * (\<beta> + Cm / 2))"
        by (simp add: algebra_simps)
      show ?thesis
        unfolding \<epsilon>K_def using den0 h4 by (simp add: pos_divide_le_eq)
    qed
    show False using final epsK eK0 by linarith
  qed
  show ?thesis using that bmem[folded b_def] w concl by blast
qed

section \<open>Compactness: an exactly orthogonal direction\<close>

theorem exit_val_touch_orth:
  fixes K :: "(real^'n::finite) set" and x q :: "real^'n" and M :: "real^'n^'n"
  assumes T: "0 < T" and L1: "1 \<le> L" and Kc: "closed K" and eb: "0 < ebar"
    and touch: "\<And>z. dist z x \<le> ebar \<Longrightarrow>
        enn2real (exit_val k L T K z)
          \<le> enn2real (exit_val k L T K x) + q \<bullet> (z - x)
            + ((z - x) \<bullet> (M *v (z - x))) / 2"
  obtains b where "b \<in> sconstraint k L" and "- trace (M ** b) / 2 \<le> 1"
    and "b *v q = 0"
proof -
  have L0: "0 \<le> L" using L1 by simp
  have ex: "\<exists>b. b \<in> sconstraint k L \<and> - trace (M ** b) / 2 \<le> 1
      \<and> q \<bullet> (b *v q) < 1 / real (Suc n)" for n :: nat
  proof -
    obtain b where "b \<in> sconstraint k L" "- trace (M ** b) / 2 \<le> 1"
      "q \<bullet> (b *v q) < 1 / real (Suc n)"
      using exit_val_touch_near_orth[OF T L1 Kc eb touch,
          where \<epsilon>\<^sub>0 = "1 / real (Suc n)"] by auto
    then show ?thesis by blast
  qed
  then obtain bs where bs: "\<And>n :: nat. bs n \<in> sconstraint k L
      \<and> - trace (M ** bs n) / 2 \<le> 1
      \<and> q \<bullet> (bs n *v q) < 1 / real (Suc n)"
    by metis
  have rng: "range bs \<subseteq> sconstraint k L" using bs by blast
  have bdd: "bounded (range bs)"
    by (rule bounded_subset[OF bounded_sconstraint[OF L0] rng])
  obtain l \<sigma> where sm: "strict_mono \<sigma>" and lim: "(bs \<circ> \<sigma>) \<longlonglongrightarrow> l"
    using bounded_imp_convergent_subsequence[OF bdd] by blast
  have inS: "(bs \<circ> \<sigma>) n \<in> sconstraint k L" for n
    using rng by (auto simp: o_def)
  have lmem: "l \<in> sconstraint k L"
    by (rule closed_sequentially[OF closed_sconstraint inS lim])
  have psd_l: "psd l"
    using lmem unfolding sconstraint_def Pi_constraint_def by auto
  \<comment> \<open>the value passes to the limit\<close>
  have trlim: "(\<lambda>n. trace (M ** bs (\<sigma> n))) \<longlonglongrightarrow> trace (M ** l)"
  proof -
    have "(\<lambda>n. trace (M ** (bs \<circ> \<sigma>) n)) \<longlonglongrightarrow> trace (M ** l)"
      by (rule bounded_linear.tendsto[OF bounded_linear_trace_mult_left lim])    then show ?thesis by (simp add: o_def)
  qed
  have w: "- trace (M ** l) / 2 \<le> 1"
  proof -
    have h1: "(\<lambda>n. - trace (M ** bs (\<sigma> n)) / 2) \<longlonglongrightarrow> - trace (M ** l) / 2"      by (intro tendsto_intros trlim) simp
    have h2: "\<exists>N. \<forall>n\<ge>N. - trace (M ** bs (\<sigma> n)) / 2 \<le> 1"
      using bs by blast
    show ?thesis by (rule LIMSEQ_le_const2[OF h1 h2])
  qed  have qlim: "(\<lambda>n. q \<bullet> (bs (\<sigma> n) *v q)) \<longlonglongrightarrow> q \<bullet> (l *v q)"
  proof -
    have "(\<lambda>n. q \<bullet> ((bs \<circ> \<sigma>) n *v q)) \<longlonglongrightarrow> q \<bullet> (l *v q)"
      by (rule bounded_linear.tendsto[OF bounded_linear_quadform lim])    then show ?thesis by (simp add: o_def)
  qed
  have qge: "0 \<le> q \<bullet> (l *v q)"
  proof (rule LIMSEQ_le_const[OF qlim])
    have "psd (bs (\<sigma> n))" for n
      using bs[of "\<sigma> n"] unfolding sconstraint_def Pi_constraint_def by auto
    then show "\<exists>N. \<forall>n\<ge>N. 0 \<le> q \<bullet> (bs (\<sigma> n) *v q)"
      unfolding psd_def by blast
  qed
  have qle: "q \<bullet> (l *v q) \<le> 0"
  proof (rule LIMSEQ_le[OF qlim])
    show "(\<lambda>n. 1 / real (Suc n)) \<longlonglongrightarrow> 0"
      using LIMSEQ_inverse_real_of_nat by (simp add: inverse_eq_divide)
    have "q \<bullet> (bs (\<sigma> n) *v q) \<le> 1 / real (Suc n)" for n
    proof -
      have "q \<bullet> (bs (\<sigma> n) *v q) < 1 / real (Suc (\<sigma> n))"
        using bs[of "\<sigma> n"] by blast
      also have "1 / real (Suc (\<sigma> n)) \<le> 1 / real (Suc n)"
        using seq_suble[OF sm, of n] by (simp add: frac_le)
      finally show ?thesis by simp
    qed
    then show "\<exists>N. \<forall>n\<ge>N. q \<bullet> (bs (\<sigma> n) *v q) \<le> 1 / real (Suc n)" by blast
  qed
  have "q \<bullet> (l *v q) = 0" using qge qle by simp
  then have "l *v q = 0" by (rule psd_kernel_eq[OF psd_l])
  then show ?thesis using that lmem w by blast
qed

section \<open>Clause (2): the subsolution property with the paper's operator\<close>

lemma feasible_trace_le:
  fixes a :: "real^'n::finite^'n" and p :: "real^'n"
  assumes a: "a \<in> feasible k L p"
  shows "trace a \<le> real CARD('n) * L"
proof -
  have "a $ i $ i \<le> L" for i
    using feasible_entry_bound[OF a, of i i] by simp
  then have "trace a \<le> (\<Sum>i\<in>(UNIV :: 'n set). L)"
    unfolding trace_def by (rule sum_mono)
  then show ?thesis by simp
qed

text \<open>The subsolution half of clause (2), for the operator of Eq. (1.9)
  itself, orthogonality constraint included.  For each test function and
  each Hessian bump \<open>\<delta>\<close>, an anti-concentration argument together with
  compactness produces a direction that kills the gradient
  (@{thm [source] exit_val_touch_orth}); the capped spectral split converts
  it into a feasible witness (@{thm [source] sconstraint_orth_feasible}),
  and \<open>\<delta> \<rightarrow> 0\<close> concludes as in the relaxed case.\<close>

theorem exit_val_visc_subsol:
  fixes K :: "(real^'n::finite) set"
  assumes T: "0 < T" and L1: "1 \<le> L" and Kc: "closed K"
    and kn: "k < CARD('n)"
  shows "visc_subsol k L (interior K) (\<lambda>z. enn2real (exit_val k L T K z))"
  unfolding visc_subsol_def
proof (intro ballI allI impI)
  fix x :: "real^'n" and \<phi> :: "real^'n \<Rightarrow> real"
    and g :: "real^'n \<Rightarrow> real^'n" and H :: "real^'n^'n"
  assume x: "x \<in> interior K"
    and tf: "test_fun_at \<phi> g H x"
    and lm: "\<exists>e>0. \<forall>z \<in> ball x e.
        enn2real (exit_val k L T K z) - \<phi> z
          \<le> enn2real (exit_val k L T K x) - \<phi> x"
  have L0: "0 \<le> L" using L1 by simp
  from lm obtain e0 where e00: "0 < e0"
    and lme: "\<And>z. z \<in> ball x e0 \<Longrightarrow>
        enn2real (exit_val k L T K z) - \<phi> z
          \<le> enn2real (exit_val k L T K x) - \<phi> x"
    by blast
  define C where "C = real CARD('n) * L"
  have n0: "0 < real CARD('n)"
    using zero_less_card_finite[where 'a = 'n] by simp
  have C0: "0 < C"
    unfolding C_def by (intro mult_pos_pos n0) (use L1 in linarith)
  have key: "ell_op k L (g x) H \<le> 1 + \<delta> * C / 2" if d0: "0 < \<delta>" for \<delta>
  proof -
    obtain r where r0: "0 < r"
      and dom: "\<And>z. z \<in> ball x r \<Longrightarrow>
          \<phi> z \<le> \<phi> x + g x \<bullet> (z - x)
            + ((z - x) \<bullet> ((H + \<delta> *\<^sub>R mat 1) *v (z - x))) / 2"
      using test_fun_quadratic_dominates[OF tf d0] by blast
    define ebar where "ebar = min e0 r / 2"
    have eb0: "0 < ebar" using e00 r0 by (simp add: ebar_def)
    have touch: "\<And>z. dist z x \<le> ebar \<Longrightarrow>
        enn2real (exit_val k L T K z)
          \<le> enn2real (exit_val k L T K x) + g x \<bullet> (z - x)
            + ((z - x) \<bullet> ((H + \<delta> *\<^sub>R mat 1) *v (z - x))) / 2"
    proof -
      fix z assume z: "dist z x \<le> ebar"
      have zin: "z \<in> ball x e0 \<inter> ball x r"
        using z e00 r0 by (auto simp: ebar_def dist_commute)
      have "enn2real (exit_val k L T K z) - \<phi> z
          \<le> enn2real (exit_val k L T K x) - \<phi> x"
        using lme zin by blast
      moreover have "\<phi> z \<le> \<phi> x + g x \<bullet> (z - x)
          + ((z - x) \<bullet> ((H + \<delta> *\<^sub>R mat 1) *v (z - x))) / 2"
        using dom zin by blast
      ultimately show "enn2real (exit_val k L T K z)
          \<le> enn2real (exit_val k L T K x) + g x \<bullet> (z - x)
            + ((z - x) \<bullet> ((H + \<delta> *\<^sub>R mat 1) *v (z - x))) / 2"
        by linarith
    qed
    obtain b where bmem: "b \<in> sconstraint k L"
      and wb: "- trace ((H + \<delta> *\<^sub>R mat 1) ** b) / 2 \<le> 1"
      and borth: "b *v (g x) = 0"
      by (rule exit_val_touch_orth[OF T L1 Kc eb0 touch])
    obtain a where afeas: "a \<in> feasible k L (g x)"
      and aval: "- trace ((H + \<delta> *\<^sub>R mat 1) ** a) / 2
          \<le> - trace ((H + \<delta> *\<^sub>R mat 1) ** b) / 2"
      by (rule sconstraint_orth_feasible[OF kn L1 bmem borth])
    have wa: "- trace ((H + \<delta> *\<^sub>R mat 1) ** a) / 2 \<le> 1"
      using aval wb by linarith
    have split: "trace ((H + \<delta> *\<^sub>R mat 1) ** a) = trace (H ** a) + \<delta> * trace a"
    proof -
      have "(H + \<delta> *\<^sub>R mat 1) ** a = H ** a + (\<delta> *\<^sub>R mat 1) ** a"
        by (rule matrix_add_rdistrib)
      moreover have "(\<delta> *\<^sub>R mat 1) ** a = \<delta> *\<^sub>R a"
        by (simp add: scaleR_matrix_mult)
      ultimately have e1: "trace ((H + \<delta> *\<^sub>R mat 1) ** a)
          = trace (H ** a + \<delta> *\<^sub>R a)" by simp
      have e2: "trace (H ** a + \<delta> *\<^sub>R a) = trace (H ** a) + trace (\<delta> *\<^sub>R a)"
        by (simp add: trace_def sum.distrib)
      have e3: "trace (\<delta> *\<^sub>R a) = \<delta> * trace a" by (rule trace_scaleR)
      from e1 e2 e3 show ?thesis by simp
    qed
    have tra: "trace a \<le> C"
      unfolding C_def by (rule feasible_trace_le[OF afeas])
    have "- trace (H ** a) / 2 \<le> 1 + \<delta> * trace a / 2"
      using wa split by (simp add: field_simps)
    also have "\<dots> \<le> 1 + \<delta> * C / 2"
      using tra d0 by (simp add: mult_left_mono)
    finally have wH: "- trace (H ** a) / 2 \<le> 1 + \<delta> * C / 2" .
    show ?thesis by (rule ell_op_le_of_witness[OF afeas wH])
  qed
  show "ell_op k L (g x) H \<le> 1"
  proof (rule field_le_epsilon)
    fix e :: real assume e0': "0 < e"
    have d0: "0 < 2 * e / C" using e0' C0 by simp
    have "ell_op k L (g x) H \<le> 1 + (2 * e / C) * C / 2"
      by (rule key[OF d0])
    also have "\<dots> = 1 + e" using C0 by (simp add: field_simps)
    finally show "ell_op k L (g x) H \<le> 1 + e" .
  qed
qed

section \<open>The boundary subsolution clause for \<open>exit_val\<close>\<close>

text \<open>The proof of \<open>exit_val_visc_subsol\<close> does not use \<open>x \<in> interior K\<close>: it
  is driven by the local touching, and \<open>exit_val_touch_orth\<close> is indifferent
  to where \<open>x\<close> sits.  So the subsolution property holds locally on any \<open>\<Omega>\<close>.\<close>

theorem exit_val_visc_subsol_any:
  fixes K :: "(real^'n::finite) set"
  assumes T: "0 < T" and L1: "1 \<le> L" and Kc: "closed K"
    and kn: "k < CARD('n)"
  shows "visc_subsol k L \<Omega> (\<lambda>z. enn2real (exit_val k L T K z))"
  unfolding visc_subsol_def
proof (intro ballI allI impI)
  fix x :: "real^'n" and \<phi> :: "real^'n \<Rightarrow> real"
    and g :: "real^'n \<Rightarrow> real^'n" and H :: "real^'n^'n"
  assume tf: "test_fun_at \<phi> g H x"
    and lm: "\<exists>e>0. \<forall>z \<in> ball x e.
        enn2real (exit_val k L T K z) - \<phi> z
          \<le> enn2real (exit_val k L T K x) - \<phi> x"
  have L0: "0 \<le> L" using L1 by simp
  from lm obtain e0 where e00: "0 < e0"
    and lme: "\<And>z. z \<in> ball x e0 \<Longrightarrow>
        enn2real (exit_val k L T K z) - \<phi> z
          \<le> enn2real (exit_val k L T K x) - \<phi> x"
    by blast
  define C where "C = real CARD('n) * L"
  have n0: "0 < real CARD('n)"
    using zero_less_card_finite[where 'a = 'n] by simp
  have C0: "0 < C"
    unfolding C_def by (intro mult_pos_pos n0) (use L1 in linarith)
  have key: "ell_op k L (g x) H \<le> 1 + \<delta> * C / 2" if d0: "0 < \<delta>" for \<delta>
  proof -
    obtain r where r0: "0 < r"
      and dom: "\<And>z. z \<in> ball x r \<Longrightarrow>
          \<phi> z \<le> \<phi> x + g x \<bullet> (z - x)
            + ((z - x) \<bullet> ((H + \<delta> *\<^sub>R mat 1) *v (z - x))) / 2"
      using test_fun_quadratic_dominates[OF tf d0] by blast
    define ebar where "ebar = min e0 r / 2"
    have eb0: "0 < ebar" using e00 r0 by (simp add: ebar_def)
    have touch: "\<And>z. dist z x \<le> ebar \<Longrightarrow>
        enn2real (exit_val k L T K z)
          \<le> enn2real (exit_val k L T K x) + g x \<bullet> (z - x)
            + ((z - x) \<bullet> ((H + \<delta> *\<^sub>R mat 1) *v (z - x))) / 2"
    proof -
      fix z assume z: "dist z x \<le> ebar"
      have zin: "z \<in> ball x e0 \<inter> ball x r"
        using z e00 r0 by (auto simp: ebar_def dist_commute)
      have "enn2real (exit_val k L T K z) - \<phi> z
          \<le> enn2real (exit_val k L T K x) - \<phi> x"
        using lme zin by blast
      moreover have "\<phi> z \<le> \<phi> x + g x \<bullet> (z - x)
          + ((z - x) \<bullet> ((H + \<delta> *\<^sub>R mat 1) *v (z - x))) / 2"
        using dom zin by blast
      ultimately show "enn2real (exit_val k L T K z)
          \<le> enn2real (exit_val k L T K x) + g x \<bullet> (z - x)
            + ((z - x) \<bullet> ((H + \<delta> *\<^sub>R mat 1) *v (z - x))) / 2"
        by linarith
    qed
    obtain b where bmem: "b \<in> sconstraint k L"
      and wb: "- trace ((H + \<delta> *\<^sub>R mat 1) ** b) / 2 \<le> 1"
      and borth: "b *v (g x) = 0"
      by (rule exit_val_touch_orth[OF T L1 Kc eb0 touch])
    obtain a where afeas: "a \<in> feasible k L (g x)"
      and aval: "- trace ((H + \<delta> *\<^sub>R mat 1) ** a) / 2
          \<le> - trace ((H + \<delta> *\<^sub>R mat 1) ** b) / 2"
      by (rule sconstraint_orth_feasible[OF kn L1 bmem borth])
    have wa: "- trace ((H + \<delta> *\<^sub>R mat 1) ** a) / 2 \<le> 1"
      using aval wb by linarith
    have split: "trace ((H + \<delta> *\<^sub>R mat 1) ** a) = trace (H ** a) + \<delta> * trace a"
    proof -
      have "(H + \<delta> *\<^sub>R mat 1) ** a = H ** a + (\<delta> *\<^sub>R mat 1) ** a"
        by (rule matrix_add_rdistrib)
      moreover have "(\<delta> *\<^sub>R mat 1) ** a = \<delta> *\<^sub>R a"
        by (simp add: scaleR_matrix_mult)
      ultimately have e1: "trace ((H + \<delta> *\<^sub>R mat 1) ** a)
          = trace (H ** a + \<delta> *\<^sub>R a)" by simp
      have e2: "trace (H ** a + \<delta> *\<^sub>R a) = trace (H ** a) + trace (\<delta> *\<^sub>R a)"
        by (simp add: trace_def sum.distrib)
      have e3: "trace (\<delta> *\<^sub>R a) = \<delta> * trace a" by (rule trace_scaleR)
      from e1 e2 e3 show ?thesis by simp
    qed
    have tra: "trace a \<le> C"
      unfolding C_def by (rule feasible_trace_le[OF afeas])
    have "- trace (H ** a) / 2 \<le> 1 + \<delta> * trace a / 2"
      using wa split by (simp add: field_simps)
    also have "\<dots> \<le> 1 + \<delta> * C / 2"
      using tra d0 by (simp add: mult_left_mono)
    finally have wH: "- trace (H ** a) / 2 \<le> 1 + \<delta> * C / 2" .
    show ?thesis by (rule ell_op_le_of_witness[OF afeas wH])
  qed
  show "ell_op k L (g x) H \<le> 1"
  proof (rule field_le_epsilon)
    fix e :: real assume e0': "0 < e"
    have d0: "0 < 2 * e / C" using e0' C0 by simp
    have "ell_op k L (g x) H \<le> 1 + (2 * e / C) * C / 2"
      by (rule key[OF d0])
    also have "\<dots> = 1 + e" using C0 by (simp add: field_simps)
    finally show "ell_op k L (g x) H \<le> 1 + e" .
  qed
qed

text \<open>Outside \<open>K\<close> the exit time is already zero, so the value vanishes.  This
  is what makes the gate \<open>v x > 0\<close> do its work below.\<close>

lemma exit_val_zero_outside:
  fixes K :: "(real^'n::finite) set" and z :: "real^'n"
  assumes T0: "0 \<le> T" and z: "z \<notin> K"
  shows "exit_val k L T K z = 0"
proof -
  have "exit_val k L T K z \<le> 0"
    unfolding exit_val_def
  proof (rule Sup_least)
    fix e :: ennreal
    assume "e \<in> (\<lambda>Q. ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))))
        ` exit_class k L T z"
    then obtain Q where Q: "Q \<in> exit_class k L T z"
      and e: "e = ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))" by blast
    have prob: "prob_space Q" by (rule exit_class_prob[OF Q])
    have st: "AE \<omega> in Q. fst (\<omega> 0) = z \<and> snd (\<omega> 0) = 0"
      by (rule exit_class_start[OF Q])
    have zero: "AE \<omega> in Q. ennreal (pexit T K (\<lambda>t. fst (\<omega> t))) = 0"
    proof (rule eventually_mono[OF st])
      fix \<omega> :: "'n pairpath"
      assume "fst (\<omega> 0) = z \<and> snd (\<omega> 0) = 0"
      then have z0: "fst (\<omega> 0) = z" by blast
      have "pexit T K (\<lambda>t. fst (\<omega> t)) \<le> 0"
        unfolding pexit_def
        by (rule etime_le_of_mem[OF T0 order.refl T0]) (use z0 z in simp)
      moreover have "0 \<le> pexit T K (\<lambda>t. fst (\<omega> t))"
        unfolding pexit_def by (rule etime_nonneg[OF T0])
      ultimately show "ennreal (pexit T K (\<lambda>t. fst (\<omega> t))) = 0" by simp
    qed
    have "e \<le> (\<integral>\<^sup>+\<omega>. ennreal (pexit T K (\<lambda>t. fst (\<omega> t))) \<partial>Q)"
      unfolding e by (rule ess_inf_time_le_nn_integral[OF prob])
    also have "\<dots> = (\<integral>\<^sup>+\<omega>. 0 \<partial>Q)" by (rule nn_integral_cong_AE[OF zero])
    also have "\<dots> = 0" by simp
    finally show "e \<le> 0" .
  qed
  then show ?thesis by simp
qed

text \<open>Definition 3.1(a) for \<open>exit_val\<close>, including the boundary clause.  At a
  boundary point where the value is strictly positive, a touching that is
  only global over \<open>K\<close> upgrades to a local one: off \<open>K\<close> the value is \<open>0\<close>
  (\<open>exit_val_zero_outside\<close>) while the test function is continuous, so for
  \<open>z\<close> close enough to \<open>x\<close> the required inequality \<open>0 - \<phi> z \<le> v x - \<phi> x\<close>
  follows from \<open>\<phi> x - \<phi> z < v x\<close>.\<close>

theorem exit_val_subsol_bc:
  fixes K :: "(real^'n::finite) set"
  assumes T: "0 < T" and L1: "1 \<le> L" and Kc: "closed K"
    and kn: "k < CARD('n)"
  shows "visc_subsol_env k L K
      (interior K \<union> {x \<in> K - interior K. 0 < enn2real (exit_val k L T K x)})
      (\<lambda>z. enn2real (exit_val k L T K z))"
  unfolding visc_subsol_env_def
proof (intro ballI allI impI)
  define v where "v = (\<lambda>z. enn2real (exit_val k L T K z))"
  have T0: "0 \<le> T" using T by simp
  fix x :: "real^'n" and \<phi> :: "real^'n \<Rightarrow> real"
    and g :: "real^'n \<Rightarrow> real^'n" and H :: "real^'n^'n"
  assume xO: "x \<in> interior K \<union> {x \<in> K - interior K. 0 < v x}"
    and tf: "test_fun_at \<phi> g H x"
    and gmax: "\<forall>y\<in>K. v y - \<phi> y \<le> v x - \<phi> x"

  text \<open>The test function is continuous at \<open>x\<close>.\<close>
  have cphi: "isCont \<phi> x"
  proof -
    obtain ee where ee0: "0 < ee"
      and dd: "\<And>y. y \<in> ball x ee \<Longrightarrow> (\<phi> has_derivative (\<lambda>h. g y \<bullet> h)) (at y)"
      using tf unfolding test_fun_at_def by blast
    have "(\<phi> has_derivative (\<lambda>h. g x \<bullet> h)) (at x)" using dd[of x] ee0 by simp
    then have "\<phi> differentiable (at x)" by (rule differentiableI)
    then show ?thesis by (simp add: differentiable_imp_continuous_within)
  qed

  text \<open>The global touching upgrades to a local one.\<close>
  have loc: "\<exists>e>0. \<forall>z \<in> ball x e. v z - \<phi> z \<le> v x - \<phi> x"
  proof (cases "x \<in> interior K")
    case True
    obtain e where e0: "0 < e" and eK: "ball x e \<subseteq> K"
      using True unfolding mem_interior by blast
    show ?thesis
    proof (intro exI[of _ e] conjI ballI e0)
      fix z assume "z \<in> ball x e"
      then have "z \<in> K" using eK by blast
      then show "v z - \<phi> z \<le> v x - \<phi> x" using gmax by blast
    qed
  next
    case False
    then have vpos: "0 < v x" using xO by blast
    obtain e where e0: "0 < e"
      and eb: "\<And>z. dist z x < e \<Longrightarrow> \<bar>\<phi> z - \<phi> x\<bar> < v x"
    proof -
      from cphi vpos obtain s where s0: "0 < s"
        and sb: "\<And>y. y \<noteq> x \<Longrightarrow> dist y x < s \<Longrightarrow> dist (\<phi> y) (\<phi> x) < v x"
        unfolding isCont_def LIM_def by blast
      have key: "\<bar>\<phi> z - \<phi> x\<bar> < v x" if dz: "dist z x < s" for z
      proof (cases "z = x")
        case True then show ?thesis using vpos by simp
      next
        case False
        have "dist (\<phi> z) (\<phi> x) < v x" by (rule sb[OF False dz])
        then show ?thesis by (simp add: dist_real_def)
      qed
      show thesis by (rule that[OF s0 key])
    qed
    show ?thesis
    proof (intro exI[of _ e] conjI ballI e0)
      fix z assume zb: "z \<in> ball x e"
      then have dzx: "dist z x < e" by (simp add: dist_commute)
      show "v z - \<phi> z \<le> v x - \<phi> x"
      proof (cases "z \<in> K")
        case True then show ?thesis using gmax by blast
      next
        case False
        have "v z = 0" unfolding v_def
          using exit_val_zero_outside[OF T0 False] by simp
        moreover have "\<phi> x - \<phi> z < v x" using eb[OF dzx] by linarith
        ultimately show ?thesis by linarith
      qed
    qed
  qed

  have "ell_op k L (g x) H \<le> 1"
    using exit_val_visc_subsol_any[OF T L1 Kc kn, of UNIV] tf loc
    unfolding visc_subsol_def v_def by blast
  then have "ereal (ell_op k L (g x) H) \<le> 1" by simp
  with ell_op_lsc_le_ell_op[of k L "g x" H]
  show "ell_op_lsc k L (g x) H \<le> 1" by (rule order_trans)
qed


(*<*)
end
(*>*)
