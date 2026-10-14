section \<open>Theorem 1.1: the value function is the unique viscosity solution\<close>

(*<*)
theory Value_Function_Uniqueness
  imports
    "Relative_Arbitrage_Equation.Comparison_Instance" Exit_Class_Infinite Covariation_Operator
begin
(*>*)

text \<open>
  Theorem 1.1 of \<^cite>\<open>LaiShkolnikovSoner\<close> asserts that the value function \<open>v\<close> of
  Eq. (1.6) is the unique bounded upper semicontinuous viscosity solution of
  Eq. (1.9) satisfying the zero boundary condition of Definition 3.1.  This theory
  joins the two halves of that statement: the viscosity property, proved in
  @{theory Relative_Arbitrage.Value_Function_Subsolution} and
  @{theory Relative_Arbitrage.Value_Function_Supersolution}, and the comparison principle, proved in
  @{theory Relative_Arbitrage_Equation.Maximum_Principle}.
\<close>

text \<open>With \<open>v = enn2real \<circ> covariation_val S T K\<close> (the paper's \<open>exit_val k L T K\<close> at
  \<open>S = sconstraint k L\<close>), Theorem 1.1 has five clauses.

  \<^item> Finiteness, \<open>covariation_val S T K x < \<top>\<close>: \<open>covariation_val_le_T\<close>, and sharply
    \<open>covariation_val_le_ball_bound\<close>.
  \<^item> Upper semicontinuity: \<open>covariation_val_real_usc\<close> below.
  \<^item> The viscosity property of Eq. (1.9): \<open>Value_Function_Subsolution.covariation_val_visc_subsol\<close>
    for the subsolution half, with the operator itself, and
    \<open>Value_Function_Supersolution.covariation_val_supersol_lsc\<close> for the supersolution half.
  \<^item> The zero boundary condition, in the viscosity sense of
    Definition 3.1: \<open>Value_Function_Subsolution.covariation_val_subsol_bc\<close> and
    \<open>covariation_val_supersol_bc\<close> below.
  \<^item> Uniqueness: \<open>covariation_val_uniqueness\<close> below, via the paper's
    Theorem 4.2(a), Theorem 4.2(b), Theorem 4.3 and Proposition 4.1 for the
    geometric operator \<^const>\<open>covariation_op_real\<close> \<open>S\<close>; the paper's form is
    \<open>theorem_1_1_uniqueness_faithful\<close>.

  The boundary condition is a viscosity condition, not the pointwise identity
  \<open>v = 0\<close> on \<open>K - interior K\<close>, which is false in general: by Lemma 5.3 of the
  paper, a convex \<open>K\<close> has \<open>v x = 0\<close> exactly when the face containing \<open>x\<close> has
  dimension at most \<open>n - k\<close>, so the cube in \<open>\<real>\<^sup>3\<close> with \<open>k = 2\<close> has \<open>v > 0\<close> on
  the open two-dimensional faces of its boundary.  The pointwise identity is
  proved only for a ball, where it holds (\<open>Example_3_1\<close>).\<close>

text \<open>\<open>enn2real \<circ> covariation_val S T K\<close> is a viscosity solution of Eq. (1.9),
  with the operator \<^const>\<open>covariation_op\<close> \<open>S\<close>, on \<open>interior K\<close>: an ordinary
  subsolution (@{thm [source] covariation_val_visc_subsol}) and, in the enveloped
  sense of Definition 3.1(b), a supersolution
  (@{thm [source] covariation_val_supersol_lsc}), where the lower semicontinuous
  envelope replaces \<open>v\<close> because the plain supersolution property fails
  wherever \<open>v\<close> has an interior local minimum.  Both proofs are pathwise,
  built by Euler pasting of endpoint-frozen Gaussian kernels rather than
  stochastic integrals or SDE well-posedness.  The supersolution assumes
  the horizon does not bind on the interior, \<open>v\<^sub>*(x) < T/2\<close>, which for a
  bounded \<open>K\<close> holds automatically once \<open>T\<close> is large enough
  (@{thm [source] covariation_val_le_ball_bound}).\<close>

section \<open>Theorem 1.1 assembled\<close>

text \<open>The value function \<open>covariation_val\<close> as a real-valued function:
  nonnegative, globally bounded, and upper semicontinuous in the \<open>\<epsilon>\<close>-form the comparison machinery consumes.\<close>


lemma covariation_val_real_bounded:
  fixes K :: "(real^'n::finite) set"
  assumes T0: "0 \<le> T" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and th0: "0 < \<theta>" and th: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> \<theta> \<le> trace a"
    and KB: "K \<subseteq> cball 0 rK" and r0: "0 \<le> rK"
  shows "\<bar>enn2real (covariation_val S T K x)\<bar> \<le> rK * rK / \<theta>"
proof -
  have le: "covariation_val S T K x \<le> ennreal ((rK * rK - x \<bullet> x) / \<theta>)"
    by (rule covariation_val_le_ball_bound[OF T0 B0 B th0 th KB])
  have fin: "ennreal ((rK * rK - x \<bullet> x) / \<theta>) < \<top>"
    by simp
  have "enn2real (covariation_val S T K x)
      \<le> enn2real (ennreal ((rK * rK - x \<bullet> x) / \<theta>))"
    by (rule enn2real_mono[OF le fin])
  also have "\<dots> \<le> rK * rK / \<theta>"
  proof (cases "0 \<le> (rK * rK - x \<bullet> x) / \<theta>")
    case True
    then have "enn2real (ennreal ((rK * rK - x \<bullet> x) / \<theta>))
        = (rK * rK - x \<bullet> x) / \<theta>" by simp
    also have "\<dots> \<le> rK * rK / \<theta>"
      using th0 inner_ge_zero[of x] by (simp add: divide_right_mono)
    finally show ?thesis .
  next
    case False
    then have "ennreal ((rK * rK - x \<bullet> x) / \<theta>) = 0"
      by (simp add: ennreal_neg)
    then show ?thesis using th0 r0 by simp
  qed
  finally show ?thesis by simp
qed

lemma covariation_val_real_usc:
  fixes K :: "(real^'n::finite) set" and \<sigma> :: "real^'n^'n"
  assumes T: "0 < T" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and Sc: "closed S" and SST: "\<sigma> ** transpose \<sigma> \<in> S" and Kc: "closed K"
    and lt: "enn2real (covariation_val S T K z) < cc"
  shows "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> enn2real (covariation_val S T K y) < cc"
proof -
  have fin: "covariation_val S T K y < \<top>" for y
    using covariation_val_neq_top[of T S K y] T by (simp add: less_top)
  have cc0: "0 < cc" using lt enn2real_nonneg[of "covariation_val S T K z"] by linarith
  have "z \<in> {y. covariation_val S T K y < ennreal cc}" using lt fin[of z] by simp
  moreover have "open {y. covariation_val S T K y < ennreal cc}"
    by (rule covariation_val_open_less[OF T B0 B D0 D Sc SST Kc])
  ultimately obtain e where e0: "0 < e" and eU: "ball z e \<subseteq> {y. covariation_val S T K y < ennreal cc}"
    unfolding open_contains_ball by blast
  have "enn2real (covariation_val S T K y) < cc" if "dist z y < e" for y
    using eU that fin[of y] cc0 by auto
  then show ?thesis using e0 by blast
qed

text \<open>The supersolution clause of Definition 3.1 for \<open>covariation_val\<close>, with
  the boundary gate included.  The gate is vacuous: the value is nonnegative,
  hence so is its
  lower envelope, so \<open>{x. lsc_env v x < 0} = {}\<close> and the \<open>\<Omega>\<close> of
  Definition 3.1(b) collapses to \<open>interior K\<close>.\<close>

theorem covariation_val_supersol_bc:
  fixes K :: "(real^'n::finite) set"
  assumes T0: "0 < T"
    and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and Sc: "closed S" and Sv: "convex S" and Spsd: "\<And>a. a \<in> S \<Longrightarrow> psd a"
    and rot: "\<And>R b. orthogonal_matrix R \<Longrightarrow> b \<in> S \<Longrightarrow> R ** b ** transpose R \<in> S"
    and tan1: "\<And>u :: real^'n. norm u \<le> 1 \<Longrightarrow>
      tanpU (mat 1) u ** transpose (tanpU (mat 1) u) \<in> S"
    and n2: "2 \<le> CARD('n)"
    and th0: "0 < \<theta>" and th: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> \<theta> \<le> trace a"
    and Kc: "closed K" and KB: "K \<subseteq> cball 0 rK"
    and Tbig: "2 * (rK * rK) / \<theta> < T"
  shows "visc_supersol_gen test_fun_at (\<lambda>_. principal K) (covariation_op_usc S)
      (interior K \<union> {x \<in> K - interior K.
          lsc_env (\<lambda>z. enn2real (covariation_val S T K z)) x < 0})
      (lsc_env (\<lambda>z. enn2real (covariation_val S T K z)))"
proof -
  define v where "v = (\<lambda>z. enn2real (covariation_val S T K z))"
  have v0: "0 \<le> v y" for y unfolding v_def by (rule enn2real_nonneg)
  have lsc0: "0 \<le> lsc_env v x" for x by (rule lsc_env_ge[OF v0])
  have gate: "interior K \<union> {x \<in> K - interior K. lsc_env v x < 0} = interior K"
  proof
    show "interior K \<union> {x \<in> K - interior K. lsc_env v x < 0} \<subseteq> interior K"
    proof
      fix y assume "y \<in> interior K \<union> {x \<in> K - interior K. lsc_env v x < 0}"
      then consider "y \<in> interior K" | "lsc_env v y < 0" by auto
      then show "y \<in> interior K"
      proof cases
        case 1 then show ?thesis .
      next
        case 2
        have "0 \<le> lsc_env v y" by (rule lsc0)
        then have False using 2 by linarith
        then show ?thesis by simp
      qed
    qed
    show "interior K \<subseteq> interior K \<union> {x \<in> K - interior K. lsc_env v x < 0}"
      by blast
  qed
  have "visc_supersol_gen test_fun_at (\<lambda>_. principal K) (covariation_op_usc S) (interior K)
      (lsc_env v)"
    unfolding v_def
    by (rule covariation_val_supersol_lsc_bounded[OF T0 B0 B D0 D Sc Sv Spsd rot tan1 n2 th0 th
          Kc KB Tbig])
  then show ?thesis unfolding v_def[symmetric] gate .
qed

text \<open>\<^bold>\<open>Theorem 1.1, uniqueness clause.\<close>  \<open>covariation_val\<close> is upper
  semicontinuous (\<open>covariation_val_real_usc\<close>), nonnegative, globally bounded
  (\<open>covariation_val_real_bounded\<close>) and satisfies both clauses of Definition 3.1
  with their boundary gates (\<open>covariation_val_subsol_bc\<close>,
  \<open>covariation_val_supersol_bc\<close>); on an expandable \<open>K\<close> it is the only such
  function.  The comparison principle applies because \<^const>\<open>covariation_op_real\<close>
  is a geometric operator (\<open>covariation_op_real_geometric_operator\<close>): the
  hypotheses on \<open>S\<close> are those of the supersolution property, and the
  sphere-tangential rates supply a rate annihilating each gradient.\<close>

theorem covariation_val_uniqueness:
  fixes K :: "(real^'n::finite) set" and u :: "real^'n \<Rightarrow> real"
  assumes T0: "0 < T"
    and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and Sc: "closed S" and Sv: "convex S" and Spsd: "\<And>a. a \<in> S \<Longrightarrow> psd a"
    and rot: "\<And>R b. orthogonal_matrix R \<Longrightarrow> b \<in> S \<Longrightarrow> R ** b ** transpose R \<in> S"
    and tan1: "\<And>u :: real^'n. norm u \<le> 1 \<Longrightarrow>
      tanpU (mat 1) u ** transpose (tanpU (mat 1) u) \<in> S"
    and n2: "2 \<le> CARD('n)"
    and th0: "0 < \<theta>" and th: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> \<theta> \<le> trace a"
    and cK: "compact K" and neK: "K \<noteq> {}" and expK: "expandable K"
    and KB: "K \<subseteq> cball 0 rK"
    and Tbig: "2 * (rK * rK) / \<theta> < T"
    and uscu: "\<And>c z. u z < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> u y < c"
    and Bu: "\<And>y. \<bar>u y\<bar> \<le> Bd"
    and subu: "visc_subsol_gen test_fun_C2 (\<lambda>_. principal K) (covariation_op_lsc S)
      (interior K \<union> {x \<in> K - interior K. 0 < u x}) u"
    and supu: "visc_supersol_gen test_fun_C2 (\<lambda>_. principal K) (covariation_op_usc S)
      (interior K \<union> {x \<in> K - interior K. lsc_env u x < 0}) (lsc_env u)"
    and x: "x \<in> K"
  shows "u x = enn2real (covariation_val S T K x)"
proof -
  define v where "v = (\<lambda>z. enn2real (covariation_val S T K z))"
  have kill: "\<exists>a\<in>S. a *v p = 0" for p :: "real^'n"
    by (rule tangential_rates_kill) (rule tan1)
  have Kc: "closed K" by (rule compact_imp_closed[OF cK])
  have SST: "tanpU (mat 1) 0 ** transpose (tanpU (mat 1) (0 :: real^'n)) \<in> S"
    by (rule tan1) simp
  have "norm x \<le> rK" using subsetD[OF KB x] by simp
  then have r0: "0 \<le> rK" using norm_ge_zero[of x] by linarith
  have Bv: "\<bar>v y\<bar> \<le> rK * rK / \<theta>" for y
    unfolding v_def by (rule covariation_val_real_bounded[OF less_imp_le[OF T0] B0 B th0 th KB r0])
  have uscv: "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> v y < c" if "v z < c" for c z
    unfolding v_def
    by (rule covariation_val_real_usc[OF T0 B0 B D0 D Sc SST Kc that[unfolded v_def]])
  have "visc_subsol_gen test_fun_at (\<lambda>_. principal K) (covariation_op_lsc S)
      (interior K \<union> {x \<in> K - interior K. 0 < v x}) v"
    unfolding v_def
    by (rule visc_subsol_gen_mono[OF covariation_val_subsol_bc[OF T0 B0 B D0 D Sc Sv SST Spsd Kc]
          covariation_op_lsc_le])
  then have subv: "visc_subsol_gen test_fun_C2 (\<lambda>_. principal K) (covariation_op_lsc S)
      (interior K \<union> {x \<in> K - interior K. 0 < v x}) v"
    by (rule visc_subsol_gen_test_mono) (rule test_fun_C2_imp_test_fun_at)
  have "visc_supersol_gen test_fun_at (\<lambda>_. principal K) (covariation_op_usc S)
      (interior K \<union> {x \<in> K - interior K. lsc_env v x < 0}) (lsc_env v)"
    unfolding v_def
    by (rule covariation_val_supersol_bc[OF T0 B0 B D0 D Sc Sv Spsd rot tan1 n2 th0 th Kc KB Tbig])
  then have supv: "visc_supersol_gen test_fun_C2 (\<lambda>_. principal K) (covariation_op_usc S)
      (interior K \<union> {x \<in> K - interior K. lsc_env v x < 0}) (lsc_env v)"
    by (rule visc_supersol_gen_test_mono) (rule test_fun_C2_imp_test_fun_at)
  have "u x = v x"
    by (rule covariation_op_uniqueness_expandable[OF B Spsd rot kill
          cK neK expK uscu uscv Bu Bv subu supu subv supv x])
  then show ?thesis unfolding v_def .
qed

text \<open>The paper's statement, at \<open>S = sconstraint k L\<close>.\<close>

theorem theorem_1_1_uniqueness_faithful:
  fixes K :: "(real^'n::finite) set" and u :: "real^'n \<Rightarrow> real"
  assumes T0: "0 < T" and L1: "1 \<le> L" and k1: "1 \<le> k" and kn: "k < CARD('n)"
    and cK: "compact K" and neK: "K \<noteq> {}" and expK: "expandable K"
    and KB: "K \<subseteq> cball 0 rK" and r0: "0 \<le> rK"
    and Tbig: "2 * (rK * rK) / real (CARD('n) - k) < T"
    and uscu: "\<And>c z. u z < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> u y < c"
    and Bu: "\<And>y. \<bar>u y\<bar> \<le> Bd"
    and subu: "visc_subsol_env2 k L K
      (interior K \<union> {x \<in> K - interior K. 0 < u x}) u"
    and supu: "visc_supersol_env2 k L K
      (interior K \<union> {x \<in> K - interior K. lsc_env u x < 0}) (lsc_env u)"
    and x: "x \<in> K"
  shows "u x = enn2real (exit_val k L T K x)"
proof -
  have L0: "0 \<le> L" using L1 by simp
  have n2: "2 \<le> CARD('n)" using k1 kn by linarith
  show ?thesis
    unfolding exit_val_eq_covariation_val
    by (rule covariation_val_uniqueness[OF T0 sconstraint_bounds[OF L0] closed_sconstraint
          sconstraint_convex sconstraint_psd_entry(1) sconstraint_conj
          tanpU_id_sq_sconstraint[OF _ k1 L1] n2 sconstraint_trace_bounds(3,4)[OF kn L0]
          cK neK expK KB Tbig uscu Bu
          subu[unfolded visc_subsol_env2_eq_gen ell_op_lsc_eq_covariation_op_lsc[OF k1 kn L1]]
          supu[unfolded visc_supersol_env2_eq_gen ell_op_usc_eq_covariation_op_usc[OF k1 kn L1]]
          x])
qed

section \<open>The clauses for the value function of Eq. (1.6)\<close>

text \<open>Everything above is stated at a finite horizon.  Since
  @{thm [source] iexit_val_eq_exit_val_ball} identifies the two value
  functions uniformly in the point once the horizon exceeds \<open>r\<^sup>2/(n-k)\<close>, the
  horizon can be chosen inside each proof
  (@{thm [source] iexit_val_eq_exit_val_horizon}) and disappears from the statements:
  what follows is Theorem 1.1 for the value function of Eq. (1.6) as the paper
  writes it, on \<open>C([0,\<infinity>))\<close>.\<close>

text \<open>The bound of Eq. (3.10) on the value, in \<open>ennreal\<close>.  Unlike a bound on
  \<open>enn2real\<close> of the value, it also says that the value is finite: \<open>enn2real\<close>
  maps \<open>\<top>\<close> to \<open>0\<close>, so the bound on \<open>\<bar>enn2real \<dots>\<bar>\<close> alone would hold vacuously at \<open>\<top>\<close>.
  Every clause below reads the value function through \<open>enn2real\<close>, so this is
  what makes those readings the paper's \<open>v\<close>.\<close>

theorem icovariation_val_le_ball_bound:
  fixes K :: "(real^'n::finite) set" and \<sigma> :: "real^'n^'n"
  assumes Sc: "closed S" and Sv: "convex S" and SST: "\<sigma> ** transpose \<sigma> \<in> S"
    and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and th0: "0 < \<theta>" and th: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> \<theta> \<le> trace a"
    and Kc: "closed K" and KB: "K \<subseteq> cball 0 rK"
  shows "icovariation_val S K x \<le> ennreal ((rK * rK - x \<bullet> x) / \<theta>)"
proof -
  obtain T :: real where T0: "0 < T" and "rK * rK / \<theta> < T"
    and "2 * (rK * rK) / \<theta> < T" and eq: "icovariation_val S K = covariation_val S T K"
    by (rule icovariation_val_eq_covariation_val_horizon[OF Sc Sv SST B0 B th0 th Kc KB])
  show ?thesis unfolding eq
    by (rule covariation_val_le_ball_bound[OF less_imp_le[OF T0] B0 B th0 th KB])
qed

text \<open>\<^bold>\<open>Clause (1): upper semicontinuity.\<close>\<close>

theorem icovariation_val_real_usc:
  fixes K :: "(real^'n::finite) set" and \<sigma> :: "real^'n^'n"
  assumes Sc: "closed S" and Sv: "convex S" and SST: "\<sigma> ** transpose \<sigma> \<in> S"
    and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and th0: "0 < \<theta>" and th: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> \<theta> \<le> trace a"
    and cK: "compact K"
    and lt: "enn2real (icovariation_val S K z) < c"
  shows "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> enn2real (icovariation_val S K y) < c"
proof -
  have Kc: "closed K" by (rule compact_imp_closed[OF cK])
  obtain rK :: real where r0: "0 \<le> rK" and KB: "K \<subseteq> cball 0 rK"
    using compact_cball_bound[OF cK] by blast
  obtain T :: real where T0: "0 < T" and "rK * rK / \<theta> < T"
    and "2 * (rK * rK) / \<theta> < T" and eq: "icovariation_val S K = covariation_val S T K"
    by (rule icovariation_val_eq_covariation_val_horizon[OF Sc Sv SST B0 B th0 th Kc KB])
  show ?thesis unfolding eq
    by (rule covariation_val_real_usc[OF T0 B0 B D0 D Sc SST Kc lt[unfolded eq]])
qed

text \<open>\<^bold>\<open>Clauses (2) and (3), subsolution half.\<close>  Definition 3.1(a) on the
  interior of \<open>K\<close> and at the boundary points where the value is positive: the
  subsolution half of the viscosity property of Eq. (1.9) and of the zero
  boundary condition at once.  The supersolution half is stated below with the
  paper's envelope (\<open>icovariation_val_supersol_bc_K\<close>); there the hypothesis
  that the horizon does not bind at interior points is discharged by the a
  priori bound.\<close>

theorem icovariation_val_subsol_bc:
  fixes K :: "(real^'n::finite) set" and \<sigma> :: "real^'n^'n"
  assumes B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and Sc: "closed S" and Sv: "convex S" and SST: "\<sigma> ** transpose \<sigma> \<in> S"
    and Spsd: "\<And>a. a \<in> S \<Longrightarrow> psd a"
    and th0: "0 < \<theta>" and th: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> \<theta> \<le> trace a"
    and cK: "compact K"
  shows "visc_subsol_gen test_fun_at (\<lambda>_. principal K) (covariation_op S)
      (interior K \<union> {x \<in> K - interior K. 0 < enn2real (icovariation_val S K x)})
      (\<lambda>z. enn2real (icovariation_val S K z))"
proof -
  have Kc: "closed K" by (rule compact_imp_closed[OF cK])
  obtain rK :: real where r0: "0 \<le> rK" and KB: "K \<subseteq> cball 0 rK"
    using compact_cball_bound[OF cK] by blast
  obtain T :: real where T0: "0 < T" and "rK * rK / \<theta> < T"
    and "2 * (rK * rK) / \<theta> < T" and eq: "icovariation_val S K = covariation_val S T K"
    by (rule icovariation_val_eq_covariation_val_horizon[OF Sc Sv SST B0 B th0 th Kc KB])
  show ?thesis unfolding eq
    by (rule covariation_val_subsol_bc[OF T0 B0 B D0 D Sc Sv SST Spsd Kc])
qed

theorem iexit_val_subsol_bc:
  fixes K :: "(real^'n::finite) set"
  assumes kn: "k < CARD('n)" and L: "1 \<le> L" and cK: "compact K"
  shows "visc_subsol_env k L K
      (interior K \<union> {x \<in> K - interior K. 0 < enn2real (iexit_val k L K x)})
      (\<lambda>z. enn2real (iexit_val k L K z))"
proof -
  have L0: "0 \<le> L" using L by simp
  show ?thesis
    unfolding visc_subsol_env_eq_gen iexit_val_eq_icovariation_val
    by (rule visc_subsol_gen_mono[OF icovariation_val_subsol_bc[OF sconstraint_bounds[OF L0]
          closed_sconstraint sconstraint_convex mat_1_rate_in_sconstraint[OF L]
          sconstraint_psd_entry(1) sconstraint_trace_bounds(3,4)[OF kn L0] cK]
          ell_op_lsc_le_covariation_op[OF kn L]])
qed

text \<open>\<^bold>\<open>Clause (4): uniqueness.\<close>\<close>

theorem icovariation_val_uniqueness:
  fixes K :: "(real^'n::finite) set" and u :: "real^'n \<Rightarrow> real"
  assumes B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and Sc: "closed S" and Sv: "convex S" and Spsd: "\<And>a. a \<in> S \<Longrightarrow> psd a"
    and rot: "\<And>R b. orthogonal_matrix R \<Longrightarrow> b \<in> S \<Longrightarrow> R ** b ** transpose R \<in> S"
    and tan1: "\<And>u :: real^'n. norm u \<le> 1 \<Longrightarrow>
      tanpU (mat 1) u ** transpose (tanpU (mat 1) u) \<in> S"
    and n2: "2 \<le> CARD('n)"
    and th0: "0 < \<theta>" and th: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> \<theta> \<le> trace a"
    and cK: "compact K" and neK: "K \<noteq> {}" and expK: "expandable K"
    and usc: "\<And>c z. u z < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> u y < c"
    and bnd: "\<And>y. \<bar>u y\<bar> \<le> Bd"
    and sub: "visc_subsol_gen test_fun_C2 (\<lambda>_. principal K) (covariation_op_lsc S)
        (interior K \<union> {x \<in> K - interior K. 0 < u x}) u"
    and sups: "visc_supersol_gen test_fun_C2 (\<lambda>_. principal K) (covariation_op_usc S)
        (interior K \<union> {x \<in> K - interior K. lsc_env u x < 0}) (lsc_env u)"
    and xK: "x \<in> K"
  shows "u x = enn2real (icovariation_val S K x)"
proof -
  have SST: "tanpU (mat 1) 0 ** transpose (tanpU (mat 1) (0 :: real^'n)) \<in> S"
    by (rule tan1) simp
  have Kc: "closed K" by (rule compact_imp_closed[OF cK])
  obtain rK :: real where r0: "0 \<le> rK" and KB: "K \<subseteq> cball 0 rK"
    using compact_cball_bound[OF cK] by blast
  obtain T :: real where T0: "0 < T" and "rK * rK / \<theta> < T"
    and T2: "2 * (rK * rK) / \<theta> < T" and eq: "icovariation_val S K = covariation_val S T K"
    by (rule icovariation_val_eq_covariation_val_horizon[OF Sc Sv SST B0 B th0 th Kc KB])
  show ?thesis unfolding eq
    by (rule covariation_val_uniqueness[OF T0 B0 B D0 D Sc Sv Spsd rot tan1 n2 th0 th
          cK neK expK KB T2 usc bnd sub sups xK])
qed

theorem iexit_val_uniqueness:
  fixes K :: "(real^'n::finite) set" and u :: "real^'n \<Rightarrow> real"
  assumes kn: "k < CARD('n)" and L1: "1 \<le> L" and k1: "1 \<le> k"
    and cK: "compact K" and neK: "K \<noteq> {}" and expK: "expandable K"
    and usc: "\<And>c z. u z < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> u y < c"
    and bnd: "\<And>y. \<bar>u y\<bar> \<le> Bd"
    and sub: "visc_subsol_env2 k L K
        (interior K \<union> {x \<in> K - interior K. 0 < u x}) u"
    and sups: "visc_supersol_env2 k L K
        (interior K \<union> {x \<in> K - interior K. lsc_env u x < 0}) (lsc_env u)"
    and xK: "x \<in> K"
  shows "u x = enn2real (iexit_val k L K x)"
proof -
  have L0: "0 \<le> L" using L1 by simp
  have n2: "2 \<le> CARD('n)" using k1 kn by linarith
  show ?thesis
    unfolding iexit_val_eq_icovariation_val
    by (rule icovariation_val_uniqueness[OF sconstraint_bounds[OF L0] closed_sconstraint
          sconstraint_convex sconstraint_psd_entry(1) sconstraint_conj
          tanpU_id_sq_sconstraint[OF _ k1 L1] n2 sconstraint_trace_bounds(3,4)[OF kn L0]
          cK neK expK usc bnd
          sub[unfolded visc_subsol_env2_eq_gen ell_op_lsc_eq_covariation_op_lsc[OF k1 kn L1]]
          sups[unfolded visc_supersol_env2_eq_gen ell_op_usc_eq_covariation_op_usc[OF k1 kn L1]]
          xK])
qed

text \<open>\<^bold>\<open>Clauses (3) and (4) with the paper's own envelope.\<close>  Definition 3.1
  reads \<open>u\<^sub>*\<close> within \<open>K\<close>, which is @{const lsc_envK}; the clauses above read it
  over balls of \<open>real^'n\<close>.  The two differ only on \<open>K - interior K\<close>, and there
  the difference is real: on a cube with \<open>k = 2\<close> the value function is positive
  on the open two-dimensional faces, so its liminf within \<open>K\<close> is positive
  there while its liminf over balls of \<open>real^'n\<close> is \<open>0\<close>.  Both clauses are
  therefore restated, not derived by a weakening.\<close>

theorem covariation_val_supersol_bc_K:
  fixes K :: "(real^'n::finite) set"
  assumes T0: "0 < T"
    and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and Sc: "closed S" and Sv: "convex S" and Spsd: "\<And>a. a \<in> S \<Longrightarrow> psd a"
    and rot: "\<And>R b. orthogonal_matrix R \<Longrightarrow> b \<in> S \<Longrightarrow> R ** b ** transpose R \<in> S"
    and tan1: "\<And>u :: real^'n. norm u \<le> 1 \<Longrightarrow>
      tanpU (mat 1) u ** transpose (tanpU (mat 1) u) \<in> S"
    and n2: "2 \<le> CARD('n)"
    and th0: "0 < \<theta>" and th: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> \<theta> \<le> trace a"
    and Kc: "closed K" and KB: "K \<subseteq> cball 0 rK"
    and Tbig: "2 * (rK * rK) / \<theta> < T"
  shows "visc_supersol_gen test_fun_at (\<lambda>_. principal K) (covariation_op_usc S)
      (interior K \<union> {x \<in> K - interior K.
          lsc_envK K (\<lambda>z. enn2real (covariation_val S T K z)) x < 0})
      (lsc_envK K (\<lambda>z. enn2real (covariation_val S T K z)))"
proof -
  define v where "v = (\<lambda>z :: real^'n. enn2real (covariation_val S T K z))"
  have v0: "0 \<le> v y" for y unfolding v_def by (rule enn2real_nonneg)
  have gate: "interior K \<union> {x \<in> K - interior K. lsc_envK K v x < 0} = interior K"
  proof
    show "interior K \<union> {x \<in> K - interior K. lsc_envK K v x < 0} \<subseteq> interior K"
    proof
      fix y assume y: "y \<in> interior K \<union> {x \<in> K - interior K. lsc_envK K v x < 0}"
      show "y \<in> interior K"
      proof (cases "y \<in> interior K")
        case True then show ?thesis .
      next
        case False
        then have yK: "y \<in> K" and neg: "lsc_envK K v y < 0" using y by auto
        have "0 \<le> lsc_envK K v y" by (rule lsc_envK_ge[OF v0 yK])
        then show ?thesis using neg by linarith
      qed
    qed
    show "interior K \<subseteq> interior K \<union> {x \<in> K - interior K. lsc_envK K v x < 0}"
      by blast
  qed
  have cap: "\<And>y. y \<in> interior K \<Longrightarrow>
      lsc_env (\<lambda>z. enn2real (covariation_val S T K z)) y < T / 2"
    by (rule covariation_val_cap_inert[OF less_imp_le[OF T0] B0 B th0 th KB Tbig])
  have main: "visc_supersol_gen test_fun_at (\<lambda>_. principal K) (covariation_op_usc S) (interior K)
      (lsc_envK K v)"
    unfolding v_def
    by (rule covariation_val_supersol_envK[OF T0 B0 B D0 D Sc Sv Spsd rot tan1 n2 Kc cap])
  show ?thesis using main unfolding v_def[symmetric] gate .
qed

theorem icovariation_val_supersol_bc_K:
  fixes K :: "(real^'n::finite) set"
  assumes B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and Sc: "closed S" and Sv: "convex S" and Spsd: "\<And>a. a \<in> S \<Longrightarrow> psd a"
    and rot: "\<And>R b. orthogonal_matrix R \<Longrightarrow> b \<in> S \<Longrightarrow> R ** b ** transpose R \<in> S"
    and tan1: "\<And>u :: real^'n. norm u \<le> 1 \<Longrightarrow>
      tanpU (mat 1) u ** transpose (tanpU (mat 1) u) \<in> S"
    and n2: "2 \<le> CARD('n)"
    and th0: "0 < \<theta>" and th: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> \<theta> \<le> trace a"
    and cK: "compact K"
  shows "visc_supersol_gen test_fun_at (\<lambda>_. principal K) (covariation_op_usc S)
      (interior K \<union> {x \<in> K - interior K.
         lsc_envK K (\<lambda>z. enn2real (icovariation_val S K z)) x < 0})
      (lsc_envK K (\<lambda>z. enn2real (icovariation_val S K z)))"
proof -
  have SST: "tanpU (mat 1) 0 ** transpose (tanpU (mat 1) (0 :: real^'n)) \<in> S"
    by (rule tan1) simp
  have Kc: "closed K" by (rule compact_imp_closed[OF cK])
  obtain rK :: real where r0: "0 \<le> rK" and KB: "K \<subseteq> cball 0 rK"
    using compact_cball_bound[OF cK] by blast
  obtain T :: real where T0: "0 < T" and "rK * rK / \<theta> < T"
    and T2: "2 * (rK * rK) / \<theta> < T" and eq: "icovariation_val S K = covariation_val S T K"
    by (rule icovariation_val_eq_covariation_val_horizon[OF Sc Sv SST B0 B th0 th Kc KB])
  show ?thesis unfolding eq
    by (rule covariation_val_supersol_bc_K[OF T0 B0 B D0 D Sc Sv Spsd rot tan1 n2 th0 th Kc KB T2])
qed

theorem iexit_val_supersol_bc_K:
  fixes K :: "(real^'n::finite) set"
  assumes kn: "k < CARD('n)" and L1: "1 \<le> L" and k1: "1 \<le> k" and cK: "compact K"
  shows "visc_supersol_env k L K
      (interior K \<union> {x \<in> K - interior K.
         lsc_envK K (\<lambda>z. enn2real (iexit_val k L K z)) x < 0})
      (lsc_envK K (\<lambda>z. enn2real (iexit_val k L K z)))"
proof -
  have L0: "0 \<le> L" using L1 by simp
  have n2: "2 \<le> CARD('n)" using k1 kn by linarith
  show ?thesis
    unfolding visc_supersol_env_eq_gen ell_op_usc_eq_covariation_op_usc[OF k1 kn L1]
      iexit_val_eq_icovariation_val
    by (rule icovariation_val_supersol_bc_K[OF sconstraint_bounds[OF L0] closed_sconstraint
          sconstraint_convex sconstraint_psd_entry(1) sconstraint_conj
          tanpU_id_sq_sconstraint[OF _ k1 L1] n2 sconstraint_trace_bounds(3,4)[OF kn L0] cK])
qed

text \<open>The interior clause on its own, which is Definition 3.1(b) for
  \<^const>\<open>iexit_val\<close> with the paper's envelope: the boundary gate is empty,
  since the value function is nonnegative and so is its liminf within \<open>K\<close>.\<close>

theorem icovariation_val_uniqueness_K:
  fixes K :: "(real^'n::finite) set" and u :: "real^'n \<Rightarrow> real"
  assumes B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and Sc: "closed S" and Sv: "convex S" and Spsd: "\<And>a. a \<in> S \<Longrightarrow> psd a"
    and rot: "\<And>R b. orthogonal_matrix R \<Longrightarrow> b \<in> S \<Longrightarrow> R ** b ** transpose R \<in> S"
    and tan1: "\<And>u :: real^'n. norm u \<le> 1 \<Longrightarrow>
      tanpU (mat 1) u ** transpose (tanpU (mat 1) u) \<in> S"
    and n2: "2 \<le> CARD('n)"
    and th0: "0 < \<theta>" and th: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> \<theta> \<le> trace a"
    and cK: "compact K" and neK: "K \<noteq> {}" and expK: "expandable K"
    and usc: "\<And>c z. z \<in> K \<Longrightarrow> u z < c \<Longrightarrow>
      \<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> u y < c"
    and bnd: "\<And>y. y \<in> K \<Longrightarrow> \<bar>u y\<bar> \<le> Bd"
    and sub: "visc_subsol_gen test_fun_C2 (\<lambda>_. principal K) (covariation_op_lsc S)
        (interior K \<union> {x \<in> K - interior K. 0 < u x}) u"
    and sups: "visc_supersol_gen test_fun_C2 (\<lambda>_. principal K) (covariation_op_usc S)
        (interior K \<union> {x \<in> K - interior K. lsc_envK K u x < 0}) (lsc_envK K u)"
    and xK: "x \<in> K"
  shows "u x = enn2real (icovariation_val S K x)"
proof -
  have Kc: "closed K" by (rule compact_imp_closed[OF cK])
  have Bu: "u y \<le> Bd" if "y \<in> K" for y
    using bnd[OF that] by (simp add: abs_le_iff)
  have iK: "interior K \<subseteq> K" by (rule interior_subset)
  define ubar where "ubar = Kext K u"
  have eqK: "ubar y = u y" if "y \<in> K" for y
    unfolding ubar_def by (rule Kext_eq_on_K[OF Kc neK Bu usc that])
  have bnd': "\<bar>ubar y\<bar> \<le> Bd" for y
    unfolding ubar_def by (rule Kext_bounded[OF Kc neK bnd])
  have usc': "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> ubar y < c" if lt: "ubar z < c" for c z
  proof -
    have lt': "Kext K u z < c" using lt unfolding ubar_def .
    have "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> Kext K u y < c"
      by (rule Kext_usc[OF Kc neK Bu lt'])
    then show ?thesis unfolding ubar_def .
  qed
  have lscK: "lsc_env ubar y = lsc_envK K u y" if "y \<in> K" for y
    unfolding ubar_def by (rule lsc_env_Kext[OF Kc neK bnd usc that])
  have gate1: "{z \<in> K - interior K. 0 < ubar z}
      = {z \<in> K - interior K. 0 < u z}"
    using eqK by auto
  have gate2: "{z \<in> K - interior K. lsc_env ubar z < 0}
      = {z \<in> K - interior K. lsc_envK K u z < 0}"
    using lscK by auto
  have sub': "visc_subsol_gen test_fun_C2 (\<lambda>_. principal K) (covariation_op_lsc S)
      (interior K \<union> {z \<in> K - interior K. 0 < ubar z}) ubar"
    unfolding gate1
    by (rule visc_subsol_gen_cong[OF sub]) (use eqK iK in \<open>auto simp: eventually_principal\<close>)
  have sups': "visc_supersol_gen test_fun_C2 (\<lambda>_. principal K) (covariation_op_usc S)
      (interior K \<union> {z \<in> K - interior K. lsc_env ubar z < 0}) (lsc_env ubar)"
    unfolding gate2
    by (rule visc_supersol_gen_cong[OF sups]) (use lscK iK in \<open>auto simp: eventually_principal\<close>)
  have "ubar x = enn2real (icovariation_val S K x)"
    by (rule icovariation_val_uniqueness[OF B0 B D0 D Sc Sv Spsd rot tan1 n2 th0 th
          cK neK expK usc' bnd' sub' sups' xK])
  then show ?thesis using eqK[OF xK] by simp
qed

theorem iexit_val_uniqueness_K:
  fixes K :: "(real^'n::finite) set" and u :: "real^'n \<Rightarrow> real"
  assumes kn: "k < CARD('n)" and L1: "1 \<le> L" and k1: "1 \<le> k"
    and cK: "compact K" and neK: "K \<noteq> {}" and expK: "expandable K"
    and usc: "\<And>c z. z \<in> K \<Longrightarrow> u z < c \<Longrightarrow>
      \<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> u y < c"
    and bnd: "\<And>y. y \<in> K \<Longrightarrow> \<bar>u y\<bar> \<le> Bd"
    and sub: "visc_subsol_env2 k L K
        (interior K \<union> {x \<in> K - interior K. 0 < u x}) u"
    and sups: "visc_supersol_env2 k L K
        (interior K \<union> {x \<in> K - interior K. lsc_envK K u x < 0}) (lsc_envK K u)"
    and xK: "x \<in> K"
  shows "u x = enn2real (iexit_val k L K x)"
proof -
  have L0: "0 \<le> L" using L1 by simp
  have n2: "2 \<le> CARD('n)" using k1 kn by linarith
  show ?thesis
    unfolding iexit_val_eq_icovariation_val
    by (rule icovariation_val_uniqueness_K[OF sconstraint_bounds[OF L0] closed_sconstraint
          sconstraint_convex sconstraint_psd_entry(1) sconstraint_conj
          tanpU_id_sq_sconstraint[OF _ k1 L1] n2 sconstraint_trace_bounds(3,4)[OF kn L0]
          cK neK expK usc bnd
          sub[unfolded visc_subsol_env2_eq_gen ell_op_lsc_eq_covariation_op_lsc[OF k1 kn L1]]
          sups[unfolded visc_supersol_env2_eq_gen ell_op_usc_eq_covariation_op_usc[OF k1 kn L1]]
          xK])
qed

(*<*)
end
(*>*)
