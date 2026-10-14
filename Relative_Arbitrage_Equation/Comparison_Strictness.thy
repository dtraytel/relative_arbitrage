section \<open>Strictness, scaling, and the envelope route\<close>

(*<*)
theory Comparison_Strictness
  imports
    Geometric_Operator
begin

(*>*)


text \<open>What the operator contributes to the comparison argument: it reads
  only the symmetric part of the Hessian, a subsolution can be scaled to a
  strict one, and the envelope forms of the two solution notions can be
  played against each other.  Nothing here doubles a variable yet.\<close>

section \<open>The viscosity notions: congruence, monotonicity, test classes\<close>

text \<open>\<open>trace_mul_comm\<close> is HOL-Analysis's \<open>trace_mul_sym\<close>.\<close>

text \<open>\<open>matrix_mult_scaleR_left\<close> is HOL-Analysis's \<open>scalar_matrix_assoc\<close>, reversed.\<close>

context geometric_operator
begin

lemma visc_subsol_env2_cong:
  fixes f1 f2 :: "real^'n::finite \<Rightarrow> real"
  assumes OK: "\<Omega> \<subseteq> K" and eq: "\<And>y. y \<in> K \<Longrightarrow> f1 y = f2 y"
    and h: "subsol_env2 K \<Omega> f1"
  shows "subsol_env2 K \<Omega> f2"
  by (rule visc_subsol_gen_cong[OF h])
    (use OK eq in \<open>auto simp: eventually_principal\<close>)

lemma visc_supersol_env2_cong:
  fixes f1 f2 :: "real^'n::finite \<Rightarrow> real"
  assumes OK: "\<Omega> \<subseteq> K" and eq: "\<And>y. y \<in> K \<Longrightarrow> f1 y = f2 y"
    and h: "supersol_env2 K \<Omega> f1"
  shows "supersol_env2 K \<Omega> f2"
  by (rule visc_supersol_gen_cong[OF h])
    (use OK eq in \<open>auto simp: eventually_principal\<close>)

lemma visc_supersol_env2_mono:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes "supersol_env2 K \<Omega> u" and "\<Omega>' \<subseteq> \<Omega>"
  shows "supersol_env2 K \<Omega>' u"
  using assms unfolding supersol_env2_iff by blast

lemma visc_subsol_env_imp_env2:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes "subsol_env K \<Omega> u"
  shows "subsol_env2 K \<Omega> u"
  using assms test_fun_C2_imp_test_fun_at
  unfolding subsol_env_iff subsol_env2_iff by blast

lemma visc_supersol_env_imp_env2:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes "supersol_env K \<Omega> u"
  shows "supersol_env2 K \<Omega> u"
  using assms test_fun_C2_imp_test_fun_at
  unfolding supersol_env_iff supersol_env2_iff by blast

end

text \<open>The two places where the paper-facing hypothesis is actually consumed:
  a local touching is deepened by a quartic into a global one over \<open>K\<close>
  (@{thm [source] local_max_quartic_deepen}).  The \<open>C\<^sup>2\<close> versions use
  @{thm [source] test_fun_C2_quartic_shift} where the \<^const>\<open>test_fun_at\<close> versions
  use @{thm [source] test_fun_at_quartic_shift}: the quartic shift of a
  \<open>C\<^sup>2\<close> function is again \<open>C\<^sup>2\<close>, with the same two-jet at \<open>x\<close>.\<close>

theorem visc_supersol_env2_local:
  fixes K :: "(real^'n::finite) set" and w \<phi> :: "real^'n \<Rightarrow> real"
    and g :: "real^'n \<Rightarrow> real^'n" and H :: "real^'n^'n"
    and G :: "real^'n \<Rightarrow> real^'n^'n \<Rightarrow> ereal"
  assumes sup: "visc_supersol_gen test_fun_C2 (\<lambda>_. principal K) G \<Omega> w"
    and x\<Omega>: "x \<in> \<Omega>"
    and tf: "test_fun_C2 \<phi> g H x"
    and wlo: "\<And>y. y \<in> K \<Longrightarrow> Bw \<le> w y"
    and phi: "\<And>y. y \<in> K \<Longrightarrow> \<phi> y \<le> B\<phi>"
    and r0: "0 < r"
    and lm: "\<And>y. y \<in> ball x r \<Longrightarrow> w x - \<phi> x \<le> w y - \<phi> y"
  shows "1 \<le> G (g x) H"
  by (rule visc_supersol_gen_principal_local[OF sup x\<Omega>
        test_fun_C2_quartic_shift[OF tf] wlo phi r0 lm])

theorem visc_subsol_env2_local:
  fixes K :: "(real^'n::finite) set" and u \<phi> :: "real^'n \<Rightarrow> real"
    and g :: "real^'n \<Rightarrow> real^'n" and H :: "real^'n^'n"
    and G :: "real^'n \<Rightarrow> real^'n^'n \<Rightarrow> ereal"
  assumes sub: "visc_subsol_gen test_fun_C2 (\<lambda>_. principal K) G \<Omega> u"
    and x\<Omega>: "x \<in> \<Omega>"
    and tf: "test_fun_C2 \<phi> g H x"
    and uhi: "\<And>y. y \<in> K \<Longrightarrow> u y \<le> Bu"
    and phi: "\<And>y. y \<in> K \<Longrightarrow> B\<phi> \<le> \<phi> y"
    and r0: "0 < r"
    and lm: "\<And>y. y \<in> ball x r \<Longrightarrow> u y - \<phi> y \<le> u x - \<phi> x"
  shows "G (g x) H \<le> 1"
  by (rule visc_subsol_gen_principal_local[OF sub x\<Omega>
        test_fun_C2_quartic_shift[OF tf] uhi phi r0 lm])

text \<open>\<open>supersol_usc\<close> is the supersolution notion with local touching and
  \<open>F\<^sup>*\<close>; the comparison argument reaches it from the paper's notion.\<close>

theorem visc_supersol_env_imp_jet:
  fixes K :: "(real^'n::finite) set" and w :: "real^'n \<Rightarrow> real"
    and F :: "real^'n \<Rightarrow> real^'n^'n \<Rightarrow> real"
  assumes sup: "visc_supersol_gen test_fun_C2 (\<lambda>_. principal K) (op_usc F) \<Omega> w"
    and Kb: "bounded K"
    and wlo: "\<And>y. y \<in> K \<Longrightarrow> Bw \<le> w y"
  shows "visc_supersol_gen test_fun_at nhds (op_usc F) \<Omega> w"
  unfolding visc_supersol_gen_nhds
proof (intro ballI allI impI)
  fix x :: "real^'n" and \<phi> :: "real^'n \<Rightarrow> real"
    and g :: "real^'n \<Rightarrow> real^'n" and H :: "real^'n^'n"
  assume x: "x \<in> \<Omega>" and tf: "test_fun_at \<phi> g H x"
    and lm: "\<exists>e>0. \<forall>y \<in> ball x e. w x - \<phi> x \<le> w y - \<phi> y"
  have symH: "transpose H = H" using tf unfolding test_fun_at_def by blast
  obtain e0 where e00: "0 < e0"
    and lme: "\<And>y. y \<in> ball x e0 \<Longrightarrow> w x - \<phi> x \<le> w y - \<phi> y"
    using lm by blast
  have step: "1 \<le> op_usc F (g x) (H - \<delta> *\<^sub>R mat 1)"
    if d: "0 < \<delta>" for \<delta>
  proof -
    have symM: "transpose (H - \<delta> *\<^sub>R mat 1) = H - \<delta> *\<^sub>R mat 1"
      by (rule transpose_shift_diff[OF symH])
    obtain r where r0: "0 < r"
      and mino: "\<And>z. z \<in> ball x r \<Longrightarrow>
        \<phi> x + g x \<bullet> (z - x)
          + ((z - x) \<bullet> ((H - \<delta> *\<^sub>R mat 1) *v (z - x))) / 2 \<le> \<phi> z"
    proof (rule test_fun_quadratic_minorates[OF tf d])
      fix rr :: real
      assume a1: "0 < rr" and a2: "\<And>z. z \<in> ball x rr \<Longrightarrow>
        \<phi> x + g x \<bullet> (z - x)
          + ((z - x) \<bullet> ((H - \<delta> *\<^sub>R mat 1) *v (z - x))) / 2 \<le> \<phi> z"
      show thesis by (rule that[OF a1 a2])
    qed
    define \<psi> where "\<psi> = (\<lambda>z. \<phi> x + (g x \<bullet> (z - x)
      + ((z - x) \<bullet> ((H - \<delta> *\<^sub>R mat 1) *v (z - x))) / 2))"
    define gg where "gg = (\<lambda>z. g x + (H - \<delta> *\<^sub>R mat 1) *v (z - x))"
    have tfp: "test_fun_C2 \<psi> gg (H - \<delta> *\<^sub>R mat 1) x"
      unfolding \<psi>_def gg_def
      by (rule test_fun_C2_add_const[OF jet_test_fun_C2[OF symM]])
    have ggx: "gg x = g x" unfolding gg_def by simp
    have psix: "\<psi> x = \<phi> x" unfolding \<psi>_def by simp
    obtain B where B: "\<And>z. z \<in> K \<Longrightarrow>
      g x \<bullet> (z - x)
        + ((z - x) \<bullet> ((H - \<delta> *\<^sub>R mat 1) *v (z - x))) / 2 \<le> B"
    proof (rule quad_bdd_above_on_bounded[OF Kb,
            where p = "g x" and yh = x and M = "H - \<delta> *\<^sub>R mat 1"])
      fix BB :: real
      assume "\<And>z. z \<in> K \<Longrightarrow>
        g x \<bullet> (z - x)
          + ((z - x) \<bullet> ((H - \<delta> *\<^sub>R mat 1) *v (z - x))) / 2 \<le> BB"
      then show thesis by (rule that)
    qed
    have Bp: "\<And>z. z \<in> K \<Longrightarrow> \<psi> z \<le> \<phi> x + B"
      unfolding \<psi>_def using B by simp
    have r0': "0 < min r e0" using r0 e00 by simp
    have lm': "w x - \<psi> x \<le> w y - \<psi> y" if y: "y \<in> ball x (min r e0)" for y
    proof -
      have y1: "y \<in> ball x r" using y by simp
      have y2: "y \<in> ball x e0" using y by simp
      have "\<psi> y \<le> \<phi> y" unfolding \<psi>_def using mino[OF y1] by simp
      then show ?thesis using lme[OF y2] unfolding psix by simp
    qed
    have "1 \<le> op_usc F (gg x) (H - \<delta> *\<^sub>R mat 1)"
      by (rule visc_supersol_env2_local[OF sup x tfp wlo Bp r0' lm'])
    then show ?thesis unfolding ggx .
  qed
  show "1 \<le> op_usc F (g x) H"
    by (rule op_usc_ge_one_shift[OF step])
qed

text \<open>\<open>quad_bdd_below_on_bounded\<close> lives in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

text \<open>The subsolution counterpart of \<open>visc_supersol_env_imp_jet\<close> lands on the
  envelope-free notion, since \<open>F\<^sub>* = F\<close> at symmetric matrices (the locale's
  \<open>lsc_at_zero\<close> at \<open>p = 0\<close> and \<open>lsc_off_zero\<close>
  elsewhere); only the touching needs upgrading from global on \<open>K\<close> to local,
  via @{thm [source] visc_subsol_env2_local}.\<close>

context geometric_operator
begin

theorem visc_subsol_env_imp_visc_subsol:
  fixes K :: "(real^'n::finite) set" and u :: "real^'n \<Rightarrow> real"
  assumes sub: "subsol_env2 K \<Omega> u"
    and Kb: "bounded K"
    and uhi: "\<And>y. y \<in> K \<Longrightarrow> u y \<le> Bu"
  shows "subsol \<Omega> u"
  unfolding subsol_iff
proof (intro ballI allI impI)
  fix x :: "real^'n" and \<phi> :: "real^'n \<Rightarrow> real"
    and g :: "real^'n \<Rightarrow> real^'n" and H :: "real^'n^'n"
  assume x: "x \<in> \<Omega>" and tf: "test_fun_at \<phi> g H x"
    and lm: "\<exists>e>0. \<forall>y \<in> ball x e. u y - \<phi> y \<le> u x - \<phi> x"
  have symH: "transpose H = H" using tf unfolding test_fun_at_def by blast
  obtain e0 where e00: "0 < e0"
    and lme: "\<And>y. y \<in> ball x e0 \<Longrightarrow> u y - \<phi> y \<le> u x - \<phi> x"
    using lm by blast
  have step: "F (g x) (H + \<delta> *\<^sub>R mat 1) \<le> 1" if d: "0 < \<delta>" for \<delta>
  proof -
    have symM: "transpose (H + \<delta> *\<^sub>R mat 1) = H + \<delta> *\<^sub>R mat 1"
      by (rule transpose_shift_add[OF symH])
    obtain r where r0: "0 < r"
      and majo: "\<And>z. z \<in> ball x r \<Longrightarrow>
        \<phi> z \<le> \<phi> x + g x \<bullet> (z - x)
          + ((z - x) \<bullet> ((H + \<delta> *\<^sub>R mat 1) *v (z - x))) / 2"
    proof (rule test_fun_quadratic_dominates[OF tf d])
      fix rr :: real
      assume a1: "0 < rr" and a2: "\<And>z. z \<in> ball x rr \<Longrightarrow>
        \<phi> z \<le> \<phi> x + g x \<bullet> (z - x)
          + ((z - x) \<bullet> ((H + \<delta> *\<^sub>R mat 1) *v (z - x))) / 2"
      show thesis by (rule that[OF a1 a2])
    qed
    define \<psi> where "\<psi> = (\<lambda>z. \<phi> x + (g x \<bullet> (z - x)
      + ((z - x) \<bullet> ((H + \<delta> *\<^sub>R mat 1) *v (z - x))) / 2))"
    define gg where "gg = (\<lambda>z. g x + (H + \<delta> *\<^sub>R mat 1) *v (z - x))"
    have tfp: "test_fun_C2 \<psi> gg (H + \<delta> *\<^sub>R mat 1) x"
      unfolding \<psi>_def gg_def
      by (rule test_fun_C2_add_const[OF jet_test_fun_C2[OF symM]])
    have ggx: "gg x = g x" unfolding gg_def by simp
    have psix: "\<psi> x = \<phi> x" unfolding \<psi>_def by simp
    obtain B where B: "\<And>z. z \<in> K \<Longrightarrow>
      B \<le> g x \<bullet> (z - x)
        + ((z - x) \<bullet> ((H + \<delta> *\<^sub>R mat 1) *v (z - x))) / 2"
    proof (rule quad_bdd_below_on_bounded[OF Kb,
            where p = "g x" and yh = x and M = "H + \<delta> *\<^sub>R mat 1"])
      fix BB :: real
      assume "\<And>z. z \<in> K \<Longrightarrow>
        BB \<le> g x \<bullet> (z - x)
          + ((z - x) \<bullet> ((H + \<delta> *\<^sub>R mat 1) *v (z - x))) / 2"
      then show thesis by (rule that)
    qed
    have Bp: "\<And>z. z \<in> K \<Longrightarrow> \<phi> x + B \<le> \<psi> z"
      unfolding \<psi>_def using B by simp
    have r0': "0 < min r e0" using r0 e00 by simp
    have lm': "u y - \<psi> y \<le> u x - \<psi> x" if y: "y \<in> ball x (min r e0)" for y
    proof -
      have y1: "y \<in> ball x r" using y by simp
      have y2: "y \<in> ball x e0" using y by simp
      have "\<phi> y \<le> \<psi> y" unfolding \<psi>_def using majo[OF y1] by simp
      then show ?thesis using lme[OF y2] unfolding psix by simp
    qed
    have lsc: "F_lsc (gg x) (H + \<delta> *\<^sub>R mat 1) \<le> 1"
      by (rule visc_subsol_env2_local[OF sub x tfp uhi Bp r0' lm'])
    show ?thesis
    proof (cases "g x = 0")
      case True
      have "F_lsc (0 :: real^'n) (H + \<delta> *\<^sub>R mat 1)
          = ereal (F (0 :: real^'n) (H + \<delta> *\<^sub>R mat 1))"
        by (rule lsc_at_zero)
      then show ?thesis using lsc unfolding ggx True by simp
    next
      case False
      have "F_lsc (g x) (H + \<delta> *\<^sub>R mat 1)
          = ereal (F (g x) (H + \<delta> *\<^sub>R mat 1))"
        by (rule lsc_off_zero[OF symM False])
      then show ?thesis using lsc unfolding ggx by simp
    qed
  qed
  show "F (g x) H \<le> 1"
  proof (rule field_le_epsilon)
    fix e :: real assume e0: "0 < e"
    obtain C where C0: "0 < C"
      and gap: "\<And>p M \<delta>. 0 \<le> \<delta> \<Longrightarrow> F p M \<le> F p (M + \<delta> *\<^sub>R mat 1) + C * \<delta>"
      using shift_bound_pos by blast
    define \<delta> where "\<delta> = e / C"
    have d0: "0 < \<delta>" unfolding \<delta>_def using e0 C0 by simp
    have eq: "C * \<delta> = e"
      unfolding \<delta>_def using C0 by simp
    show "F (g x) H \<le> 1 + e"
      using gap[of \<delta> "g x" H] d0 step[OF d0] eq by linarith
  qed
qed


subsection \<open>Where the strictness comes from\<close>

text \<open>\<open>F\<close> has no zeroth-order term, so a subsolution cannot be made strict
  by subtracting a constant. But \<open>F\<close> is positively homogeneous in \<open>M\<close>
  (\<open>homogeneous\<close>) and invariant under positive dilations of \<open>p\<close>
  (\<open>dilation\<close>): scaling a subsolution by \<open>\<theta> \<in> (0,1)\<close> sends \<open>(p, X)\<close> to
  \<open>(\<theta> p, \<theta> X)\<close> and \<open>F(p,X) \<le> 1\<close> to the strict
  \<open>F(\<theta> p, \<theta> X) \<le> \<theta> < 1\<close>.  For the operator of Eq. (1.9),
  \<open>F(p, M) = Inf {- tr(M a)/2 | a feasible}\<close>, the dilation invariance holds
  because the feasible set depends on \<open>p\<close> only through \<open>a *v p = 0\<close>.\<close>

text \<open>Scaling a subsolution by \<open>\<theta> \<in> (0,1)\<close> makes its operator inequality
  strict, since \<open>F\<close> has no zeroth-order term. With degenerate
  ellipticity (\<open>elliptic\<close>), a scaled subsolution and an unscaled
  supersolution sharing a jet pair \<open>X \<preceq> Y\<close> are inconsistent -- the
  contradiction underlying Theorem 4.2(a).\<close>

subsection \<open>Scaling a subsolution\<close>

text \<open>A test function scales, so a subsolution scaled by \<open>\<theta> \<in> (0,1)\<close>
  satisfies the strict operator inequality at each of its test points.\<close>


subsection \<open>Freezing one variable in the doubled maximum\<close>

text \<open>The two frozen penalties are smooth quadratics with the same gradient
  \<open>\<alpha> *\<^sub>R (xh - yh)\<close> at their respective points, and Hessians
  \<open>\<alpha> *\<^sub>R mat 1\<close> and \<open>- \<alpha> *\<^sub>R mat 1\<close>. The common gradient lets the two
  viscosity inequalities be compared at a common \<open>p\<close>; the wrongly-ordered
  Hessians are why the theorem on sums is needed to replace them by an
  ordered pair \<open>X \<preceq> Y\<close>.\<close>

text \<open>The same gradient at the other frozen point, letting the subsolution
  and supersolution inequalities be evaluated at a common vector
  \<open>p = \<alpha> *\<^sub>R (xh - yh)\<close>.\<close>

text \<open>The two Hessians, \<open>\<alpha> I\<close> and \<open>- \<alpha> I\<close>, are ordered the wrong way, the
  obstruction the theorem on sums removes.\<close>

text \<open>Packaging both frozen penalties as test functions supplies exactly the
  hypotheses \<open>visc_subsol\<close> and \<open>supersol_jet\<close> require: freezing one
  variable of the doubled maximum leaves \<open>u\<close> minus the first penalty
  maximal at \<open>xh\<close>, and \<open>w\<close> minus the second minimal at \<open>yh\<close>. So the
  doubled maximum feeds into the two viscosity inequalities.\<close>

subsection \<open>What naive doubling delivers\<close>

text \<open>Feeding the two frozen test functions into the two viscosity
  definitions gives the two operator inequalities at the common vector
  \<open>p = \<alpha> *\<^sub>R (xh - yh)\<close>, with Hessians \<open>\<alpha> I\<close> and \<open>- \<alpha> I\<close>.\<close>

text \<open>Degenerate ellipticity would close the argument if the Hessians were
  ordered \<open>X \<preceq> Y\<close>, i.e. \<open>psd ((- \<alpha>) *\<^sub>R mat 1 - \<alpha> *\<^sub>R mat 1)\<close>; for
  \<open>\<alpha> > 0\<close> that matrix is \<open>(- 2 * \<alpha>) *\<^sub>R mat 1\<close>, negative definite. So the
  two inequalities arrive with Hessians ordered the wrong way, and replacing
  \<open>(\<alpha> I, - \<alpha> I)\<close> by an ordered pair \<open>X \<preceq> Y\<close> is the theorem on sums' role.\<close>

subsection \<open>From the abstract matrix inequality to \<open>psd\<close>\<close>

text \<open>\<open>matrix_diff_vec\<close> lives in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


subsection \<open>The envelope route for removing the jet correction\<close>

text \<open>\<open>superjet_local_max\<close> introduces a strictly convex correction
  \<open>(\<delta>/2) * norm k\<^sup>2\<close>, so the matrix reaching the operator is \<open>X + \<delta> I\<close>
  rather than \<open>X\<close>. Removing \<open>\<delta>\<close> passes to closed second-order jets via the
  envelopes: the two envelope inequalities sandwich the sharp one, and
  the envelope-free notions already imply the envelope ones on an open
  \<open>\<Omega> \<subseteq> K\<close> (@{thm [source] visc_subsol_gen_filter_mono} with
  @{thm [source] nhds_le_principal_of_open}).\<close>

text \<open>And the same for the upper envelope, by the dual argument: the same
  translation carries \<open>ball (p, M) e\<close> onto \<open>ball (p, N) e\<close>, and the
  integrand decreases along it, so the suprema compare and then the infima
  over the radius do.\<close>

subsection \<open>The envelope-form contradiction\<close>

text \<open>Ellipticity of the envelopes alone gives \<open>F\<^sup>*(p, Y) \<le> F\<^sup>*(p, X)\<close>, but
  combined with \<open>F\<^sub>*(p, X) < 1\<close> this is consistent wherever the two
  envelopes separate at \<open>(p, X)\<close>, i.e. wherever \<open>F\<close> is discontinuous. The
  mixed-envelope inequalities close only where the envelopes coincide with
  \<open>F\<close>, which the locale assumes at symmetric matrices off the origin
  (\<open>lsc_off_zero\<close>, \<open>usc_off_zero\<close>; for the operator of Eq. (1.9) this is
  Lemma 3.1's last clause), reducing the envelope contradiction to the
  envelope-free one.\<close>

theorem env_strict_contradiction:
  fixes X Y :: "real^'n::finite^'n"
  assumes psd: "psd (Y - X)"
    and symX: "transpose X = X" and symY: "transpose Y = Y"
    and p: "p \<noteq> 0" and sub: "F_lsc p X < 1" and sup: "1 \<le> F_usc p Y"
  shows False
proof -
  have eX: "F_lsc p X = ereal (F p X)"
    by (rule lsc_off_zero[OF symX p])
  have eY: "F_usc p Y = ereal (F p Y)"
    by (rule usc_off_zero[OF symY p])
  have subr: "F p X < 1"
    using sub unfolding eX by (simp add: one_ereal_def)
  have supr: "1 \<le> F p Y"
    using sup unfolding eY by (simp add: one_ereal_def)
  show False
    using elliptic[OF psd, of p] subr supr by linarith
qed

end

text \<open>The same for the non-strict sandwich, the form in which the envelope
  inequalities first arrive from the doubling.\<close>

text \<open>At \<open>p = 0\<close> the two envelopes may disagree: \<open>lsc_at_zero\<close> gives
  \<open>F\<^sub>*(0, M) = F(0, M)\<close>, while for the operator of Eq. (1.9) \<open>eq36\<close>
  gives \<open>F\<^sup>*(0, M) = eq36_rhs k L M\<close>,
  whose index range omits the eigenvalue \<open>\<lambda>\<^sub>(\<^sub>1\<^sub>)(M)\<close> of Eq. (3.5). So
  \<open>1 \<le> F\<^sup>*(0, Y)\<close> is strictly weaker than \<open>1 \<le> F(0, Y)\<close>, and envelope
  ellipticity cannot close the gap -- the degeneracy Lemma 3.1 isolates, and
  why the doubling needs the shared gradient to be nonzero.\<close>

subsection \<open>The dichotomy the side condition forces on the doubling\<close>

text \<open>In the doubling, the shared gradient at the maximising pair
  \<open>(x', y')\<close> of \<open>\<Phi>(x,y) = u x - w y - (\<alpha>/2) \<bar>x - y\<bar>\<^sup>2\<close> is
  \<open>p = \<alpha> (x' - y')\<close>, so \<open>p \<noteq> 0\<close> means the maximising pair is off the
  diagonal. For \<open>\<alpha> \<noteq> 0\<close> the gradient vanishes precisely on the diagonal.\<close>

subsection \<open>The penalty estimate\<close>

text \<open>\<open>doubling_dist_bound\<close> lives in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

subsection \<open>The dichotomy for a general penalty\<close>

text \<open>\<open>doubling_diagonal_max_gen\<close>, \<open>doubling_off_diagonal_gen\<close>, \<open>doubling_penalty_bound_gen\<close> live in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

subsection \<open>Monotonicity of the doubled maximum in the penalty parameter\<close>

text \<open>The other ingredient of the \<open>\<alpha> \<rightarrow> \<infinity>\<close> passage: the doubled maximum is
  antimonotone in \<open>\<alpha>\<close>, since a larger penalty can only decrease the
  supremum, the maximiser for larger \<open>\<alpha>\<close> being an admissible competitor for
  smaller \<open>\<alpha>\<close>. Since the doubled maximum is at least the value of
  \<open>u - w\<close> at any diagonal point, this pins the family between two
  \<open>\<alpha>\<close>-independent bounds, so the limit exists without a compactness
  argument.\<close>

subsection \<open>The components of the maximiser merge, with no subsequences\<close>

text \<open>Because \<open>doubling_dist_bound\<close> comes with an explicit constant,
  \<open>x'\<^sub>\<alpha> - y'\<^sub>\<alpha> \<rightarrow> 0\<close> is a sandwich between \<open>0\<close> and \<open>2D/\<alpha>\<close>, needing
  neither compactness of \<open>K\<close> nor a subsequence.\<close>

subsection \<open>The diagonal branch \<open>p = 0\<close>\<close>

text \<open>The dichotomy leaves the diagonal branch \<open>p = 0\<close>. For the operator
  of Eq. (1.9), since \<open>eq36\<close> identifies \<open>F\<^sup>*(0, M)\<close> with
  \<open>eq36_rhs k L M\<close>, ellipticity of \<open>F\<^sup>*\<close>
  transfers to \<open>eq36_rhs\<close>, a statement about the eigenvalue expression of
  Eq. (3.6).\<close>

text \<open>The gap between the two envelopes at the origin,
  \<open>eq36_rhs k L M - F(0, M)\<close>, is nonnegative: \<open>ell_op_le_eq36\<close> specialised
  to \<open>p = 0\<close>, combined with \<open>ell_op_lsc_at_zero\<close>.\<close>

text \<open>For that operator, at \<open>p = 0\<close>, \<open>F\<^sub>*(0,X) = F(0,X)\<close> and
  \<open>F\<^sup>*(0,Y) = eq36_rhs k L Y\<close>, with
  \<open>eq36_rhs\<close> antitone; the supersolution gives \<open>1 \<le> eq36_rhs k L X\<close> and
  the subsolution \<open>F(0,X) < 1\<close>. These are consistent because
  \<open>F(0,X) \<le> eq36_rhs k L X\<close> with room to spare, so the envelope gap at
  \<open>p = 0\<close> does not vanish in general.\<close>

subsection \<open>Existence of the maximising pair\<close>

text \<open>\<open>doubling_maximiser_exists_gen\<close> lives in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

text \<open>The packaged form: on a compact \<open>K\<close> the doubling produces a
  maximising pair together with the penalty bound and the diagonal lower
  bound already proved for it.\<close>

subsection \<open>Discharging the remaining bare hypothesis of the penalty estimate\<close>

text \<open>\<open>doubling_upper_bound_exists\<close> lives in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

text \<open>Combining the two attainment results with the penalty estimate: on a
  compact \<open>K\<close> with continuous data the doubling produces a maximising pair
  whose penalty is bounded by an \<open>\<alpha>\<close>-independent constant, and whose two
  components are within \<open>O(1/\<surd>\<alpha>)\<close> of each other.\<close>

subsection \<open>Producing the local-max hypotheses from a jet\<close>

text \<open>\<open>visc_subsol_scaled_uniform\<close> and \<open>supersol_jet\<close> take local max/min
  statements for the jet test function as hypotheses; these are
  exactly what \<open>superjet_local_max\<close> yields from an Alexandrov jet once the
  test matrix is corrected by \<open>\<delta> I\<close>, since the \<open>(\<delta>/2)\<bar>k\<bar>\<^sup>2\<close> slack it
  leaves is precisely the extra quadratic form contributed by \<open>\<delta> I\<close>.\<close>

text \<open>\<open>quad_form_shift_identity\<close> lives in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>

text \<open>\<open>quad_form_shift_identity_neg\<close> lives in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>

text \<open>The mirror image for the supersolution side: a subjet of \<open>v\<close> at \<open>yh\<close>
  gives the local-min statement, with correction \<open>- \<delta> I\<close>, following from
  the same theorem applied to \<open>-v\<close>, whose jet data is \<open>(-p, -A)\<close>.\<close>

subsection \<open>The jet hypothesis only ever needs one side\<close>

text \<open>\<open>superjet_local_max_onesided\<close> lives in @{theory Second_Order_Viscosity_Analysis.Theorem_On_Sums}.\<close>

text \<open>\<open>onesided_of_dominated\<close> lives in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>


text \<open>\<open>jet_imp_local_min_test_onesided\<close> lives in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

subsection \<open>Removing the jet correction\<close>

text \<open>The \<open>\<delta>\<close> from \<open>superjet_local_max\<close> cannot cancel against
  \<open>X \<preceq> Y\<close>: correcting to \<open>X + \<delta> I\<close>, \<open>Y - \<delta> I\<close> would need
  \<open>Y - X \<succeq> 2\<delta> I\<close>, but the theorem on sums gives only \<open>Y - X \<succeq> 0\<close>, so
  \<open>\<delta>\<close> is removed by a limit instead. Degenerate ellipticity gives
  \<open>F(p, M + \<delta> I) \<le> F(p, M)\<close>, and since \<open>F\<^sub>*\<close> is the limit over points near
  \<open>(p, M)\<close>, \<open>F(p, M + \<delta> I) \<le> 1\<close> for all \<open>\<delta>\<close> already gives
  \<open>F\<^sub>*(p, M) \<le> 1\<close>.\<close>

text \<open>The mirror statement for the upper envelope, needed by the
  supersolution side: a lower bound at the shifted matrices \<open>M - \<delta> I\<close>
  transfers to \<open>F\<^sup>*\<close> at \<open>M\<close>, for the dual reason.\<close>

subsection \<open>Making the strictness survive the limit\<close>

text \<open>The two shift theorems above are stated with bound \<open>1\<close>, enough for the
  sandwich but not the contradiction: passing to the limit turns
  \<open>F(p, X + \<delta> I) < 1\<close> into \<open>F\<^sub>*(p, X) \<le> 1\<close>, losing strictness. The fix:
  the strictness from \<open>\<theta>\<close>-scaling is uniform,
  \<open>F(\<theta> p, \<theta> X) = \<theta> F(p, X) \<le> \<theta>\<close> with \<open>\<theta> < 1\<close> independent of \<open>\<delta>\<close>, and a
  uniform bound survives the limit, so the shift theorems are restated with
  an arbitrary bound \<open>c\<close> in place of \<open>1\<close>.\<close>

subsection \<open>The uniform strict bound, and the shifted families\<close>

text \<open>A subsolution scaled by \<open>\<theta>\<close> satisfies \<open>F \<le> \<theta>\<close> at each of its test
  points, which for \<open>\<theta> < 1\<close> is stronger than \<open>F < 1\<close>; this is the bound
  that survives the \<open>\<delta> \<rightarrow> 0\<close> limit.\<close>

theorem visc_subsol_scaled_uniform:
  fixes u :: "real^'n::finite \<Rightarrow> real" and H :: "real^'n^'n"
    and F :: "real^'n \<Rightarrow> real^'n^'n \<Rightarrow> real"
  assumes sub: "visc_subsol_gen test_fun_at nhds (\<lambda>p M. ereal (F p M)) \<Omega> u"
    and dil: "\<And>c M. 0 < c \<Longrightarrow> F (c *\<^sub>R g x) M = F (g x) M"
    and hom: "\<And>t. 0 < t \<Longrightarrow> F (g x) (t *\<^sub>R H) = t * F (g x) H"
    and t: "0 < \<theta>"
    and x: "x \<in> \<Omega>"
    and tf: "test_fun_at \<phi> g H x"
    and maxloc: "\<exists>e>0. \<forall>y \<in> ball x e. \<theta> * u y - \<phi> y \<le> \<theta> * u x - \<phi> x"
  shows "F (g x) H \<le> \<theta>"
proof -
  define c where "c = 1/\<theta>"
  have c0: "0 < c" unfolding c_def using t by simp
  have tfc: "test_fun_at (\<lambda>z. c * \<phi> z) (\<lambda>z. c *\<^sub>R g z) (c *\<^sub>R H) x"
    by (rule test_fun_at_scaleR[OF tf c0])
  obtain e where e: "0 < e"
    and m: "\<And>y. y \<in> ball x e \<Longrightarrow> \<theta> * u y - \<phi> y \<le> \<theta> * u x - \<phi> x"
    using maxloc by blast
  have mc: "\<exists>e>0. \<forall>y \<in> ball x e. u y - c * \<phi> y \<le> u x - c * \<phi> x"
  proof (rule exI[of _ e], intro conjI ballI)
    show "0 < e" by (rule e)
    fix y assume y: "y \<in> ball x e"
    have "(\<theta> * u y - \<phi> y) * c \<le> (\<theta> * u x - \<phi> x) * c"
      using m[OF y] c0 by (intro mult_right_mono) auto
    thus "u y - c * \<phi> y \<le> u x - c * \<phi> x"
      unfolding c_def using t by (simp add: field_simps)
  qed
  have "ereal (F ((\<lambda>z. c *\<^sub>R g z) x) (c *\<^sub>R H)) \<le> 1"
    using sub x tfc mc unfolding visc_subsol_gen_nhds by blast
  hence step: "F (c *\<^sub>R g x) (c *\<^sub>R H) \<le> 1" by simp
  have "F (c *\<^sub>R g x) (c *\<^sub>R H) = F (g x) (c *\<^sub>R H)"
    by (rule dil) (use c0 in simp)
  also have "\<dots> = c * F (g x) H"
    by (rule hom[OF c0])
  finally have "c * F (g x) H \<le> 1" using step by simp
  thus ?thesis
    unfolding c_def using t by (simp add: field_simps)
qed

text \<open>Symmetry of the corrected matrices, needed by the jet test function:
  transposition is additive entrywise, so both directions of the correction
  preserve symmetry.\<close>

theorem supersol_shifted_bound_onesided:
  fixes w :: "real^'n::finite \<Rightarrow> real" and Ym :: "real^'n^'n"
    and G :: "real^'n \<Rightarrow> real^'n^'n \<Rightarrow> ereal"
  assumes sup: "visc_supersol_gen test_fun_at nhds G \<Omega> w"
    and yh: "yh \<in> \<Omega>"
    and Ys: "transpose Ym = Ym"
    and ub: "\<And>c. 0 < c \<Longrightarrow> \<forall>\<^sub>F hh in at 0.
        ((- w) (yh + hh) - (- w) yh - (- p) \<bullet> hh
          - (hh \<bullet> ((- Ym) *v hh))/2) / (norm hh)\<^sup>2 < c"
    and d: "0 < \<delta>"
  shows "1 \<le> G p (Ym - \<delta> *\<^sub>R mat 1)"
proof -
  have sym: "transpose (Ym - \<delta> *\<^sub>R mat 1) = Ym - \<delta> *\<^sub>R mat 1"
    by (rule transpose_shift_diff[OF Ys])
  have tf: "test_fun_at
      (\<lambda>z. p \<bullet> (z - yh)
        + ((z - yh) \<bullet> ((Ym - \<delta> *\<^sub>R mat 1) *v (z - yh)))/2)
      (\<lambda>z. p + (Ym - \<delta> *\<^sub>R mat 1) *v (z - yh)) (Ym - \<delta> *\<^sub>R mat 1) yh"
    by (rule jet_test_fun_at[OF sym])
  have g: "(\<lambda>z. p + (Ym - \<delta> *\<^sub>R mat 1) *v (z - yh)) yh = p"
    by simp
  have minloc: "\<exists>e>0. \<forall>z \<in> ball yh e.
      w yh - (p \<bullet> (yh - yh)
          + ((yh - yh) \<bullet> ((Ym - \<delta> *\<^sub>R mat 1) *v (yh - yh)))/2)
      \<le> w z - (p \<bullet> (z - yh)
          + ((z - yh) \<bullet> ((Ym - \<delta> *\<^sub>R mat 1) *v (z - yh)))/2)"
    by (rule jet_imp_local_min_test_onesided[OF ub d])
  have "1 \<le> G ((\<lambda>z. p + (Ym - \<delta> *\<^sub>R mat 1) *v (z - yh)) yh)
      (Ym - \<delta> *\<^sub>R mat 1)"
    using sup yh tf minloc unfolding visc_supersol_gen_nhds by blast
  thus ?thesis unfolding g .
qed

(*<*)
end
(*>*)
