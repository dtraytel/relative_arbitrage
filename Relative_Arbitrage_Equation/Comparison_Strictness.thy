section \<open>Strictness, scaling, and the envelope route\<close>

(*<*)
theory Comparison_Strictness
  imports
    Geometric_Operator
begin

(*>*)


text \<open>Facts about the solution notions that the comparison argument uses
  before any variable is doubled: congruence and monotonicity of the
  notions with touching over a set, the passage from touching over a
  bounded set to local touching, strict subsolutions by scaling, and the
  contradiction between a strict subsolution and a supersolution at a
  common nonzero gradient with ordered Hessians.\<close>

subsection \<open>Congruence, monotonicity and test classes\<close>

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

subsection \<open>From touching over a set to local touching\<close>

text \<open>A local touching is deepened by a quartic into a touching over
  \<open>K\<close> (@{thm [source] local_max_quartic_deepen}), so a solution whose
  test functions touch over a bounded \<open>K\<close> satisfies its inequality also
  at test functions that touch only locally.  The \<open>C\<^sup>2\<close> versions use
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

text \<open>For the upper envelope of any operator, a supersolution whose
  \<open>C\<^sup>2\<close> test functions touch over a bounded \<open>K\<close> is a supersolution with
  \<^const>\<open>test_fun_at\<close> test functions touching locally.  Below a
  \<^const>\<open>test_fun_at\<close> function with Hessian \<open>H\<close> lies, near \<open>x\<close>, the
  quadratic with the same gradient and Hessian \<open>H - \<delta> I\<close>, which gives
  \<open>1 \<le> F\<^sup>*(p, H - \<delta> I)\<close>; and \<open>F\<^sup>*\<close> passes to the limit \<open>\<delta> \<rightarrow> 0\<close>
  (\<open>op_usc_ge_one_shift\<close>).\<close>

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

text \<open>The subsolution counterpart of \<open>visc_supersol_env_imp_jet\<close> lands on
  the envelope-free notion: the quadratic with Hessian \<open>H + \<delta> I\<close> lies
  above the test function near \<open>x\<close> and gives
  \<open>F\<^sub>*(p, H + \<delta> I) \<le> 1\<close> (via @{thm [source] visc_subsol_env2_local});
  \<open>F\<^sub>* = F\<close> at symmetric matrices (the locale's \<open>lsc_at_zero\<close> at
  \<open>p = 0\<close> and \<open>lsc_off_zero\<close> elsewhere), and the locale's \<open>shift_bound\<close>
  removes \<open>\<delta>\<close>.\<close>

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


subsection \<open>The contradiction at ordered Hessians\<close>

text \<open>A strict subsolution inequality \<open>F\<^sub>*(p, X) < 1\<close> and a
  supersolution inequality \<open>1 \<le> F\<^sup>*(p, Y)\<close> at a common gradient
  \<open>p \<noteq> 0\<close> with \<open>X \<preceq> Y\<close> contradict each other: off \<open>p = 0\<close> both
  envelopes are \<open>F\<close> at symmetric matrices (\<open>lsc_off_zero\<close>,
  \<open>usc_off_zero\<close>), and degenerate ellipticity gives
  \<open>F(p, Y) \<le> F(p, X)\<close>.  At \<open>p = 0\<close> the two envelopes may differ, so
  \<open>1 \<le> F\<^sup>*(0, Y)\<close> is weaker than \<open>1 \<le> F(0, Y)\<close>; this is why the
  doubling has to keep the common gradient away from zero.\<close>

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

subsection \<open>Strict subsolutions by scaling\<close>

text \<open>\<open>F\<close> has no zeroth-order term, so a subsolution cannot be made strict
  by subtracting a constant.  If \<open>F\<close> is positively homogeneous in \<open>M\<close>
  and invariant under positive dilations of \<open>p\<close> (the hypotheses \<open>hom\<close>
  and \<open>dil\<close>, needed only at the gradient in question), then a test
  function touching \<open>\<theta> u\<close> from above, for \<open>\<theta> \<in> (0, 1)\<close>, gives
  \<open>F \<le> \<theta>\<close> at its jet.  The bound \<open>\<theta>\<close> does not depend on any later
  perturbation, so it survives the limit that removes a jet correction
  \<open>\<delta> I\<close>, where a bare strict inequality would turn into \<open>\<le> 1\<close>.\<close>

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

subsection \<open>The supersolution inequality at a one-sided subjet\<close>

text \<open>If \<open>(p, Y)\<close> is a second-order subjet of \<open>w\<close> at \<open>yh\<close> in the
  one-sided sense of the hypothesis \<open>ub\<close>, then for every \<open>\<delta> > 0\<close> the
  quadratic with gradient \<open>p\<close> and Hessian \<open>Y - \<delta> I\<close> touches \<open>w\<close> from
  below near \<open>yh\<close> (\<open>jet_imp_local_min_test_onesided\<close>), so the
  supersolution inequality holds at \<open>(p, Y - \<delta> I)\<close>.  The correction
  cannot be cancelled against the ordering \<open>X \<preceq> Y\<close> that the theorem on
  sums provides, so it is removed by a limit instead.\<close>

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
