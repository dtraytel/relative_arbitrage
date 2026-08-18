section \<open>Strictness, scaling, and the envelope route\<close>

(*<*)
theory Comparison_Strictness
  imports Comparison_Jets
begin

(*>*)


text \<open>What the operator contributes to the comparison argument: it reads
  only the symmetric part of the Hessian, a subsolution can be scaled to a
  strict one, and the envelope forms of the two solution notions can be
  played against each other.  Nothing here doubles a variable yet.\<close>

section \<open>\<open>F\<close> reads only the symmetric part of \<open>M\<close>\<close>

text \<open>Definition 3.1 takes the envelopes of \<open>F\<close> over \<open>\<real>\<^sup>n \<times> \<S>\<^sup>n\<close>, the paper's
  symmetric matrices, whereas \<^const>\<open>ell_op_lsc\<close> and \<^const>\<open>ell_op_usc\<close> take them
  over \<open>\<real>\<^sup>n \<times> \<real>\<^sup>n\<^sup>\<times>\<^sup>n\<close>.  Nothing changes: the feasible matrices are psd, hence
  symmetric, so \<open>F\<close> factors through \<open>M \<mapsto> (M + M\<^sup>T)/2\<close>, and that map is a
  contraction fixing \<open>\<S>\<^sup>n\<close> --- so every ball around a symmetric \<open>M\<close> realises the
  same set of values as its symmetric part does.\<close>

text \<open>\<open>trace_mul_comm\<close> is HOL-Analysis's \<open>trace_mul_sym\<close>.\<close>

text \<open>\<open>matrix_mult_scaleR_left\<close> is \<open>scaleR_matrix_mult\<close> from
  @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>

lemma visc_subsol_env2_cong:
  fixes f1 f2 :: "real^'n::finite \<Rightarrow> real"
  assumes OK: "\<Omega> \<subseteq> K" and eq: "\<And>y. y \<in> K \<Longrightarrow> f1 y = f2 y"
    and h: "visc_subsol_env2 k L K \<Omega> f1"
  shows "visc_subsol_env2 k L K \<Omega> f2"
  unfolding visc_subsol_env2_def
proof (intro ballI allI impI)
  fix x :: "real^'n" and \<phi> g and H :: "real^'n^'n"
  assume x: "x \<in> \<Omega>" and tf: "test_fun_C2 \<phi> g H x"
    and gl: "\<forall>y\<in>K. f2 y - \<phi> y \<le> f2 x - \<phi> x"
  have xK: "x \<in> K" using x OK by blast
  have "\<forall>y\<in>K. f1 y - \<phi> y \<le> f1 x - \<phi> x"
    using gl eq xK by (metis (no_types, lifting))
  then show "ell_op_lsc k L (g x) H \<le> 1"
    using h x tf unfolding visc_subsol_env2_def by blast
qed

lemma visc_supersol_env2_cong:
  fixes f1 f2 :: "real^'n::finite \<Rightarrow> real"
  assumes OK: "\<Omega> \<subseteq> K" and eq: "\<And>y. y \<in> K \<Longrightarrow> f1 y = f2 y"
    and h: "visc_supersol_env2 k L K \<Omega> f1"
  shows "visc_supersol_env2 k L K \<Omega> f2"
  unfolding visc_supersol_env2_def
proof (intro ballI allI impI)
  fix x :: "real^'n" and \<phi> g and H :: "real^'n^'n"
  assume x: "x \<in> \<Omega>" and tf: "test_fun_C2 \<phi> g H x"
    and gl: "\<forall>y\<in>K. f2 x - \<phi> x \<le> f2 y - \<phi> y"
  have xK: "x \<in> K" using x OK by blast
  have "\<forall>y\<in>K. f1 x - \<phi> x \<le> f1 y - \<phi> y"
    using gl eq xK by (metis (no_types, lifting))
  then show "1 \<le> ell_op_usc k L (g x) H"
    using h x tf unfolding visc_supersol_env2_def by blast
qed

lemma visc_supersol_env2_mono:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes "visc_supersol_env2 k L K \<Omega> u" and "\<Omega>' \<subseteq> \<Omega>"
  shows "visc_supersol_env2 k L K \<Omega>' u"
  using assms unfolding visc_supersol_env2_def by blast

lemma visc_subsol_env_imp_env2:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes "visc_subsol_env k L K \<Omega> u"
  shows "visc_subsol_env2 k L K \<Omega> u"
  using assms test_fun_C2_imp_test_fun_at
  unfolding visc_subsol_env_def visc_subsol_env2_def by blast

lemma visc_supersol_env_imp_env2:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes "visc_supersol_env k L K \<Omega> u"
  shows "visc_supersol_env2 k L K \<Omega> u"
  using assms test_fun_C2_imp_test_fun_at
  unfolding visc_supersol_env_def visc_supersol_env2_def by blast

text \<open>The two places where the paper-facing hypothesis is actually consumed:
  a local touching is deepened by a quartic into a global one over \<open>K\<close>.  The
  \<open>C\<^sup>2\<close> versions are the originals with @{thm [source] test_fun_C2_quartic_shift}
  in place of @{thm [source] test_fun_at_quartic_shift}; the quartic shift of a
  \<open>C\<^sup>2\<close> function is again \<open>C\<^sup>2\<close>, so nothing else moves.\<close>

theorem visc_supersol_env2_local:
  fixes K :: "(real^'n::finite) set" and w \<phi> :: "real^'n \<Rightarrow> real"
    and g :: "real^'n \<Rightarrow> real^'n" and H :: "real^'n^'n"
  assumes sup: "visc_supersol_env2 k L K \<Omega> w"
    and x\<Omega>: "x \<in> \<Omega>"
    and tf: "test_fun_C2 \<phi> g H x"
    and wlo: "\<And>y. y \<in> K \<Longrightarrow> Bw \<le> w y"
    and phi: "\<And>y. y \<in> K \<Longrightarrow> \<phi> y \<le> B\<phi>"
    and r0: "0 < r"
    and lm: "\<And>y. y \<in> ball x r \<Longrightarrow> w x - \<phi> x \<le> w y - \<phi> y"
  shows "1 \<le> ell_op_usc k L (g x) H"
proof -
  have r40: "0 < r ^ 4" using r0 by simp
  define C where "C = max 0 ((w x - \<phi> x - Bw + B\<phi>) / r ^ 4)"
  have C0: "0 \<le> C" unfolding C_def by simp
  have Cbig: "w x - \<phi> x - Bw + B\<phi> \<le> C * r ^ 4"
  proof -
    have "(w x - \<phi> x - Bw + B\<phi>) / r ^ 4 \<le> C" unfolding C_def by simp
    then have "(w x - \<phi> x - Bw + B\<phi>) / r ^ 4 * r ^ 4 \<le> C * r ^ 4"
      by (rule mult_right_mono) (use r40 in linarith)
    then show ?thesis using r40 by simp
  qed
  define \<psi> where "\<psi> = (\<lambda>z. \<phi> z - C * ((z - x) \<bullet> (z - x))\<^sup>2)"
  define gg where
    "gg = (\<lambda>z. g z - (4 * C * ((z - x) \<bullet> (z - x))) *\<^sub>R (z - x))"
  have tf': "test_fun_C2 \<psi> gg H x"
    unfolding \<psi>_def gg_def by (rule test_fun_C2_quartic_shift[OF tf])
  have ggx: "gg x = g x" unfolding gg_def by simp
  have psix: "\<psi> x = \<phi> x" unfolding \<psi>_def by simp
  have glob: "w x - \<psi> x \<le> w y - \<psi> y" if yK: "y \<in> K" for y
  proof (cases "y \<in> ball x r")
    case True
    have nn: "0 \<le> C * ((y - x) \<bullet> (y - x))\<^sup>2"
      by (rule mult_nonneg_nonneg[OF C0]) simp
    show ?thesis using lm[OF True] nn unfolding \<psi>_def psix[unfolded \<psi>_def]
      by simp
  next
    case False
    then have dxy: "r \<le> dist x y" by simp
    have sq: "r\<^sup>2 \<le> (y - x) \<bullet> (y - x)"
    proof -
      have "r \<le> norm (y - x)"
        using dxy by (simp add: dist_norm norm_minus_commute)
      then have "r\<^sup>2 \<le> (norm (y - x))\<^sup>2" using r0 by (intro power_mono) auto
      then show ?thesis by (simp add: dot_square_norm)
    qed
    have q4: "r ^ 4 \<le> ((y - x) \<bullet> (y - x))\<^sup>2"
    proof -
      have "(r\<^sup>2)\<^sup>2 \<le> ((y - x) \<bullet> (y - x))\<^sup>2" using sq by (intro power_mono) auto
      then show ?thesis by (simp add: power_even_eq)
    qed
    have cq: "C * r ^ 4 \<le> C * ((y - x) \<bullet> (y - x))\<^sup>2"
      by (rule mult_left_mono[OF q4 C0])
    have lo: "Bw \<le> w y" by (rule wlo[OF yK])
    have hi: "\<phi> y \<le> B\<phi>" by (rule phi[OF yK])
    show ?thesis unfolding \<psi>_def using Cbig cq lo hi by simp
  qed
  have "1 \<le> ell_op_usc k L (gg x) H"
    using sup[unfolded visc_supersol_env2_def] x\<Omega> tf' glob by blast
  then show ?thesis unfolding ggx .
qed

theorem visc_subsol_env2_local:
  fixes K :: "(real^'n::finite) set" and u \<phi> :: "real^'n \<Rightarrow> real"
    and g :: "real^'n \<Rightarrow> real^'n" and H :: "real^'n^'n"
  assumes sub: "visc_subsol_env2 k L K \<Omega> u"
    and x\<Omega>: "x \<in> \<Omega>"
    and tf: "test_fun_C2 \<phi> g H x"
    and uhi: "\<And>y. y \<in> K \<Longrightarrow> u y \<le> Bu"
    and phi: "\<And>y. y \<in> K \<Longrightarrow> B\<phi> \<le> \<phi> y"
    and r0: "0 < r"
    and lm: "\<And>y. y \<in> ball x r \<Longrightarrow> u y - \<phi> y \<le> u x - \<phi> x"
  shows "ell_op_lsc k L (g x) H \<le> 1"
proof -
  have r40: "0 < r ^ 4" using r0 by simp
  define C where "C = max 0 ((Bu - B\<phi> - (u x - \<phi> x)) / r ^ 4)"
  have C0: "0 \<le> C" unfolding C_def by simp
  have Cbig: "Bu - B\<phi> - (u x - \<phi> x) \<le> C * r ^ 4"
  proof -
    have "(Bu - B\<phi> - (u x - \<phi> x)) / r ^ 4 \<le> C" unfolding C_def by simp
    then have "(Bu - B\<phi> - (u x - \<phi> x)) / r ^ 4 * r ^ 4 \<le> C * r ^ 4"
      by (rule mult_right_mono) (use r40 in linarith)
    then show ?thesis using r40 by simp
  qed
  define \<psi> where "\<psi> = (\<lambda>z. \<phi> z - (- C) * ((z - x) \<bullet> (z - x))\<^sup>2)"
  define gg where
    "gg = (\<lambda>z. g z - (4 * (- C) * ((z - x) \<bullet> (z - x))) *\<^sub>R (z - x))"
  have tf': "test_fun_C2 \<psi> gg H x"
    unfolding \<psi>_def gg_def by (rule test_fun_C2_quartic_shift[OF tf])
  have ggx: "gg x = g x" unfolding gg_def by simp
  have psix: "\<psi> x = \<phi> x" unfolding \<psi>_def by simp
  have glob: "u y - \<psi> y \<le> u x - \<psi> x" if yK: "y \<in> K" for y
  proof (cases "y \<in> ball x r")
    case True
    have nn: "0 \<le> C * ((y - x) \<bullet> (y - x))\<^sup>2"
      by (rule mult_nonneg_nonneg[OF C0]) simp
    show ?thesis using lm[OF True] nn unfolding \<psi>_def psix[unfolded \<psi>_def]
      by simp
  next
    case False
    then have dxy: "r \<le> dist x y" by simp
    have sq: "r\<^sup>2 \<le> (y - x) \<bullet> (y - x)"
    proof -
      have "r \<le> norm (y - x)"
        using dxy by (simp add: dist_norm norm_minus_commute)
      then have "r\<^sup>2 \<le> (norm (y - x))\<^sup>2" using r0 by (intro power_mono) auto
      then show ?thesis by (simp add: dot_square_norm)
    qed
    have q4: "r ^ 4 \<le> ((y - x) \<bullet> (y - x))\<^sup>2"
    proof -
      have "(r\<^sup>2)\<^sup>2 \<le> ((y - x) \<bullet> (y - x))\<^sup>2" using sq by (intro power_mono) auto
      then show ?thesis by (simp add: power_even_eq)
    qed
    have cq: "C * r ^ 4 \<le> C * ((y - x) \<bullet> (y - x))\<^sup>2"
      by (rule mult_left_mono[OF q4 C0])
    have hi: "u y \<le> Bu" by (rule uhi[OF yK])
    have lo: "B\<phi> \<le> \<phi> y" by (rule phi[OF yK])
    show ?thesis unfolding \<psi>_def using Cbig cq hi lo by simp
  qed
  have "ell_op_lsc k L (gg x) H \<le> 1"
    using sub[unfolded visc_subsol_env2_def] x\<Omega> tf' glob by blast
  then show ?thesis unfolding ggx .
qed

text \<open>\<open>supersol_jet\<close> lives in @{theory Relative_Arbitrage.Viscosity_Definitions}.\<close>

theorem visc_supersol_env_imp_jet:
  fixes K :: "(real^'n::finite) set" and w :: "real^'n \<Rightarrow> real"
  assumes sup: "visc_supersol_env2 k L K \<Omega> w"
    and Kb: "bounded K"
    and wlo: "\<And>y. y \<in> K \<Longrightarrow> Bw \<le> w y"
  shows "supersol_jet k L \<Omega> w"
  unfolding supersol_jet_def
proof (intro ballI allI impI)
  fix x :: "real^'n" and \<phi> :: "real^'n \<Rightarrow> real"
    and g :: "real^'n \<Rightarrow> real^'n" and H :: "real^'n^'n"
  assume x: "x \<in> \<Omega>" and tf: "test_fun_at \<phi> g H x"
    and lm: "\<exists>e>0. \<forall>y \<in> ball x e. w x - \<phi> x \<le> w y - \<phi> y"
  have symH: "transpose H = H" using tf unfolding test_fun_at_def by blast
  obtain e0 where e00: "0 < e0"
    and lme: "\<And>y. y \<in> ball x e0 \<Longrightarrow> w x - \<phi> x \<le> w y - \<phi> y"
    using lm by blast
  have step: "1 \<le> ell_op_usc k L (g x) (H - \<delta> *\<^sub>R mat 1)"
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
    have "1 \<le> ell_op_usc k L (gg x) (H - \<delta> *\<^sub>R mat 1)"
      by (rule visc_supersol_env2_local[OF sup x tfp wlo Bp r0' lm'])
    then show ?thesis unfolding ggx .
  qed
  define es where "es = (\<lambda>j :: nat. 1 / real (Suc j))"
  have es0: "0 < es j" for j unfolding es_def by simp
  have ge: "1 \<le> ell_op_usc k L (g x) (H - es j *\<^sub>R mat 1)" for j
    by (rule step[OF es0])
  have lim: "(\<lambda>j. (g x, H - es j *\<^sub>R mat 1)) \<longlonglongrightarrow> (g x, H)"
  proof -
    have "es \<longlonglongrightarrow> 0" unfolding es_def
      using LIMSEQ_inverse_real_of_nat by (simp add: divide_inverse)
    then have "(\<lambda>j. es j *\<^sub>R (mat 1 :: real^'n^'n)) \<longlonglongrightarrow> 0 *\<^sub>R mat 1"
      by (rule tendsto_scaleR[OF _ tendsto_const])
    then have z: "(\<lambda>j. es j *\<^sub>R (mat 1 :: real^'n^'n)) \<longlonglongrightarrow> 0" by simp
    have "(\<lambda>j. H - es j *\<^sub>R (mat 1 :: real^'n^'n)) \<longlonglongrightarrow> H - 0"
      by (rule tendsto_diff[OF tendsto_const z])
    then have m: "(\<lambda>j. H - es j *\<^sub>R (mat 1 :: real^'n^'n)) \<longlonglongrightarrow> H" by simp
    show ?thesis by (rule tendsto_Pair[OF tendsto_const m])
  qed
  show "1 \<le> ell_op_usc k L (g x) H"
    by (rule ell_op_usc_ge_one_limit[OF ge lim])
qed

text \<open>\<open>quad_bdd_below_on_bounded\<close> lives in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

text \<open>The subsolution counterpart of \<open>visc_supersol_env_imp_jet\<close> lands on the
  envelope-free notion, since \<open>F\<^sub>* = F\<close> everywhere (@{thm [source]
  ell_op_lsc_at_zero} at \<open>p = 0\<close>, @{thm [source] ell_op_lsc_off_zero}
  elsewhere); only the touching needs upgrading from global on \<open>K\<close> to local,
  via @{thm [source] visc_subsol_env_local}.\<close>

theorem visc_subsol_env_imp_visc_subsol:
  fixes K :: "(real^'n::finite) set" and u :: "real^'n \<Rightarrow> real"
  assumes sub: "visc_subsol_env2 k L K \<Omega> u"
    and Kb: "bounded K"
    and uhi: "\<And>y. y \<in> K \<Longrightarrow> u y \<le> Bu"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
  shows "visc_subsol k L \<Omega> u"
  unfolding visc_subsol_def
proof (intro ballI allI impI)
  fix x :: "real^'n" and \<phi> :: "real^'n \<Rightarrow> real"
    and g :: "real^'n \<Rightarrow> real^'n" and H :: "real^'n^'n"
  assume x: "x \<in> \<Omega>" and tf: "test_fun_at \<phi> g H x"
    and lm: "\<exists>e>0. \<forall>y \<in> ball x e. u y - \<phi> y \<le> u x - \<phi> x"
  have symH: "transpose H = H" using tf unfolding test_fun_at_def by blast
  obtain e0 where e00: "0 < e0"
    and lme: "\<And>y. y \<in> ball x e0 \<Longrightarrow> u y - \<phi> y \<le> u x - \<phi> x"
    using lm by blast
  have step: "ell_op k L (g x) (H + \<delta> *\<^sub>R mat 1) \<le> 1" if d: "0 < \<delta>" for \<delta>
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
    have lsc: "ell_op_lsc k L (gg x) (H + \<delta> *\<^sub>R mat 1) \<le> 1"
      by (rule visc_subsol_env2_local[OF sub x tfp uhi Bp r0' lm'])
    show ?thesis
    proof (cases "g x = 0")
      case True
      have "ell_op_lsc k L (0 :: real^'n) (H + \<delta> *\<^sub>R mat 1)
          = ereal (ell_op k L (0 :: real^'n) (H + \<delta> *\<^sub>R mat 1))"
        by (rule ell_op_lsc_at_zero[OF kk(1) kk(2) LL])
      then show ?thesis using lsc unfolding ggx True by simp
    next
      case False
      have "ell_op_lsc k L (g x) (H + \<delta> *\<^sub>R mat 1)
          = ereal (ell_op k L (g x) (H + \<delta> *\<^sub>R mat 1))"
        by (rule ell_op_lsc_off_zero[OF symM False LL kk(1) kk(2)])
      then show ?thesis using lsc unfolding ggx by simp
    qed
  qed
  show "ell_op k L (g x) H \<le> 1"
  proof (rule field_le_epsilon)
    fix e :: real assume e0: "0 < e"
    have A0: "0 < real CARD('n) * L / 2" using LL by simp
    define \<delta> where "\<delta> = e / (real CARD('n) * L / 2)"
    have d0: "0 < \<delta>" unfolding \<delta>_def using e0 A0 by simp
    have ne: "feasible k L (g x) \<noteq> ({} :: (real^'n^'n) set)"
      by (rule feasible_nonempty[OF kk(1) kk(2) LL])
    have gap: "ell_op k L (g x) H
        \<le> ell_op k L (g x) (H + \<delta> *\<^sub>R mat 1) + mgap L H (H + \<delta> *\<^sub>R mat 1)"
      by (rule ell_op_M_gap[OF ne])
    have mg: "mgap L H (H + \<delta> *\<^sub>R mat 1) = \<delta> * real CARD('n) * L / 2"
      by (rule mgap_shift_id(1)[OF less_imp_le[OF d0]])
    have L0: "L \<noteq> 0" using LL by linarith
    have eq: "\<delta> * real CARD('n) * L / 2 = e"
      unfolding \<delta>_def using A0 L0 by (simp add: field_simps)
    have mg': "mgap L H (H + \<delta> *\<^sub>R mat 1) = e" using mg eq by simp
    show "ell_op k L (g x) H \<le> 1 + e"
      using gap step[OF d0] mg' by linarith
  qed
qed


lemma ell_op_strict_contradiction:
  fixes X Y :: "real^'n::finite^'n"
  assumes psd: "psd (Y - X)"
    and ne: "feasible k L p \<noteq> ({} :: (real^'n^'n) set)"
    and sub: "ell_op k L p X < 1" and sup: "1 \<le> ell_op k L p Y"
  shows False
proof -
  have "ell_op k L p Y \<le> ell_op k L p X"
    by (rule ell_op_elliptic_le[OF psd ne])
  thus False using sub sup by linarith
qed

subsection \<open>Where the strictness comes from\<close>

text \<open>\<open>F(p, M) = Inf {- tr(M a)/2 | a feasible}\<close> has no zeroth-order term, so
  a subsolution cannot be made strict by subtracting a constant. But \<open>F\<close> is
  positively homogeneous in \<open>M\<close>, and the feasible set depends on \<open>p\<close> only
  through \<open>a *v p = 0\<close>: scaling a subsolution by \<open>\<theta> \<in> (0,1)\<close> sends
  \<open>(p, X)\<close> to \<open>(\<theta> p, \<theta> X)\<close> and \<open>F(p,X) \<le> 1\<close> to the strict
  \<open>F(\<theta> p, \<theta> X) \<le> \<theta> < 1\<close>.\<close>

lemma feasible_scaleR_p:
  fixes p :: "real^'n::finite"
  assumes t: "\<theta> \<noteq> 0"
  shows "feasible k L (\<theta> *\<^sub>R p) = feasible k L p"
proof -
  have iff: "(a *v (\<theta> *\<^sub>R p) = 0) = (a *v p = 0)" for a :: "real^'n^'n"
  proof -
    have "a *v (\<theta> *\<^sub>R p) = \<theta> *\<^sub>R (a *v p)"
      by (simp add: scaleR_matrix_vector_assoc[symmetric]
          matrix_scaleR_vector_ac)
    thus ?thesis using t by simp
  qed
  show ?thesis unfolding feasible_def using iff by auto
qed

text \<open>Scaling a conditionally-complete infimum by a positive constant:
  \<open>cInf_mult_pos\<close> lives in @{theory Relative_Arbitrage.Operator_Envelopes}.\<close>

text \<open>Positive homogeneity of \<open>F\<close> in the matrix argument: with
  \<open>feasible_scaleR_p\<close>, this is the strict-perturbation mechanism, scaling
  a subsolution's jet to \<open>(\<theta> p, \<theta> X)\<close> and its value to
  \<open>\<theta> F(p,X) \<le> \<theta> < 1\<close>.\<close>

lemma ell_op_scaleR_matrix:
  fixes M :: "real^'n::finite^'n"
  assumes t: "0 < \<theta>" and ne: "feasible k L p \<noteq> ({} :: (real^'n^'n) set)"
  shows "ell_op k L p (\<theta> *\<^sub>R M) = \<theta> * ell_op k L p M"
proof -
  have pt: "- trace ((\<theta> *\<^sub>R M) ** a) / 2 = \<theta> * (- trace (M ** a) / 2)"
    for a :: "real^'n^'n"
  proof -
    have "(\<theta> *\<^sub>R M) ** a = \<theta> *\<^sub>R (M ** a)"
      by (rule scaleR_matrix_mult)
    thus ?thesis by (simp add: trace_scaleR)
  qed
  have img: "(\<lambda>a. - trace ((\<theta> *\<^sub>R M) ** a) / 2) ` feasible k L p
      = (\<lambda>x. \<theta> * x) ` ((\<lambda>a. - trace (M ** a) / 2) ` feasible k L p)"
    unfolding image_image using pt by simp
  show ?thesis
    unfolding ell_op_def img
    by (rule cInf_mult_pos[OF t _ ell_op_bdd_below]) (use ne in simp)
qed

lemma ell_op_scaleR_p:
  fixes M :: "real^'n::finite^'n" and p :: "real^'n"
  assumes t: "\<theta> \<noteq> 0"
  shows "ell_op k L (\<theta> *\<^sub>R p) M = ell_op k L p M"
  unfolding ell_op_def feasible_scaleR_p[OF t] ..

text \<open>Scaling a subsolution by \<open>\<theta> \<in> (0,1)\<close> makes its operator inequality
  strict, since \<open>F\<close> has no zeroth-order term. With
  \<open>ell_op_strict_contradiction\<close>, a scaled subsolution and an unscaled
  supersolution sharing a jet pair \<open>X \<preceq> Y\<close> are inconsistent -- the
  contradiction underlying Theorem 4.2(a).\<close>

subsection \<open>Scaling a subsolution\<close>

text \<open>A test function scales, so a subsolution scaled by \<open>\<theta> \<in> (0,1)\<close>
  satisfies the strict operator inequality at each of its test points.\<close>


theorem visc_subsol_scaled_strict:
  fixes u :: "real^'n::finite \<Rightarrow> real" and H :: "real^'n^'n"
  assumes sub: "visc_subsol k L \<Omega> u"
    and t: "0 < \<theta>" "\<theta> < 1"
    and x: "x \<in> \<Omega>"
    and tf: "test_fun_at \<phi> g H x"
    and ne: "feasible k L (g x) \<noteq> ({} :: (real^'n^'n) set)"
    and maxloc: "\<exists>e>0. \<forall>y \<in> ball x e. \<theta> * u y - \<phi> y \<le> \<theta> * u x - \<phi> x"
  shows "ell_op k L (g x) H < 1"
proof -
  define c where "c = 1/\<theta>"
  have c0: "0 < c" unfolding c_def using t(1) by simp
  have cn: "c \<noteq> 0" using c0 by simp
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
      unfolding c_def using t(1) by (simp add: field_simps)
  qed
  have "ell_op k L ((\<lambda>z. c *\<^sub>R g z) x) (c *\<^sub>R H) \<le> 1"
    using sub x tfc mc unfolding visc_subsol_def by blast
  hence step: "ell_op k L (c *\<^sub>R g x) (c *\<^sub>R H) \<le> 1" by simp
  have "ell_op k L (c *\<^sub>R g x) (c *\<^sub>R H) = ell_op k L (g x) (c *\<^sub>R H)"
    by (rule ell_op_scaleR_p[OF cn])
  also have "\<dots> = c * ell_op k L (g x) H"
    by (rule ell_op_scaleR_matrix[OF c0 ne])
  finally have "c * ell_op k L (g x) H \<le> 1" using step by simp
  hence "ell_op k L (g x) H \<le> \<theta>"
    unfolding c_def using t(1) by (simp add: field_simps)
  thus ?thesis using t(2) by linarith
qed

subsection \<open>Freezing one variable in the doubled maximum\<close>

text \<open>\<open>doubling_partial_max_fst\<close>, \<open>doubling_partial_min_snd\<close> live in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

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

text \<open>Packaging both frozen penalties as test functions supplies, with
  \<open>doubling_partial_max_fst\<close> and \<open>doubling_partial_min_snd\<close>, exactly the
  hypotheses \<open>visc_subsol\<close> and \<open>supersol_jet\<close> require, so the doubled
  maximum feeds into the two viscosity inequalities.\<close>

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



theorem comparison_contradiction:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
    and X Y :: "(real^'n) \<Rightarrow> (real^'n)"
  assumes sub: "visc_subsol k L \<Omega> u" and sup: "supersol_jet k L \<Omega> w"
    and t: "0 < \<theta>" "\<theta> < 1"
    and xh: "xh \<in> \<Omega>" and yh: "yh \<in> \<Omega>"
    and lX: "linear X" and lY: "linear Y"
    and symX: "\<And>v z. v \<bullet> X z = z \<bullet> X v"
    and symY: "\<And>v z. v \<bullet> Y z = z \<bullet> Y v"
    and ord: "\<And>v. v \<bullet> X v \<le> v \<bullet> Y v"
    and ne: "feasible k L p \<noteq> ({} :: (real^'n^'n) set)"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L" and pnz: "p \<noteq> 0"
    and subtest: "\<exists>e>0. \<forall>z \<in> ball xh e.
        \<theta> * u z - (p \<bullet> (z - xh) + ((z - xh) \<bullet> (matrix X *v (z - xh)))/2)
        \<le> \<theta> * u xh
        - (p \<bullet> (xh - xh) + ((xh - xh) \<bullet> (matrix X *v (xh - xh)))/2)"
    and suptest: "\<exists>e>0. \<forall>z \<in> ball yh e.
        w yh - (p \<bullet> (yh - yh) + ((yh - yh) \<bullet> (matrix Y *v (yh - yh)))/2)
        \<le> w z - (p \<bullet> (z - yh) + ((z - yh) \<bullet> (matrix Y *v (z - yh)))/2)"
  shows False
proof -
  have tfX: "test_fun_at
      (\<lambda>z. p \<bullet> (z - xh) + ((z - xh) \<bullet> (matrix X *v (z - xh)))/2)
      (\<lambda>z. p + matrix X *v (z - xh)) (matrix X) xh"
    by (rule jet_test_fun_at_abstract[OF lX symX])
  have gX: "(\<lambda>z. p + matrix X *v (z - xh)) xh = p" by simp
  have neX: "feasible k L ((\<lambda>z. p + matrix X *v (z - xh)) xh)
      \<noteq> ({} :: (real^'n^'n) set)"
    unfolding gX by (rule ne)
  have strict: "ell_op k L ((\<lambda>z. p + matrix X *v (z - xh)) xh) (matrix X) < 1"
    by (rule visc_subsol_scaled_strict[OF sub t(1) t(2) xh tfX neX subtest])
  hence strictp: "ell_op k L p (matrix X) < 1" unfolding gX .
  have tfY: "test_fun_at
      (\<lambda>z. p \<bullet> (z - yh) + ((z - yh) \<bullet> (matrix Y *v (z - yh)))/2)
      (\<lambda>z. p + matrix Y *v (z - yh)) (matrix Y) yh"
    by (rule jet_test_fun_at_abstract[OF lY symY])
  have gY: "(\<lambda>z. p + matrix Y *v (z - yh)) yh = p" by simp
  have "1 \<le> ell_op_usc k L ((\<lambda>z. p + matrix Y *v (z - yh)) yh) (matrix Y)"
    using sup yh tfY suptest unfolding supersol_jet_def by blast
  hence "1 \<le> ell_op_usc k L p (matrix Y)" unfolding gY .
  hence supp: "1 \<le> ell_op k L p (matrix Y)"
    unfolding ell_op_usc_eq_at_nonzero[OF kk(1) kk(2) LL pnz] by simp
  have psdXY: "psd (matrix Y - matrix X)"
    by (rule psd_of_abstract_le[OF lX lY symX symY ord])
  show False
    by (rule ell_op_strict_contradiction[OF psdXY ne strictp supp])
qed

subsection \<open>The envelope route for removing the jet correction\<close>

text \<open>\<open>superjet_local_max\<close> introduces a strictly convex correction
  \<open>(\<delta>/2) * norm k\<^sup>2\<close>, so the matrix reaching the operator is \<open>X + \<delta> I\<close>
  rather than \<open>X\<close>. Removing \<open>\<delta>\<close> passes to closed second-order jets via the
  envelopes: the two envelope inequalities sandwich the sharp one, and
  \<open>visc_subsol_imp_env\<close> / \<open>visc_supersol_imp_env\<close> (@{theory Relative_Arbitrage.Operator_Envelopes}) show the
  envelope-free notions already imply the envelope ones on an open
  \<open>\<Omega> \<subseteq> K\<close>.\<close>

text \<open>\<open>ball_prod_shift_snd\<close> lives in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


lemma ell_op_pair_shift_snd_le:
  fixes M N :: "real^'n::finite^'n"
  assumes psd: "psd (N - M)" and k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L"
  shows "ell_op_pair k L (w + (0, N - M)) \<le> ell_op_pair k L w"
proof -
  have ne: "feasible k L (fst w) \<noteq> ({} :: (real^'n^'n) set)"
    by (rule feasible_nonempty[OF k(1) k(2) L])
  have psd': "psd ((snd w + (N - M)) - snd w)"
    using psd by simp
  have "ell_op k L (fst w) (snd w + (N - M)) \<le> ell_op k L (fst w) (snd w)"
    by (rule ell_op_elliptic_le[OF psd' ne])
  then show ?thesis
    by (simp add: ell_op_pair_def)
qed

theorem ell_op_lsc_elliptic_le:
  fixes M N :: "real^'n::finite^'n"
  assumes psd: "psd (N - M)" and k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L"
  shows "ell_op_lsc k L p N \<le> ell_op_lsc k L p M"
  unfolding ell_op_lsc_def
proof (rule SUP_mono)
  fix e :: real
  assume e: "e \<in> {0<..}"
  have "(INF w \<in> ball ((p :: real^'n), N) e. ell_op_pair k L w)
      \<le> (INF w \<in> ball ((p :: real^'n), M) e. ell_op_pair k L w)"
  proof (rule INF_mono)
    fix w :: "(real^'n) \<times> (real^'n^'n)"
    assume w: "w \<in> ball ((p :: real^'n), M) e"
    have "w + (0, N - M) \<in> ball ((p :: real^'n), N) e"
      by (rule ball_prod_shift_snd[OF w])
    moreover have "ell_op_pair k L (w + (0, N - M)) \<le> ell_op_pair k L w"
      by (rule ell_op_pair_shift_snd_le[OF psd k(1) k(2) L])
    ultimately show "\<exists>v \<in> ball ((p :: real^'n), N) e.
        ell_op_pair k L v \<le> ell_op_pair k L w"
      by blast
  qed
  with e show "\<exists>e' \<in> {0<..}. (INF w \<in> ball ((p :: real^'n), N) e. ell_op_pair k L w)
      \<le> (INF w \<in> ball ((p :: real^'n), M) e'. ell_op_pair k L w)"
    by blast
qed

text \<open>And the same for the upper envelope, by the dual argument: the same
  translation carries \<open>ball (p, M) e\<close> onto \<open>ball (p, N) e\<close>, and the
  integrand decreases along it, so the suprema compare and then the infima
  over the radius do.\<close>

theorem ell_op_usc_envelope_elliptic_le:
  fixes M N :: "real^'n::finite^'n"
  assumes psd: "psd (N - M)" and k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L"
  shows "ell_op_usc k L p N \<le> ell_op_usc k L p M"
  unfolding ell_op_usc_def
proof (rule INF_mono)
  fix e :: real
  assume e: "e \<in> {0<..}"
  have "(SUP w \<in> ball ((p :: real^'n), N) e. ell_op_pair k L w)
      \<le> (SUP w \<in> ball ((p :: real^'n), M) e. ell_op_pair k L w)"
  proof (rule SUP_mono)
    fix v :: "(real^'n) \<times> (real^'n^'n)"
    assume v: "v \<in> ball ((p :: real^'n), N) e"
    have vm: "v - (0, N - M) \<in> ball ((p :: real^'n), M) e"
    proof -
      have eq: "(v - (0, N - M)) - (p, M) = v - (p, N)"
        by (simp add: prod_eq_iff)
      have "dist (v - (0, N - M)) (p, M) = dist v (p, N)"
        unfolding dist_norm eq ..
      moreover have "dist v (p, N) < e"
        using v by (simp add: dist_commute)
      ultimately show ?thesis
        by (simp add: dist_commute)
    qed
    have "ell_op_pair k L v \<le> ell_op_pair k L (v - (0, N - M))"
    proof -
      have "ell_op_pair k L ((v - (0, N - M)) + (0, N - M))
          \<le> ell_op_pair k L (v - (0, N - M))"
        by (rule ell_op_pair_shift_snd_le[OF psd k(1) k(2) L])
      then show ?thesis by simp
    qed
    with vm show "\<exists>u \<in> ball ((p :: real^'n), M) e.
        ell_op_pair k L v \<le> ell_op_pair k L u"
      by blast
  qed
  with e show "\<exists>e' \<in> {0<..}. (SUP w \<in> ball ((p :: real^'n), N) e'. ell_op_pair k L w)
      \<le> (SUP w \<in> ball ((p :: real^'n), M) e. ell_op_pair k L w)"
    by blast
qed

subsection \<open>The envelope-form contradiction\<close>

text \<open>Ellipticity of the envelopes alone gives \<open>F\<^sup>*(p, Y) \<le> F\<^sup>*(p, X)\<close>, but
  combined with \<open>F\<^sub>*(p, X) < 1\<close> this is consistent wherever the two
  envelopes separate at \<open>(p, X)\<close>, i.e. wherever \<open>F\<close> is discontinuous. The
  mixed-envelope inequalities close only where the envelopes coincide with
  \<open>F\<close>, which by Lemma 3.1's last clause is everywhere off the origin
  (\<open>ell_op_lsc_off_zero\<close>, \<open>ell_op_usc_off_zero\<close>), reducing the envelope
  contradiction to the envelope-free one.\<close>

theorem ell_op_env_strict_contradiction:
  fixes X Y :: "real^'n::finite^'n"
  assumes psd: "psd (Y - X)"
    and symX: "transpose X = X" and symY: "transpose Y = Y"
    and p: "p \<noteq> 0" and k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L"
    and sub: "ell_op_lsc k L p X < 1" and sup: "1 \<le> ell_op_usc k L p Y"
  shows False
proof -
  have ne: "feasible k L p \<noteq> ({} :: (real^'n^'n) set)"
    by (rule feasible_nonempty[OF k(1) k(2) L])
  have eX: "ell_op_lsc k L p X = ereal (ell_op k L p X)"
    by (rule ell_op_lsc_off_zero[OF symX p L k(1) k(2)])
  have eY: "ell_op_usc k L p Y = ereal (ell_op k L p Y)"
    by (rule ell_op_usc_off_zero[OF symY p L k(1) k(2)])
  have subr: "ell_op k L p X < 1"
    using sub unfolding eX by (simp add: one_ereal_def)
  have supr: "1 \<le> ell_op k L p Y"
    using sup unfolding eY by (simp add: one_ereal_def)
  show False
    by (rule ell_op_strict_contradiction[OF psd ne subr supr])
qed

text \<open>The same for the non-strict sandwich, the form in which the envelope
  inequalities first arrive from the doubling.\<close>

text \<open>At \<open>p = 0\<close> the two envelopes disagree: \<open>ell_op_lsc_at_zero\<close> gives
  \<open>F\<^sub>*(0, M) = F(0, M)\<close>, while \<open>eq36\<close> gives \<open>F\<^sup>*(0, M) = eq36_rhs k L M\<close>,
  whose index range omits the eigenvalue \<open>\<lambda>\<^sub>(\<^sub>1\<^sub>)(M)\<close> of Eq. (3.5). So
  \<open>1 \<le> F\<^sup>*(0, Y)\<close> is strictly weaker than \<open>1 \<le> F(0, Y)\<close>, and envelope
  ellipticity cannot close the gap -- the degeneracy Lemma 3.1 isolates, and
  why the doubling needs the shared gradient to be nonzero.\<close>

subsection \<open>The dichotomy the side condition forces on the doubling\<close>

text \<open>In the doubling, the shared gradient at the maximising pair
  \<open>(x', y')\<close> of \<open>\<Phi>(x,y) = u x - w y - (\<alpha>/2) \<bar>x - y\<bar>\<^sup>2\<close> is
  \<open>p = \<alpha> (x' - y')\<close>, so \<open>p \<noteq> 0\<close> means the maximising pair is off the
  diagonal. For \<open>\<alpha> \<noteq> 0\<close> the gradient vanishes precisely on the diagonal.\<close>

text \<open>\<open>doubling_diagonal_max\<close>, \<open>doubling_off_diagonal\<close>, \<open>doubling_grad_nonzero\<close> live in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

subsection \<open>The penalty estimate\<close>

text \<open>\<open>doubling_penalty_bound\<close> and \<open>doubling_dist_bound\<close> live in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}; \<open>doubling_ge_diagonal\<close> in @{theory Second_Order_Viscosity_Analysis.Theorem_On_Sums}.\<close>

subsection \<open>The dichotomy for a general penalty\<close>

text \<open>\<open>doubling_diagonal_max_gen\<close>, \<open>doubling_off_diagonal_gen\<close>, \<open>doubling_penalty_bound_gen\<close> live in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

subsection \<open>Monotonicity of the doubled maximum in the penalty parameter\<close>

text \<open>The other ingredient of the \<open>\<alpha> \<rightarrow> \<infinity>\<close> passage: the doubled maximum is
  antimonotone in \<open>\<alpha>\<close>, since a larger penalty can only decrease the
  supremum, the maximiser for larger \<open>\<alpha>\<close> being an admissible competitor for
  smaller \<open>\<alpha>\<close>. With \<open>doubling_ge_diagonal\<close>, this pins the family between
  two \<open>\<alpha>\<close>-independent bounds, so the limit exists without a compactness
  argument.\<close>

subsection \<open>The components of the maximiser merge, with no subsequences\<close>

text \<open>Because \<open>doubling_dist_bound\<close> comes with an explicit constant,
  \<open>x'\<^sub>\<alpha> - y'\<^sub>\<alpha> \<rightarrow> 0\<close> is a sandwich between \<open>0\<close> and \<open>2D/\<alpha>\<close>, needing
  neither compactness of \<open>K\<close> nor a subsequence.\<close>

subsection \<open>The diagonal branch \<open>p = 0\<close>\<close>

text \<open>The dichotomy leaves the diagonal branch \<open>p = 0\<close>. Since \<open>eq36\<close>
  identifies \<open>F\<^sup>*(0, M)\<close> with \<open>eq36_rhs k L M\<close>, ellipticity of \<open>F\<^sup>*\<close>
  transfers to \<open>eq36_rhs\<close>, a statement about the eigenvalue expression of
  Eq. (3.6).\<close>

theorem eq36_rhs_antitone:
  fixes M N :: "real^'n::finite^'n"
  assumes psd: "psd (N - M)"
    and symM: "transpose M = M" and symN: "transpose N = N"
    and k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L"
  shows "eq36_rhs k L N \<le> eq36_rhs k L M"
proof -
  have "ereal (eq36_rhs k L N) = ell_op_usc k L (0 :: real^'n) N"
    by (rule eq36[OF symN L k(1) k(2), symmetric])
  also have "\<dots> \<le> ell_op_usc k L (0 :: real^'n) M"
    by (rule ell_op_usc_envelope_elliptic_le[OF psd k(1) k(2) L])
  also have "\<dots> = ereal (eq36_rhs k L M)"
    by (rule eq36[OF symM L k(1) k(2)])
  finally show ?thesis by simp
qed

text \<open>The gap between the two envelopes at the origin,
  \<open>eq36_rhs k L M - F(0, M)\<close>, is nonnegative: \<open>ell_op_le_eq36\<close> specialised
  to \<open>p = 0\<close>, combined with \<open>ell_op_lsc_at_zero\<close>.\<close>

text \<open>At \<open>p = 0\<close>, \<open>F\<^sub>*(0,X) = F(0,X)\<close> and \<open>F\<^sup>*(0,Y) = eq36_rhs k L Y\<close>, with
  \<open>eq36_rhs\<close> antitone; the supersolution gives \<open>1 \<le> eq36_rhs k L X\<close> and
  the subsolution \<open>F(0,X) < 1\<close>. These are consistent because
  \<open>F(0,X) \<le> eq36_rhs k L X\<close> with room to spare, so the envelope gap at
  \<open>p = 0\<close> does not vanish in general.\<close>

subsection \<open>The diagonal branch closes without further hypotheses\<close>

text \<open>\<open>small_multiple_exists\<close>, \<open>shift_limit_absurd\<close>, \<open>shift_limit_absurd2\<close> live in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>


theorem strict_contradiction_of_shifts_any_p:
  fixes X Y :: "real^'n::finite^'n" and p :: "real^'n"
  assumes psd: "psd (Y - X)"
    and k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L"
    and t: "\<theta> < 1"
    and subs: "\<And>\<delta>. 0 < \<delta> \<Longrightarrow> \<delta> < 1 \<Longrightarrow> ell_op k L p (X + \<delta> *\<^sub>R mat 1) \<le> \<theta>"
    and sups: "\<And>\<delta>. 0 < \<delta> \<Longrightarrow> \<delta> < 1 \<Longrightarrow> 1 \<le> ell_op k L p (Y - \<delta> *\<^sub>R mat 1)"
  shows False
proof -
  have ne: "feasible k L p \<noteq> ({} :: (real^'n^'n) set)"
    by (rule feasible_nonempty[OF k(1) k(2) L])
  have C0: "0 < real CARD('n) * L / 2" using k L by simp
  have cY: "1 \<le> ell_op k L p Y"
  proof (rule ccontr)
    assume "\<not> 1 \<le> ell_op k L p Y"
    then have g: "0 < 1 - ell_op k L p Y" by linarith
    obtain \<delta> where d0: "0 < \<delta>" and d1: "\<delta> < 1"
      and dlt: "\<delta> * (real CARD('n) * L / 2) < 1 - ell_op k L p Y"
      using small_multiple_exists[OF C0 g] by blast
    have dN: "\<delta> * real CARD('n) * L / 2 < 1 - ell_op k L p Y"
    proof -
      have e1: "\<delta> * real CARD('n) * L / 2 = \<delta> * (real CARD('n) * L / 2)"
        by simp
      show ?thesis unfolding e1 by (rule dlt)
    qed
    show False
      by (rule shift_limit_absurd
          [OF sups[OF d0 d1] ell_op_M_gap[OF ne]
             mgap_shift_id(2)[OF less_imp_le[OF d0]] dN])
  qed
  have cX: "ell_op k L p X \<le> \<theta>"
  proof (rule ccontr)
    assume "\<not> ell_op k L p X \<le> \<theta>"
    then have g: "0 < ell_op k L p X - \<theta>" by linarith
    obtain \<delta> where d0: "0 < \<delta>" and d1: "\<delta> < 1"
      and dlt: "\<delta> * (real CARD('n) * L / 2) < ell_op k L p X - \<theta>"
      using small_multiple_exists[OF C0 g] by blast
    have dN: "\<delta> * real CARD('n) * L / 2 < ell_op k L p X - \<theta>"
    proof -
      have e1: "\<delta> * real CARD('n) * L / 2 = \<delta> * (real CARD('n) * L / 2)"
        by simp
      show ?thesis unfolding e1 by (rule dlt)
    qed
    show False
      by (rule shift_limit_absurd2
          [OF ell_op_M_gap[OF ne] subs[OF d0 d1]
             mgap_shift_id(1)[OF less_imp_le[OF d0]] dN])
  qed
  have ell: "ell_op k L p Y \<le> ell_op k L p X"
    by (rule ell_op_elliptic_le[OF psd ne])
  from cY cX ell t show False by linarith
qed

subsection \<open>Existence of the maximising pair\<close>

text \<open>\<open>doubling_maximiser_exists\<close>, \<open>doubling_maximiser_exists_gen\<close> live in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

text \<open>The packaged form: on a compact \<open>K\<close> the doubling produces a
  maximising pair together with the penalty bound and the diagonal lower
  bound already proved for it.\<close>

subsection \<open>Discharging the remaining bare hypothesis of the penalty estimate\<close>

text \<open>\<open>doubling_upper_bound_exists\<close> lives in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

text \<open>Combining the two attainment results with the penalty estimate: on a
  compact \<open>K\<close> with continuous data the doubling produces a maximising pair
  whose penalty is bounded by an \<open>\<alpha>\<close>-independent constant, and whose two
  components are within \<open>O(1/\<surd>\<alpha>)\<close> of each other.\<close>

subsection \<open>Producing the local-max hypotheses of \<open>comparison_contradiction\<close>\<close>

text \<open>\<open>comparison_contradiction\<close> takes \<open>subtest\<close> and \<open>suptest\<close> -- local
  max/min statements for the jet test function -- as hypotheses; these are
  exactly what \<open>superjet_local_max\<close> yields from an Alexandrov jet once the
  test matrix is corrected by \<open>\<delta> I\<close>, since the \<open>(\<delta>/2)\<bar>k\<bar>\<^sup>2\<close> slack it
  leaves is precisely the extra quadratic form contributed by \<open>\<delta> I\<close>.\<close>

text \<open>\<open>quad_form_shift_identity\<close> lives in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>

text \<open>\<open>jet_imp_local_max_test\<close> lives in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

text \<open>\<open>matrix_vector_neg_left\<close>, \<open>quad_form_shift_identity_neg\<close> live in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>

text \<open>The mirror image for the supersolution side: a subjet of \<open>v\<close> at \<open>yh\<close>
  gives the local-min statement, with correction \<open>- \<delta> I\<close>, following from
  the same theorem applied to \<open>-v\<close>, whose jet data is \<open>(-p, -A)\<close>.\<close>

subsection \<open>The jet hypothesis only ever needs one side\<close>

text \<open>\<open>superjet_local_max_onesided\<close> lives in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

text \<open>\<open>onesided_of_tendsto_gen\<close>, \<open>onesided_of_dominated\<close> live in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>


text \<open>\<open>jet_imp_local_min_test_onesided\<close>, \<open>jet_imp_local_min_test\<close> live in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

subsection \<open>Removing the jet correction\<close>

text \<open>The \<open>\<delta>\<close> from \<open>jet_imp_local_max_test\<close> cannot cancel against
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

theorem ell_op_lsc_le_of_shifts:
  fixes M :: "real^'n::finite^'n" and p :: "real^'n"
  assumes b: "\<And>\<delta>. 0 < \<delta> \<Longrightarrow> \<delta> < D \<Longrightarrow> ell_op k L p (M + \<delta> *\<^sub>R mat 1) \<le> c"
    and D: "0 < D"
  shows "ell_op_lsc k L p M \<le> ereal c"
  unfolding ell_op_lsc_def
proof (rule SUP_least)
  fix e :: real
  assume "e \<in> {0<..}"
  then have e0: "0 < e" by simp
  define N where "N = norm (mat 1 :: real^'n^'n)"
  have N0: "0 \<le> N" unfolding N_def by simp
  define d where "d = min (D/2) (e/(2*(N+1)))"
  have d0: "0 < d" unfolding d_def using D e0 N0 by simp
  have dD: "d < D" unfolding d_def using D by simp
  have small: "d * N < e"
  proof -
    have dle: "d \<le> e/(2*(N+1))"
      unfolding d_def by simp
    have "d * N \<le> (e/(2*(N+1))) * N"
      by (rule mult_right_mono[OF dle N0])
    also have "(e/(2*(N+1))) * N = e * N / (2*(N+1))"
      by simp
    also have "\<dots> < e"
    proof -
      have "e * N < e * (2*(N+1))"
        using e0 N0 by simp
      moreover have "0 < 2*(N+1)"
        using N0 by simp
      ultimately show ?thesis
        by (simp add: divide_less_eq)
    qed
    finally show ?thesis .
  qed
  have dp: "dist ((p, M + d *\<^sub>R mat 1) :: (real^'n) \<times> (real^'n^'n)) (p, M)
      = d * N"
  proof -
    have "dist ((p, M + d *\<^sub>R mat 1) :: (real^'n) \<times> (real^'n^'n)) (p, M)
        = sqrt ((dist p p)\<^sup>2 + (dist (M + d *\<^sub>R mat 1) M)\<^sup>2)"
      by (rule dist_Pair_Pair)
    also have "\<dots> = dist (M + d *\<^sub>R mat 1) M"
      by simp
    also have "\<dots> = norm (d *\<^sub>R (mat 1 :: real^'n^'n))"
      by (simp add: dist_norm)
    also have "\<dots> = d * N"
      unfolding N_def using d0 by simp
    finally show ?thesis .
  qed
  have mem: "((p, M + d *\<^sub>R mat 1) :: (real^'n) \<times> (real^'n^'n))
      \<in> ball (p, M) e"
    using dp small by (simp add: dist_commute)
  have "(INF w \<in> ball ((p :: real^'n), M) e. ell_op_pair k L w)
      \<le> ell_op_pair k L (p, M + d *\<^sub>R mat 1)"
    by (rule INF_lower[OF mem])
  also have "\<dots> \<le> ereal c"
    using b[OF d0 dD] by (simp add: ell_op_pair_def)
  finally show "(INF w \<in> ball ((p :: real^'n), M) e. ell_op_pair k L w)
      \<le> ereal c" .
qed

theorem ell_op_usc_ge_of_shifts:
  fixes M :: "real^'n::finite^'n" and p :: "real^'n"
  assumes b: "\<And>\<delta>. 0 < \<delta> \<Longrightarrow> \<delta> < D \<Longrightarrow> c \<le> ell_op k L p (M - \<delta> *\<^sub>R mat 1)"
    and D: "0 < D"
  shows "ereal c \<le> ell_op_usc k L p M"
  unfolding ell_op_usc_def
proof (rule INF_greatest)
  fix e :: real
  assume "e \<in> {0<..}"
  then have e0: "0 < e" by simp
  define N where "N = norm (mat 1 :: real^'n^'n)"
  have N0: "0 \<le> N" unfolding N_def by simp
  define d where "d = min (D/2) (e/(2*(N+1)))"
  have d0: "0 < d" unfolding d_def using D e0 N0 by simp
  have dD: "d < D" unfolding d_def using D by simp
  have small: "d * N < e"
  proof -
    have dle: "d \<le> e/(2*(N+1))"
      unfolding d_def by simp
    have "d * N \<le> (e/(2*(N+1))) * N"
      by (rule mult_right_mono[OF dle N0])
    also have "(e/(2*(N+1))) * N = e * N / (2*(N+1))"
      by simp
    also have "\<dots> < e"
    proof -
      have "e * N < e * (2*(N+1))"
        using e0 N0 by simp
      moreover have "0 < 2*(N+1)"
        using N0 by simp
      ultimately show ?thesis
        by (simp add: divide_less_eq)
    qed
    finally show ?thesis .
  qed
  have dp: "dist ((p, M - d *\<^sub>R mat 1) :: (real^'n) \<times> (real^'n^'n)) (p, M)
      = d * N"
  proof -
    have "dist ((p, M - d *\<^sub>R mat 1) :: (real^'n) \<times> (real^'n^'n)) (p, M)
        = sqrt ((dist p p)\<^sup>2 + (dist (M - d *\<^sub>R mat 1) M)\<^sup>2)"
      by (rule dist_Pair_Pair)
    also have "\<dots> = dist (M - d *\<^sub>R mat 1) M"
      by simp
    also have "\<dots> = norm (d *\<^sub>R (mat 1 :: real^'n^'n))"
      by (simp add: dist_norm)
    also have "\<dots> = d * N"
      unfolding N_def using d0 by simp
    finally show ?thesis .
  qed
  have mem: "((p, M - d *\<^sub>R mat 1) :: (real^'n) \<times> (real^'n^'n))
      \<in> ball (p, M) e"
    using dp small by (simp add: dist_commute)
  have "ereal c \<le> ell_op_pair k L (p, M - d *\<^sub>R mat 1)"
    using b[OF d0 dD] by (simp add: ell_op_pair_def)
  also have "\<dots> \<le> (SUP w \<in> ball ((p :: real^'n), M) e. ell_op_pair k L w)"
    by (rule SUP_upper[OF mem])
  finally show "ereal c
      \<le> (SUP w \<in> ball ((p :: real^'n), M) e. ell_op_pair k L w)" .
qed

text \<open>The closing chain of Theorem 4.2(a) in \<open>\<delta>\<close>-corrected form: a uniform
  strict bound \<open>c < 1\<close> on the subsolution side at every \<open>X + \<delta> I\<close>, the
  supersolution bound at every \<open>Y - \<delta> I\<close>, the ordering \<open>X \<preceq> Y\<close> from the
  theorem on sums, and \<open>p \<noteq> 0\<close> from \<open>doubling_grad_nonzero\<close>. No \<open>\<delta>\<close>
  survives in the conclusion.\<close>

theorem env_strict_contradiction_of_shifts:
  fixes X Y :: "real^'n::finite^'n" and p :: "real^'n"
  assumes psd: "psd (Y - X)"
    and symX: "transpose X = X" and symY: "transpose Y = Y"
    and p: "p \<noteq> 0" and k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L"
    and D: "0 < D" and c1: "c < 1"
    and subs: "\<And>\<delta>. 0 < \<delta> \<Longrightarrow> \<delta> < D
        \<Longrightarrow> ell_op k L p (X + \<delta> *\<^sub>R mat 1) \<le> c"
    and sups: "\<And>\<delta>. 0 < \<delta> \<Longrightarrow> \<delta> < D
        \<Longrightarrow> 1 \<le> ell_op k L p (Y - \<delta> *\<^sub>R mat 1)"
  shows False
proof -
  have lsc: "ell_op_lsc k L p X \<le> ereal c"
    by (rule ell_op_lsc_le_of_shifts[OF subs D])
  have c1e: "ereal c < 1"
    using c1 by (simp add: one_ereal_def)
  have sub: "ell_op_lsc k L p X < 1"
    using lsc c1e by (rule le_less_trans)
  have sup: "1 \<le> ell_op_usc k L p Y"
    using ell_op_usc_ge_of_shifts[OF sups D] by (simp add: one_ereal_def)
  show False
    by (rule ell_op_env_strict_contradiction[OF psd symX symY p k(1) k(2) L
          sub sup])
qed

subsection \<open>The uniform strict bound, and the shifted families\<close>

text \<open>\<open>visc_subsol_scaled_strict\<close> concludes \<open>F < 1\<close>, but its proof actually
  gives the stronger \<open>F \<le> \<theta>\<close>; this is the same argument stopped one step
  earlier, giving the bound that survives the \<open>\<delta> \<rightarrow> 0\<close> limit.\<close>

theorem visc_subsol_scaled_uniform:
  fixes u :: "real^'n::finite \<Rightarrow> real" and H :: "real^'n^'n"
  assumes sub: "visc_subsol k L \<Omega> u"
    and t: "0 < \<theta>"
    and x: "x \<in> \<Omega>"
    and tf: "test_fun_at \<phi> g H x"
    and ne: "feasible k L (g x) \<noteq> ({} :: (real^'n^'n) set)"
    and maxloc: "\<exists>e>0. \<forall>y \<in> ball x e. \<theta> * u y - \<phi> y \<le> \<theta> * u x - \<phi> x"
  shows "ell_op k L (g x) H \<le> \<theta>"
proof -
  define c where "c = 1/\<theta>"
  have c0: "0 < c" unfolding c_def using t by simp
  have cn: "c \<noteq> 0" using c0 by simp
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
  have "ell_op k L ((\<lambda>z. c *\<^sub>R g z) x) (c *\<^sub>R H) \<le> 1"
    using sub x tfc mc unfolding visc_subsol_def by blast
  hence step: "ell_op k L (c *\<^sub>R g x) (c *\<^sub>R H) \<le> 1" by simp
  have "ell_op k L (c *\<^sub>R g x) (c *\<^sub>R H) = ell_op k L (g x) (c *\<^sub>R H)"
    by (rule ell_op_scaleR_p[OF cn])
  also have "\<dots> = c * ell_op k L (g x) H"
    by (rule ell_op_scaleR_matrix[OF c0 ne])
  finally have "c * ell_op k L (g x) H \<le> 1" using step by simp
  thus ?thesis
    unfolding c_def using t by (simp add: field_simps)
qed

text \<open>Symmetry of the corrected matrices, needed by the jet test function:
  transposition is additive entrywise, so both directions of the correction
  preserve symmetry.\<close>

text \<open>The two producers: an Alexandrov jet of \<open>\<theta> u\<close> at \<open>x'\<close> with data
  \<open>(p, X)\<close> gives, for every \<open>\<delta> > 0\<close>, the uniform bound
  \<open>F(p, X + \<delta> I) \<le> \<theta>\<close>; dually on the supersolution side. These are the
  two families \<open>env_strict_contradiction_of_shifts\<close> consumes.\<close>

theorem subsol_shifted_bound:
  fixes u :: "real^'n::finite \<Rightarrow> real" and Xm :: "real^'n^'n"
  assumes sub: "visc_subsol k L \<Omega> u"
    and t: "0 < \<theta>"
    and xh: "xh \<in> \<Omega>"
    and Xs: "transpose Xm = Xm"
    and k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L"
    and jet: "((\<lambda>h. (\<theta> * u (xh + h) - \<theta> * u xh - p \<bullet> h
        - (h \<bullet> (Xm *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and d: "0 < \<delta>"
  shows "ell_op k L p (Xm + \<delta> *\<^sub>R mat 1) \<le> \<theta>"
proof -
  have sym: "transpose (Xm + \<delta> *\<^sub>R mat 1) = Xm + \<delta> *\<^sub>R mat 1"
    by (rule transpose_shift_add[OF Xs])
  have tf: "test_fun_at
      (\<lambda>z. p \<bullet> (z - xh)
        + ((z - xh) \<bullet> ((Xm + \<delta> *\<^sub>R mat 1) *v (z - xh)))/2)
      (\<lambda>z. p + (Xm + \<delta> *\<^sub>R mat 1) *v (z - xh)) (Xm + \<delta> *\<^sub>R mat 1) xh"
    by (rule jet_test_fun_at[OF sym])
  have g: "(\<lambda>z. p + (Xm + \<delta> *\<^sub>R mat 1) *v (z - xh)) xh = p"
    by simp
  have ne: "feasible k L ((\<lambda>z. p + (Xm + \<delta> *\<^sub>R mat 1) *v (z - xh)) xh)
      \<noteq> ({} :: (real^'n^'n) set)"
    unfolding g by (rule feasible_nonempty[OF k(1) k(2) L])
  have maxloc: "\<exists>e>0. \<forall>z \<in> ball xh e.
      \<theta> * u z - (p \<bullet> (z - xh)
          + ((z - xh) \<bullet> ((Xm + \<delta> *\<^sub>R mat 1) *v (z - xh)))/2)
      \<le> \<theta> * u xh - (p \<bullet> (xh - xh)
          + ((xh - xh) \<bullet> ((Xm + \<delta> *\<^sub>R mat 1) *v (xh - xh)))/2)"
    by (rule jet_imp_local_max_test[OF jet d])
  have "ell_op k L ((\<lambda>z. p + (Xm + \<delta> *\<^sub>R mat 1) *v (z - xh)) xh)
      (Xm + \<delta> *\<^sub>R mat 1) \<le> \<theta>"
    by (rule visc_subsol_scaled_uniform[OF sub t xh tf ne maxloc])
  thus ?thesis unfolding g .
qed

theorem supersol_shifted_bound_onesided:
  fixes w :: "real^'n::finite \<Rightarrow> real" and Ym :: "real^'n^'n"
  assumes sup: "supersol_jet k L \<Omega> w"
    and yh: "yh \<in> \<Omega>"
    and Ys: "transpose Ym = Ym"
    and ub: "\<And>c. 0 < c \<Longrightarrow> \<forall>\<^sub>F hh in at 0.
        ((- w) (yh + hh) - (- w) yh - (- p) \<bullet> hh
          - (hh \<bullet> ((- Ym) *v hh))/2) / (norm hh)\<^sup>2 < c"
    and d: "0 < \<delta>"
  shows "1 \<le> ell_op_usc k L p (Ym - \<delta> *\<^sub>R mat 1)"
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
  have "1 \<le> ell_op_usc k L ((\<lambda>z. p + (Ym - \<delta> *\<^sub>R mat 1) *v (z - yh)) yh)
      (Ym - \<delta> *\<^sub>R mat 1)"
    using sup yh tf minloc unfolding supersol_jet_def by blast
  thus ?thesis unfolding g .
qed

theorem supersol_shifted_bound:
  fixes w :: "real^'n::finite \<Rightarrow> real" and Ym :: "real^'n^'n"
  assumes sup: "supersol_jet k L \<Omega> w"
    and yh: "yh \<in> \<Omega>"
    and Ys: "transpose Ym = Ym"
    and jet: "((\<lambda>h. ((- w) (yh + h) - (- w) yh - (- p) \<bullet> h
        - (h \<bullet> ((- Ym) *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and d: "0 < \<delta>"
  shows "1 \<le> ell_op_usc k L p (Ym - \<delta> *\<^sub>R mat 1)"
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
    by (rule jet_imp_local_min_test[OF jet d])
  have "1 \<le> ell_op_usc k L ((\<lambda>z. p + (Ym - \<delta> *\<^sub>R mat 1) *v (z - yh)) yh)
      (Ym - \<delta> *\<^sub>R mat 1)"
    using sup yh tf minloc unfolding supersol_jet_def by blast
  thus ?thesis unfolding g .
qed

corollary supersol_shifted_bound_ne:
  fixes w :: "real^'n::finite \<Rightarrow> real" and Ym :: "real^'n^'n"
  assumes sup: "supersol_jet k L \<Omega> w" and yh: "yh \<in> \<Omega>"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and Ys: "transpose Ym = Ym"
    and jet: "((\<lambda>h. ((- w) (yh + h) - (- w) yh - (- p) \<bullet> h
        - (h \<bullet> ((- Ym) *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and d: "0 < \<delta>" and p0: "p \<noteq> 0"
  shows "1 \<le> ell_op k L p (Ym - \<delta> *\<^sub>R mat 1)"
proof -
  have "1 \<le> ell_op_usc k L p (Ym - \<delta> *\<^sub>R mat 1)"
    by (rule supersol_shifted_bound[OF sup yh Ys jet d])
  then show ?thesis
    unfolding ell_op_usc_eq_at_nonzero[OF kk(1) kk(2) LL p0] by simp
qed


(*<*)
end
(*>*)
