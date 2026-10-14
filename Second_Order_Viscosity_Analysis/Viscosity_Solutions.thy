section \<open>Viscosity sub- and supersolutions of a second-order equation\<close>

(*<*)
theory Viscosity_Solutions
  imports Test_Functions
begin

(*>*)

text \<open>
  Two predicates, for an arbitrary operator \<open>F\<close> on gradient-Hessian pairs,
  cover every variant of the definition in use.  Besides \<open>F\<close>, the set
  \<open>\<Omega>\<close> of points where the inequality is required and the function \<open>u\<close>,
  they take two parameters:

    \<^item> the test class \<open>T\<close>: \<open>T \<phi> g H x\<close> says that \<open>\<phi>\<close>, with gradient field
      \<open>g\<close> and Hessian \<open>H\<close> at \<open>x\<close>, may be used at \<open>x\<close>
      (e.g.\ \<^const>\<open>test_fun_at\<close> or \<^const>\<open>test_fun_C2\<close>);
    \<^item> the touching locality \<open>N\<close>: \<open>u - \<phi>\<close> has a maximum (minimum) at \<open>x\<close>
      relative to the filter \<open>N x\<close>.  The filter \<^term>\<open>nhds x\<close> gives the
      usual local touching (on a ball around \<open>x\<close>,
      \<open>visc_subsol_gen_nhds\<close> below); the filter \<^term>\<open>principal K\<close>
      gives the touching over all of a set \<open>K\<close> that a boundary-value
      problem on \<open>K\<close> uses (\<open>visc_subsol_gen_principal\<close>).

  The value type is \<^typ>\<open>ereal\<close>, so that the semicontinuous envelopes of an
  operator, through which the boundary clauses are stated, need no side
  condition.  The level is \<open>1\<close> rather than \<open>0\<close>: the equation this session
  was written for is \<open>F = 1\<close>, and normalising it would only move the
  constant.
\<close>

definition visc_subsol_gen ::
  "((real^'n \<Rightarrow> real) \<Rightarrow> (real^'n \<Rightarrow> real^'n) \<Rightarrow> real^'n^'n \<Rightarrow> real^'n \<Rightarrow> bool)
    \<Rightarrow> (real^'n \<Rightarrow> (real^'n) filter) \<Rightarrow> (real^'n \<Rightarrow> real^'n^'n \<Rightarrow> ereal)
    \<Rightarrow> (real^'n) set \<Rightarrow> (real^'n \<Rightarrow> real) \<Rightarrow> bool"
  where
  "visc_subsol_gen T N F \<Omega> u \<longleftrightarrow>
     (\<forall>x\<in>\<Omega>. \<forall>\<phi> g H. T \<phi> g H x \<longrightarrow>
        eventually (\<lambda>y. u y - \<phi> y \<le> u x - \<phi> x) (N x) \<longrightarrow> F (g x) H \<le> 1)"

definition visc_supersol_gen ::
  "((real^'n \<Rightarrow> real) \<Rightarrow> (real^'n \<Rightarrow> real^'n) \<Rightarrow> real^'n^'n \<Rightarrow> real^'n \<Rightarrow> bool)
    \<Rightarrow> (real^'n \<Rightarrow> (real^'n) filter) \<Rightarrow> (real^'n \<Rightarrow> real^'n^'n \<Rightarrow> ereal)
    \<Rightarrow> (real^'n) set \<Rightarrow> (real^'n \<Rightarrow> real) \<Rightarrow> bool"
  where
  "visc_supersol_gen T N F \<Omega> u \<longleftrightarrow>
     (\<forall>x\<in>\<Omega>. \<forall>\<phi> g H. T \<phi> g H x \<longrightarrow>
        eventually (\<lambda>y. u x - \<phi> x \<le> u y - \<phi> y) (N x) \<longrightarrow> 1 \<le> F (g x) H)"

definition visc_sol_gen ::
  "((real^'n \<Rightarrow> real) \<Rightarrow> (real^'n \<Rightarrow> real^'n) \<Rightarrow> real^'n^'n \<Rightarrow> real^'n \<Rightarrow> bool)
    \<Rightarrow> (real^'n \<Rightarrow> (real^'n) filter) \<Rightarrow> (real^'n \<Rightarrow> real^'n^'n \<Rightarrow> ereal)
    \<Rightarrow> (real^'n) set \<Rightarrow> (real^'n \<Rightarrow> real) \<Rightarrow> bool"
  where
  "visc_sol_gen T N F \<Omega> u \<longleftrightarrow> visc_subsol_gen T N F \<Omega> u \<and> visc_supersol_gen T N F \<Omega> u"

subsection \<open>The two touching localities in elementary form\<close>

lemma eventually_nhds_ball_iff:
  "eventually P (nhds x) \<longleftrightarrow> (\<exists>e>0. \<forall>y\<in>ball x e. P y)"
  by (simp add: eventually_nhds_metric ball_def dist_commute)

lemma visc_subsol_gen_nhds:
  "visc_subsol_gen T nhds F \<Omega> u \<longleftrightarrow>
     (\<forall>x\<in>\<Omega>. \<forall>\<phi> g H. T \<phi> g H x \<longrightarrow>
        (\<exists>e>0. \<forall>y \<in> ball x e. u y - \<phi> y \<le> u x - \<phi> x) \<longrightarrow> F (g x) H \<le> 1)"
  by (simp add: visc_subsol_gen_def eventually_nhds_ball_iff)

lemma visc_supersol_gen_nhds:
  "visc_supersol_gen T nhds F \<Omega> u \<longleftrightarrow>
     (\<forall>x\<in>\<Omega>. \<forall>\<phi> g H. T \<phi> g H x \<longrightarrow>
        (\<exists>e>0. \<forall>y \<in> ball x e. u x - \<phi> x \<le> u y - \<phi> y) \<longrightarrow> 1 \<le> F (g x) H)"
  by (simp add: visc_supersol_gen_def eventually_nhds_ball_iff)

lemma visc_subsol_gen_principal:
  "visc_subsol_gen T (\<lambda>_. principal K) F \<Omega> u \<longleftrightarrow>
     (\<forall>x\<in>\<Omega>. \<forall>\<phi> g H. T \<phi> g H x \<longrightarrow>
        (\<forall>y\<in>K. u y - \<phi> y \<le> u x - \<phi> x) \<longrightarrow> F (g x) H \<le> 1)"
  by (simp add: visc_subsol_gen_def eventually_principal)

lemma visc_supersol_gen_principal:
  "visc_supersol_gen T (\<lambda>_. principal K) F \<Omega> u \<longleftrightarrow>
     (\<forall>x\<in>\<Omega>. \<forall>\<phi> g H. T \<phi> g H x \<longrightarrow>
        (\<forall>y\<in>K. u x - \<phi> x \<le> u y - \<phi> y) \<longrightarrow> 1 \<le> F (g x) H)"
  by (simp add: visc_supersol_gen_def eventually_principal)

subsection \<open>Monotonicity in each parameter\<close>

text \<open>A smaller \<open>F\<close> has more subsolutions and fewer supersolutions; this is
  what lets a proof replace \<open>F\<close> by its lower or upper envelope.\<close>

lemma visc_subsol_gen_mono:
  assumes "visc_subsol_gen T N F \<Omega> u" and "\<And>p M. G p M \<le> F p M"
  shows "visc_subsol_gen T N G \<Omega> u"
  using assms unfolding visc_subsol_gen_def by (meson order_trans)

lemma visc_supersol_gen_mono:
  assumes "visc_supersol_gen T N F \<Omega> u" and "\<And>p M. F p M \<le> G p M"
  shows "visc_supersol_gen T N G \<Omega> u"
  using assms unfolding visc_supersol_gen_def by (meson order_trans)

lemma visc_subsol_gen_subset:
  assumes "visc_subsol_gen T N F \<Omega> u" and "\<Omega>' \<subseteq> \<Omega>"
  shows "visc_subsol_gen T N F \<Omega>' u"
  using assms unfolding visc_subsol_gen_def by blast

lemma visc_supersol_gen_subset:
  assumes "visc_supersol_gen T N F \<Omega> u" and "\<Omega>' \<subseteq> \<Omega>"
  shows "visc_supersol_gen T N F \<Omega>' u"
  using assms unfolding visc_supersol_gen_def by blast

text \<open>A smaller test class constrains fewer test functions.\<close>

lemma visc_subsol_gen_test_mono:
  assumes "visc_subsol_gen T N F \<Omega> u" and "\<And>\<phi> g H x. T' \<phi> g H x \<Longrightarrow> T \<phi> g H x"
  shows "visc_subsol_gen T' N F \<Omega> u"
  using assms unfolding visc_subsol_gen_def by blast

lemma visc_supersol_gen_test_mono:
  assumes "visc_supersol_gen T N F \<Omega> u" and "\<And>\<phi> g H x. T' \<phi> g H x \<Longrightarrow> T \<phi> g H x"
  shows "visc_supersol_gen T' N F \<Omega> u"
  using assms unfolding visc_supersol_gen_def by blast

text \<open>A coarser locality (fewer touchings) constrains fewer test functions:
  a touching relative to \<open>N x\<close> is one relative to any finer \<open>N' x\<close>.  With
  \<open>N' = nhds\<close> and \<open>N = \<lambda>_. principal K\<close> this is the passage from local to
  global touching on an open \<open>\<Omega> \<subseteq> K\<close>
  (\<open>nhds_le_principal_of_open\<close>).\<close>

lemma visc_subsol_gen_filter_mono:
  assumes "visc_subsol_gen T N' F \<Omega> u" and "\<And>x. x \<in> \<Omega> \<Longrightarrow> N' x \<le> N x"
  shows "visc_subsol_gen T N F \<Omega> u"
  using assms unfolding visc_subsol_gen_def by (meson filter_leD)

lemma visc_supersol_gen_filter_mono:
  assumes "visc_supersol_gen T N' F \<Omega> u" and "\<And>x. x \<in> \<Omega> \<Longrightarrow> N' x \<le> N x"
  shows "visc_supersol_gen T N F \<Omega> u"
  using assms unfolding visc_supersol_gen_def by (meson filter_leD)

lemma nhds_le_principal_of_open:
  assumes "open \<Omega>" and "\<Omega> \<subseteq> K" and "x \<in> \<Omega>"
  shows "nhds x \<le> principal K"
proof -
  have "eventually (\<lambda>y. y \<in> \<Omega>) (nhds x)" by (rule eventually_nhds_in_open[OF assms(1,3)])
  then show ?thesis unfolding le_principal by eventually_elim (use assms(2) in blast)
qed

text \<open>Only the values of \<open>u\<close> at the points of \<open>\<Omega>\<close> and near them, in the
  sense of the locality, matter.\<close>

lemma visc_subsol_gen_cong:
  assumes "visc_subsol_gen T N F \<Omega> u"
    and "\<And>x. x \<in> \<Omega> \<Longrightarrow> u x = u' x"
    and "\<And>x. x \<in> \<Omega> \<Longrightarrow> eventually (\<lambda>y. u y = u' y) (N x)"
  shows "visc_subsol_gen T N F \<Omega> u'"
  unfolding visc_subsol_gen_def
proof (intro ballI allI impI)
  fix x \<phi> g H
  assume x: "x \<in> \<Omega>" and tf: "T \<phi> g H x"
    and ev: "eventually (\<lambda>y. u' y - \<phi> y \<le> u' x - \<phi> x) (N x)"
  have "eventually (\<lambda>y. u y - \<phi> y \<le> u x - \<phi> x) (N x)"
    using eventually_conj[OF ev assms(3)[OF x]] by eventually_elim (simp add: assms(2)[OF x])
  then show "F (g x) H \<le> 1" using assms(1) x tf unfolding visc_subsol_gen_def by blast
qed

lemma visc_supersol_gen_cong:
  assumes "visc_supersol_gen T N F \<Omega> u"
    and "\<And>x. x \<in> \<Omega> \<Longrightarrow> u x = u' x"
    and "\<And>x. x \<in> \<Omega> \<Longrightarrow> eventually (\<lambda>y. u y = u' y) (N x)"
  shows "visc_supersol_gen T N F \<Omega> u'"
  unfolding visc_supersol_gen_def
proof (intro ballI allI impI)
  fix x \<phi> g H
  assume x: "x \<in> \<Omega>" and tf: "T \<phi> g H x"
    and ev: "eventually (\<lambda>y. u' x - \<phi> x \<le> u' y - \<phi> y) (N x)"
  have "eventually (\<lambda>y. u x - \<phi> x \<le> u y - \<phi> y) (N x)"
    using eventually_conj[OF ev assms(3)[OF x]] by eventually_elim (simp add: assms(2)[OF x])
  then show "1 \<le> F (g x) H" using assms(1) x tf unfolding visc_supersol_gen_def by blast
qed

subsection \<open>From a global touching over \<open>K\<close> back to a local one\<close>

text \<open>The converse of the filter monotonicity, for a test class closed
  under subtracting a quartic \<open>C\<bar>z - x\<bar>\<^sup>4\<close> (both \<^const>\<open>test_fun_at\<close> and
  \<^const>\<open>test_fun_C2\<close> are: @{thm [source] test_fun_at_quartic_shift},
  @{thm [source] test_fun_C2_quartic_shift}): a solution for the touching
  over \<open>K\<close> also satisfies the inequality at a local touching, provided
  \<open>u\<close> and \<open>\<phi>\<close> are bounded on \<open>K\<close> in the right direction.  The quartic
  shares \<open>\<phi>\<close>'s two-jet at \<open>x\<close> and, for large \<open>C\<close>, turns the local
  touching into a global one (@{thm [source] local_max_quartic_deepen}).\<close>

lemma visc_subsol_gen_principal_local:
  fixes u \<phi> :: "real^'n::finite \<Rightarrow> real"
  assumes sub: "visc_subsol_gen T (\<lambda>_. principal K) F \<Omega> u"
    and x\<Omega>: "x \<in> \<Omega>"
    and tf: "\<And>C. T (\<lambda>z. \<phi> z - C * ((z - x) \<bullet> (z - x))\<^sup>2)
                   (\<lambda>z. g z - (4 * C * ((z - x) \<bullet> (z - x))) *\<^sub>R (z - x)) H x"
    and uhi: "\<And>y. y \<in> K \<Longrightarrow> u y \<le> Bu"
    and phi: "\<And>y. y \<in> K \<Longrightarrow> B\<phi> \<le> \<phi> y"
    and r0: "0 < r"
    and lm: "\<And>y. y \<in> ball x r \<Longrightarrow> u y - \<phi> y \<le> u x - \<phi> x"
  shows "F (g x) H \<le> 1"
proof -
  obtain C where glob: "\<And>y. y \<in> K \<Longrightarrow>
      u y - (\<phi> y + C * ((y - x) \<bullet> (y - x))\<^sup>2) \<le> u x - \<phi> x"
    using local_max_quartic_deepen[where u = u and \<phi> = \<phi>, OF uhi phi r0 lm] by blast
  have "F (g x - (4 * (- C) * ((x - x) \<bullet> (x - x))) *\<^sub>R (x - x)) H \<le> 1"
    by (rule sub[unfolded visc_subsol_gen_principal, rule_format, OF x\<Omega> tf])
      (drule glob; simp; linarith)
  then show ?thesis by simp
qed

lemma visc_supersol_gen_principal_local:
  fixes w \<phi> :: "real^'n::finite \<Rightarrow> real"
  assumes sup: "visc_supersol_gen T (\<lambda>_. principal K) F \<Omega> w"
    and x\<Omega>: "x \<in> \<Omega>"
    and tf: "\<And>C. T (\<lambda>z. \<phi> z - C * ((z - x) \<bullet> (z - x))\<^sup>2)
                   (\<lambda>z. g z - (4 * C * ((z - x) \<bullet> (z - x))) *\<^sub>R (z - x)) H x"
    and wlo: "\<And>y. y \<in> K \<Longrightarrow> Bw \<le> w y"
    and phi: "\<And>y. y \<in> K \<Longrightarrow> \<phi> y \<le> B\<phi>"
    and r0: "0 < r"
    and lm: "\<And>y. y \<in> ball x r \<Longrightarrow> w x - \<phi> x \<le> w y - \<phi> y"
  shows "1 \<le> F (g x) H"
proof -
  have "\<exists>C. \<forall>y\<in>K. - w y - (- \<phi> y + C * ((y - x) \<bullet> (y - x))\<^sup>2) \<le> - w x - - \<phi> x"
  proof (rule local_max_quartic_deepen[where Bu = "- Bw" and B\<phi> = "- B\<phi>", OF _ _ r0])
    show "- w y \<le> - Bw" if "y \<in> K" for y using wlo[OF that] by linarith
    show "- B\<phi> \<le> - \<phi> y" if "y \<in> K" for y using phi[OF that] by linarith
    show "- w y - - \<phi> y \<le> - w x - - \<phi> x" if "y \<in> ball x r" for y
      using lm[OF that] by linarith
  qed
  then obtain C where glob: "\<And>y. y \<in> K \<Longrightarrow>
      - w y - (- \<phi> y + C * ((y - x) \<bullet> (y - x))\<^sup>2) \<le> - w x - - \<phi> x" by blast
  have "1 \<le> F (g x - (4 * C * ((x - x) \<bullet> (x - x))) *\<^sub>R (x - x)) H"
    by (rule sup[unfolded visc_supersol_gen_principal, rule_format, OF x\<Omega> tf])
      (drule glob; simp; linarith)
  then show ?thesis by simp
qed

(*<*)
end
(*>*)
