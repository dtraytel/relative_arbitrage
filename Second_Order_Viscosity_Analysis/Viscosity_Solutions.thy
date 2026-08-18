section \<open>Viscosity sub- and supersolutions of a second-order equation\<close>

(*<*)
theory Viscosity_Solutions
  imports Test_Functions
begin

(*>*)

text \<open>
  The definitions the comparison machinery of this session exists to serve,
  for an arbitrary degenerate elliptic operator \<open>F\<close> on gradient-Hessian
  pairs.  The value type is \<^typ>\<open>ereal\<close> so that the semicontinuous
  envelopes of \<open>F\<close>, which the boundary clauses are stated through, need no
  side condition.

  Four notions, differing in where the test function touches and in which
  envelope of \<open>F\<close> the conclusion is read:

    \<^item> \<open>visc_subsol_gen\<close> / \<open>visc_supersol_gen\<close> --- the touching is local,
      on a ball around \<open>x\<close>;
    \<^item> \<open>visc_subsol_gen_env\<close> / \<open>visc_supersol_gen_env\<close> --- the touching is
      global on a set \<open>K\<close>, which is what a maximum principle produces.

  The level is \<open>1\<close> rather than \<open>0\<close>: the equation this session was written
  for is \<open>F = 1\<close>, and normalising it would only move the constant.
\<close>

definition visc_subsol_gen ::
  "(real^'n \<Rightarrow> real^'n^'n \<Rightarrow> ereal) \<Rightarrow> (real^'n) set \<Rightarrow> (real^'n \<Rightarrow> real) \<Rightarrow> bool"
  where
  "visc_subsol_gen F \<Omega> u \<longleftrightarrow>
     (\<forall>x\<in>\<Omega>. \<forall>\<phi> g H. test_fun_at \<phi> g H x \<longrightarrow>
        (\<exists>e>0. \<forall>y \<in> ball x e. u y - \<phi> y \<le> u x - \<phi> x) \<longrightarrow>
        F (g x) H \<le> 1)"

definition visc_supersol_gen ::
  "(real^'n \<Rightarrow> real^'n^'n \<Rightarrow> ereal) \<Rightarrow> (real^'n) set \<Rightarrow> (real^'n \<Rightarrow> real) \<Rightarrow> bool"
  where
  "visc_supersol_gen F \<Omega> u \<longleftrightarrow>
     (\<forall>x\<in>\<Omega>. \<forall>\<phi> g H. test_fun_at \<phi> g H x \<longrightarrow>
        (\<exists>e>0. \<forall>y \<in> ball x e. u x - \<phi> x \<le> u y - \<phi> y) \<longrightarrow>
        1 \<le> F (g x) H)"

definition visc_sol_gen ::
  "(real^'n \<Rightarrow> real^'n^'n \<Rightarrow> ereal) \<Rightarrow> (real^'n) set \<Rightarrow> (real^'n \<Rightarrow> real) \<Rightarrow> bool"
  where "visc_sol_gen F \<Omega> u \<longleftrightarrow> visc_subsol_gen F \<Omega> u \<and> visc_supersol_gen F \<Omega> u"

definition visc_subsol_gen_env ::
  "(real^'n \<Rightarrow> real^'n^'n \<Rightarrow> ereal) \<Rightarrow> (real^'n) set \<Rightarrow> (real^'n) set
     \<Rightarrow> (real^'n \<Rightarrow> real) \<Rightarrow> bool"
  where
  "visc_subsol_gen_env F K \<Omega> u \<longleftrightarrow>
     (\<forall>x\<in>\<Omega>. \<forall>\<phi> g H. test_fun_at \<phi> g H x \<longrightarrow>
        (\<forall>y\<in>K. u y - \<phi> y \<le> u x - \<phi> x) \<longrightarrow> F (g x) H \<le> 1)"

definition visc_supersol_gen_env ::
  "(real^'n \<Rightarrow> real^'n^'n \<Rightarrow> ereal) \<Rightarrow> (real^'n) set \<Rightarrow> (real^'n) set
     \<Rightarrow> (real^'n \<Rightarrow> real) \<Rightarrow> bool"
  where
  "visc_supersol_gen_env F K \<Omega> u \<longleftrightarrow>
     (\<forall>x\<in>\<Omega>. \<forall>\<phi> g H. test_fun_at \<phi> g H x \<longrightarrow>
        (\<forall>y\<in>K. u x - \<phi> x \<le> u y - \<phi> y) \<longrightarrow> 1 \<le> F (g x) H)"

text \<open>The maximum principle as a predicate on the operator and the set,
  which is what a comparison theorem discharges and everything downstream of
  it consumes: for a subsolution \<open>u\<close> and a supersolution \<open>w\<close>, continuous on
  \<open>K\<close>, the difference \<open>u - w\<close> attains its maximum over \<open>K\<close> on the
  boundary.\<close>

definition max_principle_boundary_gen ::
  "(real^'n \<Rightarrow> real^'n^'n \<Rightarrow> ereal) \<Rightarrow> (real^'n \<Rightarrow> real^'n^'n \<Rightarrow> ereal)
     \<Rightarrow> (real^'n) set \<Rightarrow> bool"
  where
  "max_principle_boundary_gen Fsub Fsuper K \<longleftrightarrow>
     (\<forall>u w. visc_subsol_gen_env Fsub K (interior K) u
        \<longrightarrow> visc_supersol_gen_env Fsuper K (interior K) w
        \<longrightarrow> continuous_on K u \<longrightarrow> continuous_on K w
        \<longrightarrow> (\<exists>x \<in> K - interior K. \<forall>y \<in> K. u y - w y \<le> u x - w x))"

text \<open>Monotonicity in the operator: a smaller \<open>F\<close> has more subsolutions and
  fewer supersolutions.  This is the only fact stated here, and it is the
  one that lets a proof replace \<open>F\<close> by its lower or upper envelope.\<close>

lemma visc_subsol_gen_mono:
  assumes "visc_subsol_gen F \<Omega> u" and "\<And>p M. G p M \<le> F p M"
  shows "visc_subsol_gen G \<Omega> u"
  using assms unfolding visc_subsol_gen_def by (meson order_trans)

lemma visc_supersol_gen_mono:
  assumes "visc_supersol_gen F \<Omega> u" and "\<And>p M. F p M \<le> G p M"
  shows "visc_supersol_gen G \<Omega> u"
  using assms unfolding visc_supersol_gen_def by (meson order_trans)

lemma visc_subsol_gen_env_imp:
  assumes "visc_subsol_gen_env F K \<Omega> u" and "\<Omega>' \<subseteq> \<Omega>"
  shows "visc_subsol_gen_env F K \<Omega>' u"
  using assms unfolding visc_subsol_gen_env_def by blast

lemma visc_supersol_gen_env_imp:
  assumes "visc_supersol_gen_env F K \<Omega> u" and "\<Omega>' \<subseteq> \<Omega>"
  shows "visc_supersol_gen_env F K \<Omega>' u"
  using assms unfolding visc_supersol_gen_env_def by blast

(*<*)
end
(*>*)
