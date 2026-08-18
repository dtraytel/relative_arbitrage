section \<open>The viscosity-solution predicates, in one place\<close>

(*<*)
theory Viscosity_Definitions
  imports Curvature_Operator "Semicontinuous_Analysis.Semicontinuous_Envelopes"
    "Second_Order_Viscosity_Analysis.Test_Functions"
    "Second_Order_Viscosity_Analysis.Viscosity_Solutions"
begin

(*>*)




definition ell_op_pair ::
  "nat \<Rightarrow> real \<Rightarrow> (real^'n::finite) \<times> (real^'n^'n) \<Rightarrow> ereal"
  where
  "ell_op_pair k L z = ereal (ell_op k L (fst z) (snd z))"

text \<open>\<open>F\<^sub>*(z) = lim\<^bsub>e\<down>0\<^esub> inf\<^bsub>|w-z|<e\<^esub> F(w)\<close> and dually; the limits are
  monotone in \<open>e\<close>, so they are a supremum and an infimum respectively.\<close>

definition ell_op_lsc ::
  "nat \<Rightarrow> real \<Rightarrow> (real^'n::finite) \<Rightarrow> (real^'n^'n) \<Rightarrow> ereal"
  where
  "ell_op_lsc k L p M =
     (SUP e \<in> {0<..}. INF w \<in> ball (p, M) e. ell_op_pair k L w)"

definition ell_op_usc ::
  "nat \<Rightarrow> real \<Rightarrow> (real^'n::finite) \<Rightarrow> (real^'n^'n) \<Rightarrow> ereal"
  where
  "ell_op_usc k L p M =
     (INF e \<in> {0<..}. SUP w \<in> ball (p, M) e. ell_op_pair k L w)"

definition visc_subsol ::
  "nat \<Rightarrow> real \<Rightarrow> (real^'n) set \<Rightarrow> (real^'n \<Rightarrow> real) \<Rightarrow> bool"
  where
  "visc_subsol k L \<Omega> u \<longleftrightarrow>
     (\<forall>x\<in>\<Omega>. \<forall>\<phi> g H. test_fun_at \<phi> g H x \<longrightarrow>
        (\<exists>e>0. \<forall>y \<in> ball x e. u y - \<phi> y \<le> u x - \<phi> x) \<longrightarrow>
        ell_op k L (g x) H \<le> 1)"

definition visc_supersol ::
  "nat \<Rightarrow> real \<Rightarrow> (real^'n) set \<Rightarrow> (real^'n \<Rightarrow> real) \<Rightarrow> bool"
  where
  "visc_supersol k L \<Omega> u \<longleftrightarrow>
     (\<forall>x\<in>\<Omega>. \<forall>\<phi> g H. test_fun_at \<phi> g H x \<longrightarrow>
        (\<exists>e>0. \<forall>y \<in> ball x e. u x - \<phi> x \<le> u y - \<phi> y) \<longrightarrow>
        1 \<le> ell_op k L (g x) H)"

definition visc_sol ::
  "nat \<Rightarrow> real \<Rightarrow> (real^'n) set \<Rightarrow> (real^'n \<Rightarrow> real) \<Rightarrow> bool"
  where
  "visc_sol k L \<Omega> u \<longleftrightarrow> visc_subsol k L \<Omega> u \<and> visc_supersol k L \<Omega> u"

text \<open>The paper's touching condition is global: \<open>(u - \<phi>)(x)\<close> is the maximum
  of \<open>u - \<phi>\<close> over all of \<open>K\<close> (resp. the minimum, for supersolutions).  The
  test-function data \<open>(\<phi>, g, H)\<close> is the same as in
  \<open>Curvature_Operator\<close>, i.e. \<open>g\<close> is the gradient and \<open>H\<close> the Hessian.\<close>

definition visc_subsol_env ::
  "nat \<Rightarrow> real \<Rightarrow> (real^'n::finite) set \<Rightarrow> (real^'n) set
     \<Rightarrow> (real^'n \<Rightarrow> real) \<Rightarrow> bool"
  where
  "visc_subsol_env k L K \<Omega> u \<longleftrightarrow>
     (\<forall>x\<in>\<Omega>. \<forall>\<phi> g H. test_fun_at \<phi> g H x \<longrightarrow>
        (\<forall>y\<in>K. u y - \<phi> y \<le> u x - \<phi> x) \<longrightarrow>
        ell_op_lsc k L (g x) H \<le> 1)"

definition visc_supersol_env ::
  "nat \<Rightarrow> real \<Rightarrow> (real^'n::finite) set \<Rightarrow> (real^'n) set
     \<Rightarrow> (real^'n \<Rightarrow> real) \<Rightarrow> bool"
  where
  "visc_supersol_env k L K \<Omega> u \<longleftrightarrow>
     (\<forall>x\<in>\<Omega>. \<forall>\<phi> g H. test_fun_at \<phi> g H x \<longrightarrow>
        (\<forall>y\<in>K. u x - \<phi> x \<le> u y - \<phi> y) \<longrightarrow>
        1 \<le> ell_op_usc k L (g x) H)"

definition visc_sol_env ::
  "nat \<Rightarrow> real \<Rightarrow> (real^'n::finite) set \<Rightarrow> (real^'n) set
     \<Rightarrow> (real^'n \<Rightarrow> real) \<Rightarrow> bool"
  where
  "visc_sol_env k L K \<Omega> u \<longleftrightarrow>
     visc_subsol_env k L K \<Omega> u \<and> visc_supersol_env k L K \<Omega> u"

text \<open>Definition 3.1 itself, now with the paper's own test-function class.\<close>

definition visc_subsol_env2 ::
  "nat \<Rightarrow> real \<Rightarrow> (real^'n::finite) set \<Rightarrow> (real^'n) set
     \<Rightarrow> (real^'n \<Rightarrow> real) \<Rightarrow> bool"
  where
  "visc_subsol_env2 k L K \<Omega> u \<longleftrightarrow>
     (\<forall>x\<in>\<Omega>. \<forall>\<phi> g H. test_fun_C2 \<phi> g H x \<longrightarrow>
        (\<forall>y\<in>K. u y - \<phi> y \<le> u x - \<phi> x) \<longrightarrow>
        ell_op_lsc k L (g x) H \<le> 1)"

definition visc_supersol_env2 ::
  "nat \<Rightarrow> real \<Rightarrow> (real^'n::finite) set \<Rightarrow> (real^'n) set
     \<Rightarrow> (real^'n \<Rightarrow> real) \<Rightarrow> bool"
  where
  "visc_supersol_env2 k L K \<Omega> u \<longleftrightarrow>
     (\<forall>x\<in>\<Omega>. \<forall>\<phi> g H. test_fun_C2 \<phi> g H x \<longrightarrow>
        (\<forall>y\<in>K. u x - \<phi> x \<le> u y - \<phi> y) \<longrightarrow>
        1 \<le> ell_op_usc k L (g x) H)"

text \<open>Definition 3.1(b), verbatim: the test function touches the lower
  envelope from below, globally on \<open>K\<close>, and the conclusion is the
  inequality for the upper envelope \<open>F\<^sup>*\<close> of the operator.\<close>

definition visc_supersol_lsc ::
  "nat \<Rightarrow> real \<Rightarrow> (real^'n::finite) set \<Rightarrow> (real^'n) set
     \<Rightarrow> (real^'n \<Rightarrow> real) \<Rightarrow> bool"
  where
  "visc_supersol_lsc k L K \<Omega> u \<longleftrightarrow>
     (\<forall>x\<in>\<Omega>. \<forall>\<phi> g H. test_fun_at \<phi> g H x \<longrightarrow>
        (\<forall>y\<in>K. lsc_env u x - \<phi> x \<le> lsc_env u y - \<phi> y) \<longrightarrow>
        1 \<le> ell_op_usc k L (g x) H)"

definition supersol_jet ::
  "nat \<Rightarrow> real \<Rightarrow> (real^'n::finite) set \<Rightarrow> (real^'n \<Rightarrow> real) \<Rightarrow> bool"
  where
  "supersol_jet k L \<Omega> w \<longleftrightarrow>
     (\<forall>x\<in>\<Omega>. \<forall>\<phi> g H. test_fun_at \<phi> g H x \<longrightarrow>
        (\<exists>e>0. \<forall>y \<in> ball x e. w x - \<phi> x \<le> w y - \<phi> y) \<longrightarrow>
        1 \<le> ell_op_usc k L (g x) H)"

text \<open>Theorem 4.2(a) -- the maximum principle: for a subsolution \<open>u\<close> and
  supersolution \<open>w\<close>, \<open>u - w\<close> attains its maximum over compact \<open>K\<close> on the
  boundary -- is proved in the paper via doubling and the Crandall--Ishii
  "theorem on sums" [CI90], which needs sup-convolutions, semiconvexity and
  Alexandrov/Jensen, none available in this HOL-Analysis or the AFP.  It is
  isolated as the predicate \<open>max_principle_boundary\<close> below, from which
  everything downstream -- 4.2(b), Theorem 4.3, Proposition 4.1 -- is proved
  unconditionally.

  The interface needs continuity of \<open>u\<close> and \<open>w\<close> on \<open>K\<close>:
  \<open>visc_subsol k L (interior K) u\<close> constrains only \<open>interior K\<close>, so raising
  \<open>w\<close> by a constant on \<open>K - interior K\<close> destroys every boundary maximum,
  making the predicate genuinely false without continuity, as
  \<open>max_principle_boundary_counterexample\<close> \<open>(Comparison\_Principle)\<close> shows for
  the continuity-free \<open>max_principle_boundary_raw\<close>.  Plain continuity,
  rather than a usc/lsc split, matches the rest of the development and this
  HOL-Analysis's lack of a semicontinuity library.\<close>

definition max_principle_boundary_raw ::
  "nat \<Rightarrow> real \<Rightarrow> (real^'n::finite) set \<Rightarrow> bool"
  where
  "max_principle_boundary_raw k L K \<longleftrightarrow>
     (\<forall>u w. visc_subsol k L (interior K) u \<longrightarrow> visc_supersol k L (interior K) w
        \<longrightarrow> (\<exists>x \<in> K - interior K.
               \<forall>y \<in> K. u y - w y \<le> u x - w x))"

definition max_principle_boundary ::
  "nat \<Rightarrow> real \<Rightarrow> (real^'n::finite) set \<Rightarrow> bool"
  where
  "max_principle_boundary k L K \<longleftrightarrow>
     (\<forall>u w. visc_subsol_env k L K (interior K) u
        \<longrightarrow> visc_supersol_env k L K (interior K) w
        \<longrightarrow> continuous_on K u \<longrightarrow> continuous_on K w
        \<longrightarrow> (\<exists>x \<in> K - interior K.
               \<forall>y \<in> K. u y - w y \<le> u x - w x))"



text \<open>The four notions above are the generic ones of
  @{theory Second_Order_Viscosity_Analysis.Viscosity_Solutions} at this
  paper's operator; the equations below are the bridge, and are what lets a
  reader instantiate the machinery of that session at a different \<open>F\<close>.\<close>

lemma visc_subsol_eq_gen:
  "visc_subsol k L \<Omega> u = visc_subsol_gen (\<lambda>p M. ereal (ell_op k L p M)) \<Omega> u"
  by (simp add: visc_subsol_def visc_subsol_gen_def)

lemma visc_supersol_eq_gen:
  "visc_supersol k L \<Omega> u = visc_supersol_gen (\<lambda>p M. ereal (ell_op k L p M)) \<Omega> u"
  by (simp add: visc_supersol_def visc_supersol_gen_def)

lemma visc_subsol_env_eq_gen:
  "visc_subsol_env k L K \<Omega> u = visc_subsol_gen_env (ell_op_lsc k L) K \<Omega> u"
  by (simp add: visc_subsol_env_def visc_subsol_gen_env_def)

lemma visc_supersol_env_eq_gen:
  "visc_supersol_env k L K \<Omega> u = visc_supersol_gen_env (ell_op_usc k L) K \<Omega> u"
  by (simp add: visc_supersol_env_def visc_supersol_gen_env_def)

lemma max_principle_boundary_eq_gen:
  "max_principle_boundary k L K
     = max_principle_boundary_gen (ell_op_lsc k L) (ell_op_usc k L) K"
  by (simp add: max_principle_boundary_def max_principle_boundary_gen_def
      visc_subsol_env_eq_gen visc_supersol_env_eq_gen)

(*<*)
end
(*>*)
