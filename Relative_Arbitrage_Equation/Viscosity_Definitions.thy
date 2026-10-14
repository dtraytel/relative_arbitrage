section \<open>The viscosity-solution predicates, in one place\<close>

(*<*)
theory Viscosity_Definitions
  imports
    Elliptic_Operator Geometric_Operator
    "Semicontinuous_Analysis.Semicontinuous_Envelopes"
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
  \<open>Elliptic_Operator\<close>, i.e. \<open>g\<close> is the gradient and \<open>H\<close> the Hessian.\<close>

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

section \<open>The bridge to the generic predicates\<close>

text \<open>Every predicate above is an instance of the two generic predicates of
  @{theory Second_Order_Viscosity_Analysis.Viscosity_Solutions}: the test class is
  \<^const>\<open>test_fun_at\<close> or \<^const>\<open>test_fun_C2\<close>, the touching is local
  (\<^term>\<open>nhds\<close>) or over \<open>K\<close> (\<^term>\<open>\<lambda>_. principal K\<close>), the operator is
  \<open>F\<close>, \<open>F\<^sub>*\<close> or \<open>F\<^sup>*\<close>, and the function is \<open>u\<close> or its lower
  envelope.  The equations below are proved, not definitional, so that the
  definitions above read as the paper does.\<close>

text \<open>The two envelopes are those of @{theory Relative_Arbitrage_Equation.Geometric_Operator}.\<close>

lemma ell_op_lsc_eq_op_lsc: "ell_op_lsc k L = op_lsc (ell_op k L)"
  by (intro ext) (simp add: ell_op_lsc_def op_lsc_def ell_op_pair_def)

lemma ell_op_usc_eq_op_usc: "ell_op_usc k L = op_usc (ell_op k L)"
  by (intro ext) (simp add: ell_op_usc_def op_usc_def ell_op_pair_def)

lemma visc_subsol_eq_gen:
  "visc_subsol k L \<Omega> u = visc_subsol_gen test_fun_at nhds (\<lambda>p M. ereal (ell_op k L p M)) \<Omega> u"
  by (simp add: visc_subsol_def visc_subsol_gen_nhds)

lemma visc_supersol_eq_gen:
  "visc_supersol k L \<Omega> u = visc_supersol_gen test_fun_at nhds (\<lambda>p M. ereal (ell_op k L p M)) \<Omega> u"
  by (simp add: visc_supersol_def visc_supersol_gen_nhds)

lemma visc_sol_eq_gen:
  "visc_sol k L \<Omega> u = visc_sol_gen test_fun_at nhds (\<lambda>p M. ereal (ell_op k L p M)) \<Omega> u"
  by (simp add: visc_sol_def visc_sol_gen_def visc_subsol_eq_gen visc_supersol_eq_gen)

lemma visc_subsol_env_eq_gen:
  "visc_subsol_env k L K \<Omega> u = visc_subsol_gen test_fun_at (\<lambda>_. principal K) (ell_op_lsc k L) \<Omega> u"
  by (simp add: visc_subsol_env_def visc_subsol_gen_principal)

lemma visc_supersol_env_eq_gen:
  "visc_supersol_env k L K \<Omega> u = visc_supersol_gen test_fun_at (\<lambda>_. principal K) (ell_op_usc k L) \<Omega> u"
  by (simp add: visc_supersol_env_def visc_supersol_gen_principal)

lemma visc_sol_env_eq_gen:
  "visc_sol_env k L K \<Omega> u \<longleftrightarrow>
     visc_subsol_gen test_fun_at (\<lambda>_. principal K) (ell_op_lsc k L) \<Omega> u \<and>
     visc_supersol_gen test_fun_at (\<lambda>_. principal K) (ell_op_usc k L) \<Omega> u"
  by (simp add: visc_sol_env_def visc_subsol_env_eq_gen visc_supersol_env_eq_gen)

lemma visc_subsol_env2_eq_gen:
  "visc_subsol_env2 k L K \<Omega> u = visc_subsol_gen test_fun_C2 (\<lambda>_. principal K) (ell_op_lsc k L) \<Omega> u"
  by (simp add: visc_subsol_env2_def visc_subsol_gen_principal)

lemma visc_supersol_env2_eq_gen:
  "visc_supersol_env2 k L K \<Omega> u = visc_supersol_gen test_fun_C2 (\<lambda>_. principal K) (ell_op_usc k L) \<Omega> u"
  by (simp add: visc_supersol_env2_def visc_supersol_gen_principal)

lemma visc_supersol_lsc_eq_gen:
  "visc_supersol_lsc k L K \<Omega> u
     = visc_supersol_gen test_fun_at (\<lambda>_. principal K) (ell_op_usc k L) \<Omega> (lsc_env u)"
  by (simp add: visc_supersol_lsc_def visc_supersol_gen_principal)

lemma supersol_jet_eq_gen:
  "supersol_jet k L \<Omega> w = visc_supersol_gen test_fun_at nhds (ell_op_usc k L) \<Omega> w"
  by (simp add: supersol_jet_def visc_supersol_gen_nhds)

(*<*)
end
(*>*)
