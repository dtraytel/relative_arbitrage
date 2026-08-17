section \<open>The viscosity-solution predicates, in one place\<close>

(*<*)
theory Viscosity_Definitions
  imports Curvature_Operator "Semicontinuous_Analysis.Semicontinuous_Envelopes"
begin

(*>*)

text \<open>
  Every notion of viscosity sub- and supersolution the development uses, and
  the test-function predicates they quantify over.  They were spread over
  five theories, each defined where it was first needed; the implications
  between them stay where their proofs' machinery is, but the definitions
  are collected here so that the five variants can be read against each
  other.

  The envelope operators \<open>ell_op_lsc\<close> and \<open>ell_op_usc\<close> come along because
  three of the predicates are stated through them, and their definitions
  need nothing beyond \<open>ell_op\<close>.  Their calculus is in
  \<open>Operator_Envelopes\<close>.
\<close>

definition test_fun_at ::
  "(real^'n \<Rightarrow> real) \<Rightarrow> (real^'n \<Rightarrow> real^'n) \<Rightarrow> real^'n^'n \<Rightarrow> real^'n \<Rightarrow> bool"
  where
  "test_fun_at \<phi> g H x \<longleftrightarrow>
     transpose H = H \<and>
     (\<exists>e>0. \<forall>y \<in> ball x e. (\<phi> has_derivative (\<lambda>h. g y \<bullet> h)) (at y)) \<and>
     (g has_derivative (\<lambda>h. H *v h)) (at x)"

text \<open>\<^const>\<open>test_fun_at\<close> asks only that \<open>\<phi>\<close> be differentiable near \<open>x\<close> with
  gradient field \<open>g\<close>, and that \<open>g\<close> be differentiable at \<open>x\<close>; away from \<open>x\<close> it
  constrains \<open>\<phi>\<close> not at all.  Definition 3.1 quantifies over \<open>\<phi> \<in> C\<^sup>2(\<real>\<^sup>n)\<close>,
  a strictly smaller class.  For the assertions that the value function is a
  sub- or supersolution the larger class is the stronger statement, so nothing
  is lost there; but the uniqueness clause \<^emph>\<open>assumes\<close> the property of a
  competitor, and there the larger class would make the hypothesis stronger
  than the paper's and the theorem correspondingly weaker.  So the class is
  spelled out here: a gradient field defined everywhere, together with a
  \<^emph>\<open>continuous\<close> symmetric Hessian field.\<close>

definition test_fun_C2 ::
  "(real^'n::finite \<Rightarrow> real) \<Rightarrow> (real^'n \<Rightarrow> real^'n) \<Rightarrow> real^'n^'n \<Rightarrow> real^'n \<Rightarrow> bool"
  where
  "test_fun_C2 \<phi> g H x \<longleftrightarrow>
     (\<exists>G. (\<forall>y. (\<phi> has_derivative (\<lambda>h. g y \<bullet> h)) (at y)) \<and>
          (\<forall>y. (g has_derivative (\<lambda>h. G y *v h)) (at y)) \<and>
          (\<forall>y. transpose (G y) = G y) \<and>
          continuous_on UNIV G \<and> G x = H)"

definition sym_part :: "real^'n::finite^'n \<Rightarrow> real^'n^'n" where
  "sym_part M = (1/2) *\<^sub>R (M + transpose M)"

text \<open>The paper's hypothesis on \<open>K\<close> for the uniqueness clause of Theorem 1.1:
  a family \<open>T\<^sub>\<iota>\<close> of rotation-dilation-translations, \<open>\<iota> \<in> (1,2]\<close>, with
  \<open>K \<subseteq> (T\<^sub>\<iota> \` K)^\<circ>\<close> and \<open>T\<^sub>\<iota> \<rightarrow> id\<close>, phrased as an \<open>\<epsilon>\<close>-statement with
  the inverse map written out so no invertibility side condition is
  carried.\<close>

definition expandable :: "(real^'n::finite) set \<Rightarrow> bool" where
  "expandable K \<longleftrightarrow>
     (\<forall>e > 0. \<exists>R b c. orthogonal_matrix R \<and> 1 < c \<and> c < 1 + e
        \<and> K \<subseteq> interior ((\<lambda>x. c *\<^sub>R (R *v x) + b) ` K)
        \<and> (\<forall>x \<in> K. dist ((1/c) *\<^sub>R (transpose R *v (x - b))) x \<le> e))"

text \<open>The envelopes are taken in the pair \<open>(p, M)\<close> jointly, as in the
  paper, so \<open>F\<close> is first packaged as a function on the product metric
  space, with values in \<open>ereal\<close> so that the suprema and infima below are
  unconditionally defined.\<close>

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


(*<*)
end
(*>*)
