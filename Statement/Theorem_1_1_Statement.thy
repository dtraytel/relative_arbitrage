(*<*)
theory Theorem_1_1_Statement
  imports Statement_Auxiliary
begin

declare [[show_question_marks = false, names_short = true]]
(*>*)

text \<open>
  Equation and result numbers throughout --- Eq. (1.5)--(1.10), Definition 3.1,
  Lemma 3.1, Example 3.1, Theorem 1.1 --- are those of
  \<^cite>\<open>LaiShkolnikovSoner\<close>, and ``the paper'' always means that one.

  Throughout, \<open>'n\<close> is a finite index type, \<open>n = CARD('n)\<close>, and
  \<open>real^'n\<close> and \<open>real^'n^'n\<close> are vectors and matrices over it.  \<open>**\<close> is
  matrix multiplication, \<open>*v\<close> matrix-vector application, \<open>\<bullet>\<close> the inner
  product and \<open>trace\<close> the trace.  An underscore in an identifier is
  typeset as a hyphen, so \<open>iexit_val\<close> appears as \<open>iexit-val\<close>.
\<close>

section \<open>The operator of Eq. (1.9)\<close>

text \<open>A matrix is positive semidefinite when it is symmetric and its quadratic
  form is nonnegative:\<close>

text \<open>@{thm [display] psd_def}\<close>

text \<open>The two spectral conditions are stated through their Courant--Fischer
  variational characterisations, which is equivalent for symmetric matrices and
  avoids developing the spectral theorem.  \<open>eigen_lb a m\<close> says that the \<open>m\<close>
  smallest eigenvalues of \<open>a\<close> are at least \<open>1\<close>, and \<open>eigen_ub a L\<close> that the
  largest is at most \<open>L\<close>:\<close>

text \<open>@{thm [display] eigen_lb_def eigen_ub_def}\<close>

text \<open>The feasible set of Eq. (1.9) at a gradient \<open>p\<close> adds the orthogonality
  constraint \<open>a *v p = 0\<close>:\<close>

text \<open>@{thm [display] feasible_def}\<close>

text \<open>and the operator \<open>F\<close> of Eq. (1.9) is the infimum over it:\<close>

text \<open>@{thm [display] ell_op_def}\<close>

section \<open>The class of Eq. (1.7)\<close>

text \<open>The covariation constraint of Eq. (1.5).  \<open>Pi_proj a m\<close> is the infimum of
  \<open>trace (a ** P)\<close> over rank-\<open>m\<close> orthogonal projections \<open>P\<close>, so \<open>Pi_constraint k\<close>
  is the set of positive semidefinite matrices whose projections onto every
  \<open>m\<close>-dimensional subspace have trace at least \<open>m - k\<close>; intersecting with the
  eigenvalue upper bound gives the constraint set \<open>S\<close>:\<close>

text \<open>@{thm [display] Pi_proj_def Pi_constraint_def sconstraint_def}\<close>

text \<open>One reading had to be fixed here.  Eq. (1.5) of \<^cite>\<open>LaiShkolnikovSoner\<close>
  writes the infimum over
  \<open>P\<^sup>2 = P\<close>, \<open>tr(P) = m\<close>, without asking \<open>P\<close> to be symmetric; \<^const>\<open>is_proj\<close>
  does ask.  Taken literally the infimum is \<open>-\<infinity>\<close> for essentially every \<open>a\<close>: in
  three dimensions with \<open>k = 1\<close>, \<open>m = 2\<close>, take \<open>a = u u\<^sup>T\<close> with \<open>u = (1,0,1)\<close>
  and \<open>P\<close> the rank-2 idempotent with range \<open>span{e\<^sub>1,e\<^sub>2}\<close> and kernel
  \<open>span{e\<^sub>3 + N e\<^sub>1}\<close>; then \<open>tr(P) = 2\<close>, \<open>P\<^sup>2 = P\<close> and \<open>tr(a P) = 1 - N\<close>.  So the
  literal (1.5) would define the empty set whenever \<open>k \<le> n - 2\<close>, and every
  \<open>P\<^sub>x\<close> would be empty.  The orthogonal reading is the one the paper's own
  Lemma 2.1 proof uses --- \<open>\<Pi>\<^sub>m\<close> as the sum of the \<open>m\<close> smallest eigenvalues ---
  and is what is formalised.\<close>

text \<open>A member of the class of Eq. (1.7) is a law on the continuous paths of
  \<open>C([0,\<infinity>),\<real>\<^sup>n)\<close>, as the paper writes it: the law starts at \<open>x\<close>, the coordinate
  process is a martingale, and \<^emph>\<open>some\<close> continuous adapted \<open>A\<close> compensates
  \<open>X X\<^sup>T\<close> and has all its difference quotients in \<open>S\<^sub>k\<^sup>L\<close>.  The existential reading
  of the covariation is a stated choice, and it is faithful: \<open>d\<langle>X\<rangle>/dt \<in> S\<^sub>k\<^sup>L\<close> says
  exactly that \<open>\<langle>X\<rangle>\<close> is such an \<open>A\<close>, and the compensator is unique up to
  indistinguishability.\<close>

text \<open>@{thm [display] ipath_def outerp_def xclass_def}\<close>

text \<open>One further reading, since it is not forced by the text of Eq. (1.7).
  Eq. (1.7) constrains \<open>d\<langle>X\<rangle>(t)/dt\<close>, an almost-everywhere derivative; the clause
  above asks every difference quotient \<open>(\<langle>X\<rangle>(t) - \<langle>X\<rangle>(s))/(t-s)\<close> to lie in \<open>S\<close>.
  Since \<open>S\<close> is compact and convex the two agree for absolutely continuous
  \<open>\<langle>X\<rangle>\<close>, and the difference-quotient form is what Lemma 2.3 uses (its display
  (2.8)).  They part company only if \<open>\<langle>X\<rangle>\<close> is allowed a singular part, which the
  derivative notation arguably permits; such a part only makes \<open>X\<close> exit sooner,
  so the value function is unaffected, but the choice is an interpretation.\<close>

text \<open>The exit time of a path from \<open>K\<close> before a time \<open>T\<close>, its increasing limit,
  which takes values in \<open>[0,\<infinity>]\<close>, the essential infimum of such a time under a
  law, and the value function of Eq. (1.6) as the supremum of those over the
  class:\<close>

text \<open>@{thm [display] etime_def pexit_def iexit_def ess_inf_enn_def xval_def}\<close>

section \<open>Viscosity solutions in the sense of Definition 3.1\<close>

text \<open>The lower semicontinuous envelope.  Definition 3.1 reads it within \<open>K\<close>,
  which is \<^const>\<open>lsc_envK\<close>:\<close>

text \<open>@{thm [display] lsc_envK_def}\<close>

text \<open>\<^cite>\<open>LaiShkolnikovSoner\<close> writes the envelopes as \<open>lim\<^sub>\<epsilon>\<^sub>\<down>\<^sub>0 inf\<^sub>{\<^sub>|\<^sub>y\<^sub>-\<^sub>x\<^sub>|\<^sub><\<^sub>\<epsilon>\<^sub>}\<close> without saying
  whether \<open>y\<close> ranges over \<open>K\<close> or over \<open>\<real>\<^sup>n\<close>.  Since Definition 3.1 opens with a
  bounded \<open>u : K \<rightarrow> \<real>\<close>, only the within-\<open>K\<close> reading typechecks, and that is
  \<^const>\<open>lsc_envK\<close>.  Worth pinning down in the paper, as the two genuinely
  differ on \<open>K - interior K\<close> --- exactly where the boundary clause bites.\<close>

text \<open>\<open>F\<^sub>*\<close> and \<open>F\<^sup>*\<close> are the semicontinuous envelopes of \<open>F\<close> in the pair
  \<open>(p,M)\<close> jointly, as in the paper:\<close>

text \<open>@{thm [display] ell_op_lsc_def ell_op_usc_def}\<close>

text \<open>Definition 3.1 takes those envelopes over \<open>\<real>\<^sup>n \<times> \<bbbS>\<^sup>n\<close>, the symmetric
  matrices, whereas the balls above range over all of \<open>\<real>\<^sup>n \<times> \<real>\<^sup>n\<^sup>\<times>\<^sup>n\<close>.  The two
  agree, so this is not a widening: \<open>F\<close> factors through \<open>M \<mapsto> (M + M\<^sup>T)/2\<close>,
  because the feasible matrices are positive semidefinite hence symmetric, and
  that map is a contraction fixing \<open>\<bbbS>\<^sup>n\<close>.  See \<^theory_text>\<open>ell_op_lsc_eq_over_sym\<close> and
  \<^theory_text>\<open>ell_op_usc_eq_over_sym\<close>.\<close>

text \<open>Definition 3.1 quantifies over \<open>\<phi> \<in> C\<^sup>2(\<real>\<^sup>n)\<close>, and that is the class used
  below.  The development also proves the sub- and supersolution properties for
  the wider class of functions merely differentiable near \<open>x\<close> with a gradient
  differentiable at \<open>x\<close>; for the conjuncts that \<^emph>\<open>assert\<close> those properties the
  wider class is the stronger statement, but the uniqueness conjunct \<^emph>\<open>assumes\<close>
  them of a competitor, and there the paper's own \<open>C\<^sup>2\<close> class is what is wanted,
  so it is what appears throughout.\<close>

text \<open>@{thm [display] test_fun_C2_def}\<close>

text \<open>Definition 3.1 itself, with the touching taken globally over \<open>K\<close> and the
  inequality demanded at the points of \<open>\<Omega>\<close>.  Instantiating \<open>\<Omega>\<close> at \<open>interior K\<close>
  gives the interior clause; instantiating it at the union of \<open>interior K\<close> with
  the boundary points where the envelope has the right sign gives that clause
  together with the zero boundary condition of Eq. (1.10):\<close>

text \<open>@{thm [display] visc_subsol_env2_def visc_supersol_env2_def}\<close>

text \<open>The hypothesis Theorem 4.3 and Proposition 4.1 place on \<open>K\<close>: a family of
  rotations, dilations and translations shrinking to the identity, each of
  which expands \<open>K\<close> into its own interior.\<close>

text \<open>@{thm [display] expandable_def}\<close>

text \<open>Three small departures from the wording of Theorem 1.1, all in the
  direction of a weaker hypothesis and hence a stronger uniqueness clause.  The
  linear part is any \<^const>\<open>orthogonal_matrix\<close>, so reflections are allowed and
  not just rotations.  The family is presented as \<open>\<forall>e>0. \<exists>\<dots>\<close> rather than indexed
  by \<open>\<iota> \<in> (1,2]\<close>.  Closeness to the identity is measured on the inverse map over
  \<open>K\<close>, which is what the comparison proof consumes; the dilation factor is asked
  to exceed \<open>1\<close>, which \<open>K \<subseteq> interior (T ` K)\<close> forces anyway once \<open>K\<close> has
  interior --- at \<open>c = 1\<close> the minimal enclosing ball of \<open>T\<^sup>-\<^sup>1 ` K\<close> would have to
  coincide with that of \<open>K\<close>, putting a point of \<open>T\<^sup>-\<^sup>1 ` K\<close> on its boundary
  sphere, which contradicts \<open>T\<^sup>-\<^sup>1 ` K \<subseteq> interior K\<close>.\<close>

text \<open>Every compact convex set with nonempty interior satisfies it, so the
  hypothesis is not vacuous.\<close>

section \<open>Theorem 1.1\<close>

text \<open>The value function of Eq. (1.6) is a bounded upper semicontinuous
  viscosity solution of \<open>F(\<nabla>v, \<nabla>\<^sup>2v) = 1\<close> on \<open>K\<close> with the zero boundary
  condition, in the sense of Definition 3.1, and it is the only one.  The five
  clauses are the five conjuncts below, annotated where a reading had to be
  chosen.

  The standing hypotheses of \<^cite>\<open>LaiShkolnikovSoner\<close> are \<open>1 \<le> k < n\<close> and
  \<open>1 \<le> L\<close>, and both are assumed here.  Several conjuncts are in fact proved
  without \<open>1 \<le> k\<close>, which is a strengthening rather than a gap.\<close>

theorem theorem_1_1:
  fixes K :: "(real^'n::finite) set"
  assumes kn: "k < CARD('n)" and L1: "1 \<le> L" and k1: "1 \<le> k"
    and cK: "compact K" and neK: "K \<noteq> {}" and expK: "expandable K"
  defines "v \<equiv> (\<lambda>z. enn2real (xval k L K z))"
  shows "(\<exists>B. \<forall>y. \<bar>v y\<bar> \<le> B)
         \<comment> \<open>clause (0): finiteness.  Read through \<^const>\<open>enn2real\<close>, so this also
             says the value is finite; \<open>iexit_val\<close> itself is an \<^typ>\<open>ennreal\<close>
             and on a ball is bounded by the closed form of Example 3.1.\<close>
       \<and> (\<forall>c z. v z < c \<longrightarrow> (\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> v y < c))
         \<comment> \<open>clause (1): upper semicontinuity.\<close>
       \<and> visc_subsol_env2 k L K
           (interior K \<union> {x \<in> K - interior K. 0 < v x}) v
         \<comment> \<open>clause (2), subsolution half, together with clause (3) for the
             subsolution: the touching set is the interior together with the
             boundary points where \<open>v\<close> is positive.\<close>
       \<and> visc_supersol_env2 k L K
           (interior K \<union> {x \<in> K - interior K. lsc_envK K v x < 0})
           (lsc_envK K v)
         \<comment> \<open>clause (2), supersolution half, with clause (3) for the
             supersolution.  Note the asymmetry Definition 3.1 itself has: the
             subsolution property is asked of \<open>v\<close>, the supersolution property of
             its lower envelope.  The paper's standing \<open>1 \<le> L\<close> is assumed; \<open>L = 1\<close>
             is not excluded, though Case 1 of Section 3 does not reach it as
             written --- it perturbs eigenvalues into the empty interval \<open>(1,L)\<close>
             --- and an exact-rotation covariance field is used instead.\<close>
       \<and> (\<forall>u :: real^'n \<Rightarrow> real. \<forall>Bd.
            (\<forall>c z. z \<in> K \<longrightarrow> u z < c \<longrightarrow>
               (\<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> u y < c))
            \<longrightarrow> (\<forall>y\<in>K. \<bar>u y\<bar> \<le> Bd)
            \<longrightarrow> visc_subsol_env2 k L K
                 (interior K \<union> {x \<in> K - interior K. 0 < u x}) u
            \<longrightarrow> visc_supersol_env2 k L K
                 (interior K \<union> {x \<in> K - interior K. lsc_envK K u x < 0})
                 (lsc_envK K u)
            \<longrightarrow> (\<forall>x\<in>K. u x = v x))
         \<comment> \<open>clause (4): uniqueness.  The competitor is quantified over inside
             the statement, so the whole of Theorem 1.1 is one formula.  Every
             hypothesis on it is about \<open>K\<close> alone --- semicontinuity and
             boundedness are demanded only at and between points of \<open>K\<close>, and the
             envelope is the paper's \<^const>\<open>lsc_envK\<close>.  Continuity is not
             assumed, and is not part of Theorem 1.1; boundedness is, sitting in
             Definition 3.1.\<close>"
  (*<*)
proof -
  have "v = (\<lambda>z. enn2real (iexit_val k L K z))"
    unfolding v_def
    using iexit_val_eq_xval[OF compact_imp_closed[OF cK]] L1 by simp
  then show ?thesis
    using theorem_1_1_iexit[OF kn L1 k1 cK neK expK] by simp
qed
  (*>*)

section \<open>Example 3.1\<close>

text \<open>On a ball the value function is given in closed form, for every
  \<open>1 \<le> k < n\<close>.\<close>

theorem example_3_1_closed_form:
  fixes r :: real and x :: "real^'n::finite"
  assumes k1: "1 \<le> k" and kn: "k < CARD('n)" and L1: "1 \<le> L" and r0: "0 < r"
  shows "enn2real (xval k L (cball 0 r) x)
      = max ((r * r - x \<bullet> x) / real (CARD('n) - k)) 0"
  (*<*)
proof -
  have eq: "iexit_val k L (cball 0 r) x = xval k L (cball 0 r) x"
    using L1 by (intro iexit_val_eq_xval[OF closed_cball]) simp
  show ?thesis
    unfolding eq[symmetric]
    by (rule example_3_1_iexit[OF k1 kn L1 r0])
qed
  (*>*)

(*<*)
end
(*>*)
