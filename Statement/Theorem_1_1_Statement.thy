(*<*)
theory Theorem_1_1_Statement
  imports
    "Relative_Arbitrage.Value_Function_Uniqueness"
    "Relative_Arbitrage.Exit_Class_Infinite"
    "Relative_Arbitrage.Exit_Class_Marginals"
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

text \<open>A member of the class of Eq. (1.7) is presented as a law on the continuous
  paths of \<open>C([0,\<infinity>))\<close> taking values in pairs: the first coordinate is the process
  \<open>X\<close>, the second its covariation \<open>\<langle>X\<rangle>\<close>, carried as a genuine path coordinate
  rather than as a derived object.  The four clauses are: the law starts at \<open>x\<close>
  with zero covariation; the difference quotients of the second coordinate lie
  in the constraint set; the first coordinate is a martingale; and the
  compensated square is a martingale.  Why the covariation is carried rather
  than derived, and what that costs, is recorded below.\<close>

text \<open>@{thm [display] ipath_def iexit_class_def}\<close>

text \<open>Two readings to record here, since neither is forced by the text of
  Eq. (1.7).

  \<^item> \<^bold>\<open>The class is a set of laws of the pair \<close>\<open>(X, \<langle>X\<rangle>)\<close>\<^bold>\<open>, not of \<close>\<open>X\<close>\<^bold>\<open> alone.\<close>
  \<open>P\<^sub>x\<close> is a set of laws on \<open>C([0,\<infinity>),\<real>\<^sup>n)\<close>; here the covariation is a second path
  coordinate, which is what makes the class closed under weak limits and is the
  encoding the paper's own Lemma 2.3 proof uses.  A consequence is that the
  martingale clauses are stated for the natural filtration of the \<^emph>\<open>pair\<close>, a
  priori larger than the filtration of \<open>X\<close> that Proposition 2.4 names.  Both
  directions are now closed --- \<^theory_text>\<open>iexit_class_X_own_filtration\<close> shows \<open>X\<close> is a
  martingale for its own filtration, and the paper's class is identified with
  the \<open>X\<close>-marginals of this one in the subsection below.

  \<^item> \<^bold>\<open>The covariation constraint is read as Lipschitz-with-density.\<close>  Eq. (1.7)
  constrains \<open>d\<langle>X\<rangle>(t)/dt\<close>, an almost-everywhere derivative; the clause above asks
  every difference quotient \<open>(\<langle>X\<rangle>(t) - \<langle>X\<rangle>(s))/(t-s)\<close> to lie in \<open>S\<close>.  Since \<open>S\<close>
  is compact and convex the two agree for absolutely continuous \<open>\<langle>X\<rangle>\<close>, and the
  difference-quotient form is again what Lemma 2.3 uses (its display (2.8)).
  They part company only if \<open>\<langle>X\<rangle>\<close> is allowed a singular part, which the
  derivative notation arguably permits; such a part only makes \<open>X\<close> exit sooner,
  so the value function is unaffected, but the choice is an interpretation.\<close>

text \<open>The exit time of a path from \<open>K\<close> before a time \<open>T\<close>, its increasing limit,
  which takes values in \<open>[0,\<infinity>]\<close>, the essential infimum of such a time under a
  law, and the value function of Eq. (1.6) as the supremum of those over the
  class:\<close>

text \<open>@{thm [display] etime_def pexit_def iexit_def ess_inf_enn_def iexit_val_def}\<close>

subsection \<open>The paper's own class \<open>P\<^sub>x\<close>, of laws of \<open>X\<close> alone\<close>

text \<open>Eq. (1.6)--(1.7) with the covariation left implicit, as the paper writes
  them: a law of the \<open>\<real>\<^sup>n\<close>-valued path alone, belonging to the class when
  \<^emph>\<open>some\<close> continuous adapted \<open>A\<close> compensates \<open>X X\<^sup>T\<close> and has all its difference
  quotients in \<open>S\<^sub>k\<^sup>L\<close>.  That existential reading is a stated choice, and it is
  faithful: \<open>d\<langle>X\<rangle>/dt \<in> S\<^sub>k\<^sup>L\<close> says exactly that \<open>\<langle>X\<rangle>\<close> is such an \<open>A\<close>, and the
  compensator is unique up to indistinguishability.\<close>

text \<open>@{thm [display] xclass_def xval_def}\<close>

text \<open>The two classes correspond, in both directions, and the two value
  functions are equal.  The \<open>X\<close>-marginal of a pair law lies in \<open>P\<^sub>x\<close>; conversely a
  \<open>P\<^sub>x\<close>-law lifts along \<open>w \<mapsto> (w, \<langle>w\<rangle>)\<close>, where the covariation is recovered as a
  functional of the path alone --- an adapted, everywhere-continuous version of
  the pathwise limit of dyadic sums.\<close>

theorem paper_class_marginal:
  fixes P :: "('n::finite pairpath) measure"
  assumes "P \<in> iexit_class k L x" and "0 \<le> L"
  shows "ipath_law P (\<lambda>t \<omega>. fst (\<omega> t)) \<in> xclass k L x"
  using assms by (rule iexit_class_marginal_in_xclass)

theorem paper_class_lift:
  fixes Q :: "((real \<Rightarrow> real^'n::finite) measure)"
  assumes "Q \<in> xclass k L x" and "0 \<le> L"
  shows "ipath_law Q (\<lambda>t w. (w t, qvmata (4 * L) w t)) \<in> iexit_class k L x"
  using assms by (rule xclass_lift_in_iexit_class)

theorem paper_value_function_agrees:
  fixes K :: "(real^'n::finite) set"
  assumes "closed K" and "0 \<le> L"
  shows "iexit_val k L K x = xval k L K x"
  using assms by (rule iexit_val_eq_xval)

text \<open>So every clause of Theorem 1.1 below, though stated for
  \<^const>\<open>iexit_val\<close>, is a statement about the paper's own value function
  \<^const>\<open>xval\<close> of Eq. (1.6).\<close>

section \<open>Viscosity solutions in the sense of Definition 3.1\<close>

text \<open>A test function at \<open>x\<close> is differentiable near \<open>x\<close> with gradient \<open>g\<close>, and
  \<open>g\<close> is differentiable at \<open>x\<close> with symmetric derivative \<open>H\<close>:\<close>

text \<open>@{thm [display] test_fun_at_def}\<close>

text \<open>The lower semicontinuous envelope.  Definition 3.1 reads it within \<open>K\<close>,
  which is \<^const>\<open>lsc_envK\<close>; \<^const>\<open>lsc_env\<close> is the same liminf over balls of
  \<open>real^'n\<close>.  The two agree at interior points of \<open>K\<close> and differ in general on
  \<open>K - interior K\<close>, so it is \<^const>\<open>lsc_envK\<close> that the clauses below use:\<close>

text \<open>@{thm [display] lsc_env_def lsc_envK_def}\<close>

text \<open>\<^cite>\<open>LaiShkolnikovSoner\<close> writes the envelopes as \<open>lim\<^sub>\<epsilon>\<^sub>\<down>\<^sub>0 inf\<^sub>{\<^sub>|\<^sub>y\<^sub>-\<^sub>x\<^sub>|\<^sub><\<^sub>\<epsilon>\<^sub>}\<close> without saying
  whether \<open>y\<close> ranges over \<open>K\<close> or over \<open>\<real>\<^sup>n\<close>.  Since Definition 3.1 opens with a
  bounded \<open>u : K \<rightarrow> \<real>\<close>, only the within-\<open>K\<close> reading typechecks, and that is
  \<^const>\<open>lsc_envK\<close>.  Worth pinning down in the paper, as the two genuinely
  differ on \<open>K - interior K\<close> --- exactly where the boundary clause bites.\<close>

text \<open>Definition 3.1, with the touching taken globally over \<open>K\<close> and the
  inequality demanded at the points of \<open>\<Omega>\<close>.  Instantiating \<open>\<Omega>\<close> at
  \<open>interior K\<close> gives the interior clause; instantiating it at the union of
  \<open>interior K\<close> with the boundary points where the envelope has the right sign
  gives the clause together with the zero boundary condition of Eq. (1.10).\<close>

text \<open>@{thm [display] visc_subsol_env_def visc_supersol_env_def}\<close>

text \<open>\<open>F\<^sub>*\<close> and \<open>F\<^sup>*\<close> here are the semicontinuous envelopes of \<open>F\<close> in the pair
  \<open>(p,M)\<close> jointly, as in the paper:\<close>

text \<open>@{thm [display] ell_op_lsc_def ell_op_usc_def}\<close>

text \<open>Definition 3.1 takes those envelopes over \<open>\<real>\<^sup>n \<times> \<bbbS>\<^sup>n\<close>, the symmetric
  matrices, whereas the balls above range over all of \<open>\<real>\<^sup>n \<times> \<real>\<^sup>n\<^sup>\<times>\<^sup>n\<close>.  The two
  agree, so this is not a widening: \<open>F\<close> factors through \<open>M \<mapsto> (M + M\<^sup>T)/2\<close>,
  because the feasible matrices are positive semidefinite hence symmetric, and
  that map is a contraction fixing \<open>\<bbbS>\<^sup>n\<close>.  See \<^theory_text>\<open>ell_op_lsc_eq_over_sym\<close> and
  \<^theory_text>\<open>ell_op_usc_eq_over_sym\<close>.\<close>

text \<open>The test function above is only asked to be differentiable near \<open>x\<close> with
  a gradient that is differentiable at \<open>x\<close>; away from \<open>x\<close> it is unconstrained.
  Definition 3.1 quantifies over \<open>\<phi> \<in> C\<^sup>2(\<real>\<^sup>n)\<close>, which is a smaller class, so for
  the clauses that \<^emph>\<open>assert\<close> the sub- and supersolution property the form above is
  the stronger one.  The uniqueness clause instead \<^emph>\<open>assumes\<close> the property of a
  competitor, and there the paper's own class is what is wanted:\<close>

text \<open>@{thm [display] test_fun_C2_def}\<close>

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

theorem convex_sets_are_expandable:
  fixes K :: "(real^'n::finite) set"
  assumes "convex K" and "compact K" and "interior K \<noteq> {}"
  shows "expandable K"
  by (rule convex_expandable[OF assms(2,1,3)])

section \<open>The five clauses of Theorem 1.1\<close>

text \<open>Stated for \<^const>\<open>iexit_val\<close>, the value function of Eq. (1.6) itself,
  hence by \<^theory_text>\<open>paper_value_function_agrees\<close> for the paper's \<open>P\<^sub>x\<close> value function
  too.  Compactness of \<open>K\<close> enters as closedness together with a ball bound; the
  radius is named only in clause (0), where it appears in the conclusion.\<close>

text \<open>The standing hypotheses of \<^cite>\<open>LaiShkolnikovSoner\<close> are \<open>1 \<le> k < n\<close> and \<open>1 \<le> L\<close>.  Each clause
  below assumes only what its proof uses, so \<open>1 \<le> k\<close> appears on the
  supersolution and uniqueness clauses but not on (0), (1) and the subsolution
  halves, which hold at \<open>k = 0\<close> too.  That is a strengthening, not a gap: each
  clause still implies its counterpart under Theorem 1.1's own hypotheses.  The
  extra generality is thin --- at \<open>k = 0\<close> the set \<^const>\<open>feasible\<close> is empty at
  every nonzero gradient, so \<^const>\<open>ell_op\<close> is an infimum of the empty set ---
  but nothing is gained by hiding it.\<close>

text \<open>\<^bold>\<open>Clause (0): finiteness.\<close>  On a ball the value is bounded by the
  closed-form value of Example 3.1.  In \<open>ennreal\<close>, so that it also says the
  value is finite --- \<^const>\<open>enn2real\<close> sends \<open>\<top>\<close> to \<open>0\<close>, so a bound on
  \<open>\<bar>enn2real \<dots>\<bar>\<close> alone would hold vacuously there, and every clause below
  reads the value function through \<^const>\<open>enn2real\<close>.\<close>

theorem clause_0_finite:
  fixes K :: "(real^'n::finite) set"
  assumes "k < CARD('n)" and "1 \<le> L" and "compact K"
    and "K \<subseteq> cball 0 rK"
  shows "iexit_val k L K x
      \<le> ennreal ((rK * rK - x \<bullet> x) / real (CARD('n) - k))"
  by (rule iexit_val_le_ball_bound
        [OF assms(1,2) compact_imp_closed[OF assms(3)] assms(4)])

theorem clause_0_not_infinite:
  fixes K :: "(real^'n::finite) set"
  assumes "k < CARD('n)" and "1 \<le> L" and "compact K"
  shows "iexit_val k L K x \<noteq> \<top>"
  by (rule iexit_val_neq_top[OF assms])

text \<open>\<^bold>\<open>Clause (1): upper semicontinuity.\<close>\<close>

theorem clause_1_upper_semicontinuous:
  fixes K :: "(real^'n::finite) set"
  assumes "k < CARD('n)" and "1 \<le> L" and "compact K"
    and "enn2real (iexit_val k L K z) < c"
  shows "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> enn2real (iexit_val k L K y) < c"
  by (rule iexit_val_real_usc[OF assms])

text \<open>\<^bold>\<open>Clause (2), subsolution half.\<close>  With the operator of Eq. (1.9) itself,
  orthogonality constraint included, and with the touching taken locally, which
  is stronger than Definition 3.1(a).\<close>

theorem clause_2_subsolution:
  fixes K :: "(real^'n::finite) set"
  assumes "k < CARD('n)" and "1 \<le> L" and "compact K"
  shows "visc_subsol k L (interior K) (\<lambda>z. enn2real (iexit_val k L K z))"
  by (rule iexit_val_visc_subsol[OF assms])

text \<open>\<^bold>\<open>Clause (2), supersolution half\<close>, in the form of Definition 3.1(b), for
  the lower semicontinuous envelope.

  The standing assumption is \<open>1 \<le> L\<close>, the paper's own.  The value \<open>L = 1\<close> is
  included, and is the case of Remark 1.1(c), where the equation becomes the
  arrival time formulation of the Ambrosio--Soner co-dimension mean curvature
  flow.  Case 1 of Section 3 of \<^cite>\<open>LaiShkolnikovSoner\<close> does not reach it as written: it
  perturbs the eigenvalues of the witness into the open interval \<open>(1,L)\<close>,
  which is empty at \<open>L = 1\<close>.  What is used here instead is a covariance field
  of exact rotations, whose spectrum does not move at all, so no margin is
  needed --- see \<open>rotSF_exists\<close>.\<close>

theorem clause_2_supersolution:
  fixes K :: "(real^'n::finite) set"
  assumes "k < CARD('n)" and "1 \<le> L" and "1 \<le> k" and "compact K"
  shows "visc_supersol_env k L K (interior K)
      (lsc_envK K (\<lambda>u. enn2real (iexit_val k L K u)))"
  by (rule iexit_val_supersol_lsc_K[OF assms])

text \<open>\<^bold>\<open>Clause (3): the zero boundary condition of Eq. (1.10)\<close>, in the viscosity
  sense of Definition 3.1.  Both halves hold with the boundary gate included.

  This is not the pointwise identity \<open>v = 0\<close> on \<open>K - interior K\<close>, which is false
  in general: by Lemma 5.3 of \<^cite>\<open>LaiShkolnikovSoner\<close> a convex \<open>K\<close> has \<open>v x = 0\<close> exactly when
  the face containing \<open>x\<close> has dimension at most \<open>n - k\<close>, so the cube in three
  dimensions with \<open>k = 2\<close> has \<open>v > 0\<close> on the open two-dimensional faces of its
  boundary.  On a ball the pointwise identity does hold, and is part of
  Example 3.1 below.\<close>

theorem clause_3_boundary_subsolution:
  fixes K :: "(real^'n::finite) set"
  assumes "k < CARD('n)" and "1 \<le> L" and "compact K"
  shows "visc_subsol_env k L K
      (interior K \<union> {x \<in> K - interior K. 0 < enn2real (iexit_val k L K x)})
      (\<lambda>z. enn2real (iexit_val k L K z))"
  by (rule iexit_val_subsol_bc[OF assms])

theorem clause_3_boundary_supersolution:
  fixes K :: "(real^'n::finite) set"
  assumes "k < CARD('n)" and "1 \<le> L" and "1 \<le> k" and "compact K"
  shows "visc_supersol_env k L K
      (interior K \<union> {x \<in> K - interior K.
         lsc_envK K (\<lambda>z. enn2real (iexit_val k L K z)) x < 0})
      (lsc_envK K (\<lambda>z. enn2real (iexit_val k L K z)))"
  by (rule iexit_val_supersol_bc_K[OF assms])

text \<open>\<^bold>\<open>Clause (4): uniqueness.\<close>  Any bounded upper semicontinuous function that
  satisfies both clauses of Definition 3.1 with their boundary gates, on an
  expandable compact \<open>K\<close>, equals the value function on \<open>K\<close>.  Continuity is not
  assumed, and is not part of Theorem 1.1.  Boundedness is: it sits in
  Definition 3.1, which opens each of its clauses with \<open>a bounded function
  u : K \<rightarrow> \<real>\<close>, rather than beside the statement of Theorem 1.1.

  Every hypothesis is about \<open>K\<close> alone: semicontinuity and boundedness are
  demanded only at and between points of \<open>K\<close>, and the envelope is the paper's
  \<^const>\<open>lsc_envK\<close>.  The competitor is still typed \<open>real^'n \<Rightarrow> real\<close> --- there
  are no partial functions here --- but its values off \<open>K\<close> are unconstrained
  and unused.\<close>

theorem clause_4_uniqueness:
  fixes K :: "(real^'n::finite) set" and u :: "real^'n \<Rightarrow> real"
  assumes "k < CARD('n)" and "1 \<le> L" and "1 \<le> k"
    and "compact K" and "K \<noteq> {}" and "expandable K"
    and "\<And>c z. z \<in> K \<Longrightarrow> u z < c \<Longrightarrow>
           \<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> u y < c"
    and "\<And>y. y \<in> K \<Longrightarrow> \<bar>u y\<bar> \<le> Bd"
    and "visc_subsol_env2 k L K
           (interior K \<union> {x \<in> K - interior K. 0 < u x}) u"
    and "visc_supersol_env2 k L K
           (interior K \<union> {x \<in> K - interior K. lsc_envK K u x < 0})
           (lsc_envK K u)"
    and "x \<in> K"
  shows "u x = enn2real (iexit_val k L K x)"
  by (rule iexit_val_uniqueness_K[OF assms])

section \<open>Theorem 1.1, assembled\<close>

text \<open>The five clauses put back together into the shape of the paper's
  statement: the value function of Eq. (1.6) is a bounded upper semicontinuous
  viscosity solution of \<open>F(\<nabla>v, \<nabla>\<^sup>2v) = 1\<close> on \<open>K\<close> with the zero boundary
  condition, in the sense of Definition 3.1, and it is the only one.

  The competitor is quantified over inside the statement, so the whole of
  Theorem 1.1 is one formula.  Note the asymmetry that Definition 3.1 itself
  has: \<^const>\<open>visc_subsol_env2\<close> is asked of \<open>u\<close>, \<^const>\<open>visc_supersol_env2\<close> of
  its lower envelope \<^const>\<open>lsc_envK\<close>.\<close>

theorem theorem_1_1:
  fixes K :: "(real^'n::finite) set"
  assumes kn: "k < CARD('n)" and L1: "1 \<le> L" and k1: "1 \<le> k"
    and cK: "compact K" and neK: "K \<noteq> {}" and expK: "expandable K"
  defines "v \<equiv> (\<lambda>z. enn2real (iexit_val k L K z))"
  shows "(\<exists>B. \<forall>y. \<bar>v y\<bar> \<le> B)
       \<and> (\<forall>c z. v z < c \<longrightarrow> (\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> v y < c))
       \<and> visc_subsol_env2 k L K
           (interior K \<union> {x \<in> K - interior K. 0 < v x}) v
       \<and> visc_supersol_env2 k L K
           (interior K \<union> {x \<in> K - interior K. lsc_envK K v x < 0})
           (lsc_envK K v)
       \<and> (\<forall>u :: real^'n \<Rightarrow> real. \<forall>Bd.
            (\<forall>c z. z \<in> K \<longrightarrow> u z < c \<longrightarrow>
               (\<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> u y < c))
            \<longrightarrow> (\<forall>y\<in>K. \<bar>u y\<bar> \<le> Bd)
            \<longrightarrow> visc_subsol_env2 k L K
                 (interior K \<union> {x \<in> K - interior K. 0 < u x}) u
            \<longrightarrow> visc_supersol_env2 k L K
                 (interior K \<union> {x \<in> K - interior K. lsc_envK K u x < 0})
                 (lsc_envK K u)
            \<longrightarrow> (\<forall>x\<in>K. u x = v x))"
proof -
  have bnd: "\<exists>B. \<forall>y. \<bar>v y\<bar> \<le> B"
  proof -
    obtain rK :: real where r0: "0 \<le> rK" and KB: "K \<subseteq> cball 0 rK"
      using compact_cball_bound[OF cK] by blast
    show ?thesis
      unfolding v_def
      by (intro exI[of _ "rK * rK / real (CARD('n) - k)"] allI)
         (rule iexit_val_real_bounded[OF kn L1 cK KB r0])
  qed
  have usc: "\<forall>c z. v z < c \<longrightarrow> (\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> v y < c)"
    unfolding v_def
    by (intro allI impI clause_1_upper_semicontinuous[OF kn L1 cK])
  have sub: "visc_subsol_env2 k L K
      (interior K \<union> {x \<in> K - interior K. 0 < v x}) v"
    unfolding v_def
    by (rule visc_subsol_env_imp_env2
          [OF clause_3_boundary_subsolution[OF kn L1 cK]])
  have sup: "visc_supersol_env2 k L K
      (interior K \<union> {x \<in> K - interior K. lsc_envK K v x < 0}) (lsc_envK K v)"
    unfolding v_def
    by (rule visc_supersol_env_imp_env2
          [OF clause_3_boundary_supersolution[OF kn L1 k1 cK]])
  have uniq: "\<forall>x\<in>K. u x = v x"
    if "\<forall>c z. z \<in> K \<longrightarrow> u z < c \<longrightarrow> (\<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> u y < c)"
      and "\<forall>y\<in>K. \<bar>u y\<bar> \<le> Bd"
      and "visc_subsol_env2 k L K
             (interior K \<union> {x \<in> K - interior K. 0 < u x}) u"
      and "visc_supersol_env2 k L K
             (interior K \<union> {x \<in> K - interior K. lsc_envK K u x < 0})
             (lsc_envK K u)"
    for u :: "real^'n \<Rightarrow> real" and Bd
    unfolding v_def
    using that
    by (intro ballI clause_4_uniqueness[OF kn L1 k1 cK neK expK]) blast+
  from bnd usc sub sup uniq show ?thesis by blast
qed

section \<open>Example 3.1\<close>

text \<open>On a ball the value function is given in closed form, for every
  \<open>1 \<le> k < n\<close>.\<close>

theorem example_3_1_closed_form:
  fixes r :: real and x :: "real^'n::finite"
  assumes "1 \<le> k" and "k < CARD('n)" and "1 \<le> L" and "0 < r"
  shows "enn2real (iexit_val k L (cball 0 r) x)
      = max ((r * r - x \<bullet> x) / real (CARD('n) - k)) 0"
  by (rule example_3_1_uncapped[OF assms])

(*<*)
end
(*>*)
