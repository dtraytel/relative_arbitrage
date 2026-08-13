(*<*)
theory Theorem_1_1_Statement
  imports
    "Relative_Arbitrage.Value_Function_Uniqueness"
    "Relative_Arbitrage.Exit_Class_Infinite"
begin

declare [[show_question_marks = false, names_short = true]]
(*>*)

text \<open>
  Throughout, \<open>'n\<close> is a finite index type, \<open>n = CARD('n)\<close>, and
  \<open>real^'n\<close> and \<open>real^'n^'n\<close> are vectors and matrices over it.  \<open>**\<close> is
  matrix multiplication, \<open>*v\<close> matrix-vector application, \<open>\<bullet>\<close> the inner
  product and \<open>trace\<close> the trace.  An underscore in an identifier is
  typeset as a hyphen, so \<open>exit_val\<close> appears as \<open>exit-val\<close>.
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

text \<open>A member of the class of Eq. (1.7) is presented as a law on the space of
  continuous paths taking values in pairs: the first coordinate is the process
  \<open>X\<close>, the second its covariation \<open>\<langle>X\<rangle>\<close>, carried as a genuine path coordinate
  rather than as a derived object.  This is what makes the class closed under
  weak limits, and is the encoding the paper's own proof of Lemma 2.3 uses.
  The four clauses are: the law starts at \<open>x\<close> with zero covariation; the
  difference quotients of the second coordinate lie in the constraint set; the
  first coordinate is a martingale; and the compensated square is a
  martingale.\<close>

text \<open>@{thm [display] exit_class_def}\<close>

text \<open>The exit time of a path from \<open>K\<close>, capped at the horizon \<open>T\<close>, and the
  essential infimum of a time under a law:\<close>

text \<open>@{thm [display] etime_def pexit_def ess_inf_time_def}\<close>

text \<open>The value function of Eq. (1.6) is then the supremum, over the class, of
  the essential infimum of the exit time of the first coordinate:\<close>

text \<open>@{thm [display] exit_val_def}\<close>

subsection \<open>The same class and value function without the horizon\<close>

text \<open>The horizon \<open>T\<close> above is a device of the proofs, not of the statement.
  The paper's own class and value function are formalised separately, on the
  continuous paths of \<open>C([0,\<infinity>))\<close> --- so with the covariation constraint at
  every pair of times and with no stopping in the martingale clauses --- and
  the two value functions are then proved equal.\<close>

text \<open>@{thm [display] ipath_def iexit_class_def}\<close>

text \<open>The uncapped exit time takes values in \<open>[0,\<infinity>]\<close>, being the increasing
  limit of the capped ones, and the value function of Eq. (1.6) is again the
  supremum over the class of its essential infimum:\<close>

text \<open>@{thm [display] iexit_def ess_inf_enn_def iexit_val_def}\<close>

text \<open>The two agree.  The construction behind it glues an independent Brownian
  continuation with covariation \<open>t \<sqdot> I\<close> onto a horizon-\<open>T\<close> law at time \<open>T\<close>,
  producing a member of the uncapped class whose restriction to \<open>[0,T]\<close> is
  the law one started from; the hypothesis is that the horizon does not bind,
  which for a bounded \<open>K\<close> is the a priori bound of Eq. (3.10).\<close>

theorem uncapped_value_function_agrees:
  fixes K :: "(real^'n::finite) set" and r :: real
  assumes "k < CARD('n)" and "1 \<le> L" and "0 < T" and "closed K"
    and "K \<subseteq> cball 0 r"
    and "(r * r - x \<bullet> x) / real (CARD('n) - k) < T"
  shows "iexit_val k L K x = exit_val k L T K x"
  using assms by (rule iexit_val_eq_exit_val_bounded)

text \<open>Every clause below therefore holds verbatim for \<^const>\<open>iexit_val\<close>, the
  paper's own \<open>v\<close>, under its own hypotheses; the hypothesis \<open>Tbig\<close> that
  appears in them says exactly that the horizon does not bind.\<close>

section \<open>Viscosity solutions in the sense of Definition 3.1\<close>

text \<open>A test function at \<open>x\<close> is differentiable near \<open>x\<close> with gradient \<open>g\<close>, and
  \<open>g\<close> is differentiable at \<open>x\<close> with symmetric derivative \<open>H\<close>:\<close>

text \<open>@{thm [display] test_fun_at_def}\<close>

text \<open>The lower semicontinuous envelope:\<close>

text \<open>@{thm [display] lsc_env_def}\<close>

text \<open>Definition 3.1, with the touching taken globally over \<open>K\<close> and the
  inequality demanded at the points of \<open>\<Omega>\<close>.  Instantiating \<open>\<Omega>\<close> at
  \<open>interior K\<close> gives the interior clause; instantiating it at the union of
  \<open>interior K\<close> with the boundary points where the envelope has the right sign
  gives the clause together with the zero boundary condition of Eq. (1.10).\<close>

text \<open>@{thm [display] visc_subsol_env_def visc_supersol_env_def}\<close>

text \<open>The hypothesis Theorem 4.3 and Proposition 4.1 place on \<open>K\<close>: a family of
  rotations, dilations and translations shrinking to the identity, each of
  which expands \<open>K\<close> into its own interior.\<close>

text \<open>@{thm [display] expandable_def}\<close>

text \<open>Every compact convex set with nonempty interior satisfies it, so the
  hypothesis is not vacuous.\<close>

theorem convex_sets_are_expandable:
  fixes K :: "(real^'n::finite) set"
  assumes "convex K" and "compact K" and "interior K \<noteq> {}"
  shows "expandable K"
  by (rule convex_expandable[OF assms(2,1,3)])

section \<open>The five clauses of Theorem 1.1\<close>

text \<open>\<^bold>\<open>Clause (0): finiteness.\<close>  The value never exceeds the horizon, and on a
  ball it is bounded by the closed-form value of Example 3.1.\<close>

theorem clause_0_finite:
  fixes K :: "(real^'n::finite) set"
  assumes "0 \<le> T" and "0 \<le> L" and "K \<subseteq> cball 0 rK" and "0 \<le> rK"
    and "k < CARD('n)"
  shows "\<bar>enn2real (exit_val k L T K x)\<bar> \<le> rK * rK / real (CARD('n) - k)"
  by (rule exit_val_real_bounded[OF assms(5,1,2,3,4)])

text \<open>\<^bold>\<open>Clause (1): upper semicontinuity.\<close>\<close>

theorem clause_1_upper_semicontinuous:
  fixes K :: "(real^'n::finite) set"
  assumes "0 < T" and "1 \<le> L" and "closed K" and "k < CARD('n)"
    and "K \<subseteq> cball 0 rK"
    and "enn2real (exit_val k L T K z) < c"
  shows "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> enn2real (exit_val k L T K y) < c"
  by (rule exit_val_real_usc[OF assms])

text \<open>\<^bold>\<open>Clause (2), subsolution half.\<close>  With the operator of Eq. (1.9) itself,
  orthogonality constraint included, and with the touching taken locally, which
  is stronger than Definition 3.1(a).\<close>

theorem clause_2_subsolution:
  fixes K :: "(real^'n::finite) set"
  assumes "0 < T" and "1 \<le> L" and "closed K" and "k < CARD('n)"
  shows "visc_subsol k L (interior K) (\<lambda>z. enn2real (exit_val k L T K z))"
  by (rule exit_val_visc_subsol[OF assms])

text \<open>\<^bold>\<open>Clause (2), supersolution half\<close>, in the form of Definition 3.1(b), for
  the lower semicontinuous envelope.  The hypothesis says the horizon does not
  bind at interior points.\<close>

theorem clause_2_supersolution:
  fixes K :: "(real^'n::finite) set"
  assumes "0 < T" and "1 < L" and "1 \<le> k" and "k < CARD('n)" and "closed K"
    and "\<And>x :: real^'n. x \<in> interior K \<Longrightarrow>
           lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) x < T / 2"
  shows "visc_supersol_lsc k L K (interior K)
      (\<lambda>u. enn2real (exit_val k L T K u))"
  by (rule exit_val_supersol_lsc[OF assms])

text \<open>\<^bold>\<open>Clause (3): the zero boundary condition of Eq. (1.10)\<close>, in the viscosity
  sense of Definition 3.1.  Both halves hold with the boundary gate included.

  This is not the pointwise identity \<open>v = 0\<close> on \<open>K - interior K\<close>, which is false
  in general: by Lemma 5.3 of the paper a convex \<open>K\<close> has \<open>v x = 0\<close> exactly when
  the face containing \<open>x\<close> has dimension at most \<open>n - k\<close>, so the cube in three
  dimensions with \<open>k = 2\<close> has \<open>v > 0\<close> on the open two-dimensional faces of its
  boundary.  On a ball the pointwise identity does hold, and is part of
  Example 3.1 below.\<close>

theorem clause_3_boundary_subsolution:
  fixes K :: "(real^'n::finite) set"
  assumes "0 < T" and "1 \<le> L" and "closed K" and "k < CARD('n)"
  shows "visc_subsol_env k L K
      (interior K \<union> {x \<in> K - interior K. 0 < enn2real (exit_val k L T K x)})
      (\<lambda>z. enn2real (exit_val k L T K z))"
  by (rule exit_val_subsol_bc[OF assms])

theorem clause_3_boundary_supersolution:
  fixes K :: "(real^'n::finite) set"
  assumes "0 < T" and "1 < L" and "1 \<le> k" and "k < CARD('n)" and "closed K"
    and "K \<subseteq> cball 0 rK"
    and "2 * (rK * rK) / real (CARD('n) - k) < T"
  shows "visc_supersol_env k L K
      (interior K \<union> {x \<in> K - interior K.
         lsc_env (\<lambda>z. enn2real (exit_val k L T K z)) x < 0})
      (lsc_env (\<lambda>z. enn2real (exit_val k L T K z)))"
  by (rule exit_val_supersol_bc[OF assms])

text \<open>\<^bold>\<open>Clause (4): uniqueness.\<close>  Any bounded upper semicontinuous function that
  satisfies both clauses of Definition 3.1 with their boundary gates, on an
  expandable compact \<open>K\<close>, equals the value function on \<open>K\<close>.  Continuity is not
  assumed, and is not part of Theorem 1.1.\<close>

theorem clause_4_uniqueness:
  fixes K :: "(real^'n::finite) set" and u :: "real^'n \<Rightarrow> real"
  assumes "0 < T" and "1 < L" and "1 \<le> k" and "k < CARD('n)"
    and "compact K" and "K \<noteq> {}" and "expandable K"
    and "K \<subseteq> cball 0 rK" and "0 \<le> rK"
    and "2 * (rK * rK) / real (CARD('n) - k) < T"
    and "\<And>c z. u z < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> u y < c"
    and "\<And>y. \<bar>u y\<bar> \<le> rK * rK / real (CARD('n) - k)"
    and "visc_subsol_env k L K
           (interior K \<union> {x \<in> K - interior K. 0 < u x}) u"
    and "visc_supersol_env k L K
           (interior K \<union> {x \<in> K - interior K. lsc_env u x < 0}) (lsc_env u)"
    and "x \<in> K"
  shows "u x = enn2real (exit_val k L T K x)"
  by (rule theorem_1_1_uniqueness_faithful[OF assms])

section \<open>Example 3.1\<close>

text \<open>On a ball the value function is given in closed form, for every
  \<open>1 \<le> k < n\<close>.  The hypothesis on \<open>T\<close> says that the horizon does not bind.\<close>

theorem example_3_1_closed_form:
  fixes r :: real and x :: "real^'n::finite"
  assumes "1 \<le> k" and "k < CARD('n)" and "1 \<le> L" and "0 < T" and "0 < r"
    and "r * r / real (CARD('n) - k) \<le> T"
  shows "enn2real (exit_val k L T (cball 0 r) x)
      = max ((r * r - x \<bullet> x) / real (CARD('n) - k)) 0"
  by (rule example_3_1[OF assms])

section \<open>What is not claimed\<close>

text \<open>
  \<^item> The horizon \<open>T\<close> is part of the clauses above; the paper has none.  It is
    not a restriction --- the paper's own value function on \<open>C([0,\<infinity>))\<close> is
    formalised and proved equal to it --- but the clauses are stated for the
    capped one, and the identification carries the hypothesis that the horizon
    does not bind.
  \<^item> Continuity of the value function is not proved.  It is not needed for
    Theorem 1.1, and the paper proves it only in its Section 5 under further
    hypotheses.
  \<^item> The clause \<open>1 < L\<close> is used where the paper writes \<open>L \<ge> 1\<close>; the strict form
    is what the supersolution argument consumes.
\<close>

(*<*)
end
(*>*)
