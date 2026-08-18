(*<*)
theory Theorem_1_1_Statement
  imports Statement_Auxiliary
begin

declare [[show_question_marks = false, names_short = true]]
(*>*)

text \<open>
  All numbering is that of \<^cite>\<open>LaiShkolnikovSoner\<close>.  \<open>'n\<close> is a finite index
  type and \<open>n = CARD('n)\<close>; \<open>real^'n\<close> and \<open>real^'n^'n\<close> are vectors and matrices
  over it; \<open>**\<close> is matrix multiplication, \<open>*v\<close> matrix-vector application,
  \<open>\<bullet>\<close> the inner product.
\<close>

section \<open>The operator of Eq. (1.9)\<close>

text \<open>Positive semidefinite: symmetric, with nonnegative quadratic form.\<close>

text \<open>@{thm [display] psd_def}\<close>

text \<open>The spectral conditions, through their Courant--Fischer
  characterisations: the \<open>m\<close>-th largest eigenvalue of \<open>a\<close> is at least \<open>1\<close>,
  respectively the largest is at most \<open>L\<close>.  So \<open>eigen_lb a (n - k)\<close> in
  \<^const>\<open>feasible\<close> is the paper's \<open>\<lambda>\<^sub>(\<^sub>n\<^sub>-\<^sub>k\<^sub>) \<ge> 1\<close>.\<close>

text \<open>@{thm [display] eigen_lb_def eigen_ub_def}\<close>

text \<open>The feasible set of Eq. (1.9) at a gradient \<open>p\<close>, adding \<open>a *v p = 0\<close>.\<close>

text \<open>@{thm [display] feasible_def}\<close>

text \<open>The operator \<open>F\<close> of Eq. (1.9), the infimum over it.\<close>

text \<open>@{thm [display] ell_op_def}\<close>

section \<open>The class of Eq. (1.7)\<close>

text \<open>The covariation constraint of Eq. (1.5).  \<open>Pi_proj a m\<close> is the infimum
  of \<open>trace (a ** P)\<close> over rank-\<open>m\<close> orthogonal projections; \<open>Pi_constraint k\<close>
  asks \<open>a\<close> to be positive semidefinite with that infimum at least \<open>m - k\<close> for
  every \<open>m\<close> with \<open>k < m \<le> n\<close>, and intersecting with the eigenvalue upper bound
  gives \<open>S\<close>.\<close>

text \<open>@{thm [display] is_proj_def Pi_proj_def Pi_constraint_def sconstraint_def}\<close>

text \<open>\<^bold>\<open>Orthogonality of \<close>\<open>P\<close>\<^bold>\<open> is required.\<close>  Eq. (1.5) writes the infimum
  over \<open>P\<^sup>2 = P\<close>, \<open>tr(P) = m\<close> without asking \<open>P\<close> to be symmetric.  Read
  literally the infimum is unbounded below, so \<open>S\<close> and every \<open>P\<^sub>x\<close> would be
  empty whenever \<open>k \<le> n - 2\<close>: in three dimensions with \<open>m = 2\<close>,
  \<open>a = u u\<^sup>T\<close> for \<open>u = (1,0,1)\<close> and \<open>P\<close> the rank-2 idempotent with range
  \<open>span{e\<^sub>1,e\<^sub>2}\<close> and kernel \<open>span{e\<^sub>3 + N e\<^sub>1}\<close> give \<open>tr(a P) = 1 - N\<close>.  The
  orthogonal reading is the one Lemma 2.1's own proof uses.\<close>

text \<open>A member of the class of Eq. (1.7): a law on \<open>C([0,\<infinity>),\<real>\<^sup>n)\<close> starting at
  \<open>x\<close> whose coordinate process is a martingale and for which \<^emph>\<open>some\<close> continuous
  adapted \<open>A\<close> compensates \<open>X X\<^sup>T\<close> with all difference quotients in \<open>S\<^sub>k\<^sup>L\<close>.  The
  existential is faithful: \<open>d\<langle>X\<rangle>/dt \<in> S\<^sub>k\<^sup>L\<close> says exactly that \<open>\<langle>X\<rangle>\<close> is such an
  \<open>A\<close>, and the compensator is unique up to indistinguishability.\<close>

text \<open>@{thm [display] ipath_def ipath_gen_def ipath_space_def outerp_def xclass_def}\<close>

text \<open>\<^bold>\<open>The covariation constraint is read as Lipschitz-with-density.\<close>
  Eq. (1.7) constrains the almost-everywhere derivative \<open>d\<langle>X\<rangle>(t)/dt\<close>; above,
  every difference quotient lies in \<open>S\<close>.  As \<open>S\<close> is compact and convex the two
  agree for absolutely continuous \<open>\<langle>X\<rangle>\<close>, and the difference-quotient form is
  what Lemma 2.3 uses.  They part only if \<open>\<langle>X\<rangle>\<close> has a singular part, which the
  derivative notation arguably permits; such a part only makes \<open>X\<close> exit sooner,
  so the value function is unaffected.\<close>

text \<open>The exit time from \<open>K\<close> before \<open>T\<close>, its increasing limit in \<open>[0,\<infinity>]\<close>, the
  essential infimum of a time under a law, and the value function of Eq. (1.6)
  as the supremum of those over the class.\<close>

text \<open>@{thm [display] etime_def pexit_def iexit_def ess_inf_def xval_def}\<close>

section \<open>Viscosity solutions in the sense of Definition 3.1\<close>

text \<open>The lower semicontinuous envelope, read within \<open>K\<close>.\<close>

text \<open>@{thm [display] lsc_envK_def}\<close>

text \<open>\<^bold>\<open>The envelope is taken within \<close>\<open>K\<close>\<^bold>\<open>.\<close>  The paper writes
  \<open>lim\<^sub>\<epsilon>\<^sub>\<down>\<^sub>0 inf\<^sub>{\<^sub>|\<^sub>y\<^sub>-\<^sub>x\<^sub>|\<^sub><\<^sub>\<epsilon>\<^sub>}\<close> without saying whether \<open>y\<close> ranges over \<open>K\<close> or \<open>\<real>\<^sup>n\<close>; only the
  former typechecks against Definition 3.1's bounded \<open>u : K \<rightarrow> \<real>\<close>.  Worth
  pinning down, as the two differ on \<open>K - interior K\<close> --- exactly where the
  boundary clause bites.\<close>

text \<open>\<open>F\<^sub>*\<close> and \<open>F\<^sup>*\<close>, the semicontinuous envelopes of \<open>F\<close> in \<open>(p,M)\<close> jointly.\<close>

text \<open>@{thm [display] ell_op_pair_def ell_op_lsc_def ell_op_usc_def}\<close>

text \<open>Definition 3.1 takes these over the symmetric \<open>\<real>\<^sup>n \<times> \<bbbS>\<^sup>n\<close> where the balls
  above range over \<open>\<real>\<^sup>n \<times> \<real>\<^sup>n\<^sup>\<times>\<^sup>n\<close>.  Not a widening: \<open>F\<close> factors through
  \<open>M \<mapsto> (M + M\<^sup>T)/2\<close>, the feasible matrices being symmetric, and that map is a
  contraction fixing \<open>\<bbbS>\<^sup>n\<close>.\<close>

text \<open>Definition 3.1's test functions, \<open>\<phi> \<in> C\<^sup>2(\<real>\<^sup>n)\<close>.\<close>

text \<open>@{thm [display] test_fun_C2_def}\<close>

text \<open>Definition 3.1 itself, touching taken globally over \<open>K\<close> and the inequality
  demanded on \<open>\<Omega>\<close>.  Taking \<open>\<Omega>\<close> to be \<open>interior K\<close> gives the interior clause;
  adjoining the boundary points where the envelope has the right sign gives it
  together with the zero boundary condition of Eq. (1.10).\<close>

text \<open>@{thm [display] visc_subsol_env2_def visc_supersol_env2_def}\<close>

text \<open>The hypothesis Theorem 4.3 and Proposition 4.1 place on \<open>K\<close>: a family of
  rotations, dilations and translations shrinking to the identity, each
  expanding \<open>K\<close> into its own interior.\<close>

text \<open>@{thm [display] expandable_def}\<close>

text \<open>Three departures from Theorem 1.1's wording.  The linear part is any
  \<^const>\<open>orthogonal_matrix\<close>, so reflections are allowed as well as rotations,
  which weakens the hypothesis and so strengthens the uniqueness clause.  The
  family is presented as \<open>\<forall>e>0. \<exists>\<dots>\<close> rather than indexed by \<open>\<iota> \<in> (1,2]\<close>, and
  closeness to the identity is measured on the inverse map over \<open>K\<close>, which is
  what the comparison argument consumes.  Every compact convex set with nonempty
  interior is expandable, so the hypothesis is not vacuous.\<close>

section \<open>Theorem 1.1\<close>

text \<open>The value function of Eq. (1.6) is a bounded upper semicontinuous
  viscosity solution of \<open>F(\<nabla>v, \<nabla>\<^sup>2v) = 1\<close> on \<open>K\<close> with the zero boundary
  condition, in the sense of Definition 3.1, and the only one.  The five
  conjuncts below carry the five clauses, (2) and (3) together occupying the
  sub- and supersolution halves; the paper's standing \<open>1 \<le> k < n\<close> and \<open>1 \<le> L\<close>
  are assumed.\<close>

text_raw \<open>\newpage\<close>

theorem theorem_1_1:
  fixes K :: "(real^'n::finite) set"
  assumes kn: "k < CARD('n)" and L1: "1 \<le> L" and k1: "1 \<le> k"
    and cK: "compact K" and neK: "K \<noteq> {}" and expK: "expandable K"
  defines "v \<equiv> (\<lambda>z. enn2real (xval k L K z))"
  shows "(\<exists>B :: real. \<forall>y. xval k L K y \<le> ennreal B)
         \<comment> \<open>clause (0): finiteness and boundedness together.  The bound is
             converted up rather than the value down: \<open>ennreal B\<close> is finite, so
             this also rules out \<open>xval y = \<top>\<close>.  Bounding \<open>v\<close> instead would not,
             \<^const>\<open>enn2real\<close> sending \<open>\<top>\<close> to \<open>0\<close>.\<close>
       \<and> (\<forall>c z. v z < c \<longrightarrow> (\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> v y < c))
         \<comment> \<open>clause (1): upper semicontinuity.\<close>
       \<and> visc_subsol_env2 k L K
           (interior K \<union> {x \<in> K - interior K. 0 < v x}) v
         \<comment> \<open>clauses (2) and (3), subsolution: the touching set is the
             interior together with the boundary points where \<open>v\<close> is positive.\<close>
       \<and> visc_supersol_env2 k L K
           (interior K \<union> {x \<in> K - interior K. lsc_envK K v x < 0})
           (lsc_envK K v)
         \<comment> \<open>clauses (2) and (3), supersolution.  Note Definition 3.1's own
             asymmetry: the subsolution property is asked of \<open>v\<close>, the
             supersolution property of its lower envelope.  \<open>L = 1\<close> is included,
             though Case 1 of Section 3 does not reach it as written --- it
             perturbs eigenvalues into the empty interval \<open>(1,L)\<close>.\<close>
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
         \<comment> \<open>clause (4): uniqueness.  The competitor is quantified inside the
             statement, so Theorem 1.1 is one formula.  Every hypothesis on it
             is about \<open>K\<close> alone.  Continuity is not assumed; boundedness is,
             sitting in Definition 3.1.\<close>"
  (*<*)
proof -
  have veq: "v = (\<lambda>z. enn2real (iexit_val k L K z))"
    unfolding v_def
    using iexit_val_eq_xval[OF compact_imp_closed[OF cK]] L1 by simp
  obtain rK :: real where KB: "K \<subseteq> cball 0 rK"
    using compact_cball_bound[OF cK] by blast
  have bnd: "\<exists>B :: real. \<forall>y. xval k L K y \<le> ennreal B"
  proof (intro exI[of _ "rK * rK / real (CARD('n) - k)"] allI)
    fix y
    have "iexit_val k L K y \<le> ennreal ((rK * rK - y \<bullet> y) / real (CARD('n) - k))"
      by (rule clause_0_finite[OF kn L1 cK KB])
    also have "\<dots> \<le> ennreal (rK * rK / real (CARD('n) - k))"
      by (intro ennreal_leI divide_right_mono) auto
    finally show "xval k L K y \<le> ennreal (rK * rK / real (CARD('n) - k))"
      using iexit_val_eq_xval[OF compact_imp_closed[OF cK]] L1 by simp
  qed
  show ?thesis
    using bnd theorem_1_1_iexit[OF kn L1 k1 cK neK expK] veq by simp
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
