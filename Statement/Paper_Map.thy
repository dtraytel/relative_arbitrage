section \<open>A map of the paper, item by item\<close>

(*<*)
theory Paper_Map
  imports
    "Relative_Arbitrage_Statement.Paper_Readings"
    "Relative_Arbitrage.Proposition_2_4"
    "Relative_Arbitrage.Exit_Class_Expected_Exit_Time"
begin
(*>*)

text \<open>The reader's index of the paper \<^cite>\<open>LaiShkolnikovSoner\<close>.  Every numbered definition, theorem, lemma, proposition,
  example and remark of the paper appears below, in the paper's order, and so
  does every numbered equation outside a proof ((2.1) is the set \<open>A\<close> of
  Lemma 2.1), together with two equations from proofs, (3.10) and (4.4), whose
  content is formalised in its own right.  The other numbered equations are
  steps inside proofs and are not listed.  An item that is formalised gets a
  theorem named after it
  (\<open>paper_lemma_2_2\<close>, \<open>paper_theorem_4_2_a\<close>, \<dots>) stating the formal result in
  the form closest to the paper, proved from the working lemma by \<open>rule\<close> or a
  few lines of plumbing; the text before it says what the paper states and
  exactly how the formal statement differs.  An item that is not formalised gets
  a text saying so, and what exists towards it.

  The definitions are displayed in \<open>Theorem_1_1_Statement\<close>, and the readings
  of the paper's wording are checked in \<open>Paper_Readings\<close>.  The theorems of
  this theory are the root set of every dead-code pass.

  Throughout, \<open>1 \<le> k < n\<close> and \<open>1 \<le> L\<close> are the paper's standing
  assumptions; a formal statement that needs fewer says so.\<close>


section \<open>Section 1: the problem and Theorem 1.1\<close>

subsection \<open>Definition 1.1 and Eqs. (1.1)--(1.4): the market\<close>

text \<open>Definition 1.1 (relative arbitrage), the self-financing condition (1.1) and
  the volatility conditions (1.2)--(1.4) concern the market weights \<open>\<mu>\<close> in
  \<open>\<real>\<^sup>d\<close>, \<open>d = n + 1\<close>.  They motivate the problem and are not formalised;
  nor is Remark 1.1(a), the representation \<open>T\<^sup>* = v(U\<mu>(0))\<close> by the
  fundamental theorem of asset pricing.  The formalisation starts at Eq. (1.6), in
  \<open>\<real>\<^sup>n\<close>.  The \<open>n \<times> n\<close> form of the set in Eq. (1.4) is
  \<^const>\<open>suff_volatile\<close>, displayed at Lemma 2.1.\<close>

subsection \<open>Eq. (1.5): the convexified constraint\<close>

text \<open>Eq. (1.5) is also written for the market's \<open>d \<times> d\<close> matrices; the
  formalisation uses its \<open>n \<times> n\<close> form, the first line of Eq. (1.7).  \<open>\<Pi>\<^sub>m\<close> is
  \<^const>\<open>Pi_proj\<close>, read over \<^emph>\<open>orthogonal\<close> projections of trace \<open>m\<close>; the
  literal reading over idempotents sends \<open>\<Pi>\<^sub>m(a)\<close> to \<open>-\<infinity>\<close> for every
  non-scalar \<open>a\<close> (@{thm [source] literal_reading_unbounded}).  The constraint
  set is \<^const>\<open>Pi_constraint\<close>, and \<^const>\<open>sconstraint\<close> adds the bound
  \<open>\<lambda>\<^sub>(\<^sub>1\<^sub>) \<le> L\<close>.  All are displayed in \<open>Theorem_1_1_Statement\<close>.\<close>

subsection \<open>Eqs. (1.6)--(1.8): the value function, the class \<open>\<P>\<^sub>x\<close>, the exit time\<close>

text \<open>The value function of Eq. (1.6) is \<^const>\<open>xval\<close>, the supremum over the
  class \<^const>\<open>xclass\<close> of Eq. (1.7) of the essential infimum of the exit time
  \<^const>\<open>iexit\<close> of Eq. (1.8); all are displayed, with their ingredients, in
  \<open>Theorem_1_1_Statement\<close>.  Differences: \<^const>\<open>xval\<close> takes values in
  \<open>[0,\<infinity>]\<close>, the paper's real \<open>v\<close> is \<open>enn2real \<circ> xval\<close>, and clause (0) of
  Theorem 1.1 shows that \<^const>\<open>xval\<close> is finite; \<open>d\<langle>X\<rangle>/dt\<close> is read as the
  density of an absolutely continuous compensator (\<^const>\<open>density_cond\<close>);
  \<open>\<tau>\<^sub>K\<close> is the increasing limit of the exit times capped at \<open>T\<close>
  (\<^const>\<open>pexit\<close>).\<close>

subsection \<open>Eq. (1.9): the operator \<open>F\<close>\<close>

text \<open>\<open>F\<close> is \<^const>\<open>ell_op\<close>, the infimum over \<^const>\<open>feasible\<close>
  (displayed in \<open>Theorem_1_1_Statement\<close>).  The condition
  \<open>\<lambda>\<^sub>(\<^sub>n\<^sub>-\<^sub>k\<^sub>)(a) \<ge> 1\<close> is stated in Courant--Fischer form,
  \<open>eigen_lb a (n - k)\<close>; for symmetric \<open>a\<close> that is exactly the paper's condition
  on the ordered eigenvalues (\<open>Paper_Readings\<close>, @{thm [source] eigen_lb_reading}).
  The condition \<open>\<lambda>\<^sub>(\<^sub>1\<^sub>)(a) \<le> L\<close> is stated in Rayleigh-quotient form,
  \<^const>\<open>eigen_ub\<close>; no lemma states its equivalence with \<open>eigval 1 a \<le> L\<close>.\<close>

theorem paper_eq_1_9:
  fixes a :: "real^'n::finite^'n"
  assumes "transpose a = a" and "0 < m" and "m \<le> CARD('n)"
  shows "eigen_lb a m \<longleftrightarrow> 1 \<le> eigval m a"
  by (rule eigen_lb_reading[OF assms])

subsection \<open>Theorem 1.1\<close>

text \<open>Theorem 1.1 is @{thm [source] theorem_1_1} of \<open>Theorem_1_1_Statement\<close>,
  where each clause is explained.  Differences from the paper: \<open>v\<close> is
  \<open>enn2real \<circ> xval\<close>, and clause (0) bounds \<^const>\<open>xval\<close> itself; the
  uniqueness hypothesis is \<^const>\<open>expandable\<close>, which the paper's family
  \<open>T\<^sub>\<iota>\<close> implies for compact \<open>K\<close> (@{thm [source] paper_expandable_imp_expandable});
  Definition 3.1 is read with the lower envelope within \<open>K\<close> and with \<open>F\<^sub>*\<close>,
  \<open>F\<^sup>*\<close> taken over \<open>\<real>\<^sup>n \<times> \<real>\<^sup>n\<^sup>\<times>\<^sup>n\<close>, which at symmetric matrices agree with
  the paper's (@{thm [source] ell_op_lsc_sym_eq}, @{thm [source] ell_op_usc_sym_eq});
  the subsolution clauses are applied to \<open>v\<close> and \<open>u\<close> rather than to their
  upper envelopes, which agree with them on \<open>K\<close> by upper semicontinuity;
  the competitor \<open>u\<close> of clause (4) is upper semicontinuous relative to \<open>K\<close> and
  bounded on \<open>K\<close> (boundedness is part of Definition 3.1), and none of its values
  off \<open>K\<close> is read.\<close>

theorem paper_theorem_1_1:
  fixes K :: "(real^'n::finite) set"
  assumes kn: "k < CARD('n)" and L1: "1 \<le> L" and k1: "1 \<le> k"
    and cK: "compact K"
  defines "v \<equiv> (\<lambda>z. enn2real (xval k L K z))"
  shows "(\<exists>B :: real. \<forall>y. xval k L K y \<le> ennreal B)
       \<and> (\<forall>c z. v z < c \<longrightarrow> (\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> v y < c))
       \<and> visc_subsol_env2 k L K
           (interior K \<union> {x \<in> K - interior K. 0 < v x}) v
       \<and> visc_supersol_env2 k L K
           (interior K \<union> {x \<in> K - interior K. lsc_envK K v x < 0})
           (lsc_envK K v)
       \<and> (expandable K \<longrightarrow>
          (\<forall>u :: real^'n \<Rightarrow> real. \<forall>Bd.
            (\<forall>c z. z \<in> K \<longrightarrow> u z < c \<longrightarrow>
               (\<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> u y < c))
            \<longrightarrow> (\<forall>y\<in>K. \<bar>u y\<bar> \<le> Bd)
            \<longrightarrow> visc_subsol_env2 k L K
                 (interior K \<union> {x \<in> K - interior K. 0 < u x}) u
            \<longrightarrow> visc_supersol_env2 k L K
                 (interior K \<union> {x \<in> K - interior K. lsc_envK K u x < 0})
                 (lsc_envK K u)
            \<longrightarrow> (\<forall>x\<in>K. u x = v x)))"
  unfolding v_def by (rule theorem_1_1[OF kn L1 k1 cK])

subsection \<open>Remark 1.1\<close>

text \<open>Part (a) is discussed above.  The geometric identity of part (b),
  Eq. (1.10), \<open>F(c\<^sub>1p, c\<^sub>1M + c\<^sub>2pp\<^sup>T) = c\<^sub>1F(p,M)\<close>, is not stated.  What is
  stated: \<open>F\<close> does not see positive scalings of \<open>p\<close>
  (@{thm [source] ell_op_scale}) and is positively homogeneous in \<open>M\<close> when the
  feasible set is nonempty (@{thm [source] ell_op_scaleR_matrix}), which
  together give the case \<open>c\<^sub>2 = 0\<close>; that adding \<open>c\<^sub>2pp\<^sup>T\<close> to \<open>M\<close> does not change
  \<open>F(p, \<cdot>)\<close> is not stated.  Parts (c) and (d) are a comment and an open
  problem.\<close>


section \<open>Section 2: properties of the value function\<close>

subsection \<open>Lemma 2.1\<close>

text \<open>For \<open>1 \<le> k \<le> n - 1\<close>, the convex hull of
  \<open>{a \<in> \<bbbS>\<^sup>n\<^sub>+ : \<lambda>\<^sub>(\<^sub>n\<^sub>-\<^sub>k\<^sub>)(a) \<ge> 1}\<close> is the set \<open>A\<close> of those \<open>a \<in> \<bbbS>\<^sup>n\<^sub>+\<close> with
  \<open>\<Pi>\<^sub>m(a) \<ge> m - k\<close> for \<open>m = k+1, \<dots>, n\<close> (Eq. (2.1)).  The first set is the following
  (\<open>eigen_lb\<close> being \<open>\<lambda>\<^sub>(\<^sub>n\<^sub>-\<^sub>k\<^sub>) \<ge> 1\<close> by @{thm [source] paper_eq_1_9}), and \<open>A\<close> is
  \<^const>\<open>Pi_constraint\<close>, with \<open>\<Pi>\<^sub>m\<close> read over orthogonal projections.  The formal
  statement also allows \<open>k = 0\<close>.  It is \<open>Paper_Readings\<close>' @{thm [source] lemma_2_1}.\<close>

text \<open>@{thm [display] suff_volatile_def}\<close>

theorem paper_lemma_2_1:
  assumes "k < CARD('n::finite)"
  shows "convex hull (suff_volatile k) = (Pi_constraint k :: (real^'n^'n) set)"
  by (rule lemma_2_1[OF assms])

subsection \<open>Lemma 2.2\<close>

text \<open>If \<open>S \<subseteq> \<bbbS>\<^sup>n\<^sub>+\<close> is bounded, the continuous martingale laws with
  \<open>X(0) = x\<close> and \<open>d\<langle>X\<rangle>/dt \<in> S\<close> form a relatively compact set for weak
  convergence; in particular every \<open>\<P>\<^sub>x\<close> is relatively compact.

  The formal statement differs in three ways.  It is proved only for
  \<open>S = sconstraint k L\<close> (for any \<open>k\<close> and any \<open>L \<ge> 0\<close>), not for an arbitrary
  bounded \<open>S\<close>.  It is about \<^const>\<open>exit_class\<close>, not \<open>\<P>\<^sub>x\<close>: laws of the
  pair \<open>(X, A)\<close> on the continuous paths over \<open>[0,T]\<close>, \<open>A\<close> the compensator
  of \<open>XX\<^sup>T\<close>, starting at \<open>0\<close> with difference quotients in \<open>S\<close>, \<open>X\<close> and
  \<open>XX\<^sup>T - A\<close> martingales up to \<open>T\<close> for the filtration of the pair.  And the
  topology is weak convergence on that path space, with the uniform metric
  \<^const>\<open>path_metric\<close>.  The proof is the paper's: a uniform fourth moment of
  the increments (@{thm [source] exit_class_fourth_moment}, coordinatewise, with
  the constant \<open>8L\<^sup>2\<close>), tightness
  (@{thm [source] tight_on_set_paper_pair_class}), and Prokhorov's theorem
  (@{thm [source] tight_imp_relatively_compact}).\<close>

text \<open>@{thm [display] exit_class_def}\<close>

theorem paper_lemma_2_2:
  fixes x :: "real^'n::finite"
  assumes T: "0 < T" and L: "0 \<le> L"
  shows "compactin (weak_conv_topology (mtopology_of (path_metric T :: ('n pairpath) metric)))
      (weak_conv_topology (mtopology_of (path_metric T :: ('n pairpath) metric))
         closure_of exit_class k L T x)"
proof -
  let ?X = "mtopology_of (path_metric T :: ('n pairpath) metric)"
  have met: "metrizable_space ?X"
    unfolding mtopology_of_def
    by (rule Metric_space.metrizable_space_mtopology[OF Metric_space_mspace_mdist])
  have sep: "separable_space ?X" by (rule separable_path_metric)
  have bound: "exit_class k L T x
      \<subseteq> {N. N (space N) \<le> ennreal 1 \<and> sets N = sets (borel_of ?X)}"
  proof
    fix N :: "('n pairpath) measure"
    assume N: "N \<in> exit_class k L T x"
    have "prob_space N" by (rule exit_class_prob[OF N])
    then have "N (space N) \<le> ennreal 1" by (simp add: prob_space.emeasure_space_1)
    moreover have "sets N = sets (borel_of ?X)" by (rule exit_class_sets[OF N])
    ultimately show "N \<in> {N. N (space N) \<le> ennreal 1 \<and> sets N = sets (borel_of ?X)}"
      by simp
  qed
  have tight: "tight_on_set ?X (exit_class k L T x)"
    by (rule tight_on_set_paper_pair_class[OF T L]) simp
  show ?thesis by (rule tight_imp_relatively_compact[OF met sep bound tight])
qed

subsection \<open>Lemma 2.3\<close>

text \<open>If \<open>S\<close> is compact and convex, that set of laws is compact; in
  particular every \<open>\<P>\<^sub>x\<close> is compact.  The formal statement has the three
  differences of Lemma 2.2 (\<open>sconstraint k L\<close> is compact and convex:
  @{thm [source] sconstraint_convex}, @{thm [source] closed_sconstraint},
  @{thm [source] bounded_sconstraint}).  Closedness under weak limits is
  @{thm [source] exit_class_weak_closed}.  Compactness of \<open>\<P>\<^sub>x\<close> itself, on
  \<open>C([0,\<infinity>), \<real>\<^sup>n)\<close>, is not stated.\<close>

theorem paper_lemma_2_3:
  fixes x :: "real^'n::finite"
  assumes "0 < T" and "0 \<le> L"
  shows "compactin (weak_conv_topology (mtopology_of (path_metric T :: ('n pairpath) metric)))
      (exit_class k L T x)"
  by (rule exit_class_compactin_weak[OF assms])

subsection \<open>Proposition 2.4 and Eq. (2.9)\<close>

text \<open>For compact \<open>K\<close>, \<open>v\<close> is upper semicontinuous on \<open>\<real>\<^sup>n\<close>; for every
  \<open>x \<in> \<real>\<^sup>n\<close> and every stopping time \<open>\<theta>\<close> of the filtration of \<open>X\<close>, the dynamic
  programming principle Eq. (2.9) holds; and every optimiser of Eq. (1.6) attains
  the supremum in (2.9).

  Upper semicontinuity is proved for \<open>v\<close> itself (@{thm [source] xval_usc}).
  The rest is proved for the horizon-\<open>T\<close> value \<^const>\<open>exit_val\<close> over
  \<^const>\<open>exit_class\<close> (displayed at Lemma 2.2), not for \<open>v\<close>: \<open>\<theta>\<close> is a measurable
  function of the pair path with values in \<open>[0,T]\<close> that is a stopping time in
  Galmarino's form (\<^const>\<open>path_stopping_time\<close>), for the filtration of the
  pair \<open>(X, A)\<close> rather than that of \<open>X\<close>; \<open>\<theta> \<and> \<tau>\<^sub>K\<close> is the capped
  exit time \<open>pexit \<theta>\<close>; the indicator of \<open>{\<theta> \<le> \<tau>\<^sub>K}\<close> is replaced by that of
  \<open>pexit \<theta> = \<theta> \<and> X(\<theta>) \<in> K\<close>, which differs from it only where
  \<open>X(\<theta>) \<notin> K\<close>, where the value vanishes; and \<open>v(X(\<theta>))\<close> is the value
  \<open>exit_val (T - \<theta>)\<close> of the remaining horizon (@{thm [source] exit_val_dpp_time},
  @{thm [source] exit_val_dpp_time_optimizer}).  The formal statement does not
  need \<open>1 \<le> k\<close>.  The transfer to \<open>v\<close> is not done.  The identification of \<open>v\<close>
  with \<^const>\<open>exit_val\<close> at large horizons exists
  (@{thm [source] iexit_val_eq_exit_val_ball}, @{thm [source] xval_eq_iexit_val});
  the transport of essential infima between the class of Eq. (1.7) and
  \<^const>\<open>exit_class\<close>, Galmarino's test for the coordinate filtration on
  \<open>[0,\<infinity>)\<close>, and a limit argument for unbounded \<open>\<theta>\<close> do not.
  Remark 2.1 is a comment.\<close>

text \<open>@{thm [display] exit_val_def ess_inf_time_def path_stopping_time_def}\<close>

theorem paper_proposition_2_4:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and \<theta> :: "'n pairpath \<Rightarrow> real"
  assumes kn: "k < CARD('n)" and L1: "1 \<le> L" and cK: "compact K"
    and T0: "0 < T" and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
  defines "v \<equiv> (\<lambda>z. enn2real (xval k L K z))"
    and "G \<equiv> (\<lambda>\<omega>. pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
            + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
               then enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0))"
  shows "\<forall>c z. v z < c \<longrightarrow> (\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> v y < c)"
    and "exit_val k L T K x = (SUP P \<in> exit_class k L T x. ess_inf_time P G)"
    and "\<And>P. P \<in> exit_class k L T x \<Longrightarrow>
           ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))) = exit_val k L T K x \<Longrightarrow>
           ess_inf_time P G = exit_val k L T K x"
proof -
  have Kc: "closed K" by (rule compact_imp_closed[OF cK])
  show "\<forall>c z. v z < c \<longrightarrow> (\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> v y < c)"
    unfolding v_def using xval_usc[OF kn L1 cK] by blast
  show "exit_val k L T K x = (SUP P \<in> exit_class k L T x. ess_inf_time P G)"
    unfolding G_def by (rule exit_val_dpp_time[OF T0 L1 Kc st thM])
  show "ess_inf_time P G = exit_val k L T K x"
    if "P \<in> exit_class k L T x"
      and "ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))) = exit_val k L T K x"
    for P
    unfolding G_def by (rule exit_val_dpp_time_optimizer[OF T0 L1 Kc st thM that])
qed


section \<open>Section 3: the viscosity solution property\<close>

subsection \<open>Definition 3.1 and Eqs. (3.1)--(3.3)\<close>

text \<open>Eq. (3.1) repeats Eq. (1.9).  Definition 3.1 is displayed in
  \<open>Theorem_1_1_Statement\<close> as \<^const>\<open>visc_subsol_env2\<close> and
  \<^const>\<open>visc_supersol_env2\<close>, whose argument \<open>\<Omega>\<close> is the set of points where
  the inequality (3.2), resp. (3.3), is demanded.  Part (a) for \<open>u\<close> is
  \<open>visc_subsol_env2 k L K (interior K) u\<close>, and adjoining
  \<open>{x \<in> K - interior K. 0 < u x}\<close> to \<open>\<Omega>\<close> adds the zero boundary condition;
  part (b) is \<^const>\<open>visc_supersol_env2\<close> applied to the lower envelope
  \<open>lsc_envK K u\<close>, with \<open>lsc_envK K u x < 0\<close> in the boundary part of \<open>\<Omega>\<close>;
  part (c) is both.  The test functions \<open>\<phi> \<in> C\<^sup>2(\<real>\<^sup>n)\<close> are
  \<^const>\<open>test_fun_C2\<close>, and \<open>F\<^sub>*\<close>, \<open>F\<^sup>*\<close> are \<^const>\<open>ell_op_lsc\<close>,
  \<^const>\<open>ell_op_usc\<close>.  Differences: the lower envelope \<open>u\<^sub>*\<close> is taken within
  \<open>K\<close> (\<^const>\<open>lsc_envK\<close>; \<open>Paper_Readings\<close> shows this is the reading that uses
  only the data on \<open>K\<close>); \<open>F\<^sub>*\<close> and \<open>F\<^sup>*\<close> are taken over \<open>\<real>\<^sup>n \<times> \<real>\<^sup>n\<^sup>\<times>\<^sup>n\<close>,
  and at the symmetric Hessians where Definition 3.1 evaluates them they agree with
  the envelopes over \<open>\<real>\<^sup>n \<times> \<bbbS>\<^sup>n\<close> (@{thm [source] ell_op_lsc_sym_eq},
  @{thm [source] ell_op_usc_sym_eq}); the subsolution clause is applied to \<open>u\<close>, not
  to \<open>u\<^sup>*\<close>, which agree on \<open>K\<close> when \<open>u\<close> is upper semicontinuous relative to \<open>K\<close>,
  as every result below assumes; the boundedness that the paper builds into the
  definition is a separate hypothesis where it is needed; \<open>\<partial>K\<close> is
  \<open>K - interior K\<close>.\<close>

subsection \<open>Eqs. (3.4) and (3.5)\<close>

text \<open>Eq. (3.4) defines \<open>M\<^sub>p\<close> (@{thm [source] Mp_def}, displayed in
  \<open>Paper_Readings\<close>).  Eq. (3.5), the closed form of \<open>F\<close> in the ordered
  eigenvalues of \<open>M\<^sub>p\<close>, is proved for \<open>p \<noteq> 0\<close> only; at \<open>p = 0\<close>, where
  \<open>M\<^sub>p = M\<close>, it is not stated.  The paper's sums with indicators of
  \<open>\<lambda>\<^sub>i > 0\<close> and \<open>\<lambda>\<^sub>i \<le> 0\<close> are regrouped as \<open>L max(\<lambda>\<^sub>i, 0)\<close> over all
  \<open>i\<close> plus \<open>min(\<lambda>\<^sub>i, 0)\<close> over \<open>i \<le> n - k\<close>.  It is \<open>Paper_Readings\<close>'
  @{thm [source] eq_3_5}.\<close>

theorem paper_eq_3_5:
  fixes M :: "real^'n::finite^'n"
  assumes "transpose M = M" and "p \<noteq> 0" and "1 \<le> L"
    and "1 \<le> k" "k < CARD('n)"
  shows "ell_op k L p M
      = - (1/2) * (L * (\<Sum>i\<in>{1..CARD('n)}. max (eigval i (Mp p M)) 0)
                   + (\<Sum>i\<in>{1..CARD('n) - k}. min (eigval i (Mp p M)) 0))"
  by (rule eq_3_5[OF assms])

subsection \<open>Lemma 3.1 and Eq. (3.6)\<close>

text \<open>\<open>F\<^sub>* = F\<^sup>* = F\<close> on \<open>(\<real>\<^sup>n \<setminus> {0}) \<times> \<bbbS>\<^sup>n\<close>, \<open>F\<^sub>* = F\<close> on
  \<open>{0} \<times> \<bbbS>\<^sup>n\<close>, and \<open>F\<^sup>*(0,M)\<close> is given by Eq. (3.6), whose right-hand side,
  regrouped as for (3.5), is \<^const>\<open>eq36_rhs\<close> (displayed in \<open>Paper_Readings\<close>).
  The envelopes are \<open>ereal\<close>-valued and taken over \<open>\<real>\<^sup>n \<times> \<real>\<^sup>n\<^sup>\<times>\<^sup>n\<close>; at
  symmetric \<open>M\<close>, the only arguments stated here, they agree with those over
  \<open>\<real>\<^sup>n \<times> \<bbbS>\<^sup>n\<close> (@{thm [source] ell_op_lsc_sym_eq}, @{thm [source] ell_op_usc_sym_eq}).
  It is \<open>Paper_Readings\<close>' @{thm [source] lemma_3_1}.\<close>

theorem paper_lemma_3_1:
  fixes M :: "real^'n::finite^'n" and p :: "real^'n"
  assumes sym: "transpose M = M" and L: "1 \<le> L" and k: "1 \<le> k" "k < CARD('n)"
  shows "p \<noteq> 0 \<Longrightarrow> ell_op_lsc k L p M = ereal (ell_op k L p M)
                 \<and> ell_op_usc k L p M = ereal (ell_op k L p M)"
    and "ell_op_lsc k L (0 :: real^'n) M = ereal (ell_op k L 0 M)"
    and "ell_op_usc k L (0 :: real^'n) M = ereal (eq36_rhs k L M)"
  using lemma_3_1[OF sym L k] by blast+

subsection \<open>Example 3.1 and Eqs. (3.9), (3.10)\<close>

text \<open>On the closed ball of radius \<open>r > 0\<close>,
  \<open>v(x) = max(r\<^sup>2 - |x|\<^sup>2, 0)/(n - k)\<close> for every \<open>x \<in> \<real>\<^sup>n\<close> (Eq. (3.9)).
  Formally this is @{thm [source] example_3_1_closed_form} of
  \<open>Theorem_1_1_Statement\<close>, for \<open>v = enn2real \<circ> xval\<close>, with the same quantity
  written as \<open>max ((r\<^sup>2 - |x|\<^sup>2)/(n - k)) 0\<close>.\<close>

theorem paper_example_3_1:
  fixes r :: real and x :: "real^'n::finite"
  assumes "1 \<le> k" and "k < CARD('n)" and "1 \<le> L" and "0 < r"
  shows "enn2real (xval k L (cball 0 r) x)
      = max ((r * r - x \<bullet> x) / real (CARD('n) - k)) 0"
  by (rule example_3_1_closed_form[OF assms])

text \<open>Eq. (3.10), in the proof of Example 3.1, bounds \<open>P-ess inf \<tau>\<^sub>K\<close> by
  \<open>lim\<^sub>t E[\<tau>\<^sub>K \<and> t] \<le> (r\<^sup>2 - |x|\<^sup>2)/(n - k)\<close> for \<open>x\<close> in the ball and
  \<open>P \<in> \<P>\<^sub>x\<close>.  Formally: the bound on the expectation \<open>E[\<tau>\<^sub>K]\<close>, for every
  member of \<^const>\<open>xclass\<close>, every closed \<open>K\<close> inside the ball and every \<open>x\<close>, with
  \<open>0 \<le> L\<close> in place of \<open>1 \<le> L\<close> and without \<open>1 \<le> k\<close>.  The first inequality of
  (3.10), essential infimum below expectation, is not restated.\<close>

theorem paper_eq_3_10:
  fixes Q :: "(real \<Rightarrow> real^'n::finite) measure" and K :: "(real^'n) set"
  assumes "Q \<in> xclass k L x" and "k < CARD('n)" and "0 \<le> L"
    and "closed K" and "K \<subseteq> cball 0 r"
  shows "(\<integral>\<^sup>+w. iexit K w \<partial>Q) \<le> ennreal ((r * r - x \<bullet> x) / real (CARD('n) - k))"
  by (rule xclass_expected_exit_time[OF assms])

subsection \<open>Section 3.1: the subsolution property\<close>

text \<open>\<open>v\<close> satisfies Definition 3.1(a) with the zero boundary condition.
  Formally @{thm [source] xval_subsolution}, for every compact \<open>K\<close>, stated for
  \<open>v\<close> itself (\<open>v = v\<^sup>*\<close> by Proposition 2.4); \<open>1 \<le> k\<close> is not needed.\<close>

theorem paper_section_3_1_subsolution:
  fixes K :: "(real^'n::finite) set"
  assumes kn: "k < CARD('n)" and L1: "1 \<le> L" and cK: "compact K"
  defines "v \<equiv> (\<lambda>z. enn2real (xval k L K z))"
  shows "visc_subsol_env2 k L K (interior K \<union> {x \<in> K - interior K. 0 < v x}) v"
  unfolding v_def by (rule xval_subsolution[OF kn L1 cK])

subsection \<open>Section 3.2: the supersolution property\<close>

text \<open>\<open>v\<close> satisfies Definition 3.1(b) with the zero boundary condition, i.e.
  \<open>v\<^sub>* = lsc_envK K v\<close> is a supersolution.  Formally
  @{thm [source] xval_supersolution}, for every compact \<open>K\<close>.  As the paper
  notes, the boundary part of \<open>\<Omega>\<close> is empty since \<open>v \<ge> 0\<close>
  (@{thm [source] boundary_set_empty_K}).  \<open>L = 1\<close> is included, although the
  paper's Case 1 perturbs the eigenvalues of \<open>a\<close> into \<open>(1,L)\<close>, which is empty
  when \<open>L = 1\<close>.\<close>

theorem paper_section_3_2_supersolution:
  fixes K :: "(real^'n::finite) set"
  assumes kn: "k < CARD('n)" and L1: "1 \<le> L" and k1: "1 \<le> k" and cK: "compact K"
  defines "v \<equiv> (\<lambda>z. enn2real (xval k L K z))"
  shows "visc_supersol_env2 k L K
      (interior K \<union> {x \<in> K - interior K. lsc_envK K v x < 0}) (lsc_envK K v)"
  unfolding v_def by (rule xval_supersolution[OF kn L1 k1 cK])


section \<open>Section 4: uniqueness\<close>

text \<open>The working lemmas of Proposition 4.1, Theorem 4.2(b) and Theorem 4.3 take
  functions that are semicontinuous and bounded on all of \<open>\<real>\<^sup>n\<close>.  The
  restatements below take, as the paper does, data on \<open>K\<close> (or \<open>K'\<close>) only, and
  reduce to the working lemmas by extending upper semicontinuous data from \<open>K\<close>
  with \<^const>\<open>Kext\<close>, and lower semicontinuous data \<open>w\<close> as \<open>- Kext K (- w)\<close>;
  either extension changes nothing on \<open>K\<close> and keeps the bound.  Where \<open>w\<close> is
  lower semicontinuous relative to \<open>K\<close> (to \<open>K'\<close> in Theorem 4.2(b)), the
  supersolution clause of Definition 3.1 is applied to \<open>w\<close> itself rather than
  to \<open>w\<^sub>*\<close>; the two agree there.\<close>

(*<*)
lemma paper_map_Kext:
  fixes K :: "(real^'n::finite) set" and u :: "real^'n \<Rightarrow> real"
  assumes Kc: "closed K" and neK: "K \<noteq> {}"
    and usc: "\<And>c z. z \<in> K \<Longrightarrow> u z < c \<Longrightarrow> \<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> u y < c"
    and bnd: "\<And>y. y \<in> K \<Longrightarrow> \<bar>u y\<bar> \<le> B"
  shows "\<And>y. y \<in> K \<Longrightarrow> Kext K u y = u y"
    and "\<And>c z. Kext K u z < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> Kext K u y < c"
    and "\<And>y. \<bar>Kext K u y\<bar> \<le> B"
    and "\<And>y. y \<in> K \<Longrightarrow> lsc_env (Kext K u) y = lsc_envK K u y"
proof -
  have Bu: "u y \<le> B" if "y \<in> K" for y using bnd[OF that] by (simp add: abs_le_iff)
  show "Kext K u y = u y" if "y \<in> K" for y
    by (rule Kext_eq_on_K[OF Kc neK Bu usc that])
  show "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> Kext K u y < c" if "Kext K u z < c" for c z
    by (rule Kext_usc[OF Kc neK Bu that])
  show "\<bar>Kext K u y\<bar> \<le> B" for y
    by (rule Kext_bounded[OF Kc neK bnd])
  show "lsc_env (Kext K u) y = lsc_envK K u y" if "y \<in> K" for y
    by (rule lsc_env_Kext[OF Kc neK bnd usc that])
qed
(*>*)

subsection \<open>Proposition 4.1\<close>

text \<open>Under the \<open>T\<^sub>\<iota>\<close> hypothesis, the upper semicontinuous viscosity
  solution of \<open>F = 1\<close> on \<open>K\<close> with the zero boundary condition is unique.
  Formally: for \<^const>\<open>expandable\<close> \<open>K\<close> (implied by the paper's hypothesis,
  @{thm [source] paper_expandable_imp_expandable}), two functions that are upper
  semicontinuous relative to \<open>K\<close>, bounded on \<open>K\<close>, and satisfy Definition 3.1
  with the zero boundary condition agree on \<open>K\<close>.  A common bound \<open>B\<close> is no
  loss.  Working lemma: @{thm [source] uniqueness_expandable}, for data on
  \<open>\<real>\<^sup>n\<close> and with the lower envelope \<^const>\<open>lsc_env\<close> over \<open>\<real>\<^sup>n\<close>.\<close>

theorem paper_proposition_4_1:
  fixes K :: "(real^'n::finite) set" and u w :: "real^'n \<Rightarrow> real"
  assumes kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and cK: "compact K" and expK: "expandable K"
    and uscu: "\<And>c z. z \<in> K \<Longrightarrow> u z < c \<Longrightarrow> \<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> u y < c"
    and Bu: "\<And>y. y \<in> K \<Longrightarrow> \<bar>u y\<bar> \<le> B"
    and subu: "visc_subsol_env2 k L K (interior K \<union> {x \<in> K - interior K. 0 < u x}) u"
    and supu: "visc_supersol_env2 k L K
      (interior K \<union> {x \<in> K - interior K. lsc_envK K u x < 0}) (lsc_envK K u)"
    and uscw: "\<And>c z. z \<in> K \<Longrightarrow> w z < c \<Longrightarrow> \<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> w y < c"
    and Bw: "\<And>y. y \<in> K \<Longrightarrow> \<bar>w y\<bar> \<le> B"
    and subw: "visc_subsol_env2 k L K (interior K \<union> {x \<in> K - interior K. 0 < w x}) w"
    and supw: "visc_supersol_env2 k L K
      (interior K \<union> {x \<in> K - interior K. lsc_envK K w x < 0}) (lsc_envK K w)"
    and x: "x \<in> K"
  shows "u x = w x"
proof -
  have Kc: "closed K" by (rule compact_imp_closed[OF cK])
  have neK: "K \<noteq> {}" using x by blast
  have iK: "interior K \<subseteq> K" by (rule interior_subset)
  \<comment> \<open>\<open>u\<close>, extended from \<open>K\<close>\<close>
  have eu1: "Kext K u y = u y" if "y \<in> K" for y
    by (rule paper_map_Kext(1)[OF Kc neK uscu Bu that])
  have eu2: "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> Kext K u y < c" if "Kext K u z < c" for c z
    by (rule paper_map_Kext(2)[OF Kc neK uscu Bu that])
  have eu3: "\<bar>Kext K u y\<bar> \<le> B" for y
    by (rule paper_map_Kext(3)[OF Kc neK uscu Bu])
  have eu4: "lsc_env (Kext K u) y = lsc_envK K u y" if "y \<in> K" for y
    by (rule paper_map_Kext(4)[OF Kc neK uscu Bu that])
  have gu1: "{z \<in> K - interior K. 0 < Kext K u z} = {z \<in> K - interior K. 0 < u z}"
    using eu1 by auto
  have gu2: "{z \<in> K - interior K. lsc_env (Kext K u) z < 0}
      = {z \<in> K - interior K. lsc_envK K u z < 0}"
    using eu4 by auto
  have subu': "visc_subsol_env2 k L K
      (interior K \<union> {z \<in> K - interior K. 0 < Kext K u z}) (Kext K u)"
    unfolding gu1 by (rule visc_subsol_env2_cong[OF _ _ subu]) (use eu1 iK in auto)
  have supu': "visc_supersol_env2 k L K
      (interior K \<union> {z \<in> K - interior K. lsc_env (Kext K u) z < 0}) (lsc_env (Kext K u))"
    unfolding gu2 by (rule visc_supersol_env2_cong[OF _ _ supu]) (use eu4 iK in auto)
  \<comment> \<open>\<open>w\<close>, likewise\<close>
  have ew1: "Kext K w y = w y" if "y \<in> K" for y
    by (rule paper_map_Kext(1)[OF Kc neK uscw Bw that])
  have ew2: "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> Kext K w y < c" if "Kext K w z < c" for c z
    by (rule paper_map_Kext(2)[OF Kc neK uscw Bw that])
  have ew3: "\<bar>Kext K w y\<bar> \<le> B" for y
    by (rule paper_map_Kext(3)[OF Kc neK uscw Bw])
  have ew4: "lsc_env (Kext K w) y = lsc_envK K w y" if "y \<in> K" for y
    by (rule paper_map_Kext(4)[OF Kc neK uscw Bw that])
  have gw1: "{z \<in> K - interior K. 0 < Kext K w z} = {z \<in> K - interior K. 0 < w z}"
    using ew1 by auto
  have gw2: "{z \<in> K - interior K. lsc_env (Kext K w) z < 0}
      = {z \<in> K - interior K. lsc_envK K w z < 0}"
    using ew4 by auto
  have subw': "visc_subsol_env2 k L K
      (interior K \<union> {z \<in> K - interior K. 0 < Kext K w z}) (Kext K w)"
    unfolding gw1 by (rule visc_subsol_env2_cong[OF _ _ subw]) (use ew1 iK in auto)
  have supw': "visc_supersol_env2 k L K
      (interior K \<union> {z \<in> K - interior K. lsc_env (Kext K w) z < 0}) (lsc_env (Kext K w))"
    unfolding gw2 by (rule visc_supersol_env2_cong[OF _ _ supw]) (use ew4 iK in auto)
  have "Kext K u x = Kext K w x"
    by (rule uniqueness_expandable[OF kk LL cK neK expK eu2 ew2 eu3 ew3
          subu' supu' subw' supw' x])
  then show ?thesis using eu1[OF x] ew1[OF x] by simp
qed

subsection \<open>Remark 4.1\<close>

text \<open>Besides comments, Remark 4.1 says that the \<open>T\<^sub>\<iota>\<close> hypothesis holds for
  every compact convex \<open>K\<close> with nonempty interior.  This is proved for the formal
  hypothesis \<^const>\<open>expandable\<close> (\<open>Paper_Readings\<close>'
  @{thm [source] convex_sets_are_expandable}); that such \<open>K\<close> satisfy the
  paper's own hypothesis, \<^const>\<open>paper_expandable\<close>, is not stated.\<close>

theorem paper_remark_4_1:
  fixes K :: "(real^'n::finite) set"
  assumes "compact K" and "convex K" and "interior K \<noteq> {}"
  shows "expandable K"
  by (rule convex_sets_are_expandable[OF assms])

subsection \<open>Theorem 4.2(a)\<close>

text \<open>If \<open>u\<close> is an upper semicontinuous subsolution and \<open>w\<close> a lower
  semicontinuous supersolution (Definition 3.1, in the interior of \<open>K\<close>), then
  \<open>u - w\<close> attains its maximum over \<open>K\<close> at a point of \<open>\<partial>K\<close>.  Formally
  @{thm [source] max_principle_usc_lsc}, with semicontinuity relative to \<open>K\<close>, the
  boundedness of Definition 3.1 as an explicit common bound \<open>|u|, |w| \<le> B\<close> on
  \<open>K\<close> (the paper's proof uses \<open>\<parallel>u\<parallel>\<^sub>\<infinity>\<close>, \<open>\<parallel>w\<parallel>\<^sub>\<infinity>\<close>), and \<open>K \<noteq> {}\<close>, without which
  there is no boundary point.\<close>

theorem paper_theorem_4_2_a:
  fixes K :: "(real^'n::finite) set" and u w :: "real^'n \<Rightarrow> real"
  assumes "1 \<le> k" "k < CARD('n)" and "1 \<le> L"
    and "compact K" and "K \<noteq> {}"
    and "\<And>c z. z \<in> K \<Longrightarrow> u z < c \<Longrightarrow> \<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> u y < c"
    and "\<And>c z. z \<in> K \<Longrightarrow> c < w z \<Longrightarrow> \<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> c < w y"
    and "\<And>y. y \<in> K \<Longrightarrow> \<bar>u y\<bar> \<le> B" and "\<And>y. y \<in> K \<Longrightarrow> \<bar>w y\<bar> \<le> B"
    and "visc_subsol_env2 k L K (interior K) u"
    and "visc_supersol_env2 k L K (interior K) w"
  shows "\<exists>x \<in> K - interior K. \<forall>y\<in>K. u y - w y \<le> u x - w x"
  by (rule max_principle_usc_lsc[OF assms])

subsection \<open>Theorem 4.2(b)\<close>

text \<open>If moreover \<open>u\<close> satisfies the zero boundary condition, and \<open>w\<close> is a lower
  semicontinuous supersolution with the zero boundary condition on a compact \<open>K'\<close>
  with \<open>K \<subseteq> interior K'\<close>, then \<open>u \<le> w\<close> on \<open>K\<close>.  Formally with data on \<open>K\<close>
  for \<open>u\<close> and on \<open>K'\<close> for \<open>w\<close>, bounded there by a common \<open>B\<close>.  The working
  lemma @{thm [source] comparison_two_domain} takes data on \<open>\<real>\<^sup>n\<close> and assumes
  \<open>w \<ge> 0\<close> on \<open>K'\<close> in place of \<open>w\<close>'s boundary condition; the restatement derives
  \<open>w \<ge> 0\<close> from that condition as the paper does
  (@{thm [source] supersol_bc_nonneg}), extending \<open>-w\<close> from \<open>K'\<close> by
  \<^const>\<open>Kext\<close>.\<close>

theorem paper_theorem_4_2_b:
  fixes u w :: "real^'n::finite \<Rightarrow> real" and K K' :: "(real^'n) set"
  assumes kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and cK: "compact K" and cK': "compact K'" and KK': "K \<subseteq> interior K'"
    and uscu: "\<And>c z. z \<in> K \<Longrightarrow> u z < c \<Longrightarrow> \<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> u y < c"
    and lscw: "\<And>c z. z \<in> K' \<Longrightarrow> c < w z \<Longrightarrow> \<exists>e>0. \<forall>y\<in>K'. dist z y < e \<longrightarrow> c < w y"
    and Bu: "\<And>y. y \<in> K \<Longrightarrow> \<bar>u y\<bar> \<le> B" and Bw: "\<And>y. y \<in> K' \<Longrightarrow> \<bar>w y\<bar> \<le> B"
    and subu: "visc_subsol_env2 k L K (interior K \<union> {x \<in> K - interior K. 0 < u x}) u"
    and supw: "visc_supersol_env2 k L K'
      (interior K' \<union> {x \<in> K' - interior K'. w x < 0}) w"
    and x: "x \<in> K"
  shows "u x \<le> w x"
proof -
  have Kc: "closed K" by (rule compact_imp_closed[OF cK])
  have K'c: "closed K'" by (rule compact_imp_closed[OF cK'])
  have neK: "K \<noteq> {}" using x by blast
  have xK': "x \<in> K'" using x KK' interior_subset by blast
  have neK': "K' \<noteq> {}" using xK' by blast
  have iK: "interior K \<subseteq> K" by (rule interior_subset)
  have iK': "interior K' \<subseteq> K'" by (rule interior_subset)
  \<comment> \<open>\<open>u\<close>, extended from \<open>K\<close>\<close>
  have eu1: "Kext K u y = u y" if "y \<in> K" for y
    by (rule paper_map_Kext(1)[OF Kc neK uscu Bu that])
  have eu2: "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> Kext K u y < c" if "Kext K u z < c" for c z
    by (rule paper_map_Kext(2)[OF Kc neK uscu Bu that])
  have eu3: "\<bar>Kext K u y\<bar> \<le> B" for y
    by (rule paper_map_Kext(3)[OF Kc neK uscu Bu])
  have gu1: "{z \<in> K - interior K. 0 < Kext K u z} = {z \<in> K - interior K. 0 < u z}"
    using eu1 by auto
  have subu': "visc_subsol_env2 k L K
      (interior K \<union> {z \<in> K - interior K. 0 < Kext K u z}) (Kext K u)"
    unfolding gu1 by (rule visc_subsol_env2_cong[OF _ _ subu]) (use eu1 iK in auto)
  \<comment> \<open>\<open>w\<close>, extended from \<open>K'\<close> as \<open>- Kext K' (- w)\<close>\<close>
  define nw where "nw = (\<lambda>y. - w y)"
  have uscnw: "\<exists>e>0. \<forall>y\<in>K'. dist z y < e \<longrightarrow> nw y < c"
    if z: "z \<in> K'" and lt: "nw z < c" for c z
  proof -
    have "- c < w z" using lt unfolding nw_def by linarith
    from lscw[OF z this] obtain e
      where e: "0 < e" and h: "\<forall>y\<in>K'. dist z y < e \<longrightarrow> - c < w y"
      by blast
    show ?thesis
    proof (intro exI[of _ e] conjI ballI impI)
      show "0 < e" by (rule e)
      fix y assume "y \<in> K'" and "dist z y < e"
      then have "- c < w y" using h by blast
      then show "nw y < c" unfolding nw_def by linarith
    qed
  qed
  have Bnw: "\<bar>nw y\<bar> \<le> B" if "y \<in> K'" for y using Bw[OF that] by (simp add: nw_def)
  have ew1: "Kext K' nw y = nw y" if "y \<in> K'" for y
    by (rule paper_map_Kext(1)[OF K'c neK' uscnw Bnw that])
  have ew2: "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> Kext K' nw y < c" if "Kext K' nw z < c" for c z
    by (rule paper_map_Kext(2)[OF K'c neK' uscnw Bnw that])
  have ew3: "\<bar>Kext K' nw y\<bar> \<le> B" for y
    by (rule paper_map_Kext(3)[OF K'c neK' uscnw Bnw])
  define wt where "wt = (\<lambda>y. - Kext K' nw y)"
  have wtK': "wt y = w y" if "y \<in> K'" for y
    using ew1[OF that] by (simp add: wt_def nw_def)
  have lscwt: "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> c < wt y" if lt: "c < wt z" for c z
  proof -
    have "Kext K' nw z < - c" using lt unfolding wt_def by linarith
    from ew2[OF this] obtain e
      where e: "0 < e" and h: "\<forall>y. dist z y < e \<longrightarrow> Kext K' nw y < - c"
      by blast
    show ?thesis
    proof (intro exI[of _ e] conjI allI impI)
      show "0 < e" by (rule e)
      fix y assume "dist z y < e"
      then have "Kext K' nw y < - c" using h by blast
      then show "c < wt y" unfolding wt_def by linarith
    qed
  qed
  have Bwt: "\<bar>wt y\<bar> \<le> B" for y using ew3[of y] by (simp add: wt_def)
  have lbwt: "- B \<le> wt y" if "y \<in> K'" for y using Bwt[of y] by (simp add: abs_le_iff)
  have gw: "{z \<in> K' - interior K'. wt z < 0} = {z \<in> K' - interior K'. w z < 0}"
    using wtK' by auto
  have supwt: "visc_supersol_env2 k L K'
      (interior K' \<union> {z \<in> K' - interior K'. wt z < 0}) wt"
    unfolding gw by (rule visc_supersol_env2_cong[OF _ _ supw]) (use wtK' iK' in auto)
  have supwt': "visc_supersol_env2 k L K' (interior K') wt"
    by (rule visc_supersol_env2_mono[OF supwt]) blast
  \<comment> \<open>the paper's step: a supersolution with the zero boundary condition is \<open>\<ge> 0\<close>\<close>
  have w0: "0 \<le> wt y" if "y \<in> K'" for y
    by (rule supersol_bc_nonneg[OF kk LL cK' neK' lscwt lbwt supwt that])
  have "Kext K u x \<le> wt x"
    by (rule comparison_two_domain[OF kk LL cK neK cK' KK' eu2 lscwt eu3 Bwt
          subu' supwt' w0 x])
  then show ?thesis using eu1[OF x] wtK'[OF xK'] by simp
qed

subsection \<open>Theorem 4.3\<close>

text \<open>Under the \<open>T\<^sub>\<iota>\<close> hypothesis, an upper semicontinuous subsolution \<open>u\<close> and a
  lower semicontinuous supersolution \<open>w\<close>, both with the zero boundary
  condition, satisfy \<open>u \<le> w\<^sup>*\<close> on \<open>K\<close>.  Formally for \<^const>\<open>expandable\<close> \<open>K\<close>,
  with \<open>u\<close> and \<open>w\<close> semicontinuous relative to \<open>K\<close> and bounded on \<open>K\<close> by a
  common \<open>B\<close>; \<open>w\<^sup>*\<close>, the upper envelope within \<open>K\<close>, is written
  \<open>- lsc_envK K (- w)\<close>.  The working lemma @{thm [source] comparison_expandable}
  takes \<open>u\<close> and \<open>w\<close> semicontinuous and bounded on all of \<open>\<real>\<^sup>n\<close> and concludes
  with the upper envelope \<^const>\<open>usc_env\<close> over \<open>\<real>\<^sup>n\<close>, which at points of
  \<open>\<partial>K\<close> can exceed the envelope within \<open>K\<close>.  For the extension
  \<open>- Kext K (- w)\<close> the two envelopes agree at every point of \<open>K\<close>
  (@{thm [source] lsc_env_Kext}), so the restatement loses nothing.\<close>

theorem paper_theorem_4_3:
  fixes u w :: "real^'n::finite \<Rightarrow> real" and K :: "(real^'n) set"
  assumes kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and cK: "compact K" and expK: "expandable K"
    and uscu: "\<And>c z. z \<in> K \<Longrightarrow> u z < c \<Longrightarrow> \<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> u y < c"
    and lscw: "\<And>c z. z \<in> K \<Longrightarrow> c < w z \<Longrightarrow> \<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> c < w y"
    and Bu: "\<And>y. y \<in> K \<Longrightarrow> \<bar>u y\<bar> \<le> B" and Bw: "\<And>y. y \<in> K \<Longrightarrow> \<bar>w y\<bar> \<le> B"
    and subu: "visc_subsol_env2 k L K (interior K \<union> {x \<in> K - interior K. 0 < u x}) u"
    and supw: "visc_supersol_env2 k L K (interior K \<union> {x \<in> K - interior K. w x < 0}) w"
    and x: "x \<in> K"
  shows "u x \<le> - lsc_envK K (\<lambda>y. - w y) x"
proof -
  have Kc: "closed K" by (rule compact_imp_closed[OF cK])
  have neK: "K \<noteq> {}" using x by blast
  have iK: "interior K \<subseteq> K" by (rule interior_subset)
  \<comment> \<open>\<open>u\<close>, extended from \<open>K\<close>\<close>
  have eu1: "Kext K u y = u y" if "y \<in> K" for y
    by (rule paper_map_Kext(1)[OF Kc neK uscu Bu that])
  have eu2: "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> Kext K u y < c" if "Kext K u z < c" for c z
    by (rule paper_map_Kext(2)[OF Kc neK uscu Bu that])
  have eu3: "\<bar>Kext K u y\<bar> \<le> B" for y
    by (rule paper_map_Kext(3)[OF Kc neK uscu Bu])
  have gu1: "{z \<in> K - interior K. 0 < Kext K u z} = {z \<in> K - interior K. 0 < u z}"
    using eu1 by auto
  have subu': "visc_subsol_env2 k L K
      (interior K \<union> {z \<in> K - interior K. 0 < Kext K u z}) (Kext K u)"
    unfolding gu1 by (rule visc_subsol_env2_cong[OF _ _ subu]) (use eu1 iK in auto)
  \<comment> \<open>\<open>w\<close>, extended from \<open>K\<close> as \<open>- Kext K (- w)\<close>\<close>
  define nw where "nw = (\<lambda>y. - w y)"
  have uscnw: "\<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> nw y < c"
    if z: "z \<in> K" and lt: "nw z < c" for c z
  proof -
    have "- c < w z" using lt unfolding nw_def by linarith
    from lscw[OF z this] obtain e
      where e: "0 < e" and h: "\<forall>y\<in>K. dist z y < e \<longrightarrow> - c < w y"
      by blast
    show ?thesis
    proof (intro exI[of _ e] conjI ballI impI)
      show "0 < e" by (rule e)
      fix y assume "y \<in> K" and "dist z y < e"
      then have "- c < w y" using h by blast
      then show "nw y < c" unfolding nw_def by linarith
    qed
  qed
  have Bnw: "\<bar>nw y\<bar> \<le> B" if "y \<in> K" for y using Bw[OF that] by (simp add: nw_def)
  have ew1: "Kext K nw y = nw y" if "y \<in> K" for y
    by (rule paper_map_Kext(1)[OF Kc neK uscnw Bnw that])
  have ew2: "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> Kext K nw y < c" if "Kext K nw z < c" for c z
    by (rule paper_map_Kext(2)[OF Kc neK uscnw Bnw that])
  have ew3: "\<bar>Kext K nw y\<bar> \<le> B" for y
    by (rule paper_map_Kext(3)[OF Kc neK uscnw Bnw])
  have ew4: "lsc_env (Kext K nw) y = lsc_envK K nw y" if "y \<in> K" for y
    by (rule paper_map_Kext(4)[OF Kc neK uscnw Bnw that])
  define wt where "wt = (\<lambda>y. - Kext K nw y)"
  have wtK: "wt y = w y" if "y \<in> K" for y
    using ew1[OF that] by (simp add: wt_def nw_def)
  have lscwt: "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> c < wt y" if lt: "c < wt z" for c z
  proof -
    have "Kext K nw z < - c" using lt unfolding wt_def by linarith
    from ew2[OF this] obtain e
      where e: "0 < e" and h: "\<forall>y. dist z y < e \<longrightarrow> Kext K nw y < - c"
      by blast
    show ?thesis
    proof (intro exI[of _ e] conjI allI impI)
      show "0 < e" by (rule e)
      fix y assume "dist z y < e"
      then have "Kext K nw y < - c" using h by blast
      then show "c < wt y" unfolding wt_def by linarith
    qed
  qed
  have Bwt: "\<bar>wt y\<bar> \<le> B" for y using ew3[of y] by (simp add: wt_def)
  have gw: "{z \<in> K - interior K. wt z < 0} = {z \<in> K - interior K. w z < 0}"
    using wtK by auto
  have supwt: "visc_supersol_env2 k L K
      (interior K \<union> {z \<in> K - interior K. wt z < 0}) wt"
    unfolding gw by (rule visc_supersol_env2_cong[OF _ _ supw]) (use wtK iK in auto)
  have main: "Kext K u x \<le> usc_env wt x"
    by (rule comparison_expandable[OF kk LL cK neK expK eu2 lscwt eu3 Bwt
          subu' supwt x])
  \<comment> \<open>the global upper envelope of the extension is the one within \<open>K\<close>\<close>
  have env: "usc_env wt x = - lsc_envK K nw x"
  proof -
    have "usc_env wt x = - lsc_env (Kext K nw) x" by (simp add: usc_env_def wt_def)
    also have "\<dots> = - lsc_envK K nw x" by (simp add: ew4[OF x])
    finally show ?thesis .
  qed
  have "u x \<le> - lsc_envK K nw x" using main env eu1[OF x] by linarith
  then show ?thesis by (simp add: nw_def)
qed

subsection \<open>Eq. (4.4)\<close>

text \<open>In the proof of Theorem 4.3: \<open>F(p, M) = c\<^sup>2 F(O\<^sup>Tp, c\<^sup>-\<^sup>2O\<^sup>TMO)\<close> for every
  orthogonal \<open>O\<close>, every \<open>c > 0\<close> and every \<open>(p, M) \<in> \<real>\<^sup>n \<times> \<bbbS>\<^sup>n\<close>.  Formally
  for every \<open>M\<close>, symmetric or not, from the rotation invariance
  @{thm [source] ell_op_conj_rot} and the homogeneity
  @{thm [source] ell_op_scaleR_matrix}, the feasible set being nonempty
  (@{thm [source] feasible_nonempty}); \<open>O\<close> is written \<open>R\<close>, \<open>O\<close> being
  relation composition in Isabelle.  The step it serves, that \<open>w\<close> transformed by a
  rotation, a dilation and a translation is again a supersolution, is
  @{thm [source] visc_supersol_env_affine}; the corresponding rules for \<open>F\<^sup>*\<close> are
  @{thm [source] ell_op_usc_scale} and @{thm [source] ell_op_usc_conj_rot}.\<close>

theorem paper_eq_4_4:
  fixes p :: "real^'n::finite" and M R :: "real^'n^'n" and c :: real
  assumes k1: "1 \<le> k" and kn: "k < CARD('n)" and L1: "1 \<le> L"
    and orth: "orthogonal_matrix R" and c0: "0 < c"
  shows "ell_op k L p M
      = c\<^sup>2 * ell_op k L (transpose R *v p) ((1 / c\<^sup>2) *\<^sub>R (transpose R ** M ** R))"
proof -
  have cne: "c \<noteq> 0" using c0 by simp
  have t: "0 < 1 / c\<^sup>2" using c0 by simp
  have ne: "feasible k L (transpose R *v p) \<noteq> {}"
    by (rule feasible_nonempty[OF k1 kn L1])
  have rot: "ell_op k L (transpose R *v p) (transpose R ** M ** R) = ell_op k L p M"
    using ell_op_conj_rot[where R = "transpose R" and k = k and L = L and p = p and M = M]
      orth
    by simp
  have sc: "ell_op k L (transpose R *v p) ((1 / c\<^sup>2) *\<^sub>R (transpose R ** M ** R))
      = (1 / c\<^sup>2) * ell_op k L p M"
    using ell_op_scaleR_matrix[OF t ne, where M = "transpose R ** M ** R"] rot
    by simp
  show ?thesis
    unfolding sc using cne by (simp add: field_simps)
qed


section \<open>Section 5: continuity of the value function\<close>

text \<open>Nothing of Section 5 is formalised.

  \<^item> Proposition 5.1 (for convex \<open>K\<close>, \<open>v\<close> is continuous on \<open>interior K\<close>): not
    formalised.  The paper's proof dilates \<open>v\<close> into \<open>interior K\<close> and compares the
    dilated \<open>v\<close>, as a subsolution, with \<open>v\<^sub>*\<close> by Theorem 4.2(b).  The comparison
    step is formal (@{thm [source] paper_theorem_4_2_b} above); the dilation
    invariance of Definition 3.1 is formal only for supersolutions
    (@{thm [source] visc_supersol_env_affine}).
  \<^item> Proposition 5.2 (if moreover \<open>v = 0\<close> on \<open>\<partial>K\<close>, \<open>v\<close> is continuous on \<open>K\<close>): not
    formalised; besides Proposition 5.1 it uses only \<open>v \<ge> 0\<close> and upper
    semicontinuity (@{thm [source] xval_usc}).
  \<^item> Lemma 5.3 (\<open>v(x) = 0\<close> iff the face of \<open>K\<close> containing \<open>x\<close> in its relative
    interior has dimension at most \<open>n - k\<close>): not formalised, nor is its
    deterministic core (a covariance degenerate on a subspace \<open>W\<close> satisfies
    \<open>eigen_lb a m\<close> only if \<open>m + dim W \<le> n\<close>); an earlier version of the
    development proved that core, but no theory contains it now.
  \<^item> Propositions 5.4 (\<open>k \<le> 2\<close>) and 5.5 (polytopes): not formalised; their
    proofs defer to Lemmas 5.6, 5.7 and Corollary 5.9(iii) of Larsson and Ruf's
    \<^emph>\<open>Minimum curvature flow and martingale exit times\<close>, which are not in the
    repository.\<close>

(*<*)
end
(*>*)
