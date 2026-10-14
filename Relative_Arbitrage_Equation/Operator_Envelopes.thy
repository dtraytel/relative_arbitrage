
(*<*)
theory Operator_Envelopes
  imports
    Viscosity_Definitions
    "Semicontinuous_Analysis.Semicontinuity"
    "Symmetric_Matrix_Spectra.Householder_Rotation"
begin

(*>*)

text \<open>
  Defines the lower and upper semicontinuous envelopes \<open>F\<^sub>*\<close> and \<open>F\<^sup>*\<close>
  of the operator \<open>F\<close> of Eq. (1.9), as ereal-valued functions with no
  side conditions, and states Definition 3.1 of \<^cite>\<open>LaiShkolnikovSoner\<close>:
  a subsolution satisfies
  \<open>F\<^sub>*(grad phi, Hess phi) \<le> 1\<close> and a supersolution
  \<open>F\<^sup>*(grad phi, Hess phi) \<ge> 1\<close>, with the paper's global touching
  condition, a maximum over \<open>K\<close> rather than on a small ball. It proves
  the sandwich \<open>F\<^sub>* \<le> F \<le> F\<^sup>*\<close>, that the envelope-free viscosity
  notions of \<open>Curvature_Operator\<close> imply the envelope ones, hence that
  Example 3.1 satisfies Definition 3.1 as stated, and the clause of
  Lemma 3.1 at the degenerate point, \<open>F\<^sub>* = F\<close> on \<open>{0} \<times> S\<^sup>n\<close>, using
  that at \<open>p = 0\<close> the constraint \<open>a p = 0\<close> is vacuous and that \<open>F\<close> is
  Lipschitz in \<open>M\<close> uniformly in \<open>p\<close>.

  The test functions here are the \<^const>\<open>test_fun_at\<close> ones, which are less
  regular than Definition 3.1's \<open>C\<^sup>2\<close>; that makes these notions the stronger,
  which is what the clauses \<^emph>\<open>asserting\<close> the viscosity property want.  The
  uniqueness clause needs the paper's own class instead; \<open>Comparison_Principle\<close>
  restates Definition 3.1 over it as \<open>visc_subsol_env2\<close> / \<open>visc_supersol_env2\<close>.\<close>
unbundle inner_syntax

section \<open>The operator of Eq. (1.9) on pairs\<close>

text \<open>\<open>ell_op_pair\<close> lives in @{theory Relative_Arbitrage_Equation.Viscosity_Definitions}.\<close>

section \<open>The semicontinuous envelopes \<open>F\<^sub>*\<close> and \<open>F\<^sup>*\<close>\<close>

text \<open>\<open>ell_op_lsc\<close>, \<open>ell_op_usc\<close> live in @{theory Relative_Arbitrage_Equation.Viscosity_Definitions}.\<close>

text \<open>Every ball around \<open>z\<close> contains \<open>z\<close>, which gives the sandwich
  \<open>F\<^sub>* \<le> F \<le> F\<^sup>*\<close>.  This is all that is needed to see that the
  envelope-free conditions are the stronger ones.\<close>

lemma ell_op_lsc_le:
  fixes p :: "real^'n::finite"
  shows "ell_op_lsc k L p M \<le> ell_op_pair k L (p, M)"
  unfolding ell_op_lsc_def
proof (rule SUP_least)
  fix e :: real assume e: "e \<in> {0<..}"
  have "(p, M) \<in> ball (p, M) e"
    using e by simp
  then show "(INF w \<in> ball (p, M) e. ell_op_pair k L w)
      \<le> ell_op_pair k L (p, M)"
    by (rule INF_lower)
qed

lemma ell_op_le_usc:
  fixes p :: "real^'n::finite"
  shows "ell_op_pair k L (p, M) \<le> ell_op_usc k L p M"
  unfolding ell_op_usc_def
proof (rule INF_greatest)
  fix e :: real assume e: "e \<in> {0<..}"
  have "(p, M) \<in> ball (p, M) e"
    using e by simp
  then show "ell_op_pair k L (p, M)
      \<le> (SUP w \<in> ball (p, M) e. ell_op_pair k L w)"
    by (rule SUP_upper)
qed

text \<open>Restated in terms of \<open>F\<close> itself.\<close>

lemma ell_op_lsc_le_ell_op:
  fixes p :: "real^'n::finite"
  shows "ell_op_lsc k L p M \<le> ereal (ell_op k L p M)"
  using ell_op_lsc_le[of k L p M] by (simp add: ell_op_pair_def)

lemma ell_op_le_ell_op_usc:
  fixes p :: "real^'n::finite"
  shows "ereal (ell_op k L p M) \<le> ell_op_usc k L p M"
  using ell_op_le_usc[of k L p M] by (simp add: ell_op_pair_def)

text \<open>The skeleton shared by every envelope evaluation below: a bound on the
  ball of radius \<open>e\<close> around \<open>x\<close> that degrades at most linearly in \<open>e\<close>, for
  all small \<open>e\<close>, passes to the envelope at \<open>x\<close>.  Stated for an arbitrary
  ereal-valued function on a metric space, since \<open>F\<^sub>*\<close> and \<open>F\<^sup>*\<close> are the ball
  envelopes of \<^const>\<open>ell_op_pair\<close>.\<close>

lemma ball_env_ge_of_bound:
  fixes F :: "'a::metric_space \<Rightarrow> ereal"
  assumes C: "0 < C" and r: "0 < r"
    and bnd: "\<And>e w. 0 < e \<Longrightarrow> e < r \<Longrightarrow> w \<in> ball x e \<Longrightarrow> ereal (c - C * e) \<le> F w"
  shows "ereal c \<le> (SUP e \<in> {0<..}. INF w \<in> ball x e. F w)"
proof (rule ereal_le_epsilon2)
  fix d :: real assume d: "0 < d"
  define e where "e = min (d / C) (r / 2)"
  have e1: "e \<le> r / 2" and e2: "e \<le> d / C"
    unfolding e_def by (rule min.cobounded2, rule min.cobounded1)
  have e: "0 < e" "e < r" "C * e \<le> d"
  proof -
    show "0 < e" using C r d unfolding e_def by simp
    show "e < r" using e1 r by linarith
    show "C * e \<le> d" using e2 C by (simp add: field_simps)
  qed
  have "ereal (c - d) \<le> (INF w \<in> ball x e. F w)"
    using e by (intro INF_greatest order_trans[OF _ bnd[OF e(1,2)]]) simp_all
  also have "\<dots> \<le> (SUP e \<in> {0<..}. INF w \<in> ball x e. F w)"
    using e(1) by (intro SUP_upper) simp
  finally have "ereal (c - d) + ereal d \<le> (SUP e \<in> {0<..}. INF w \<in> ball x e. F w) + ereal d"
    by (rule add_right_mono)
  then show "ereal c \<le> (SUP e \<in> {0<..}. INF w \<in> ball x e. F w) + ereal d" by simp
qed

lemma ball_env_le_of_bound:
  fixes F :: "'a::metric_space \<Rightarrow> ereal"
  assumes C: "0 < C" and r: "0 < r"
    and bnd: "\<And>e w. 0 < e \<Longrightarrow> e < r \<Longrightarrow> w \<in> ball x e \<Longrightarrow> F w \<le> ereal (c + C * e)"
  shows "(INF e \<in> {0<..}. SUP w \<in> ball x e. F w) \<le> ereal c"
proof (rule ereal_le_epsilon2)
  fix d :: real assume d: "0 < d"
  define e where "e = min (d / C) (r / 2)"
  have e1: "e \<le> r / 2" and e2: "e \<le> d / C"
    unfolding e_def by (rule min.cobounded2, rule min.cobounded1)
  have e: "0 < e" "e < r" "C * e \<le> d"
  proof -
    show "0 < e" using C r d unfolding e_def by simp
    show "e < r" using e1 r by linarith
    show "C * e \<le> d" using e2 C by (simp add: field_simps)
  qed
  have "(INF e \<in> {0<..}. SUP w \<in> ball x e. F w) \<le> (SUP w \<in> ball x e. F w)"
    using e(1) by (intro INF_lower) simp
  also have "\<dots> \<le> ereal (c + d)"
    using e by (intro SUP_least order_trans[OF bnd[OF e(1,2)]]) simp_all
  finally show "(INF e \<in> {0<..}. SUP w \<in> ball x e. F w) \<le> ereal c + ereal d" by simp
qed

text \<open>\<open>F\<^sup>*\<close> is upper semicontinuous by construction, so the inequality
  \<open>\<ge> 1\<close> passes through limits in \<open>(p, M)\<close>: this moves a conclusion
  obtained at perturbed jets back to the jet of interest.\<close>

lemma ell_op_usc_ge_one_limit:
  fixes ps :: "nat \<Rightarrow> real^'n::finite" and Ms :: "nat \<Rightarrow> real^'n^'n"
    and p0 :: "real^'n" and M0 :: "real^'n^'n"
  assumes ge: "\<And>j. 1 \<le> ell_op_usc k L (ps j) (Ms j)"
    and lim: "(\<lambda>j. (ps j, Ms j)) \<longlonglongrightarrow> (p0, M0)"
  shows "1 \<le> ell_op_usc k L p0 M0"
  unfolding ell_op_usc_def
proof (rule INF_greatest)
  fix e :: real assume "e \<in> {0<..}"
  then have e0: "0 < e" by simp
  have "\<forall>\<^sub>F j in sequentially. dist ((ps j, Ms j)) ((p0, M0)) < e / 2"
    by (rule tendstoD[OF lim]) (use e0 in simp)
  then obtain j where j: "dist ((ps j, Ms j)) ((p0, M0)) < e / 2"
    by (auto simp: eventually_sequentially)
  have sub: "ball ((ps j, Ms j)) (e / 2) \<subseteq> ball ((p0, M0)) e"
  proof
    fix w assume "w \<in> ball ((ps j, Ms j)) (e / 2)"
    then have "dist ((ps j, Ms j)) w < e / 2" by simp
    then have "dist ((p0, M0)) w < e"
      using j dist_triangle[of "(p0, M0)" w "(ps j, Ms j)"]
      by (simp add: dist_commute)
    then show "w \<in> ball ((p0, M0)) e" by simp
  qed
  have "(1 :: ereal) \<le> ell_op_usc k L (ps j) (Ms j)" by (rule ge)
  also have "\<dots> \<le> (SUP w \<in> ball ((ps j, Ms j)) (e / 2). ell_op_pair k L w)"
    unfolding ell_op_usc_def by (rule INF_lower) (use e0 in simp)
  also have "\<dots> \<le> (SUP w \<in> ball ((p0, M0)) e. ell_op_pair k L w)"
    by (rule SUP_subset_mono[OF sub order_refl])
  finally show "1 \<le> (SUP w \<in> ball ((p0, M0)) e. ell_op_pair k L w)" .
qed

text \<open>The special case used twice: the inequality \<open>\<ge> 1\<close> at every softened
  Hessian \<open>H - \<delta> I\<close> survives \<open>\<delta> \<rightarrow> 0\<close>.\<close>

lemma ell_op_usc_ge_one_shift:
  fixes p :: "real^'n::finite" and H :: "real^'n^'n"
  assumes ge: "\<And>\<delta>. 0 < \<delta> \<Longrightarrow> 1 \<le> ell_op_usc k L p (H - \<delta> *\<^sub>R mat 1)"
  shows "1 \<le> ell_op_usc k L p H"
proof (rule ell_op_usc_ge_one_limit[where ps = "\<lambda>_. p"
      and Ms = "\<lambda>j. H - (1 / real (Suc j)) *\<^sub>R mat 1"])
  show "1 \<le> ell_op_usc k L p (H - (1 / real (Suc j)) *\<^sub>R mat 1)" for j
    by (rule ge) simp
  have "(\<lambda>j. 1 / real (Suc j)) \<longlonglongrightarrow> 0"
    using LIMSEQ_inverse_real_of_nat by (simp add: divide_inverse)
  from tendsto_diff[OF tendsto_const tendsto_scaleR[OF this tendsto_const]]
  have "(\<lambda>j. H - (1 / real (Suc j)) *\<^sub>R (mat 1 :: real^'n^'n)) \<longlonglongrightarrow> H"
    by simp
  then show "(\<lambda>j. (p, H - (1 / real (Suc j)) *\<^sub>R mat 1)) \<longlonglongrightarrow> (p, H)"
    by (rule tendsto_Pair[OF tendsto_const])
qed

section \<open>Lemma 3.1, the clause at \<open>p = 0\<close>: \<open>F\<^sub>* = F\<close> on \<open>{0} \<times> \<bbbS>\<^sup>n\<close>\<close>

text \<open>At \<open>p = 0\<close> the constraint \<open>a p = 0\<close> of Eq. (1.9) is vacuous, so the
  feasible set is largest and \<open>F(0, \<sqdot>)\<close> is smallest.  Since \<open>F\<close> is also
  Lipschitz in \<open>M\<close> uniformly in \<open>p\<close>, the infimum near \<open>(0, M)\<close> is attained
  there, giving \<open>F\<^sub>*(0,M) = F(0,M)\<close>.\<close>

lemma feasible_zero_mono:
  fixes p :: "real^'n::finite"
  shows "feasible k L p \<subseteq> feasible k L (0 :: real^'n)"
  by (auto simp: feasible_def)

lemma ell_op_zero_le:
  fixes p :: "real^'n::finite"
  assumes ne: "feasible k L p \<noteq> ({} :: (real^'n^'n) set)"
  shows "ell_op k L (0 :: real^'n) M \<le> ell_op k L p M"
  unfolding ell_op_def
proof (rule cInf_superset_mono)
  show "(\<lambda>a. - trace (M ** a) / 2) ` feasible k L p \<noteq> {}"
    using ne by simp
  show "bdd_below ((\<lambda>a. - trace (M ** a) / 2) ` feasible k L (0 :: real^'n))"
    by (rule ell_op_bdd_below)
  show "(\<lambda>a. - trace (M ** a) / 2) ` feasible k L p
      \<subseteq> (\<lambda>a. - trace (M ** a) / 2) ` feasible k L (0 :: real^'n)"
    by (rule image_mono[OF feasible_zero_mono])
qed

text \<open>The entrywise bound \<open>|a i j| \<le> L\<close> on the feasible set turns a change of
  the Hessian argument into a uniform change of the objective.\<close>

abbreviation mgap :: "real \<Rightarrow> real^'n::finite^'n \<Rightarrow> real^'n^'n \<Rightarrow> real" where
  "mgap L M N \<equiv> entrysum (M - N) * L / 2"

text \<open>\<open>trace_mult_feasible_bound\<close>, \<open>ell_op_le_witness\<close> and \<open>ell_op_approx\<close>
  live in @{theory Relative_Arbitrage_Equation.Curvature_Operator}.\<close>

lemma ell_op_M_gap:
  fixes M N :: "real^'n::finite^'n"
  assumes ne: "feasible k L p \<noteq> ({} :: (real^'n^'n) set)"
  shows "ell_op k L p M \<le> ell_op k L p N + mgap L M N"
proof -
  have split: "trace (N ** a) + trace ((M - N) ** a) = trace (M ** a)" for a
  proof -
    have "N ** a + (M - N) ** a = M ** a"
      by (simp add: matrix_add_rdistrib[symmetric])
    then show ?thesis
      by (metis trace_add)
  qed
  have step: "ell_op k L p M \<le> - trace (N ** a) / 2 + mgap L M N"
    if a: "a \<in> feasible k L p" for a
    using ell_op_le_witness[OF a, of M] split[of a]
      trace_mult_feasible_bound[OF a, of "M - N"]
    by (simp add: abs_le_iff)
  have main: "ell_op k L p M - mgap L M N
      \<le> Inf ((\<lambda>a. - trace (N ** a) / 2) ` feasible k L p)"
  proof (rule cInf_greatest)
    show "(\<lambda>a. - trace (N ** a) / 2) ` feasible k L p \<noteq> {}"
      using ne by simp
    fix v assume "v \<in> (\<lambda>a. - trace (N ** a) / 2) ` feasible k L p"
    then obtain a where a: "a \<in> feasible k L p"
      and v: "v = - trace (N ** a) / 2"
      by blast
    show "ell_op k L p M - mgap L M N \<le> v"
      using step[OF a] v by simp
  qed
  then show ?thesis
    by (simp add: ell_op_def[of k L p N])
qed

text \<open>\<open>mgap\<close> is controlled by the matrix norm, so it vanishes as \<open>N \<rightarrow> M\<close>.\<close>

lemma mgap_le_norm:
  fixes M N :: "real^'n::finite^'n"
  assumes L: "0 \<le> L"
  shows "mgap L M N \<le> real (CARD('n) * CARD('n)) * norm (M - N) * L / 2"
  using mult_right_mono[OF entrysum_le_norm[of "M - N"] L]
  by (simp add: divide_right_mono)

lemma mgap_shift_id:
  fixes M :: "real^'n::finite^'n"
  assumes d: "0 \<le> \<delta>"
  shows "mgap L M (M + \<delta> *\<^sub>R mat 1) = \<delta> * real CARD('n) * L / 2"
    and "mgap L (M - \<delta> *\<^sub>R mat 1) M = \<delta> * real CARD('n) * L / 2"
proof -
  have "entrysum (\<delta> *\<^sub>R mat 1 :: real^'n^'n) = (\<Sum>i\<in>(UNIV::'n set). \<delta>)"
    unfolding entrysum_def
    by (intro sum.cong refl) (simp add: mat_def if_distrib abs_of_nonneg[OF d] cong: if_cong)
  then have e: "entrysum (\<delta> *\<^sub>R mat 1 :: real^'n^'n) = \<delta> * real CARD('n)"
    by simp
  show "mgap L M (M + \<delta> *\<^sub>R mat 1) = \<delta> * real CARD('n) * L / 2"
    using e entrysum_sym[of M "M + \<delta> *\<^sub>R mat 1"] by simp
  show "mgap L (M - \<delta> *\<^sub>R mat 1) M = \<delta> * real CARD('n) * L / 2"
    using e entrysum_sym[of "M - \<delta> *\<^sub>R mat 1" M] by simp
qed

subsection \<open>\<open>F\<close> and \<open>F\<^sup>*\<close> vanish with the Hessian, uniformly in the gradient\<close>

text \<open>At \<open>M = 0\<close>, \<open>F\<close> vanishes for every gradient, since every feasible \<open>a\<close>
  gives \<open>trace (0 a) = 0\<close>.  With the Lipschitz bound @{thm [source]
  ell_op_M_gap}, \<open>F\<close> is small whenever \<open>M\<close> is, uniformly in \<open>p\<close>, and this
  survives the supremum defining \<open>F\<^sup>*\<close>.  Theorem 4.2(a)'s diagonal case,
  where the doubled maximiser has \<open>x\<^sup>\<epsilon> = y\<^sup>\<epsilon>\<close>, uses \<open>F\<^sup>*(0,0) = 0\<close> for
  this reason.\<close>

lemma ell_op_zero_matrix:
  fixes p :: "real^'n::finite"
  assumes k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L"
  shows "ell_op k L p (0::real^'n^'n) = 0"
proof -
  have ne: "feasible k L p \<noteq> ({} :: (real^'n^'n) set)"
    by (rule feasible_nonempty[OF k(1) k(2) L])
  have img: "(\<lambda>a. - trace ((0::real^'n^'n) ** a) / 2) ` feasible k L p = {0}"
  proof -
    have z: "- trace ((0::real^'n^'n) ** a) / 2 = 0" for a :: "real^'n^'n"
      by (simp add: matrix_matrix_mult_def trace_def)
    show ?thesis using ne z by auto
  qed
  show ?thesis unfolding ell_op_def img by simp
qed

lemma ell_op_le_mgap_zero:
  fixes p :: "real^'n::finite" and M :: "real^'n^'n"
  assumes k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L"
  shows "ell_op k L p M \<le> mgap L M 0"
proof -
  have ne: "feasible k L p \<noteq> ({} :: (real^'n^'n) set)"
    by (rule feasible_nonempty[OF k(1) k(2) L])
  have a1: "ell_op k L p M \<le> ell_op k L p 0 + mgap L M 0"
    by (rule ell_op_M_gap[OF ne])
  have a2: "ell_op k L p (0 :: real^'n^'n) = 0"
    by (rule ell_op_zero_matrix[OF k(1) k(2) L])
  show ?thesis using a1 a2 by linarith
qed

lemma ell_op_le_scaled_norm:
  fixes p :: "real^'n::finite" and M :: "real^'n^'n"
  assumes k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L"
  shows "ell_op k L p M
      \<le> real (CARD('n) * CARD('n)) * L / 2 * norm M"
proof -
  have L0: "0 \<le> L" using L by linarith
  have a1: "ell_op k L p M \<le> mgap L M 0"
    by (rule ell_op_le_mgap_zero[OF k(1) k(2) L])
  have a2: "mgap L M 0
      \<le> real (CARD('n) * CARD('n)) * norm (M - 0) * L / 2"
    by (rule mgap_le_norm[OF L0])
  have a3: "real (CARD('n) * CARD('n)) * norm (M - 0) * L / 2
      = real (CARD('n) * CARD('n)) * L / 2 * norm M"
    by (simp add: field_simps)
  show ?thesis using a1 a2 unfolding a3 by linarith
qed

lemma ell_op_usc_le_scaled_norm:
  fixes p :: "real^'n::finite" and M :: "real^'n^'n"
  assumes k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L" and e: "0 < e"
  shows "ell_op_usc k L p M
      \<le> ereal (real (CARD('n) * CARD('n)) * L / 2 * (norm M + e))"
proof -
  define B where "B = real (CARD('n) * CARD('n)) * L / 2"
  have B0: "0 \<le> B" unfolding B_def using L by simp
  have step: "ell_op_pair k L w \<le> ereal (B * (norm M + e))"
    if w: "w \<in> ball (p, M) e" for w :: "(real^'n) \<times> (real^'n^'n)"
  proof -
    have dN: "norm (snd w - M) < e"
    proof -
      have "dist (snd w) (snd (p, M)) \<le> dist w (p, M)" by (rule dist_snd_le)
      then have "dist (snd w) M \<le> dist w (p, M)" by simp
      also have "\<dots> < e" using w by (simp add: dist_commute)
      finally show ?thesis by (simp add: dist_norm)
    qed
    have nb: "norm (snd w) \<le> norm M + e"
      using dN norm_triangle_ineq[of "snd w - M" M] by simp
    have "ell_op k L (fst w) (snd w) \<le> B * norm (snd w)"
      unfolding B_def by (rule ell_op_le_scaled_norm[OF k(1) k(2) L])
    also have "\<dots> \<le> B * (norm M + e)"
      by (rule mult_left_mono[OF nb B0])
    finally show ?thesis by (simp add: ell_op_pair_def)
  qed
  have "ell_op_usc k L p M
      \<le> (SUP w \<in> ball (p, M) e. ell_op_pair k L w)"
    unfolding ell_op_usc_def by (rule INF_lower) (use e in simp)
  also have "\<dots> \<le> ereal (B * (norm M + e))"
    by (rule SUP_least) (use step in blast)
  finally show ?thesis unfolding B_def .
qed

text \<open>Where \<open>M\<close> is small, the upper envelope is below \<open>1\<close>, whatever the
  gradient; in particular at \<open>-\<delta>I\<close> for a small enough shift.\<close>

lemma ell_op_usc_lt_one_of_small:
  fixes M :: "real^'n::finite^'n"
  assumes k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L"
    and M: "real (CARD('n) * CARD('n)) * L * norm M < 1"
  shows "ell_op_usc k L q M < 1"
proof -
  define B where "B = real (CARD('n) * CARD('n)) * L / 2"
  have B0: "0 < B"
    unfolding B_def using L by simp
  have M': "2 * B * norm M < 1"
    using M by (simp add: B_def)
  define e where "e = (1 - 2 * B * norm M) / (4 * B)"
  have e0: "0 < e"
    unfolding e_def using B0 M' by simp
  have "B * (norm M + e) = (2 * B * norm M + 1) / 4"
    unfolding e_def using B0 by (simp add: field_simps)
  then have lt: "B * (norm M + e) < 1"
    using M' by simp
  have "ell_op_usc k L q M \<le> ereal (B * (norm M + e))"
    unfolding B_def by (rule ell_op_usc_le_scaled_norm[OF k L e0])
  also have "\<dots> < 1"
    using lt by simp
  finally show ?thesis .
qed

lemma ell_op_usc_small_shift_lt_one:
  fixes k :: nat
  assumes k: "1 \<le> k" "k < CARD('n::finite)" and L: "1 \<le> L"
  obtains \<delta> :: real where "0 < \<delta>" and "\<delta> < 1"
    and "\<And>q :: real^'n.
      ell_op_usc k L q ((0::real^'n^'n) - \<delta> *\<^sub>R mat 1) < 1"
proof -
  define A where "A = real (CARD('n) * CARD('n)) * L"
  define Nm where "Nm = norm (mat 1 :: real^'n^'n)"
  have A0: "0 < A"
    unfolding A_def using L by simp
  have N1: "0 < Nm + 1"
    unfolding Nm_def using norm_ge_zero[of "mat 1 :: real^'n^'n"] by linarith
  define C where "C = A * (Nm + 1)"
  have C0: "0 < C"
    unfolding C_def using A0 N1 by simp
  define \<delta> where "\<delta> = min (1 / 2) (1 / (2 * C))"
  have d0: "0 < \<delta>" and d1: "\<delta> < 1"
    unfolding \<delta>_def using C0 by auto
  have "A * norm ((0::real^'n^'n) - \<delta> *\<^sub>R mat 1) = \<delta> * (A * Nm)"
    using d0 unfolding Nm_def by (simp add: mult_ac)
  also have "\<dots> \<le> \<delta> * C"
    unfolding C_def using d0 A0 by (intro mult_left_mono) (auto simp: algebra_simps)
  also have "\<dots> \<le> 1 / (2 * C) * C"
    using C0 unfolding \<delta>_def by (intro mult_right_mono) auto
  also have "\<dots> = 1 / 2"
    using C0 by simp
  finally have small: "A * norm ((0::real^'n^'n) - \<delta> *\<^sub>R mat 1) \<le> 1 / 2" .
  show ?thesis
    by (rule that[OF d0 d1], rule ell_op_usc_lt_one_of_small[OF k L])
      (use small in \<open>simp add: A_def\<close>)
qed

theorem ell_op_lsc_at_zero:
  fixes M :: "real^'n::finite^'n"
  assumes k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L"
  shows "ell_op_lsc k L (0 :: real^'n) M = ereal (ell_op k L (0 :: real^'n) M)"
proof (rule antisym)
  show "ell_op_lsc k L (0 :: real^'n) M \<le> ereal (ell_op k L 0 M)"
    by (rule ell_op_lsc_le_ell_op)
next
  have L0: "0 \<le> L"
    using L by simp
  define C where "C = real (CARD('n) * CARD('n)) * L / 2"
  have C_pos: "0 < C"
    using L by (simp add: C_def)
  have bound: "ereal (ell_op k L (0 :: real^'n) M - C * e) \<le> ell_op_pair k L w"
    if w: "w \<in> ball ((0 :: real^'n), M) e" for e w
  proof -
    have dN: "norm (M - snd w) \<le> e"
    proof -
      have "dist (snd w) (snd ((0 :: real^'n), M)) \<le> dist w ((0 :: real^'n), M)"
        by (rule dist_snd_le)
      then have "dist (snd w) M \<le> dist w ((0 :: real^'n), M)"
        by simp
      also have "\<dots> < e"
        using w by (simp add: dist_commute)
      finally show ?thesis
        by (simp add: dist_norm norm_minus_commute)
    qed
    have ne: "feasible k L (fst w) \<noteq> ({} :: (real^'n^'n) set)"
      by (rule feasible_nonempty[OF k L])
    have mg: "mgap L M (snd w) \<le> C * e"
    proof -
      have "mgap L M (snd w)
          \<le> real (CARD('n) * CARD('n)) * norm (M - snd w) * L / 2"
        by (rule mgap_le_norm[OF L0])
      also have "\<dots> \<le> real (CARD('n) * CARD('n)) * e * L / 2"
        using dN L0 by (simp add: divide_right_mono mult_right_mono)
      also have "\<dots> = C * e"
        by (simp add: C_def)
      finally show ?thesis .
    qed
    have "ell_op k L (0 :: real^'n) M
        \<le> ell_op k L (0 :: real^'n) (snd w) + mgap L M (snd w)"
      by (rule ell_op_M_gap) (rule feasible_nonempty[OF k L])
    also have "ell_op k L (0 :: real^'n) (snd w) \<le> ell_op k L (fst w) (snd w)"
      by (rule ell_op_zero_le[OF ne])
    finally have "ell_op k L (0 :: real^'n) M
        \<le> ell_op k L (fst w) (snd w) + C * e"
      using mg by simp
    then show "ereal (ell_op k L (0 :: real^'n) M - C * e)
        \<le> ell_op_pair k L w"
      by (simp add: ell_op_pair_def)
  qed
  show "ereal (ell_op k L (0 :: real^'n) M) \<le> ell_op_lsc k L 0 M"
    unfolding ell_op_lsc_def
    by (rule ball_env_ge_of_bound[OF C_pos zero_less_one]) (use bound in blast)
qed

text \<open>At the degenerate gradient, the subsolution inequality of
  Definition 3.1 and the envelope-free one coincide: \<open>F\<^sub>*(0,H) \<le> 1\<close> and
  \<open>F(0,H) \<le> 1\<close> are the same condition.\<close>

section \<open>Definition 3.1 in envelope form\<close>

text \<open>\<open>visc_subsol_env\<close>, \<open>visc_supersol_env\<close>, \<open>visc_sol_env\<close> live in @{theory Relative_Arbitrage_Equation.Viscosity_Definitions}.\<close>

section \<open>The envelope-free notions are the stronger ones\<close>

text \<open>Two reasons: \<open>F\<^sub>* \<le> F \<le> F\<^sup>*\<close> makes the envelope inequalities weaker
  at each test function, and a global maximum over \<open>K\<close> is in particular a
  local maximum on any ball around \<open>x\<close> that stays inside \<open>K\<close>, so the
  envelope notion constrains fewer test functions.\<close>

lemma visc_subsol_imp_env:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes sub: "visc_subsol k L \<Omega> u" and sub_K: "\<Omega> \<subseteq> K" and op: "open \<Omega>"
  shows "visc_subsol_env k L K \<Omega> u"
  unfolding visc_subsol_env_eq_gen
  by (rule visc_subsol_gen_filter_mono[OF visc_subsol_gen_mono[OF
        sub[unfolded visc_subsol_eq_gen] ell_op_lsc_le_ell_op]
        nhds_le_principal_of_open[OF op sub_K]])

lemma visc_supersol_imp_env:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes sup: "visc_supersol k L \<Omega> u" and sub_K: "\<Omega> \<subseteq> K" and op: "open \<Omega>"
  shows "visc_supersol_env k L K \<Omega> u"
  unfolding visc_supersol_env_eq_gen
  by (rule visc_supersol_gen_filter_mono[OF visc_supersol_gen_mono[OF
        sup[unfolded visc_supersol_eq_gen] ell_op_le_ell_op_usc]
        nhds_le_principal_of_open[OF op sub_K]])

section \<open>Example 3.1 satisfies Definition 3.1 as stated in the paper\<close>

text \<open>Putting \<open>K = cball 0 r\<close> and \<open>\<Omega> = ball 0 r = K\<^sup>\<circ>\<close>: the explicit
  function of Eq. (3.9) is a viscosity solution in the envelope sense of
  Definition 3.1, with zero boundary values on the sphere.\<close>

section \<open>The closed formula of Eq. (3.6)\<close>

text \<open>Eq. (3.4) defines, for \<open>p \<noteq> 0\<close>,
  \<open>M\<^sub>p = (I - pp\<^sup>T/|p|\<^sup>2) M (I - pp\<^sup>T/|p|\<^sup>2) + min (\<lambda>\<^sub>(\<^sub>n\<^sub>)(M),0) \<cdot> pp\<^sup>T/|p|\<^sup>2\<close>
  (and \<open>M\<^sub>0 = M\<close>), chosen so \<open>\<lambda>\<^sub>(\<^sub>n\<^sub>)(M)\<close> sorts to the bottom of its
  spectrum.  Diagonalising \<open>M\<^sub>p\<close> gives \<open>F(p,M) = -\<onehalf> bracket (n-k) L M\<^sub>p\<close>
  (Eq. (3.5)); the paper passes to \<open>p \<rightarrow> 0\<close> via the one-sided Poincare
  separation bound and Ky Fan's maximum principle, reaching Eq. (3.6).
  Here \<open>F\<^sup>* = F\<close> away from \<open>p = 0\<close> is instead established by transporting
  a feasible witness under orthogonal conjugation, below.  The Householder
  reflection \<open>hrefl\<close> and the rotations \<open>rotv\<close>, \<open>rotm\<close> built from it live in
  @{theory Symmetric_Matrix_Spectra.Householder_Rotation}.\<close>

subsection \<open>Feasibility is invariant under orthogonal conjugation\<close>

text \<open>\<open>orth_preserves_inner\<close> lives in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


theorem feasible_conj:
  fixes R a :: "real^'n::finite^'n" and p :: "real^'n"
  assumes orth: "transpose R ** R = mat 1"
    and orth': "R ** transpose R = mat 1"
    and aF: "a \<in> feasible k L p"
  shows "R ** a ** transpose R \<in> feasible k L (R *v p)"
proof -
  have psda: "psd a" and ap: "a *v p = 0"
    and lba: "eigen_lb a (CARD('n) - k)" and uba: "eigen_ub a L"
    using aF unfolding feasible_def by blast+
  have syma: "transpose a = a" using psda unfolding psd_def by blast
  have RTR: "transpose R *v (R *v z) = z" for z
  proof -
    have "transpose R *v (R *v z) = (transpose R ** R) *v z"
      by (metis matrix_vector_mul_assoc)
    also have "\<dots> = mat 1 *v z" unfolding orth by (rule refl)
    also have "\<dots> = z" by (rule matrix_vector_mul_lid)
    finally show ?thesis .
  qed
  have Amv: "(R ** a ** transpose R) *v z = R *v (a *v (transpose R *v z))"
    for z
    by (metis matrix_vector_mul_assoc)
  have quad: "z \<bullet> ((R ** a ** transpose R) *v z)
      = (transpose R *v z) \<bullet> (a *v (transpose R *v z))" for z
    unfolding Amv by (rule inner_transpose_matrix)
  have normT: "(transpose R *v z) \<bullet> (transpose R *v z) = z \<bullet> z" for z
  proof -
    have "transpose (transpose R) ** transpose R = mat 1"
      unfolding transpose_transpose by (rule orth')
    then show ?thesis by (rule orth_preserves_inner)
  qed
  \<comment> \<open>symmetry and definiteness\<close>
  have symA: "transpose (R ** a ** transpose R) = R ** a ** transpose R"
  proof -
    have t1: "transpose ((R ** a) ** transpose R)
        = transpose (transpose R) ** transpose (R ** a)"
      by (rule matrix_transpose_mul)
    have t2: "transpose (R ** a) = transpose a ** transpose R"
      by (rule matrix_transpose_mul)
    have t3: "transpose (transpose R) = R" by (rule transpose_transpose)
    have "transpose ((R ** a) ** transpose R) = R ** (a ** transpose R)"
      unfolding t1 t2 t3 syma by (rule refl)
    then show ?thesis by (simp add: matrix_mul_assoc)
  qed
  have psdA: "psd (R ** a ** transpose R)"
    unfolding psd_def
  proof (intro conjI allI)
    show "transpose (R ** a ** transpose R) = R ** a ** transpose R"
      by (rule symA)
  next
    fix z :: "real^'n"
    have "0 \<le> (transpose R *v z) \<bullet> (a *v (transpose R *v z))"
      using psda unfolding psd_def by blast
    then show "0 \<le> z \<bullet> ((R ** a ** transpose R) *v z)"
      using quad[of z] by simp
  qed
  \<comment> \<open>the annihilated direction moves with \<open>R\<close>\<close>
  have killA: "(R ** a ** transpose R) *v (R *v p) = 0"
  proof -
    have e1: "(R ** a ** transpose R) *v (R *v p)
        = R *v (a *v (transpose R *v (R *v p)))" by (rule Amv)
    have e2: "transpose R *v (R *v p) = p" by (rule RTR)
    have "(R ** a ** transpose R) *v (R *v p) = R *v (a *v p)"
      unfolding e1 e2 by (rule refl)
    then show ?thesis unfolding ap by simp
  qed
  \<comment> \<open>the cap, by isometry\<close>
  have ubA: "eigen_ub (R ** a ** transpose R) L"
    unfolding eigen_ub_def
  proof
    fix z :: "real^'n"
    have q: "z \<bullet> ((R ** a ** transpose R) *v z)
        = (transpose R *v z) \<bullet> (a *v (transpose R *v z))" by (rule quad)
    have le: "(transpose R *v z) \<bullet> (a *v (transpose R *v z))
        \<le> L * ((transpose R *v z) \<bullet> (transpose R *v z))"
      using uba unfolding eigen_ub_def by blast
    show "z \<bullet> ((R ** a ** transpose R) *v z) \<le> L * (z \<bullet> z)"
      using q le normT[of z] by simp
  qed
  \<comment> \<open>the floor, by moving the witnessing subspace\<close>
  have lbA: "eigen_lb (R ** a ** transpose R) (CARD('n) - k)"
  proof -
    obtain S where Ssub: "subspace S" and Sdim: "CARD('n) - k \<le> dim S"
      and Sge: "\<And>x. x \<in> S \<Longrightarrow> x \<bullet> x \<le> x \<bullet> (a *v x)"
      using lba unfolding eigen_lb_def by blast
    define S' where "S' = (\<lambda>y. R *v y) ` S"
    have linRT: "linear (\<lambda>y :: real^'n. transpose R *v y)"
      by (rule matrix_vector_mul_linear)
    have z0: "(0 :: real^'n) \<in> S" using Ssub unfolding subspace_def by blast
    have subS': "subspace S'"
    proof -
      have z': "(0 :: real^'n) \<in> S'"
      proof -
        have "R *v (0 :: real^'n) = 0" by simp
        then show ?thesis unfolding S'_def using z0 by force
      qed
      have addS: "x + y \<in> S'" if xS: "x \<in> S'" and yS: "y \<in> S'" for x y
      proof -
        from xS obtain x0 where x0: "x0 \<in> S" and xe: "x = R *v x0"
          unfolding S'_def by blast
        from yS obtain y0 where y0: "y0 \<in> S" and ye: "y = R *v y0"
          unfolding S'_def by blast
        have "x + y = R *v (x0 + y0)"
          unfolding xe ye by (simp add: matrix_vector_right_distrib)
        moreover have "x0 + y0 \<in> S"
          using Ssub x0 y0 unfolding subspace_def by blast
        ultimately show ?thesis unfolding S'_def by blast
      qed
      have scalS: "c *\<^sub>R x \<in> S'" if xS: "x \<in> S'" for c x
      proof -
        from xS obtain x0 where x0: "x0 \<in> S" and xe: "x = R *v x0"
          unfolding S'_def by blast
        have "c *\<^sub>R x = R *v (c *\<^sub>R x0)"
          unfolding xe by (simp add: matrix_vector_mult_scaleR)
        moreover have "c *\<^sub>R x0 \<in> S"
          using Ssub x0 unfolding subspace_def by blast
        ultimately show ?thesis unfolding S'_def by blast
      qed
      show ?thesis unfolding subspace_def using z' addS scalS by blast
    qed
    have Seq: "S = (\<lambda>y. transpose R *v y) ` S'"
    proof
      show "S \<subseteq> (\<lambda>y. transpose R *v y) ` S'"
      proof
        fix x assume xS: "x \<in> S"
        then have "R *v x \<in> S'" unfolding S'_def by blast
        moreover have "transpose R *v (R *v x) = x" by (rule RTR)
        ultimately show "x \<in> (\<lambda>y. transpose R *v y) ` S'" by force
      qed
    next
      show "(\<lambda>y. transpose R *v y) ` S' \<subseteq> S"
      proof
        fix z assume "z \<in> (\<lambda>y. transpose R *v y) ` S'"
        then obtain w where wS: "w \<in> S'" and ze: "z = transpose R *v w"
          by blast
        from wS obtain x where xS: "x \<in> S" and we: "w = R *v x"
          unfolding S'_def by blast
        have "z = x" unfolding ze we by (rule RTR)
        then show "z \<in> S" using xS by simp
      qed
    qed
    have dimS': "CARD('n) - k \<le> dim S'"
    proof -
      have "dim S = dim ((\<lambda>y. transpose R *v y) ` S')" using Seq by simp
      also have "\<dots> \<le> dim S'" by (rule dim_image_le[OF linRT])
      finally show ?thesis using Sdim by linarith
    qed
    have geS': "x \<bullet> x \<le> x \<bullet> ((R ** a ** transpose R) *v x)"
      if xS: "x \<in> S'" for x
    proof -
      from xS obtain y where yS: "y \<in> S" and xe: "x = R *v y"
        unfolding S'_def by blast
      have RT: "transpose R *v x = y" unfolding xe by (rule RTR)
      have eq: "x \<bullet> ((R ** a ** transpose R) *v x) = y \<bullet> (a *v y)"
      proof -
        have "x \<bullet> ((R ** a ** transpose R) *v x)
            = (transpose R *v x) \<bullet> (a *v (transpose R *v x))"
          by (rule quad)
        then show ?thesis unfolding RT .
      qed
      have nn: "x \<bullet> x = y \<bullet> y"
        unfolding xe by (rule orth_preserves_inner[OF orth])
      show ?thesis using Sge[OF yS] eq nn by simp
    qed
    show ?thesis
      unfolding eigen_lb_def
      using subS' dimS' geS' by blast
  qed
  show ?thesis
    unfolding feasible_def using psdA killA lbA ubA by simp
qed

subsection \<open>Feasibility sees only the direction of the gradient\<close>

lemma feasible_scale:
  fixes q :: "real^'n::finite"
  assumes c0: "c \<noteq> 0"
  shows "feasible k L (c *\<^sub>R q) = feasible k L q"
proof -
  have iff: "(a *v (c *\<^sub>R q) = 0) = (a *v q = 0)" for a :: "real^'n^'n"
  proof -
    have "a *v (c *\<^sub>R q) = c *\<^sub>R (a *v q)"
      by (simp add: matrix_vector_mult_scaleR)
    then show ?thesis using c0 by simp
  qed
  show ?thesis unfolding feasible_def using iff by auto
qed

subsection \<open>From a global touching over \<open>K\<close> to a local one\<close>

text \<open>Definition 3.1 constrains only test functions with a global touching
  over \<open>K\<close>, while Crandall--Ishii machinery produces local touchings from
  jet data.  The gap closes by subtracting a quartic
  \<open>\<psi> := \<phi> - C\<bar>z - x\<bar>\<^sup>4\<close>: it shares \<open>\<phi>\<close>'s two-jet at \<open>x\<close>, only deepens
  the touching inside the ball, and outside it is bounded below by
  \<open>Cr\<^sup>4\<close>, which for large \<open>C\<close> overwhelms the oscillation of \<open>w - \<phi>\<close> on
  \<open>K\<close> (\<open>local_max_quartic_deepen\<close>); the argument is the generic
  @{thm [source] visc_subsol_gen_principal_local}.  The two boundedness
  hypotheses are what a genuine \<open>C\<^sup>2\<close> test function on compact \<open>K\<close>
  supplies; \<^const>\<open>test_fun_at\<close> alone would tolerate truncating \<open>\<phi>\<close> far
  from \<open>x\<close>.\<close>

text \<open>A test function is minorised near \<open>x\<close> by its two-jet quadratic,
  once the Hessian is shifted down by any \<open>\<delta> > 0\<close>, which lets a touching
  by an arbitrary test function be replaced by a touching by a genuine
  quadratic, bounded on a bounded set.\<close>


theorem visc_subsol_env_local:
  fixes K :: "(real^'n::finite) set" and u \<phi> :: "real^'n \<Rightarrow> real"
    and g :: "real^'n \<Rightarrow> real^'n" and H :: "real^'n^'n"
  assumes sub: "visc_subsol_env k L K \<Omega> u"
    and x\<Omega>: "x \<in> \<Omega>"
    and tf: "test_fun_at \<phi> g H x"
    and uhi: "\<And>y. y \<in> K \<Longrightarrow> u y \<le> Bu"
    and phi: "\<And>y. y \<in> K \<Longrightarrow> B\<phi> \<le> \<phi> y"
    and r0: "0 < r"
    and lm: "\<And>y. y \<in> ball x r \<Longrightarrow> u y - \<phi> y \<le> u x - \<phi> x"
  shows "ell_op_lsc k L (g x) H \<le> 1"
  by (rule visc_subsol_gen_principal_local[OF sub[unfolded visc_subsol_env_eq_gen] x\<Omega>
        test_fun_at_quartic_shift[OF tf] uhi phi r0 lm])

section \<open>Semicontinuity toolbox and the invariances of \<open>F\<close>\<close>

text \<open>The semicontinuous envelopes of a general real-valued function, their
  attainment and extension lemmas, and the elementary \<open>\<epsilon>\<close>-\<open>\<delta>\<close> calculus of
  semicontinuity live in @{theory Semicontinuous_Analysis.Semicontinuity} and
  @{theory Semicontinuous_Analysis.Semicontinuous_Envelopes}.  What follows
  are the three invariances of \<open>F\<close> that make up the paper's display (4.4).\<close>

text \<open>The constant test function: the touching that Definition 3.1's boundary
  clause admits at a global minimum, and the one the paper's diagonal case
  uses to reach \<open>1 \<le> F\<^sup>*(0,0) = 0\<close>.\<close>

lemma ell_op_usc_zero_zero_lt_one:
  assumes kk: "1 \<le> k" "k < CARD('n::finite)" and LL: "1 \<le> L"
  shows "ell_op_usc k L (0 :: real^'n) (0 :: real^'n^'n) < 1"
  by (rule ell_op_usc_lt_one_of_small[OF kk LL]) simp

subsection \<open>The invariances of \<open>F\<close> --- the paper's display (4.4)\<close>


lemma ell_op_scale:
  fixes p :: "real^'n::finite" and M :: "real^'n^'n"
  assumes "c \<noteq> 0"
  shows "ell_op k L (c *\<^sub>R p) M = ell_op k L p M"
  unfolding ell_op_def feasible_scale[OF assms] ..

text \<open>\<open>trace_mul_sym\<close> is HOL-Analysis's.\<close>


lemma ell_op_conj_rot:
  fixes p :: "real^'n::finite" and M :: "real^'n^'n" and R :: "real^'n^'n"
  assumes orth: "orthogonal_matrix R"
  shows "ell_op k L (R *v p) (R ** M ** transpose R) = ell_op k L p M"
proof -
  have o1: "transpose R ** R = mat 1" and o2: "R ** transpose R = mat 1"
    using orth unfolding orthogonal_matrix_def by blast+
  have conj_id1: "transpose R ** (R ** a ** transpose R) ** R = a"
    for a :: "real^'n^'n"
  proof -
    have "transpose R ** (R ** a ** transpose R) ** R
        = (transpose R ** R) ** a ** (transpose R ** R)"
      by (simp add: matrix_mul_assoc)
    also have "\<dots> = a" unfolding o1 by simp
    finally show ?thesis .
  qed
  have conj_id2: "R ** (transpose R ** a ** R) ** transpose R = a"
    for a :: "real^'n^'n"
  proof -
    have "R ** (transpose R ** a ** R) ** transpose R
        = (R ** transpose R) ** a ** (R ** transpose R)"
      by (simp add: matrix_mul_assoc)
    also have "\<dots> = a" unfolding o2 by simp
    finally show ?thesis .
  qed
  have pback: "transpose R *v (R *v p) = p"
    by (metis o1 matrix_vector_mul_assoc matrix_vector_mul_lid)
  have bij: "(\<lambda>a. R ** a ** transpose R) ` feasible k L p = feasible k L (R *v p)"
  proof
    show "(\<lambda>a. R ** a ** transpose R) ` feasible k L p \<subseteq> feasible k L (R *v p)"
      using feasible_conj[OF o1 o2] by auto
  next
    show "feasible k L (R *v p) \<subseteq> (\<lambda>a. R ** a ** transpose R) ` feasible k L p"
    proof
      fix b assume bF: "b \<in> feasible k L (R *v p)"
      have "transpose R ** b ** transpose (transpose R)
          \<in> feasible k L (transpose R *v (R *v p))"
        by (rule feasible_conj[OF _ _ bF]) (use o1 o2 in simp_all)
      then have inF: "transpose R ** b ** R \<in> feasible k L p"
        unfolding pback by simp
      have "b = R ** (transpose R ** b ** R) ** transpose R"
        by (rule conj_id2[symmetric])
      then show "b \<in> (\<lambda>a. R ** a ** transpose R) ` feasible k L p"
        using inF by (metis image_eqI)
    qed
  qed
  have prodeq: "(R ** M ** transpose R) ** (R ** a ** transpose R)
      = R ** (M ** a) ** transpose R" for a :: "real^'n^'n"
  proof -
    have "(R ** M ** transpose R) ** (R ** a ** transpose R)
        = R ** M ** (transpose R ** R) ** a ** transpose R"
      by (simp add: matrix_mul_assoc)
    also have "\<dots> = R ** (M ** a) ** transpose R"
      unfolding o1 by (simp add: matrix_mul_assoc)
    finally show ?thesis .
  qed
  have treq: "trace ((R ** M ** transpose R) ** (R ** a ** transpose R))
      = trace (M ** a)" for a :: "real^'n^'n"
  proof -
    have "trace ((R ** M ** transpose R) ** (R ** a ** transpose R))
        = trace (R ** (M ** a) ** transpose R)"
      unfolding prodeq by (rule refl)
    also have "\<dots> = trace (transpose R ** (R ** (M ** a)))"
      by (rule trace_mul_sym)
    also have "\<dots> = trace ((transpose R ** R) ** (M ** a))"
      by (simp add: matrix_mul_assoc)
    also have "\<dots> = trace (M ** a)" unfolding o1 by simp
    finally show ?thesis .
  qed
  have "(\<lambda>a. - trace ((R ** M ** transpose R) ** a) / 2) ` feasible k L (R *v p)
      = (\<lambda>a. - trace (M ** a) / 2) ` feasible k L p"
    unfolding bij[symmetric] image_image
    by (rule image_cong[OF refl]) (simp add: treq)
  then show ?thesis unfolding ell_op_def by simp
qed

subsection \<open>Transporting the envelopes along an \<open>F\<close>-preserving homeomorphism\<close>


text \<open>\<open>matrix_mul_diff_right\<close> and \<open>matrix_mul_diff_left\<close> live in
  @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>

text \<open>\<open>matvec_orth_inv\<close>, \<open>conj_orth_inv\<close>, \<open>norm_orthogonal_matrix_vector\<close>, \<open>norm_matrix_sq_trace\<close>, \<open>norm_conj_orthogonal\<close> live in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


text \<open>\<open>pos_image_scale\<close> lives in @{theory Semicontinuous_Analysis.Semicontinuity}.\<close>


lemma ell_op_usc_transfer:
  fixes \<Psi> :: "((real^'n::finite) \<times> (real^'n^'n)) \<Rightarrow> ((real^'n) \<times> (real^'n^'n))"
  assumes F: "\<And>v. ell_op_pair k L (\<Psi> v) = ell_op_pair k L v"
    and a0: "0 < a" and b0: "0 < b"
    and sub1: "\<And>e. 0 < e \<Longrightarrow> \<Psi> ` ball z (e / a) \<subseteq> ball (\<Psi> z) e"
    and sub2: "\<And>e. 0 < e \<Longrightarrow> ball (\<Psi> z) (b * e) \<subseteq> \<Psi> ` ball z e"
  shows "(INF e \<in> {0<..}. SUP w \<in> ball (\<Psi> z) e. ell_op_pair k L w)
       = (INF e \<in> {0<..}. SUP w \<in> ball z e. ell_op_pair k L w)"
    (is "?A = ?B")
proof (rule antisym)
  have le1: "(SUP w \<in> ball (\<Psi> z) (b * e). ell_op_pair k L w)
      \<le> (SUP w \<in> ball z e. ell_op_pair k L w)" if e0: "0 < e" for e
  proof -
    have "(SUP w \<in> ball (\<Psi> z) (b * e). ell_op_pair k L w)
        \<le> (SUP w \<in> \<Psi> ` ball z e. ell_op_pair k L w)"
      by (rule SUP_subset_mono[OF sub2[OF e0]]) simp
    also have "\<dots> = (SUP v \<in> ball z e. ell_op_pair k L (\<Psi> v))"
      by (simp add: image_image)
    also have "\<dots> = (SUP v \<in> ball z e. ell_op_pair k L v)"
      by (rule SUP_cong[OF refl]) (rule F)
    finally show ?thesis .
  qed
  have imb: "(\<lambda>e. b * e) ` {0<..} = {(0::real)<..}"
  proof
    show "(\<lambda>e. b * e) ` {0<..} \<subseteq> {(0::real)<..}" using b0 by auto
    show "{(0::real)<..} \<subseteq> (\<lambda>e. b * e) ` {0<..}"
    proof
      fix x :: real assume "x \<in> {0<..}"
      then have x0: "0 < x" by simp
      have xe: "x = b * (x / b)" using b0 by simp
      have "x / b \<in> {0<..}" using x0 b0 by simp
      then show "x \<in> (\<lambda>e. b * e) ` {0<..}" using xe by (metis image_eqI)
    qed
  qed
  have "?A = (INF e \<in> {0<..}. SUP w \<in> ball (\<Psi> z) (b * e). ell_op_pair k L w)"
  proof -
    have "?A = (INF e \<in> (\<lambda>e. b * e) ` {0<..}.
        SUP w \<in> ball (\<Psi> z) e. ell_op_pair k L w)" unfolding imb by (rule refl)
    then show ?thesis by (simp add: image_image)
  qed
  also have "\<dots> \<le> ?B" by (rule INF_mono) (use le1 in blast)
  finally show "?A \<le> ?B" .
next
  have le2: "(SUP w \<in> ball z (e / a). ell_op_pair k L w)
      \<le> (SUP w \<in> ball (\<Psi> z) e. ell_op_pair k L w)" if e0: "0 < e" for e
  proof -
    have "(SUP w \<in> ball z (e / a). ell_op_pair k L w)
        = (SUP v \<in> ball z (e / a). ell_op_pair k L (\<Psi> v))"
      by (rule SUP_cong[OF refl]) (rule F[symmetric])
    also have "\<dots> = (SUP w \<in> \<Psi> ` ball z (e / a). ell_op_pair k L w)"
      by (simp add: image_image)
    also have "\<dots> \<le> (SUP w \<in> ball (\<Psi> z) e. ell_op_pair k L w)"
      by (rule SUP_subset_mono[OF sub1[OF e0]]) simp
    finally show ?thesis .
  qed
  have "?B = (INF e \<in> {0<..}. SUP w \<in> ball z (e / a). ell_op_pair k L w)"
  proof -
    have "?B = (INF e \<in> (\<lambda>e. e / a) ` {0<..}.
        SUP w \<in> ball z e. ell_op_pair k L w)"
      unfolding pos_image_scale[OF a0] by (rule refl)
    then show ?thesis by (simp add: image_image)
  qed
  also have "\<dots> \<le> ?A" by (rule INF_mono) (use le2 in blast)
  finally show "?B \<le> ?A" .
qed

subsection \<open>The two envelope invariances that Theorem 4.3 consumes\<close>

text \<open>\<open>dist_prod_scale_fst\<close> lives in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


theorem ell_op_usc_scale:
  fixes p :: "real^'n::finite" and M :: "real^'n^'n"
  assumes c0: "0 < c"
  shows "ell_op_usc k L (c *\<^sub>R p) M = ell_op_usc k L p M"
proof -
  define \<Psi> :: "((real^'n) \<times> (real^'n^'n)) \<Rightarrow> ((real^'n) \<times> (real^'n^'n))"
    where "\<Psi> = (\<lambda>v. (c *\<^sub>R fst v, snd v))"
  have F: "ell_op_pair k L (\<Psi> v) = ell_op_pair k L v" for v
    unfolding \<Psi>_def ell_op_pair_def using c0 by (simp add: ell_op_scale)
  have mx0: "0 < max c 1" using c0 by simp
  have mn0: "0 < min c 1" using c0 by simp
  have sub1: "\<Psi> ` ball (p, M) (e / max c 1) \<subseteq> ball (\<Psi> (p, M)) e" if e0: "0 < e" for e
  proof
    fix w assume "w \<in> \<Psi> ` ball (p, M) (e / max c 1)"
    then obtain v where vb: "v \<in> ball (p, M) (e / max c 1)" and wv: "w = \<Psi> v" by auto
    have dvz: "dist (p, M) v < e / max c 1" using vb by simp
    have "dist (\<Psi> (p, M)) (\<Psi> v) \<le> max c 1 * dist (p, M) v"
      unfolding \<Psi>_def by (rule dist_prod_scale_fst(1)[OF c0])
    also have "\<dots> < max c 1 * (e / max c 1)"
      by (rule mult_strict_left_mono[OF dvz mx0])
    also have "\<dots> = e" using mx0 by simp
    finally show "w \<in> ball (\<Psi> (p, M)) e" unfolding wv by simp
  qed
  have sub2: "ball (\<Psi> (p, M)) (min c 1 * e) \<subseteq> \<Psi> ` ball (p, M) e" if e0: "0 < e" for e
  proof
    fix w assume wb: "w \<in> ball (\<Psi> (p, M)) (min c 1 * e)"
    define v where "v = ((inverse c) *\<^sub>R fst w, snd w)"
    have wv: "\<Psi> v = w" unfolding \<Psi>_def v_def using c0 by simp
    have "min c 1 * dist (p, M) v \<le> dist (\<Psi> (p, M)) (\<Psi> v)"
      unfolding \<Psi>_def by (rule dist_prod_scale_fst(2)[OF c0])
    also have "\<dots> < min c 1 * e" unfolding wv using wb by simp
    finally have "dist (p, M) v < e" using mn0 by simp
    then have "v \<in> ball (p, M) e" by simp
    then show "w \<in> \<Psi> ` ball (p, M) e" using wv by (metis image_eqI)
  qed
  have "(INF e \<in> {0<..}. SUP w \<in> ball (\<Psi> (p, M)) e. ell_op_pair k L w)
      = (INF e \<in> {0<..}. SUP w \<in> ball (p, M) e. ell_op_pair k L w)"
    by (rule ell_op_usc_transfer[OF F mx0 mn0 sub1 sub2])
  then show ?thesis unfolding ell_op_usc_def \<Psi>_def by simp
qed

theorem ell_op_usc_conj_rot:
  fixes p :: "real^'n::finite" and M R :: "real^'n^'n"
  assumes orth: "orthogonal_matrix R"
  shows "ell_op_usc k L (R *v p) (R ** M ** transpose R) = ell_op_usc k L p M"
proof -
  define \<Psi> :: "((real^'n) \<times> (real^'n^'n)) \<Rightarrow> ((real^'n) \<times> (real^'n^'n))"
    where "\<Psi> = (\<lambda>v. (R *v fst v, R ** snd v ** transpose R))"
  have F: "ell_op_pair k L (\<Psi> v) = ell_op_pair k L v" for v
    unfolding \<Psi>_def ell_op_pair_def by (simp add: ell_op_conj_rot[OF orth])
  have isom: "dist (\<Psi> v) (\<Psi> v') = dist v v'" for v v'
  proof -
    have p1: "R *v fst v - R *v fst v' = R *v (fst v - fst v')"
      by (rule matrix_vector_mult_diff_distrib[symmetric])
    have p2: "R ** snd v ** transpose R - R ** snd v' ** transpose R
        = R ** (snd v - snd v') ** transpose R"
      by (simp add: matrix_mul_diff_right matrix_mul_diff_left)
    show ?thesis
      unfolding \<Psi>_def dist_prod_def dist_norm
      by (simp add: p1 p2 norm_orthogonal_matrix_vector[OF orth]
          norm_conj_orthogonal[OF orth])
  qed
  have one: "(0 :: real) < 1" by simp
  have sub1: "\<Psi> ` ball (p, M) (e / 1) \<subseteq> ball (\<Psi> (p, M)) e" if e0: "0 < e" for e
  proof
    fix w assume "w \<in> \<Psi> ` ball (p, M) (e / 1)"
    then obtain v where vb: "v \<in> ball (p, M) (e / 1)" and wv: "w = \<Psi> v" by auto
    have "dist (\<Psi> (p, M)) (\<Psi> v) = dist (p, M) v" by (rule isom)
    also have "\<dots> < e" using vb by simp
    finally show "w \<in> ball (\<Psi> (p, M)) e" unfolding wv by simp
  qed
  have sub2: "ball (\<Psi> (p, M)) (1 * e) \<subseteq> \<Psi> ` ball (p, M) e" if e0: "0 < e" for e
  proof
    fix w assume wb: "w \<in> ball (\<Psi> (p, M)) (1 * e)"
    define v where "v = (transpose R *v fst w, transpose R ** snd w ** R)"
    have fstv0: "fst v = transpose R *v fst w"
      unfolding v_def by (rule fst_conv)
    have sndv0: "snd v = transpose R ** snd w ** R"
      unfolding v_def by (rule snd_conv)
    have fstv: "R *v fst v = fst w"
      unfolding fstv0 by (rule matvec_orth_inv[OF orth])
    have sndv: "R ** snd v ** transpose R = snd w"
      unfolding sndv0 by (rule conj_orth_inv[OF orth])
    have wv: "\<Psi> v = w"
      unfolding \<Psi>_def using fstv sndv by simp
    have "dist (p, M) v = dist (\<Psi> (p, M)) (\<Psi> v)" by (rule isom[symmetric])
    also have "\<dots> < e" unfolding wv using wb by simp
    finally have "v \<in> ball (p, M) e" by simp
    then show "w \<in> \<Psi> ` ball (p, M) e" using wv by (metis image_eqI)
  qed
  have "(INF e \<in> {0<..}. SUP w \<in> ball (\<Psi> (p, M)) e. ell_op_pair k L w)
      = (INF e \<in> {0<..}. SUP w \<in> ball (p, M) e. ell_op_pair k L w)"
    by (rule ell_op_usc_transfer[OF F one one sub1 sub2])
  then show ?thesis unfolding ell_op_usc_def \<Psi>_def by simp
qed

text \<open>The \<open>ell_op_lsc\<close> versions follow from \<open>ell_op_usc_transfer\<close> verbatim with
  \<open>INF\<close> and \<open>SUP\<close> exchanged; they are not needed by Theorem 4.3, which reads the
  supersolution side only, so they are not stated.\<close>

section \<open>Congruence of the envelope-free notions, and affine images of open sets\<close>

text \<open>Monotonicity of \<open>lsc_env\<close>/\<open>usc_env\<close> and the fixpoint at points where the
  underlying function is already semicontinuous live in
  @{theory Semicontinuous_Analysis.Semicontinuous_Envelopes}.\<close>

subsection \<open>Affine maps commute with \<open>interior\<close>\<close>

text \<open>\<open>affine_interior_image\<close> lives in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


section \<open>A constant is a subsolution off \<open>K\<close>\<close>

text \<open>A test function touching from above at a local minimum of itself --
  as any touching of a locally constant function is -- satisfies the
  subsolution inequality for free.  So extending \<open>u\<close> by a constant below
  its minimum is a subsolution off \<open>K\<close>, turning Definition 3.1's gated
  \<open>\<Omega>\<close> into the open set \<open>UNIV - S\<close> with
  \<open>S = {x \<in> K - interior K. u x \<le> 0}\<close> compact -- the shape the
  Crandall--Ishii core needs.\<close>

(*<*)
end
(*>*)
