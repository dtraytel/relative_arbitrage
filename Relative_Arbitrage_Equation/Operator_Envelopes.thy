section \<open>The envelopes of the operator and Lemma 3.1\<close>

(*<*)
theory Operator_Envelopes
  imports
    Viscosity_Definitions Operator_Formula
    "Semicontinuous_Analysis.Semicontinuity"
    "Symmetric_Matrix_Spectra.Householder_Rotation"
begin

(*>*)

text \<open>
  The lower and upper semicontinuous envelopes \<open>F\<^sub>*\<close> and \<open>F\<^sup>*\<close> of the
  operator \<open>F\<close> of Eq. (1.9), \<^typ>\<open>ereal\<close>-valued with no side
  conditions, and Lemma 3.1 of \<^cite>\<open>LaiShkolnikovSoner\<close>: the sandwich
  \<open>F\<^sub>* \<le> F \<le> F\<^sup>*\<close>, \<open>F\<^sub>* = F\<close> on \<open>{0} \<times> S\<^sup>n\<close> (using that at \<open>p = 0\<close>
  the constraint \<open>a p = 0\<close> is vacuous and that \<open>F\<close> is Lipschitz in \<open>M\<close>
  uniformly in \<open>p\<close>), Eq. (3.6) for \<open>F\<^sup>*(0, M)\<close>, and \<open>F\<^sub>* = F\<^sup>* = F\<close>
  off the origin.  Also the facts about \<open>F\<close> that the comparison principles
  read: the envelope-free viscosity notions imply the envelope ones of
  Definition 3.1, and \<open>F\<close> has the invariances of display (4.4), is
  degenerate elliptic and is positively homogeneous in \<open>M\<close>.

  The envelopes and the viscosity notions are defined in
  @{theory Relative_Arbitrage_Equation.Viscosity_Definitions}.  The notions
  \<^const>\<open>visc_subsol_env\<close> and \<^const>\<open>visc_supersol_env\<close> use
  \<^const>\<open>test_fun_at\<close> test functions, which are less regular than
  Definition 3.1's \<open>C\<^sup>2\<close> ones; that makes these notions the stronger, which
  is what the clauses \<^emph>\<open>asserting\<close> the viscosity property want.  The
  uniqueness clause needs the paper's own class instead, as in
  \<^const>\<open>visc_subsol_env2\<close> and \<^const>\<open>visc_supersol_env2\<close>.\<close>

unbundle inner_syntax

subsection \<open>The semicontinuous envelopes \<open>F\<^sub>*\<close> and \<open>F\<^sup>*\<close>\<close>

text \<open>Every ball around \<open>z\<close> contains \<open>z\<close>, which gives the sandwich
  \<open>F\<^sub>* \<le> F \<le> F\<^sup>*\<close>.  This is all that is needed to see that the
  envelope-free conditions are the stronger ones.\<close>

lemma ell_op_lsc_le:
  fixes p :: "real^'n::finite"
  shows "ell_op_lsc k L p M \<le> ell_op_pair k L (p, M)"
  using op_lsc_le[of "ell_op k L" p M] by (simp add: ell_op_lsc_eq_op_lsc ell_op_pair_def)

lemma ell_op_le_usc:
  fixes p :: "real^'n::finite"
  shows "ell_op_pair k L (p, M) \<le> ell_op_usc k L p M"
  using op_usc_ge[of "ell_op k L" p M] by (simp add: ell_op_usc_eq_op_usc ell_op_pair_def)

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

text \<open>The special case used twice: the inequality \<open>\<ge> 1\<close> at every softened
  Hessian \<open>H - \<delta> I\<close> survives \<open>\<delta> \<rightarrow> 0\<close>.\<close>

subsection \<open>Lemma 3.1, the clause at \<open>p = 0\<close>: \<open>F\<^sub>* = F\<close> on \<open>{0} \<times> \<bbbS>\<^sup>n\<close>\<close>

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

subsubsection \<open>\<open>F\<close> and \<open>F\<^sup>*\<close> vanish with the Hessian, uniformly in the gradient\<close>

text \<open>At \<open>M = 0\<close>, \<open>F\<close> vanishes for every gradient, since every feasible \<open>a\<close>
  gives \<open>trace (0 a) = 0\<close>.  With the Lipschitz bound @{thm [source]
  ell_op_M_gap}, \<open>F\<close> is small whenever \<open>M\<close> is, uniformly in \<open>p\<close>, and this
  survives the supremum defining \<open>F\<^sup>*\<close>.  This gives \<open>F\<^sup>*(0, 0) < 1\<close>
  and \<open>F\<^sup>*(q, - \<delta> I) < 1\<close> for small \<open>\<delta>\<close>, uniformly in \<open>q\<close>, which the
  comparison principles use where the doubled maximiser is on the
  diagonal.\<close>

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

subsection \<open>The envelope-free notions are the stronger ones\<close>

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

subsection \<open>Invariances of the feasible set\<close>

text \<open>The feasible set is invariant under orthogonal conjugation of the
  matrix together with the gradient, and sees only the direction of the
  gradient.  These give the invariances of \<open>F\<close> of display (4.4) below.\<close>

subsubsection \<open>Feasibility is invariant under orthogonal conjugation\<close>


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

subsubsection \<open>Feasibility sees only the direction of the gradient\<close>

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

subsection \<open>The upper envelope at the origin, and the invariances of \<open>F\<close>\<close>

text \<open>\<open>F\<^sup>*(0, 0) < 1\<close>: this is what a constant test function, touching at a
  global minimum, meets in the boundary clause of Definition 3.1.\<close>

lemma ell_op_usc_zero_zero_lt_one:
  assumes kk: "1 \<le> k" "k < CARD('n::finite)" and LL: "1 \<le> L"
  shows "ell_op_usc k L (0 :: real^'n) (0 :: real^'n^'n) < 1"
  by (rule ell_op_usc_lt_one_of_small[OF kk LL]) simp

subsubsection \<open>The invariances of \<open>F\<close>: the paper's display (4.4)\<close>

lemma ell_op_scale:
  fixes p :: "real^'n::finite" and M :: "real^'n^'n"
  assumes "c \<noteq> 0"
  shows "ell_op k L (c *\<^sub>R p) M = ell_op k L p M"
  unfolding ell_op_def feasible_scale[OF assms] ..


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

subsubsection \<open>The two envelope invariances that Theorem 4.3 consumes\<close>

text \<open>Both are instances of the transport of \<open>F\<^sup>*\<close> along an \<open>F\<close>-preserving
  map, @{thm [source] op_usc_dilation} and @{thm [source] op_usc_rotation}.\<close>

theorem ell_op_usc_scale:
  fixes p :: "real^'n::finite" and M :: "real^'n^'n"
  assumes c0: "0 < c"
  shows "ell_op_usc k L (c *\<^sub>R p) M = ell_op_usc k L p M"
  unfolding ell_op_usc_eq_op_usc
  by (rule op_usc_dilation[OF _ c0]) (use c0 in \<open>simp add: ell_op_scale\<close>)

theorem ell_op_usc_conj_rot:
  fixes p :: "real^'n::finite" and M R :: "real^'n^'n"
  assumes orth: "orthogonal_matrix R"
  shows "ell_op_usc k L (R *v p) (R ** M ** transpose R) = ell_op_usc k L p M"
  unfolding ell_op_usc_eq_op_usc
  by (rule op_usc_rotation[where F = "ell_op k L", OF ell_op_conj_rot[OF orth] orth])

text \<open>The \<open>ell_op_lsc\<close> versions follow from @{thm [source] ball_usc_env_transfer} verbatim with
  \<open>INF\<close> and \<open>SUP\<close> exchanged; they are not needed by Theorem 4.3, which reads the
  supersolution side only, so they are not stated.\<close>

text \<open>The following sections prove the clauses of Lemma 3.1 of
  \<^cite>\<open>LaiShkolnikovSoner\<close> that mention the envelopes \<open>F\<^sub>*\<close> and \<open>F\<^sup>*\<close>
  away from the clause at \<open>p = 0\<close> above: Eq. (3.6) and continuity off the
  origin, from Eq. (3.5) and the index shift of Eq. (3.6) supplied by
  \<open>Operator_Formula\<close>.\<close>

subsection \<open>Eq. (3.6): the lower bound for \<open>F\<^sup>*(0, M)\<close>\<close>

text \<open>The paper obtains Eq. (3.6) by evaluating \<open>F\<close> along the sequence
  \<open>(q\<^sub>1/m, M)\<close>, with \<open>q\<^sub>1\<close> a top eigenvector of \<open>M\<close>.  Here that sequence is
  constant, since \<open>F\<close> depends on \<open>p\<close> only through its direction
  (\<open>ell_op_scaleR_dir\<close>): every ball around \<open>(0, M)\<close> contains a point
  \<open>(c q\<^sub>1, M)\<close> with the same value of \<open>F\<close>, equal to the right-hand side of
  Eq. (3.6).\<close>

definition eq36_rhs :: "nat \<Rightarrow> real \<Rightarrow> real^'n::finite^'n \<Rightarrow> real" where
  "eq36_rhs k L M =
     - (1/2) * (L * (\<Sum>i\<in>{2..CARD('n)}. max (eigval i M) 0)
        + (\<Sum>i\<in>{2..CARD('n) - k + 1}. min (eigval i M) 0))"

theorem ell_op_usc_at_zero_ge:
  fixes M :: "real^'n::finite^'n"
  assumes sym: "transpose M = M" and L: "1 \<le> L" and k: "1 \<le> k" "k < CARD('n)"
  shows "ereal (eq36_rhs k L M) \<le> ell_op_usc k L (0 :: real^'n) M"
  unfolding ell_op_usc_def
proof (rule INF_greatest)
  fix e :: real assume e: "e \<in> {0<..}"
  then have epos: "0 < e"
    by simp
  obtain q :: "real^'n" where q: "norm q = 1"
    and eigq: "M *v q = (q \<bullet> (M *v q)) *\<^sub>R q"
    and top: "q \<bullet> (M *v q) = eigval 1 M"
    using exists_top_eigenvector[OF sym] by blast
  define c where "c = e / 2"
  have cpos: "0 < c"
    unfolding c_def using epos by simp
  have ce: "c < e"
    unfolding c_def using epos by simp
  have inball: "(c *\<^sub>R q, M) \<in> ball ((0 :: real^'n), M) e"
  proof -
    have "dist (c *\<^sub>R q, M) ((0 :: real^'n), M) = norm (c *\<^sub>R q)"
      by (simp add: dist_prod_def dist_norm)
    also have "\<dots> = c"
      using cpos q by simp
    finally show ?thesis
      using ce by (simp add: dist_commute)
  qed
  have val: "ell_op_pair k L (c *\<^sub>R q, M) = ereal (eq36_rhs k L M)"
    unfolding ell_op_pair_def eq36_rhs_def
    by (simp add: ell_op_at_top_eigenvector[OF sym q eigq top L k(1) k(2) cpos])
  have "ell_op_pair k L (c *\<^sub>R q, M)
      \<le> (SUP w \<in> ball ((0 :: real^'n), M) e. ell_op_pair k L w)"
    using inball by (rule SUP_upper)
  then show "ereal (eq36_rhs k L M)
      \<le> (SUP w \<in> ball ((0 :: real^'n), M) e. ell_op_pair k L w)"
    unfolding val[symmetric] .
qed

subsection \<open>Eq. (3.6): the pointwise upper bound\<close>

text \<open>\<open>F(p, M) \<le> eq36_rhs k L M\<close> for every \<open>p\<close>, including \<open>p = 0\<close>.  For \<open>p \<noteq> 0\<close>
  this is Eq. (3.5) combined with \<open>bracket_ge_shifted\<close> (which rests on the
  general Poincare separation inequality); for \<open>p = 0\<close> it follows because
  \<open>feasible k L p \<subseteq> feasible k L 0\<close>, so the infimum at \<open>0\<close> is the smaller one
  (\<open>ell_op_zero_le\<close>).\<close>

theorem ell_op_le_eq36:
  fixes M :: "real^'n::finite^'n"
  assumes sym: "transpose M = M" and L: "1 \<le> L" and k: "1 \<le> k" "k < CARD('n)"
  shows "ell_op k L p M \<le> eq36_rhs k L M"
proof -
  have nonzero: "ell_op k L r M \<le> eq36_rhs k L M" if r: "r \<noteq> 0" for r :: "real^'n"
  proof -
    have "ell_op k L r M \<le> - (1/2) * bracket (CARD('n) - k) L (Mp r M)"
      by (rule ell_op_le_half_bracket[OF sym r L k(1) k(2)])
    also have "\<dots> \<le> eq36_rhs k L M"
    proof -
      have "L * (\<Sum>i\<in>{2..CARD('n)}. max (eigval i M) 0)
            + (\<Sum>i\<in>{2..CARD('n) - k + 1}. min (eigval i M) 0)
          \<le> bracket (CARD('n) - k) L (Mp r M)"
        by (rule bracket_ge_shifted[OF sym L k(1) k(2)])
      then show ?thesis
        unfolding eq36_rhs_def by simp
    qed
    finally show ?thesis .
  qed
  show ?thesis
  proof (cases "p = 0")
    case True
    obtain q :: "real^'n" where q: "norm q = 1"
      and eigq: "M *v q = (q \<bullet> (M *v q)) *\<^sub>R q"
      and topq: "q \<bullet> (M *v q) = eigval 1 M"
      using exists_top_eigenvector[OF sym] by blast
    have qne: "q \<noteq> 0"
      using q by auto
    have ne: "feasible k L q \<noteq> ({} :: (real^'n^'n) set)"
      using feasible_witness[OF k(1) k(2) L] by blast
    have "ell_op k L (0 :: real^'n) M \<le> ell_op k L q M"
      by (rule ell_op_zero_le[OF ne])
    also have "\<dots> \<le> eq36_rhs k L M"
      by (rule nonzero[OF qne])
    finally show ?thesis
      unfolding True .
  next
    case False
    then show ?thesis
      by (rule nonzero)
  qed
qed

subsection \<open>Eq. (3.6): the envelope upper bound, and the equality\<close>

text \<open>The upper bound for the envelope.  The nearby matrices \<open>snd w\<close> need not be
  symmetric: the comparison is made against the symmetric \<open>M\<close> using
  \<open>ell_op_M_gap\<close>, and only \<open>M\<close> itself has to be symmetric for
  \<open>ell_op_le_eq36\<close>.  This mirrors \<open>ell_op_lsc_at_zero\<close> above.\<close>

theorem ell_op_usc_at_zero_le:
  fixes M :: "real^'n::finite^'n"
  assumes sym: "transpose M = M" and L: "1 \<le> L" and k: "1 \<le> k" "k < CARD('n)"
  shows "ell_op_usc k L (0 :: real^'n) M \<le> ereal (eq36_rhs k L M)"
proof -
  have L0: "0 \<le> L"
    using L by simp
  define C where "C = real (CARD('n) * CARD('n)) * L / 2"
  have C_pos: "0 < C"
    using L by (simp add: C_def)
  have bound: "ell_op_pair k L w \<le> ereal (eq36_rhs k L M + C * e)"
    if w: "w \<in> ball ((0 :: real^'n), M) e" for e w
  proof -
    have dN: "norm (snd w - M) \<le> e"
    proof -
      have "dist (snd w) (snd ((0 :: real^'n), M)) \<le> dist w ((0 :: real^'n), M)"
        by (rule dist_snd_le)
      then have "dist (snd w) M \<le> dist w ((0 :: real^'n), M)"
        by simp
      also have "\<dots> < e"
        using w by (simp add: dist_commute)
      finally show ?thesis
        by (simp add: dist_norm)
    qed
    have ne: "feasible k L (fst w) \<noteq> ({} :: (real^'n^'n) set)"
      by (rule feasible_nonempty[OF k(1) k(2) L])
    have mg: "mgap L (snd w) M \<le> C * e"
    proof -
      have "mgap L (snd w) M
          \<le> real (CARD('n) * CARD('n)) * norm (snd w - M) * L / 2"
        by (rule mgap_le_norm[OF L0])
      also have "\<dots> \<le> real (CARD('n) * CARD('n)) * e * L / 2"
        using dN L0 by (simp add: divide_right_mono mult_right_mono)
      also have "\<dots> = C * e"
        by (simp add: C_def)
      finally show ?thesis .
    qed
    have "ell_op k L (fst w) (snd w)
        \<le> ell_op k L (fst w) M + mgap L (snd w) M"
      by (rule ell_op_M_gap[OF ne])
    also have "ell_op k L (fst w) M \<le> eq36_rhs k L M"
      by (rule ell_op_le_eq36[OF sym L k(1) k(2)])
    finally have "ell_op k L (fst w) (snd w) \<le> eq36_rhs k L M + C * e"
      using mg by simp
    then show "ell_op_pair k L w \<le> ereal (eq36_rhs k L M + C * e)"
      by (simp add: ell_op_pair_def)
  qed
  show ?thesis
    unfolding ell_op_usc_def
    by (rule ball_env_le_of_bound[OF C_pos zero_less_one]) (use bound in blast)
qed

text \<open>Eq. (3.6) of the paper:

    \<open>F\<^sup>*(0, M) = -\<onehalf> \<Sum>\<^sub>i\<^sub>=\<^sub>2\<^sup>n\<^sup>-\<^sup>k\<^sup>+\<^sup>1 [L \<lambda>\<^sub>(\<^sub>i\<^sub>)(M) 1{\<lambda>\<^sub>(\<^sub>i\<^sub>)(M)>0} + \<lambda>\<^sub>(\<^sub>i\<^sub>)(M) 1{\<lambda>\<^sub>(\<^sub>i\<^sub>)(M)\<le>0}]
                 - \<onehalf> \<Sum>\<^sub>i\<^sub>=\<^sub>n\<^sub>-\<^sub>k\<^sub>+\<^sub>2\<^sup>n L \<lambda>\<^sub>(\<^sub>i\<^sub>)(M) 1{\<lambda>\<^sub>(\<^sub>i\<^sub>)(M)>0}\<close>

  which regrouped is \<open>eq36_rhs\<close>: the positive part running over \<open>i = 2, \<dots>, n\<close>
  and the nonpositive part over \<open>i = 2, \<dots>, n-k+1\<close>.  Compared with Eq. (3.5) at
  \<open>p \<noteq> 0\<close> every index has moved up by one -- the eigenvalue \<open>\<lambda>\<^sub>(\<^sub>1\<^sub>)(M)\<close> is
  missing.\<close>

theorem eq36:
  fixes M :: "real^'n::finite^'n"
  assumes sym: "transpose M = M" and L: "1 \<le> L" and k: "1 \<le> k" "k < CARD('n)"
  shows "ell_op_usc k L (0 :: real^'n) M = ereal (eq36_rhs k L M)"
  by (rule antisym[OF ell_op_usc_at_zero_le[OF sym L k(1) k(2)]
        ell_op_usc_at_zero_ge[OF sym L k(1) k(2)]])

subsection \<open>The continuity clause of Lemma 3.1: \<open>F\<^sub>* = F\<^sup>* = F\<close> off the origin\<close>

text \<open>\<open>mgap\<close> is symmetric in its two matrix arguments, so \<open>ell_op_M_gap\<close> gives a
  two-sided bound.\<close>

lemma mgap_commute:
  fixes M N :: "real^'n::finite^'n"
  shows "mgap L M N = mgap L N M"
  using entrysum_sym[of M N] by simp

lemma ell_op_M_gap_abs:
  fixes M N :: "real^'n::finite^'n"
  assumes ne: "feasible k L p \<noteq> ({} :: (real^'n^'n) set)"
  shows "\<bar>ell_op k L p M - ell_op k L p N\<bar> \<le> mgap L M N"
proof -
  have a: "ell_op k L p M \<le> ell_op k L p N + mgap L M N"
    by (rule ell_op_M_gap[OF ne])
  have b: "ell_op k L p N \<le> ell_op k L p M + mgap L N M"
    by (rule ell_op_M_gap[OF ne])
  have c: "mgap L N M = mgap L M N" by (rule mgap_commute)
  show ?thesis
    using a b unfolding c abs_le_iff by linarith
qed

text \<open>The two variations combine: on a ball around \<open>(p, M)\<close> of radius smaller
  than \<open>norm p\<close> -- so that every nearby gradient is still nonzero -- \<open>F\<close> moves
  by at most a constant times the radius.  The \<open>p\<close>-variation is
  \<open>ell_op_lipschitz_in_p\<close> and the \<open>M\<close>-variation is \<open>ell_op_M_gap_abs\<close>.\<close>

theorem ell_op_ball_bound:
  fixes M :: "real^'n::finite^'n"
  assumes sym: "transpose M = M" and p: "p \<noteq> 0" and L: "1 \<le> L"
    and k: "1 \<le> k" "k < CARD('n)"
  shows "\<exists>C. 0 < C \<and> (\<forall>e w. 0 < e \<longrightarrow> e < norm p
      \<longrightarrow> w \<in> ball ((p :: real^'n), M) e
      \<longrightarrow> \<bar>ell_op k L (fst w) (snd w) - ell_op k L p M\<bar> \<le> C * e)"
proof -
  have L0: "0 \<le> L"
    using L by simp
  define Cm where "Cm = real (CARD('n) * CARD('n)) * L / 2"
  have Cm0: "0 \<le> Cm"
    unfolding Cm_def using L0 by simp
  obtain Cp where Cp0: "0 < Cp"
    and lipp: "\<And>p'. p' \<noteq> 0
      \<Longrightarrow> \<bar>ell_op k L p' M - ell_op k L p M\<bar> \<le> Cp * norm (p' - p)"
    using ell_op_lipschitz_in_p[OF sym p L k(1) k(2)] by blast
  define C where "C = Cp + Cm + 1"
  have C0: "0 < C"
    unfolding C_def using Cp0 Cm0 by simp
  show ?thesis
  proof (intro exI[of _ C] conjI allI impI C0)
    fix e :: real and w :: "(real^'n) \<times> (real^'n^'n)"
    assume e: "0 < e" and enp: "e < norm p" and w: "w \<in> ball ((p :: real^'n), M) e"
    have dp: "norm (fst w - p) < e"
    proof -
      have "dist (fst w) (fst ((p :: real^'n), M)) \<le> dist w ((p :: real^'n), M)"
        by (rule dist_fst_le)
      then have "dist (fst w) p \<le> dist w ((p :: real^'n), M)"
        by simp
      also have "\<dots> < e"
        using w by (simp add: dist_commute)
      finally show ?thesis
        by (simp add: dist_norm)
    qed
    have dM: "norm (M - snd w) \<le> e"
    proof -
      have "dist (snd w) (snd ((p :: real^'n), M)) \<le> dist w ((p :: real^'n), M)"
        by (rule dist_snd_le)
      then have "dist (snd w) M \<le> dist w ((p :: real^'n), M)"
        by simp
      also have "\<dots> < e"
        using w by (simp add: dist_commute)
      finally show ?thesis
        by (simp add: dist_norm norm_minus_commute)
    qed
    have wne: "fst w \<noteq> 0"
    proof
      assume z: "fst w = 0"
      have "norm p = norm (fst w - p)"
        unfolding z by simp
      also have "\<dots> < e"
        by (rule dp)
      finally show False
        using enp by simp
    qed
    have ne: "feasible k L (fst w) \<noteq> ({} :: (real^'n^'n) set)"
      by (rule feasible_nonempty[OF k(1) k(2) L])
    have g1: "\<bar>ell_op k L (fst w) (snd w) - ell_op k L (fst w) M\<bar> \<le> Cm * e"
    proof -
      have "\<bar>ell_op k L (fst w) (snd w) - ell_op k L (fst w) M\<bar>
          \<le> mgap L (snd w) M"
        by (rule ell_op_M_gap_abs[OF ne])
      also have "\<dots> = mgap L M (snd w)"
        by (rule mgap_commute)
      also have "\<dots> \<le> real (CARD('n) * CARD('n)) * norm (M - snd w) * L / 2"
        by (rule mgap_le_norm[OF L0])
      also have "\<dots> \<le> real (CARD('n) * CARD('n)) * e * L / 2"
        using dM L0 by (simp add: divide_right_mono mult_right_mono)
      also have "\<dots> = Cm * e"
        unfolding Cm_def by simp
      finally show ?thesis .
    qed
    have g2: "\<bar>ell_op k L (fst w) M - ell_op k L p M\<bar> \<le> Cp * e"
    proof -
      have "\<bar>ell_op k L (fst w) M - ell_op k L p M\<bar> \<le> Cp * norm (fst w - p)"
        by (rule lipp[OF wne])
      also have "\<dots> \<le> Cp * e"
        using dp Cp0 by (simp add: mult_left_mono)
      finally show ?thesis .
    qed
    have "\<bar>ell_op k L (fst w) (snd w) - ell_op k L p M\<bar>
        \<le> \<bar>ell_op k L (fst w) (snd w) - ell_op k L (fst w) M\<bar>
          + \<bar>ell_op k L (fst w) M - ell_op k L p M\<bar>"
      by simp
    also have "\<dots> \<le> Cm * e + Cp * e"
      using g1 g2 by simp
    also have "\<dots> \<le> C * e"
      unfolding C_def using e by (simp add: algebra_simps)
    finally show "\<bar>ell_op k L (fst w) (snd w) - ell_op k L p M\<bar> \<le> C * e" .
  qed
qed

text \<open>Both envelopes therefore collapse onto \<open>F\<close> away from the origin.  The
  radius is capped at \<open>norm p / 2\<close> so that every gradient in the ball is still
  nonzero, which is exactly where the estimate holds.\<close>

theorem ell_op_lsc_off_zero:
  fixes M :: "real^'n::finite^'n"
  assumes sym: "transpose M = M" and p: "p \<noteq> 0" and L: "1 \<le> L"
    and k: "1 \<le> k" "k < CARD('n)"
  shows "ell_op_lsc k L p M = ereal (ell_op k L p M)"
proof (rule antisym)
  show "ell_op_lsc k L p M \<le> ereal (ell_op k L p M)"
    by (rule ell_op_lsc_le_ell_op)
next
  obtain C where C0: "0 < C"
    and bnd: "\<And>e w. 0 < e \<Longrightarrow> e < norm p
      \<Longrightarrow> w \<in> ball ((p :: real^'n), M) e
      \<Longrightarrow> \<bar>ell_op k L (fst w) (snd w) - ell_op k L p M\<bar> \<le> C * e"
    using ell_op_ball_bound[OF sym p L k(1) k(2)] by blast
  have np: "0 < norm p"
    using p by simp
  show "ereal (ell_op k L p M) \<le> ell_op_lsc k L p M"
    unfolding ell_op_lsc_def
  proof (rule ball_env_ge_of_bound[OF C0 np])
    fix e w assume "0 < e" "e < norm p" "w \<in> ball (p, M) e"
    from bnd[OF this] show "ereal (ell_op k L p M - C * e) \<le> ell_op_pair k L w"
      by (simp add: ell_op_pair_def abs_le_iff)
  qed
qed

theorem ell_op_usc_off_zero:
  fixes M :: "real^'n::finite^'n"
  assumes sym: "transpose M = M" and p: "p \<noteq> 0" and L: "1 \<le> L"
    and k: "1 \<le> k" "k < CARD('n)"
  shows "ell_op_usc k L p M = ereal (ell_op k L p M)"
proof (rule antisym)
  obtain C where C0: "0 < C"
    and bnd: "\<And>e w. 0 < e \<Longrightarrow> e < norm p
      \<Longrightarrow> w \<in> ball ((p :: real^'n), M) e
      \<Longrightarrow> \<bar>ell_op k L (fst w) (snd w) - ell_op k L p M\<bar> \<le> C * e"
    using ell_op_ball_bound[OF sym p L k(1) k(2)] by blast
  have np: "0 < norm p"
    using p by simp
  show "ell_op_usc k L p M \<le> ereal (ell_op k L p M)"
    unfolding ell_op_usc_def
  proof (rule ball_env_le_of_bound[OF C0 np])
    fix e w assume "0 < e" "e < norm p" "w \<in> ball (p, M) e"
    from bnd[OF this] show "ell_op_pair k L w \<le> ereal (ell_op k L p M + C * e)"
      by (simp add: ell_op_pair_def abs_le_iff)
  qed
next
  show "ereal (ell_op k L p M) \<le> ell_op_usc k L p M"
    using ell_op_le_usc[of k L p M] by (simp add: ell_op_pair_def)
qed

text \<open>The continuity clause of Lemma 3.1: \<open>F\<^sub>* = F\<^sup>* = F\<close> off the origin.\<close>

corollary ell_op_envelopes_eq_off_zero:
  fixes M :: "real^'n::finite^'n"
  assumes sym: "transpose M = M" and p: "p \<noteq> 0" and L: "1 \<le> L"
    and k: "1 \<le> k" "k < CARD('n)"
  shows "ell_op_lsc k L p M = ereal (ell_op k L p M)"
    and "ell_op_usc k L p M = ereal (ell_op k L p M)"
    and "ell_op_lsc k L p M = ell_op_usc k L p M"
  using ell_op_lsc_off_zero[OF sym p L k(1) k(2)]
    ell_op_usc_off_zero[OF sym p L k(1) k(2)]
  by simp_all

subsection \<open>Towards Section 4: degenerate ellipticity of \<open>F\<close>\<close>

text \<open>Theorem 4.2 of the paper reaches its contradiction through Eq. (4.3),
  \<open>F(p\<^sub>\<epsilon>, M\<^sub>\<epsilon>) \<ge> F(p\<^sub>\<epsilon>, N\<^sub>\<epsilon>)\<close>, which is the degenerate ellipticity of \<open>F\<close>:
  adding a positive semidefinite matrix to the Hessian argument can only
  decrease \<open>F\<close>, since \<open>F\<close> is an infimum of \<open>-\<onehalf> tr(M a)\<close> over positive
  semidefinite \<open>a\<close>.  \<open>ell_op_pointwise_elliptic\<close> (@{theory Relative_Arbitrage_Equation.Elliptic_Operator})
  is the statement for a single \<open>a\<close>; passing to the infimum is what Section 4
  actually uses, and is proved here.\<close>

theorem ell_op_elliptic:
  fixes M Q :: "real^'n::finite^'n"
  assumes Q: "psd Q" and ne: "feasible k L p \<noteq> ({} :: (real^'n^'n) set)"
  shows "ell_op k L p (M + Q) \<le> ell_op k L p M"
  unfolding ell_op_def
proof (rule cInf_greatest)
  show "(\<lambda>a. - trace (M ** a) / 2) ` feasible k L p \<noteq> {}"
    using ne by simp
next
  fix x
  assume "x \<in> (\<lambda>a. - trace (M ** a) / 2) ` feasible k L p"
  then obtain a :: "real^'n^'n" where a: "a \<in> feasible k L p"
    and x: "x = - trace (M ** a) / 2"
    by blast
  have "Inf ((\<lambda>a. - trace ((M + Q) ** a) / 2) ` feasible k L p)
      \<le> - trace ((M + Q) ** a) / 2"
    by (intro cInf_lower imageI a ell_op_bdd_below)
  also have "\<dots> \<le> - trace (M ** a) / 2"
    by (rule ell_op_pointwise_elliptic[OF Q a])
  finally show "Inf ((\<lambda>a. - trace ((M + Q) ** a) / 2) ` feasible k L p) \<le> x"
    unfolding x .
qed

text \<open>In the ordering form Eq. (4.3) uses: if \<open>N - M\<close> is positive semidefinite
  (\<open>M \<preceq> N\<close>) then \<open>F(p, N) \<le> F(p, M)\<close>.\<close>

corollary ell_op_elliptic_le:
  fixes M N :: "real^'n::finite^'n"
  assumes psd: "psd (N - M)" and ne: "feasible k L p \<noteq> ({} :: (real^'n^'n) set)"
  shows "ell_op k L p N \<le> ell_op k L p M"
proof -
  have "N = M + (N - M)"
    by simp
  then have "ell_op k L p N = ell_op k L p (M + (N - M))"
    by simp
  also have "\<dots> \<le> ell_op k L p M"
    by (rule ell_op_elliptic[OF psd ne])
  finally show ?thesis .
qed

text \<open>Positive homogeneity of \<open>F\<close> in the matrix argument: with
  @{thm [source] feasible_scale}, this is the strict-perturbation mechanism, scaling
  a subsolution's jet to \<open>(\<theta> p, \<theta> X)\<close> and its value to
  \<open>\<theta> F(p,X) \<le> \<theta> < 1\<close>.\<close>

lemma ell_op_scaleR_matrix:
  fixes M :: "real^'n::finite^'n"
  assumes t: "0 < \<theta>" and ne: "feasible k L p \<noteq> ({} :: (real^'n^'n) set)"
  shows "ell_op k L p (\<theta> *\<^sub>R M) = \<theta> * ell_op k L p M"
proof -
  have pt: "- trace ((\<theta> *\<^sub>R M) ** a) / 2 = \<theta> * (- trace (M ** a) / 2)"
    for a :: "real^'n^'n"
  proof -
    have "(\<theta> *\<^sub>R M) ** a = \<theta> *\<^sub>R (M ** a)"
      by (rule scalar_matrix_assoc[symmetric])
    thus ?thesis by (simp add: trace_scaleR)
  qed
  have img: "(\<lambda>a. - trace ((\<theta> *\<^sub>R M) ** a) / 2) ` feasible k L p
      = (\<lambda>x. \<theta> * x) ` ((\<lambda>a. - trace (M ** a) / 2) ` feasible k L p)"
    unfolding image_image using pt by simp
  show ?thesis
    unfolding ell_op_def img
    by (rule cInf_mult_pos[OF t _ ell_op_bdd_below]) (use ne in simp)
qed

subsection \<open>Lemma 3.1\<close>

text \<open>Lemma 3.1 consists of:
  \<^item> \<open>F\<^sub>* \<le> F \<le> F\<^sup>*\<close> always (\<open>ell_op_lsc_le_ell_op\<close>, \<open>ell_op_le_ell_op_usc\<close>,
    above);
  \<^item> \<open>F\<^sub>*(0, M) = F(0, M)\<close> (\<open>ell_op_lsc_at_zero\<close>, above);
  \<^item> \<open>F(p, M) = -\<onehalf> bracket (n-k) L M\<^sub>p\<close> for \<open>p \<noteq> 0\<close>, i.e. Eq. (3.5)
    (\<open>ell_op_eq_half_bracket\<close>, @{theory Relative_Arbitrage_Equation.Operator_Formula});
  \<^item> \<open>F\<^sup>*(0, M) = eq36_rhs\<close>, i.e. Eq. (3.6) (\<open>eq36\<close>, above);
  \<^item> \<open>F\<^sub>* = F\<^sup>* = F\<close> off the origin (\<open>ell_op_envelopes_eq_off_zero\<close>, above).

  The general one-sided Poincare separation inequality
  \<open>\<lambda>\<^sub>(\<^sub>i\<^sub>)(M\<^sub>p) \<ge> \<lambda>\<^sub>(\<^sub>i\<^sub>+\<^sub>1\<^sub>)(M)\<close> for arbitrary \<open>p \<noteq> 0\<close> is \<open>poincare_separation\<close>
  (@{theory Relative_Arbitrage_Equation.Operator_Formula}); for \<open>p\<close> an eigenvector it is an equality
  (\<open>eigval_Mp_top_eigenvector\<close>).\<close>

(*<*)
end
(*>*)
