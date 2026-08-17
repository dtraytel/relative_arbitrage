
(*<*)
theory Operator_Envelopes
  imports Viscosity_Solutions "Symmetric_Matrix_Spectra.Householder_Rotation"
    "Semicontinuous_Analysis.Semicontinuity" "Semicontinuous_Analysis.Semicontinuous_Envelopes"
    "Continuous_Time_Martingales.Integrability_Criteria"
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

text \<open>\<open>ell_op_pair\<close> lives in @{theory Relative_Arbitrage.Viscosity_Definitions}.\<close>

section \<open>The semicontinuous envelopes \<open>F\<^sub>*\<close> and \<open>F\<^sup>*\<close>\<close>

text \<open>\<open>ell_op_lsc\<close>, \<open>ell_op_usc\<close> live in @{theory Relative_Arbitrage.Viscosity_Definitions}.\<close>

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

definition mgap :: "real \<Rightarrow> real^'n::finite^'n \<Rightarrow> real^'n^'n \<Rightarrow> real" where
  "mgap L M N = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j - N $ i $ j\<bar>) * L / 2"

lemma trace_mult_feasible_bound:
  fixes D :: "real^'n::finite^'n"
  assumes a: "a \<in> feasible k L p"
  shows "\<bar>trace (D ** a)\<bar> \<le> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>D $ i $ j\<bar>) * L"
proof -
  have tr: "trace (D ** a) = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. D $ i $ j * a $ j $ i)"
    by (simp add: trace_def matrix_matrix_mult_def)
  have inner_le: "\<bar>\<Sum>j\<in>(UNIV :: 'n set). D $ i $ j * a $ j $ i\<bar>
      \<le> (\<Sum>j\<in>(UNIV :: 'n set). \<bar>D $ i $ j\<bar>) * L" for i
  proof -
    have "\<bar>\<Sum>j\<in>(UNIV :: 'n set). D $ i $ j * a $ j $ i\<bar>
        \<le> (\<Sum>j\<in>(UNIV :: 'n set). \<bar>D $ i $ j * a $ j $ i\<bar>)"
      by (rule sum_abs)
    also have "\<dots> \<le> (\<Sum>j\<in>(UNIV :: 'n set). \<bar>D $ i $ j\<bar> * L)"
    proof (rule sum_mono)
      fix j :: 'n
      have "\<bar>D $ i $ j * a $ j $ i\<bar> = \<bar>D $ i $ j\<bar> * \<bar>a $ j $ i\<bar>"
        by (simp add: abs_mult)
      also have "\<dots> \<le> \<bar>D $ i $ j\<bar> * L"
        by (intro mult_left_mono feasible_entry_bound[OF a]) simp
      finally show "\<bar>D $ i $ j * a $ j $ i\<bar> \<le> \<bar>D $ i $ j\<bar> * L" .
    qed
    also have "\<dots> = (\<Sum>j\<in>(UNIV :: 'n set). \<bar>D $ i $ j\<bar>) * L"
      by (simp add: sum_distrib_right)
    finally show ?thesis .
  qed
  have "\<bar>(\<Sum>i\<in>(UNIV :: 'n set). \<Sum>j\<in>UNIV. D $ i $ j * a $ j $ i)\<bar>
      \<le> (\<Sum>i\<in>(UNIV :: 'n set). \<bar>\<Sum>j\<in>UNIV. D $ i $ j * a $ j $ i\<bar>)"
    by (rule sum_abs)
  also have "\<dots> \<le> (\<Sum>i\<in>(UNIV :: 'n set). (\<Sum>j\<in>UNIV. \<bar>D $ i $ j\<bar>) * L)"
    by (intro sum_mono inner_le)
  also have "\<dots> = (\<Sum>i\<in>(UNIV :: 'n set). \<Sum>j\<in>UNIV. \<bar>D $ i $ j\<bar>) * L"
    by (simp add: sum_distrib_right)
  finally show ?thesis
    unfolding tr .
qed

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
  proof -
    have gap: "- trace ((M - N) ** a) / 2 \<le> mgap L M N"
      using trace_mult_feasible_bound[OF a, of "M - N"]
      by (simp add: mgap_def)
    have "ell_op k L p M \<le> - trace (M ** a) / 2"
      unfolding ell_op_def
      by (intro cInf_lower imageI a ell_op_bdd_below)
    also have "- trace (M ** a) / 2
        = - trace (N ** a) / 2 + - trace ((M - N) ** a) / 2"
      using split[of a] by simp
    also have "\<dots> \<le> - trace (N ** a) / 2 + mgap L M N"
      using gap by simp
    finally show ?thesis .
  qed
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
proof -
  have entry: "\<bar>M $ i $ j - N $ i $ j\<bar> \<le> norm (M - N)" for i j
  proof -
    have "\<bar>M $ i $ j - N $ i $ j\<bar> = \<bar>(M - N) $ i $ j\<bar>"
      by simp
    also have "\<dots> \<le> norm ((M - N) $ i)"
      by (rule component_le_norm_cart)
    also have "\<dots> \<le> norm (M - N)"
      by (rule Finite_Cartesian_Product.norm_nth_le)
    finally show ?thesis .
  qed
  have "(\<Sum>i\<in>(UNIV :: 'n set). \<Sum>j\<in>UNIV. \<bar>M $ i $ j - N $ i $ j\<bar>)
      \<le> (\<Sum>i\<in>(UNIV :: 'n set). \<Sum>j\<in>(UNIV :: 'n set). norm (M - N))"
    by (intro sum_mono entry)
  also have "\<dots> = real (CARD('n) * CARD('n)) * norm (M - N)"
    by simp
  finally have "(\<Sum>i\<in>(UNIV :: 'n set). \<Sum>j\<in>UNIV. \<bar>M $ i $ j - N $ i $ j\<bar>)
      \<le> real (CARD('n) * CARD('n)) * norm (M - N)" .
  then show ?thesis
    unfolding mgap_def using L
    by (simp add: divide_right_mono mult_right_mono)
qed

lemma mgap_shift_id:
  fixes M :: "real^'n::finite^'n"
  assumes d: "0 \<le> \<delta>"
  shows "mgap L M (M + \<delta> *\<^sub>R mat 1) = \<delta> * real CARD('n) * L / 2"
    and "mgap L (M - \<delta> *\<^sub>R mat 1) M = \<delta> * real CARD('n) * L / 2"
proof -
  have row: "(\<Sum>j\<in>(UNIV::'n set). \<bar>\<delta> * (if i = j then 1 else 0)\<bar>) = \<delta>" for i
  proof -
    have "(\<Sum>j\<in>(UNIV::'n set). \<bar>\<delta> * (if i = j then 1 else 0)\<bar>)
        = (\<Sum>j\<in>(UNIV::'n set). if j = i then \<delta> else 0)"
      by (rule sum.cong) (use d in auto)
    also have "\<dots> = \<delta>" by simp
    finally show ?thesis .
  qed
  have s1: "(\<Sum>i\<in>(UNIV::'n set). \<Sum>j\<in>(UNIV::'n set).
        \<bar>M $ i $ j - (M + \<delta> *\<^sub>R mat 1) $ i $ j\<bar>) = \<delta> * real CARD('n)"
  proof -
    have "(\<Sum>i\<in>(UNIV::'n set). \<Sum>j\<in>(UNIV::'n set).
          \<bar>M $ i $ j - (M + \<delta> *\<^sub>R mat 1) $ i $ j\<bar>)
        = (\<Sum>i\<in>(UNIV::'n set). \<Sum>j\<in>(UNIV::'n set).
            \<bar>\<delta> * (if i = j then 1 else 0)\<bar>)"
      by (intro sum.cong refl) (simp add: mat_def)
    also have "\<dots> = (\<Sum>i\<in>(UNIV::'n set). \<delta>)"
      by (rule sum.cong[OF refl]) (rule row)
    finally show ?thesis by simp
  qed
  have s2: "(\<Sum>i\<in>(UNIV::'n set). \<Sum>j\<in>(UNIV::'n set).
        \<bar>(M - \<delta> *\<^sub>R mat 1) $ i $ j - M $ i $ j\<bar>) = \<delta> * real CARD('n)"
  proof -
    have "(\<Sum>i\<in>(UNIV::'n set). \<Sum>j\<in>(UNIV::'n set).
          \<bar>(M - \<delta> *\<^sub>R mat 1) $ i $ j - M $ i $ j\<bar>)
        = (\<Sum>i\<in>(UNIV::'n set). \<Sum>j\<in>(UNIV::'n set).
            \<bar>\<delta> * (if i = j then 1 else 0)\<bar>)"
      by (intro sum.cong refl) (simp add: mat_def)
    also have "\<dots> = (\<Sum>i\<in>(UNIV::'n set). \<delta>)"
      by (rule sum.cong[OF refl]) (rule row)
    finally show ?thesis by simp
  qed
  show "mgap L M (M + \<delta> *\<^sub>R mat 1) = \<delta> * real CARD('n) * L / 2"
    unfolding mgap_def s1 by simp
  show "mgap L (M - \<delta> *\<^sub>R mat 1) M = \<delta> * real CARD('n) * L / 2"
    unfolding mgap_def s2 by simp
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

text \<open>For a small enough shift, the upper envelope at \<open>-\<delta>I\<close> is below
  \<open>1\<close>, whatever the gradient.\<close>

lemma ell_op_usc_small_shift_lt_one:
  fixes k :: nat
  assumes k: "1 \<le> k" "k < CARD('n::finite)" and L: "1 \<le> L"
  obtains \<delta> :: real where "0 < \<delta>" and "\<delta> < 1"
    and "\<And>q :: real^'n.
      ell_op_usc k L q ((0::real^'n^'n) - \<delta> *\<^sub>R mat 1) < 1"
proof -
  define B where "B = real (CARD('n) * CARD('n)) * L / 2"
  have B0: "0 < B" unfolding B_def using L by simp
  define Nm where "Nm = norm (mat 1 :: real^'n^'n)"
  have Nm0: "0 \<le> Nm" unfolding Nm_def by simp
  define t where "t = 1 / (2 * B)"
  have t0: "0 < t" unfolding t_def using B0 by simp
  have Bt: "B * t = 1 / 2" unfolding t_def using B0 by simp
  define \<delta> where "\<delta> = min (1 / 2) (t / (2 * (Nm + 1)))"
  have d0: "0 < \<delta>" unfolding \<delta>_def using t0 Nm0 by simp
  have d1: "\<delta> < 1" unfolding \<delta>_def by simp
  have dN: "\<delta> * Nm \<le> t / 2"
  proof -
    have "\<delta> \<le> t / (2 * (Nm + 1))" unfolding \<delta>_def by simp
    then have "\<delta> * Nm \<le> t / (2 * (Nm + 1)) * Nm"
      by (rule mult_right_mono[OF _ Nm0])
    moreover have "t / (2 * (Nm + 1)) * Nm \<le> t / 2"
      using t0 Nm0 by (simp add: field_simps)
    ultimately show ?thesis by linarith
  qed
  have key: "ell_op_usc k L q ((0::real^'n^'n) - \<delta> *\<^sub>R mat 1) < 1"
    for q :: "real^'n"
  proof -
    have e0: "0 < t / 2" using t0 by simp
    have nrm: "norm ((0::real^'n^'n) - \<delta> *\<^sub>R mat 1) = \<delta> * Nm"
      unfolding Nm_def using d0 by simp
    have "ell_op_usc k L q ((0::real^'n^'n) - \<delta> *\<^sub>R mat 1)
        \<le> ereal (B * (norm ((0::real^'n^'n) - \<delta> *\<^sub>R mat 1) + t / 2))"
      unfolding B_def
      by (rule ell_op_usc_le_scaled_norm[OF k(1) k(2) L e0])
    also have "\<dots> = ereal (B * (\<delta> * Nm + t / 2))" unfolding nrm by (rule refl)
    also have "\<dots> \<le> ereal (B * t)"
    proof -
      have "\<delta> * Nm + t / 2 \<le> t" using dN by linarith
      then have "B * (\<delta> * Nm + t / 2) \<le> B * t"
        by (rule mult_left_mono) (use B0 in linarith)
      then show ?thesis by simp
    qed
    also have "\<dots> = ereal (1 / 2)" unfolding Bt by (rule refl)
    also have "\<dots> < 1" by simp
    finally show ?thesis .
  qed
  show ?thesis by (rule that[OF d0 d1]) (use key in blast)
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
  have bound: "ereal (ell_op k L (0 :: real^'n) M - C * e)
      \<le> (INF w \<in> ball ((0 :: real^'n), M) e. ell_op_pair k L w)" for e
  proof (rule INF_greatest)
    fix w :: "(real^'n) \<times> (real^'n^'n)"
    assume w: "w \<in> ball ((0 :: real^'n), M) e"
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
  proof (rule ereal_le_epsilon2)
    fix d :: real assume d: "0 < d"
    define e where "e = d / (2 * C)"
    have e_pos: "0 < e"
      using d C_pos by (simp add: e_def)
    have Ce: "C * e \<le> d"
      using C_pos d by (simp add: e_def)
    have "ereal (ell_op k L (0 :: real^'n) M - d)
        \<le> ereal (ell_op k L (0 :: real^'n) M - C * e)"
      using Ce by simp
    also have "\<dots> \<le> (INF w \<in> ball ((0 :: real^'n), M) e. ell_op_pair k L w)"
      by (rule bound)
    also have "\<dots> \<le> ell_op_lsc k L (0 :: real^'n) M"
      unfolding ell_op_lsc_def using e_pos by (intro SUP_upper) simp
    finally have le: "ereal (ell_op k L (0 :: real^'n) M - d)
        \<le> ell_op_lsc k L (0 :: real^'n) M" .
    have "ereal (ell_op k L (0 :: real^'n) M)
        = ereal (ell_op k L (0 :: real^'n) M - d) + ereal d"
      by simp
    also have "\<dots> \<le> ell_op_lsc k L (0 :: real^'n) M + ereal d"
      using le by (rule add_right_mono)
    finally show "ereal (ell_op k L (0 :: real^'n) M)
        \<le> ell_op_lsc k L 0 M + ereal d" .
  qed
qed

text \<open>At the degenerate gradient, the subsolution inequality of
  Definition 3.1 and the envelope-free one coincide: \<open>F\<^sub>*(0,H) \<le> 1\<close> and
  \<open>F(0,H) \<le> 1\<close> are the same condition.\<close>

corollary ell_op_lsc_at_zero_iff:
  fixes M :: "real^'n::finite^'n"
  assumes k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L"
  shows "ell_op_lsc k L (0 :: real^'n) M \<le> 1 \<longleftrightarrow> ell_op k L (0 :: real^'n) M \<le> 1"
  unfolding ell_op_lsc_at_zero[OF k L] by (simp add: one_ereal_def)

section \<open>Definition 3.1 in envelope form\<close>

text \<open>\<open>visc_subsol_env\<close>, \<open>visc_supersol_env\<close>, \<open>visc_sol_env\<close> live in @{theory Relative_Arbitrage.Viscosity_Definitions}.\<close>

section \<open>The envelope-free notions are the stronger ones\<close>

text \<open>Two reasons: \<open>F\<^sub>* \<le> F \<le> F\<^sup>*\<close> makes the envelope inequalities weaker
  at each test function, and a global maximum over \<open>K\<close> is in particular a
  local maximum on any ball around \<open>x\<close> that stays inside \<open>K\<close>, so the
  envelope notion constrains fewer test functions.\<close>

lemma visc_subsol_imp_env:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes sub: "visc_subsol k L \<Omega> u" and sub_K: "\<Omega> \<subseteq> K" and op: "open \<Omega>"
  shows "visc_subsol_env k L K \<Omega> u"
  unfolding visc_subsol_env_def
proof (intro ballI allI impI)
  fix x :: "real^'n" and \<phi> g and H :: "real^'n^'n"
  assume x: "x \<in> \<Omega>" and tf: "test_fun_at \<phi> g H x"
    and gmax: "\<forall>y\<in>K. u y - \<phi> y \<le> u x - \<phi> x"
  obtain e where e: "0 < e" "ball x e \<subseteq> \<Omega>"
    using openE[OF op x] by blast
  have loc: "\<exists>e>0. \<forall>y \<in> ball x e. u y - \<phi> y \<le> u x - \<phi> x"
  proof (intro exI[of _ e] conjI ballI e(1))
    fix y :: "real^'n" assume "y \<in> ball x e"
    with e(2) sub_K have "y \<in> K" by blast
    with gmax show "u y - \<phi> y \<le> u x - \<phi> x" by blast
  qed
  have "ell_op k L (g x) H \<le> 1"
    using sub x tf loc unfolding visc_subsol_def by blast
  then have "ereal (ell_op k L (g x) H) \<le> 1"
    by simp
  with ell_op_lsc_le_ell_op[of k L "g x" H] show "ell_op_lsc k L (g x) H \<le> 1"
    by (rule order_trans)
qed

lemma visc_supersol_imp_env:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes sup: "visc_supersol k L \<Omega> u" and sub_K: "\<Omega> \<subseteq> K" and op: "open \<Omega>"
  shows "visc_supersol_env k L K \<Omega> u"
  unfolding visc_supersol_env_def
proof (intro ballI allI impI)
  fix x :: "real^'n" and \<phi> g and H :: "real^'n^'n"
  assume x: "x \<in> \<Omega>" and tf: "test_fun_at \<phi> g H x"
    and gmin: "\<forall>y\<in>K. u x - \<phi> x \<le> u y - \<phi> y"
  obtain e where e: "0 < e" "ball x e \<subseteq> \<Omega>"
    using openE[OF op x] by blast
  have loc: "\<exists>e>0. \<forall>y \<in> ball x e. u x - \<phi> x \<le> u y - \<phi> y"
  proof (intro exI[of _ e] conjI ballI e(1))
    fix y :: "real^'n" assume "y \<in> ball x e"
    with e(2) sub_K have "y \<in> K" by blast
    with gmin show "u x - \<phi> x \<le> u y - \<phi> y" by blast
  qed
  have "1 \<le> ell_op k L (g x) H"
    using sup x tf loc unfolding visc_supersol_def by blast
  then have "(1 :: ereal) \<le> ereal (ell_op k L (g x) H)"
    by simp
  then show "1 \<le> ell_op_usc k L (g x) H"
    using ell_op_le_ell_op_usc[of k L "g x" H] by (rule order_trans)
qed

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

subsection \<open>\<open>F\<^sup>* = F\<close> away from the origin\<close>

text \<open>Feasibility depends on the gradient only through its direction, so the
  rotation carrying \<open>p\<close>'s direction to \<open>p'\<close>'s carries the whole feasible
  set across.  A near-optimal witness for \<open>(p, M)\<close> then supplies a
  competitor for every nearby \<open>(p', M')\<close>, and continuity of the pairing
  bounds the supremum defining the upper envelope by \<open>F(p, M) + \<epsilon>\<close>.\<close>

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

lemma ell_op_bdd:
  fixes p :: "real^'n::finite" and M :: "real^'n^'n"
  assumes L0: "0 \<le> L"
  shows "bdd_below ((\<lambda>a. - trace (M ** a) / 2) ` feasible k L p)"
proof (rule bdd_belowI[of _
    "- ((\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>) * L) / 2"])
  fix v assume "v \<in> (\<lambda>a. - trace (M ** a) / 2) ` feasible k L p"
  then obtain a where aF: "a \<in> feasible k L p"
    and ve: "v = - trace (M ** a) / 2" by auto
  have tr: "trace (M ** a)
      = (\<Sum>i\<in>(UNIV :: 'n set). \<Sum>l\<in>(UNIV :: 'n set).
          M $ i $ l * a $ l $ i)"
    by (simp add: trace_def matrix_matrix_mult_def)
  have "trace (M ** a)
      \<le> (\<Sum>i\<in>(UNIV :: 'n set). \<Sum>l\<in>(UNIV :: 'n set).
          \<bar>M $ i $ l\<bar> * L)"
    unfolding tr
  proof (rule sum_mono)
    fix i :: 'n assume "i \<in> (UNIV :: 'n set)"
    show "(\<Sum>l\<in>(UNIV :: 'n set). M $ i $ l * a $ l $ i)
        \<le> (\<Sum>l\<in>(UNIV :: 'n set). \<bar>M $ i $ l\<bar> * L)"
    proof (rule sum_mono)
      fix l :: 'n assume "l \<in> (UNIV :: 'n set)"
      have "M $ i $ l * a $ l $ i \<le> \<bar>M $ i $ l * a $ l $ i\<bar>"
        by simp
      also have "\<dots> = \<bar>M $ i $ l\<bar> * \<bar>a $ l $ i\<bar>"
        by (simp add: abs_mult)
      also have "\<dots> \<le> \<bar>M $ i $ l\<bar> * L"
        by (rule mult_left_mono[OF feasible_offdiag_abs_le[OF aF]]) simp
      finally show "M $ i $ l * a $ l $ i \<le> \<bar>M $ i $ l\<bar> * L" .
    qed
  qed
  also have "(\<Sum>i\<in>(UNIV :: 'n set). \<Sum>l\<in>(UNIV :: 'n set).
        \<bar>M $ i $ l\<bar> * L)
      = (\<Sum>i\<in>(UNIV :: 'n set). \<Sum>j\<in>(UNIV :: 'n set).
          \<bar>M $ i $ j\<bar>) * L"
    by (simp add: sum_distrib_right)
  finally have "trace (M ** a)
      \<le> (\<Sum>i\<in>(UNIV :: 'n set). \<Sum>j\<in>(UNIV :: 'n set).
          \<bar>M $ i $ j\<bar>) * L" .
  then show "- ((\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>) * L) / 2
      \<le> v"
    unfolding ve by linarith
qed

lemma ell_op_le_witness:
  fixes p :: "real^'n::finite" and M :: "real^'n^'n"
  assumes L0: "0 \<le> L" and aF: "a \<in> feasible k L p"
  shows "ell_op k L p M \<le> - trace (M ** a) / 2"
  unfolding ell_op_def
  by (rule cInf_lower[OF _ ell_op_bdd[OF L0]]) (use aF in auto)

lemma ell_op_approx:
  fixes p :: "real^'n::finite" and M :: "real^'n^'n"
  assumes k1: "1 \<le> k" and kn: "k < CARD('n)" and L1: "1 \<le> L"
    and e0: "0 < \<epsilon>"
  obtains a where "a \<in> feasible k L p"
    and "- trace (M ** a) / 2 < ell_op k L p M + \<epsilon>"
proof -
  have L0: "0 \<le> L" using L1 by linarith
  have ne: "(\<lambda>a. - trace (M ** a) / 2) ` feasible k L p \<noteq> {}"
    using feasible_nonempty[OF k1 kn L1] by blast
  have bdd: "bdd_below ((\<lambda>a. - trace (M ** a) / 2) ` feasible k L p)"
    by (rule ell_op_bdd[OF L0])
  have "ell_op k L p M < ell_op k L p M + \<epsilon>" using e0 by simp
  then have "\<exists>v \<in> (\<lambda>a. - trace (M ** a) / 2) ` feasible k L p.
      v < ell_op k L p M + \<epsilon>"
    unfolding ell_op_def using cInf_less_iff[OF ne bdd] by blast
  then obtain a where a1: "a \<in> feasible k L p"
    and a2: "- trace (M ** a) / 2 < ell_op k L p M + \<epsilon>" by blast
  show ?thesis by (rule that[OF a1 a2])
qed

theorem ell_op_usc_le_at_nonzero:
  fixes p :: "real^'n::finite" and M :: "real^'n^'n"
  assumes k1: "1 \<le> k" and kn: "k < CARD('n)" and L1: "1 \<le> L"
    and p0: "p \<noteq> 0"
  shows "ell_op_usc k L p M \<le> ereal (ell_op k L p M)"
proof (rule ereal_le_epsilon)
  have L0: "0 \<le> L" using L1 by linarith
  fix ee :: ereal assume ee0: "0 < ee"
  show "ell_op_usc k L p M \<le> ereal (ell_op k L p M) + ee"
  proof (cases ee)
    case (real r)
    have r0: "0 < r" using ee0 unfolding real by simp
    define u where "u = p /\<^sub>R norm p"
    have np: "0 < norm p" using p0 by simp
    have u1: "norm u = 1" unfolding u_def using np by simp
    have u0: "u \<noteq> 0" using u1 by auto
    have uu: "u \<bullet> u = 1" using u1 by (metis norm_eq_1)
    have pu: "p = norm p *\<^sub>R u" unfolding u_def using np by simp
    have hp: "0 < u \<bullet> p"
    proof -
      have "u \<bullet> p = u \<bullet> (norm p *\<^sub>R u)" using pu by simp
      also have "\<dots> = norm p * (u \<bullet> u)" by simp
      finally show ?thesis unfolding uu using np by simp
    qed
    obtain a where aF: "a \<in> feasible k L p"
      and aval: "- trace (M ** a) / 2 < ell_op k L p M + r / 2"
      by (rule ell_op_approx[OF k1 kn L1 half_gt_zero[OF r0]])
    define W where "W = {z :: (real^'n) \<times> (real^'n^'n). 0 < u \<bullet> fst z}"
    have cfst: "continuous_on A (\<lambda>z :: (real^'n) \<times> (real^'n^'n). fst z)"
      for A by (intro continuous_on_fst continuous_on_id)
    have csnd: "continuous_on A (\<lambda>z :: (real^'n) \<times> (real^'n^'n). snd z)"
      for A by (intro continuous_on_snd continuous_on_id)
    have Wopen: "open W"
    proof -
      have "continuous_on UNIV (\<lambda>z :: (real^'n) \<times> (real^'n^'n). u \<bullet> fst z)"
        by (rule continuous_on_compose2[OF
            linear_continuous_on[OF bounded_linear_inner_right] cfst]) auto
      then show ?thesis unfolding W_def
        by (rule open_Collect_less[OF continuous_on_const])
    qed
    have WpM: "(p, M) \<in> W" unfolding W_def using hp by simp
    define Rm where "Rm = (\<lambda>z :: (real^'n) \<times> (real^'n^'n).
        rotv u (fst z /\<^sub>R norm (fst z)))"
    have cR: "continuous_on W Rm"
    proof -
      have img: "fst z \<in> {q :: real^'n. 0 < u \<bullet> q}" if "z \<in> W" for z
        using that unfolding W_def by simp
      show ?thesis
        unfolding Rm_def
        by (rule continuous_on_compose2[OF
            continuous_on_rotv_dir[OF u1] cfst]) (use img in auto)
    qed
    define G where "G = (\<lambda>z :: (real^'n) \<times> (real^'n^'n).
        - trace (snd z ** (Rm z ** a ** transpose (Rm z))) / 2)"
    have cG: "continuous_on W G"
    proof -
      have "continuous_on W
          (\<lambda>z. trace (snd z ** (Rm z ** a ** transpose (Rm z))))"
        by (rule continuous_on_conj_trace[OF cR csnd])
      then show ?thesis unfolding G_def by (intro continuous_intros) auto
    qed
    have GpM: "G (p, M) = - trace (M ** a) / 2"
    proof -
      have "fst ((p, M) :: (real^'n) \<times> (real^'n^'n))
          /\<^sub>R norm (fst ((p, M) :: (real^'n) \<times> (real^'n^'n))) = u"
        unfolding u_def by simp
      then have "Rm (p, M) = rotv u u" unfolding Rm_def by simp
      also have "\<dots> = mat 1" by (rule rotv_self[OF u0])
      finally have R1: "Rm (p, M) = mat 1" .
      have "mat 1 ** a ** transpose (mat 1) = a"
        by simp
      then show ?thesis unfolding G_def R1 by simp
    qed
    have isG: "isCont G (p, M)"
      using continuous_on_interior[OF cG] WpM Wopen by (simp add: interior_open)
    obtain d1 where d10: "0 < d1"
      and d1W: "ball ((p, M) :: (real^'n) \<times> (real^'n^'n)) d1 \<subseteq> W"
      using Wopen WpM unfolding open_contains_ball by blast
    obtain d2 where d20: "0 < d2"
      and d2G: "\<And>z. dist z ((p, M) :: (real^'n) \<times> (real^'n^'n)) < d2
          \<Longrightarrow> dist (G z) (G (p, M)) < r / 2"
      using isG[unfolded continuous_at_eps_delta] half_gt_zero[OF r0] by blast
    define e where "e = min d1 d2"
    have e0': "0 < e" unfolding e_def using d10 d20 by simp
    have main: "ell_op_pair k L z \<le> ereal (ell_op k L p M + r)"
      if zb: "z \<in> ball ((p, M) :: (real^'n) \<times> (real^'n^'n)) e" for z
    proof -
      have dz: "dist ((p, M) :: (real^'n) \<times> (real^'n^'n)) z < e"
        using zb by simp
      have zW: "z \<in> W"
      proof -
        have "dist ((p, M) :: (real^'n) \<times> (real^'n^'n)) z < d1"
          using dz unfolding e_def by simp
        then have "z \<in> ball ((p, M) :: (real^'n) \<times> (real^'n^'n)) d1"
          by simp
        then show ?thesis using d1W by blast
      qed
      have Gle: "G z < G (p, M) + r / 2"
      proof -
        have "dist z ((p, M) :: (real^'n) \<times> (real^'n^'n)) < d2"
          using dz unfolding e_def by (simp add: dist_commute)
        then have "dist (G z) (G (p, M)) < r / 2" by (rule d2G)
        then have "\<bar>G z - G (p, M)\<bar> < r / 2" by (simp add: dist_real_def)
        then have "G z - G (p, M) < r / 2" using abs_less_iff by blast
        then show ?thesis by linarith
      qed
      obtain p' M' where zeq: "z = (p', M')" by (cases z)
      have hp': "0 < u \<bullet> p'" using zW unfolding W_def zeq by simp
      have p'0: "p' \<noteq> 0" using hp' by auto
      have np': "0 < norm p'" using p'0 by simp
      define v where "v = p' /\<^sub>R norm p'"
      have v1: "norm v = 1" unfolding v_def using np' by simp
      have neuv: "u + v \<noteq> 0"
        unfolding v_def by (rule halfspace_not_antipodal[OF u1 hp'])
      define R where "R = rotv u v"
      have Rorth: "transpose R ** R = mat 1" and Rorth': "R ** transpose R = mat 1"
        using rotv_orthogonal[of u v] unfolding R_def orthogonal_matrix_def by blast+
      have Ru: "R *v u = v" unfolding R_def by (rule rotv_apply[OF u1 v1 neuv])
      have Rp: "R *v p = (norm p / norm p') *\<^sub>R p'"
      proof -
        have "R *v p = R *v (norm p *\<^sub>R u)" using pu by simp
        also have "\<dots> = norm p *\<^sub>R (R *v u)"
          by (simp add: matrix_vector_mult_scaleR)
        also have "\<dots> = norm p *\<^sub>R v" unfolding Ru by (rule refl)
        also have "\<dots> = (norm p / norm p') *\<^sub>R p'"
          unfolding v_def using np' by (simp add: divide_inverse)
        finally show ?thesis .
      qed
      have aF': "R ** a ** transpose R \<in> feasible k L p'"
      proof -
        have c1: "R ** a ** transpose R \<in> feasible k L (R *v p)"
          by (rule feasible_conj[OF Rorth Rorth' aF])
        have c2: "feasible k L (R *v p) = feasible k L p'"
          unfolding Rp by (rule feasible_scale) (use np np' in simp)
        show ?thesis using c1 unfolding c2 .
      qed
      have Gz: "- trace (M' ** (R ** a ** transpose R)) / 2 = G z"
        unfolding G_def zeq Rm_def R_def v_def by simp
      have "ell_op k L p' M' \<le> - trace (M' ** (R ** a ** transpose R)) / 2"
        by (rule ell_op_le_witness[OF L0 aF'])
      then have "ell_op k L p' M' \<le> G z" unfolding Gz .
      then have "ell_op k L p' M' < ell_op k L p M + r"
        using Gle aval unfolding GpM by linarith
      then show ?thesis unfolding ell_op_pair_def zeq by simp
    qed
    have sup_le: "(SUP w \<in> ball ((p, M) :: (real^'n) \<times> (real^'n^'n)) e.
        ell_op_pair k L w) \<le> ereal (ell_op k L p M + r)"
      by (rule SUP_least) (use main in blast)
    have inf_le: "ell_op_usc k L p M
        \<le> (SUP w \<in> ball ((p, M) :: (real^'n) \<times> (real^'n^'n)) e.
            ell_op_pair k L w)"
      unfolding ell_op_usc_def by (rule INF_lower) (use e0' in simp)
    have "ell_op_usc k L p M \<le> ereal (ell_op k L p M + r)"
      using inf_le sup_le by simp
    then show ?thesis unfolding real by simp
  next
    case PInf
    then show ?thesis by simp
  next
    case MInf
    then show ?thesis using ee0 by simp
  qed
qed

subsection \<open>From a global touching over \<open>K\<close> to a local one\<close>

text \<open>Definition 3.1 constrains only test functions with a global touching
  over \<open>K\<close>, while Crandall--Ishii machinery produces local touchings from
  jet data.  The gap closes by subtracting a quartic
  \<open>\<psi> := \<phi> - C\<bar>z - x\<bar>\<^sup>4\<close>: it shares \<open>\<phi>\<close>'s two-jet at \<open>x\<close>, only deepens
  the touching inside the ball, and outside it is bounded below by
  \<open>Cr\<^sup>4\<close>, which for large \<open>C\<close> overwhelms the oscillation of \<open>w - \<phi>\<close> on
  \<open>K\<close>.  The two boundedness hypotheses are what a genuine \<open>C\<^sup>2\<close> test
  function on compact \<open>K\<close> supplies; \<^const>\<open>test_fun_at\<close> alone would
  tolerate truncating \<open>\<phi>\<close> far from \<open>x\<close>.\<close>

text \<open>A test function is minorised near \<open>x\<close> by its two-jet quadratic,
  once the Hessian is shifted down by any \<open>\<delta> > 0\<close>, which lets a touching
  by an arbitrary test function be replaced by a touching by a genuine
  quadratic, bounded on a bounded set.\<close>

lemma test_fun_quadratic_minorates:
  fixes \<phi> :: "real^'n::finite \<Rightarrow> real" and g :: "real^'n \<Rightarrow> real^'n"
    and H :: "real^'n^'n" and x :: "real^'n" and \<delta> :: real
  assumes tf: "test_fun_at \<phi> g H x" and d0: "0 < \<delta>"
  obtains r where "0 < r"
    and "\<And>z. z \<in> ball x r \<Longrightarrow>
      \<phi> x + g x \<bullet> (z - x)
        + ((z - x) \<bullet> ((H - \<delta> *\<^sub>R mat 1) *v (z - x))) / 2 \<le> \<phi> z"
proof -
  have dg: "(g has_derivative (\<lambda>h. H *v h)) (at x)"
    using tf unfolding test_fun_at_def by blast
  obtain e where e0: "0 < e"
    and dphi: "\<And>y. y \<in> ball x e \<Longrightarrow> (\<phi> has_derivative (\<lambda>h. g y \<bullet> h)) (at y)"
    using tf unfolding test_fun_at_def by blast
  have "\<forall>e>0. \<exists>d>0. \<forall>y. norm (y - x) < d \<longrightarrow>
      norm (g y - g x - (H *v (y - x))) \<le> e * norm (y - x)"
    using dg unfolding has_derivative_at_alt by blast
  moreover have "0 < \<delta> / 2" using d0 by simp
  ultimately obtain d where dd: "0 < d"
    and bnd: "\<And>y. norm (y - x) < d \<Longrightarrow>
        norm (g y - g x - (H *v (y - x))) \<le> (\<delta> / 2) * norm (y - x)"
    by blast
  define r where "r = min e d"
  have r0: "0 < r" using e0 dd by (simp add: r_def)
  have main: "\<phi> x + g x \<bullet> (z - x)
      + ((z - x) \<bullet> ((H - \<delta> *\<^sub>R mat 1) *v (z - x))) / 2 \<le> \<phi> z"
    if z: "z \<in> ball x r" for z
  proof -
    define v where "v = z - x"
    have nv: "norm v < r"
      using z by (simp add: v_def dist_norm norm_minus_commute)
    define A where "A = g x \<bullet> v"
    define B where "B = v \<bullet> ((H - \<delta> *\<^sub>R mat 1) *v v)"
    define f where "f t = (\<phi> x + t * A + t\<^sup>2 * B / 2) - \<phi> (x + t *\<^sub>R v)" for t
    have f0: "f 0 = 0" by (simp add: f_def)
    have deriv: "\<exists>y. (f has_field_derivative y) (at t) \<and> y \<le> 0"
      if t: "0 \<le> t" "t \<le> 1" for t
    proof -
      have ntv: "norm (t *\<^sub>R v) \<le> norm v"
        using t by (simp add: mult_left_le_one_le)
      have mem: "x + t *\<^sub>R v \<in> ball x e"
        using ntv nv by (simp add: dist_norm r_def)
      have d1: "((\<lambda>t. \<phi> (x + t *\<^sub>R v)) has_field_derivative
          g (x + t *\<^sub>R v) \<bullet> v) (at t)"
      proof -
        have i1: "((\<lambda>t :: real. x + t *\<^sub>R v) has_derivative (\<lambda>h. h *\<^sub>R v)) (at t)"
          by (auto intro!: derivative_eq_intros)
        have i2: "(\<phi> has_derivative (\<lambda>h. g (x + t *\<^sub>R v) \<bullet> h)) (at (x + t *\<^sub>R v))"
          by (rule dphi[OF mem])
        have "((\<lambda>t. \<phi> (x + t *\<^sub>R v)) has_derivative
            (\<lambda>h. g (x + t *\<^sub>R v) \<bullet> (h *\<^sub>R v))) (at t)"
          using diff_chain_at[OF i1 i2] by (simp add: o_def)
        then show ?thesis
          by (rule has_derivative_imp_has_field_derivative)
            (simp add: ac_simps)
      qed
      have d2: "((\<lambda>t. \<phi> x + t * A + t\<^sup>2 * B / 2) has_field_derivative
          A + t * B) (at t)"
        by (auto intro!: derivative_eq_intros)
      have df: "(f has_field_derivative
          ((A + t * B) - g (x + t *\<^sub>R v) \<bullet> v)) (at t)"
        unfolding f_def by (rule DERIV_diff[OF d2 d1])
      have expand: "(A + t * B) - g (x + t *\<^sub>R v) \<bullet> v
          = - ((g (x + t *\<^sub>R v) - g x - (H *v (t *\<^sub>R v))) \<bullet> v)
            - t * (\<delta> * (v \<bullet> v))"
      proof -
        have m1: "(H - \<delta> *\<^sub>R mat 1) *v v = H *v v - \<delta> *\<^sub>R v"
          by (simp add: matrix_vector_mult_diff_rdistrib scaleR_matrix_vector
              )
        have m2: "H *v (t *\<^sub>R v) = t *\<^sub>R (H *v v)"
          by (simp add: matrix_vector_mult_scaleR)
        show ?thesis
          unfolding A_def B_def m1 m2
          by (simp add: inner_commute
              algebra_simps)
      qed
      have small: "- ((g (x + t *\<^sub>R v) - g x - (H *v (t *\<^sub>R v))) \<bullet> v)
          \<le> (\<delta> / 2) * (t * norm v) * norm v"
      proof -
        have "norm (t *\<^sub>R v) < d"
          using ntv nv by (simp add: r_def)
        moreover have "(x + t *\<^sub>R v) - x = t *\<^sub>R v" by simp
        ultimately have nb: "norm (g (x + t *\<^sub>R v) - g x - (H *v (t *\<^sub>R v)))
            \<le> (\<delta> / 2) * norm (t *\<^sub>R v)"
          using bnd[of "x + t *\<^sub>R v"] by simp
        have "- ((g (x + t *\<^sub>R v) - g x - (H *v (t *\<^sub>R v))) \<bullet> v)
            = (- (g (x + t *\<^sub>R v) - g x - (H *v (t *\<^sub>R v)))) \<bullet> v"
          by (metis inner_minus_left)
        also have "\<dots> \<le> norm (- (g (x + t *\<^sub>R v) - g x - (H *v (t *\<^sub>R v))))
            * norm v"
          by (rule norm_cauchy_schwarz)
        also have "\<dots> = norm (g (x + t *\<^sub>R v) - g x - (H *v (t *\<^sub>R v)))
            * norm v"
          by (metis norm_minus_cancel)
        also have "\<dots> \<le> ((\<delta> / 2) * norm (t *\<^sub>R v)) * norm v"
          by (rule mult_right_mono[OF nb norm_ge_zero])
        also have "\<dots> = (\<delta> / 2) * (t * norm v) * norm v"
          using t by simp
        finally show ?thesis .
      qed
      have vv: "v \<bullet> v = norm v * norm v"
        by (simp add: dot_square_norm power2_eq_square)
      have "(A + t * B) - g (x + t *\<^sub>R v) \<bullet> v
          \<le> (\<delta> / 2) * (t * norm v) * norm v - t * (\<delta> * (norm v * norm v))"
        unfolding expand vv by (rule diff_right_mono[OF small])
      also have "\<dots> = - (\<delta> / 2) * t * (norm v * norm v)"
        by (simp add: field_simps)
      also have "\<dots> \<le> 0"
        using d0 t by simp
      finally show ?thesis using df by blast
    qed
    have "f 1 \<le> f 0"
      by (rule DERIV_nonpos_imp_nonincreasing[of 0 1 f])
        (use deriv in auto)
    then have "\<phi> x + 1 * A + 1\<^sup>2 * B / 2 \<le> \<phi> (x + 1 *\<^sub>R v)"
      using f0 by (simp add: f_def)
    then show ?thesis by (simp add: v_def A_def B_def)
  qed
  show ?thesis by (rule that[OF r0 main])
qed

text \<open>\<open>inner_scaleR_diff_eq\<close> lives in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


lemma quartic_coeff_assoc:
  fixes c u w :: real
  shows "c * (2 * u * (2 * w)) = 4 * c * u * w"
  by (simp add: field_simps)

text \<open>\<open>transpose_shift_add\<close>, \<open>transpose_shift_diff\<close> live in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


lemma test_fun_at_quartic_shift:
  fixes \<phi> :: "real^'n::finite \<Rightarrow> real" and g :: "real^'n \<Rightarrow> real^'n"
    and H :: "real^'n^'n" and x :: "real^'n" and C :: real
  assumes tf: "test_fun_at \<phi> g H x"
  shows "test_fun_at (\<lambda>z. \<phi> z - C * ((z - x) \<bullet> (z - x))\<^sup>2)
      (\<lambda>z. g z - (4 * C * ((z - x) \<bullet> (z - x))) *\<^sub>R (z - x)) H x"
  unfolding test_fun_at_def
proof (intro conjI)
  show "transpose H = H" using tf unfolding test_fun_at_def by blast
next
  obtain e where e0: "0 < e"
    and dphi: "\<And>y. y \<in> ball x e \<Longrightarrow> (\<phi> has_derivative (\<lambda>h. g y \<bullet> h)) (at y)"
    using tf unfolding test_fun_at_def by blast
  have main: "((\<lambda>z. \<phi> z - C * ((z - x) \<bullet> (z - x))\<^sup>2) has_derivative
      (\<lambda>h. (g y - (4 * C * ((y - x) \<bullet> (y - x))) *\<^sub>R (y - x)) \<bullet> h)) (at y)"
    if y: "y \<in> ball x e" for y
  proof -
    have d1: "(\<phi> has_derivative (\<lambda>h. g y \<bullet> h)) (at y)" by (rule dphi[OF y])
    have d2: "((\<lambda>z :: real^'n. C * ((z - x) \<bullet> (z - x))\<^sup>2) has_derivative
        (\<lambda>h. C * (2 * ((y - x) \<bullet> (y - x)) * (2 * ((y - x) \<bullet> h))))) (at y)"
      by (auto intro!: derivative_eq_intros simp: inner_commute)
    have d3: "((\<lambda>z. \<phi> z - C * ((z - x) \<bullet> (z - x))\<^sup>2) has_derivative
        (\<lambda>h. g y \<bullet> h
          - C * (2 * ((y - x) \<bullet> (y - x)) * (2 * ((y - x) \<bullet> h))))) (at y)"
      by (rule has_derivative_diff[OF d1 d2])
    have d4: "(\<lambda>h. g y \<bullet> h
          - C * (2 * ((y - x) \<bullet> (y - x)) * (2 * ((y - x) \<bullet> h))))
        = (\<lambda>h. (g y - (4 * C * ((y - x) \<bullet> (y - x))) *\<^sub>R (y - x)) \<bullet> h)"
    proof (rule ext)
      fix h :: "real^'n"
      show "g y \<bullet> h - C * (2 * ((y - x) \<bullet> (y - x)) * (2 * ((y - x) \<bullet> h)))
          = (g y - (4 * C * ((y - x) \<bullet> (y - x))) *\<^sub>R (y - x)) \<bullet> h"
        unfolding quartic_coeff_assoc by (rule inner_scaleR_diff_eq)
    qed
    show ?thesis using d3 unfolding d4 .
  qed
  show "\<exists>e>0. \<forall>y \<in> ball x e.
      ((\<lambda>z. \<phi> z - C * ((z - x) \<bullet> (z - x))\<^sup>2) has_derivative
        (\<lambda>h. (g y - (4 * C * ((y - x) \<bullet> (y - x))) *\<^sub>R (y - x)) \<bullet> h)) (at y)"
    using e0 main by blast
next
  have dg: "(g has_derivative (\<lambda>h. H *v h)) (at x)"
    using tf unfolding test_fun_at_def by blast
  have dq: "((\<lambda>z :: real^'n. (4 * C * ((z - x) \<bullet> (z - x))) *\<^sub>R (z - x))
      has_derivative (\<lambda>h. 0)) (at x)"
    by (auto intro!: derivative_eq_intros)
  have "((\<lambda>z. g z - (4 * C * ((z - x) \<bullet> (z - x))) *\<^sub>R (z - x)) has_derivative
      (\<lambda>h. H *v h - 0)) (at x)"
    by (rule has_derivative_diff[OF dg dq])
  then show "((\<lambda>z. g z - (4 * C * ((z - x) \<bullet> (z - x))) *\<^sub>R (z - x))
      has_derivative (\<lambda>h. H *v h)) (at x)" by simp
qed

lemma test_fun_quadratic_dominates:
  fixes \<phi> :: "real^'n::finite \<Rightarrow> real" and g :: "real^'n \<Rightarrow> real^'n"
    and H :: "real^'n^'n" and x :: "real^'n" and \<delta> :: real
  assumes tf: "test_fun_at \<phi> g H x" and d0: "0 < \<delta>"
  obtains r where "0 < r"
    and "\<And>z. z \<in> ball x r \<Longrightarrow>
      \<phi> z \<le> \<phi> x + g x \<bullet> (z - x) + ((z - x) \<bullet> ((H + \<delta> *\<^sub>R mat 1) *v (z - x))) / 2"
proof -
  have symH: "transpose H = H"
    and dg: "(g has_derivative (\<lambda>h. H *v h)) (at x)"
    using tf unfolding test_fun_at_def by blast+
  obtain e where e0: "0 < e"
    and dphi: "\<And>y. y \<in> ball x e \<Longrightarrow> (\<phi> has_derivative (\<lambda>h. g y \<bullet> h)) (at y)"
    using tf unfolding test_fun_at_def by blast
  have "\<forall>e>0. \<exists>d>0. \<forall>y. norm (y - x) < d \<longrightarrow>
      norm (g y - g x - (H *v (y - x))) \<le> e * norm (y - x)"
    using dg unfolding has_derivative_at_alt by blast
  moreover have "0 < \<delta> / 2" using d0 by simp
  ultimately obtain d where dd: "0 < d"
    and bnd: "\<And>y. norm (y - x) < d \<Longrightarrow>
        norm (g y - g x - (H *v (y - x))) \<le> (\<delta> / 2) * norm (y - x)"
    by blast
  define r where "r = min e d"
  have r0: "0 < r" using e0 dd by (simp add: r_def)
  have main: "\<phi> z \<le> \<phi> x + g x \<bullet> (z - x)
      + ((z - x) \<bullet> ((H + \<delta> *\<^sub>R mat 1) *v (z - x))) / 2"
    if z: "z \<in> ball x r" for z
  proof -
    define v where "v = z - x"
    have nv: "norm v < r"
      using z by (simp add: v_def dist_norm norm_minus_commute)
    define A where "A = g x \<bullet> v"
    define B where "B = v \<bullet> ((H + \<delta> *\<^sub>R mat 1) *v v)"
    define f where "f t = \<phi> (x + t *\<^sub>R v) - (\<phi> x + t * A + t\<^sup>2 * B / 2)" for t
    have f0: "f 0 = 0" by (simp add: f_def)
    have deriv: "\<exists>y. (f has_field_derivative y) (at t) \<and> y \<le> 0"
      if t: "0 \<le> t" "t \<le> 1" for t
    proof -
      have ntv: "norm (t *\<^sub>R v) \<le> norm v"
        using t by (simp add: mult_left_le_one_le)
      have mem: "x + t *\<^sub>R v \<in> ball x e"
        using ntv nv by (simp add: dist_norm r_def)
      have d1: "((\<lambda>t. \<phi> (x + t *\<^sub>R v)) has_field_derivative
          g (x + t *\<^sub>R v) \<bullet> v) (at t)"
      proof -
        have i1: "((\<lambda>t :: real. x + t *\<^sub>R v) has_derivative (\<lambda>h. h *\<^sub>R v)) (at t)"
          by (auto intro!: derivative_eq_intros)
        have i2: "(\<phi> has_derivative (\<lambda>h. g (x + t *\<^sub>R v) \<bullet> h)) (at (x + t *\<^sub>R v))"
          by (rule dphi[OF mem])
        have "((\<lambda>t. \<phi> (x + t *\<^sub>R v)) has_derivative
            (\<lambda>h. g (x + t *\<^sub>R v) \<bullet> (h *\<^sub>R v))) (at t)"
          using diff_chain_at[OF i1 i2] by (simp add: o_def)
        then show ?thesis
          by (rule has_derivative_imp_has_field_derivative)
            (simp add: ac_simps)
      qed
      have d2: "((\<lambda>t. \<phi> x + t * A + t\<^sup>2 * B / 2) has_field_derivative
          A + t * B) (at t)"
        by (auto intro!: derivative_eq_intros)
      have df: "(f has_field_derivative
          (g (x + t *\<^sub>R v) \<bullet> v - (A + t * B))) (at t)"
        unfolding f_def by (rule DERIV_diff[OF d1 d2])
      have expand: "g (x + t *\<^sub>R v) \<bullet> v - (A + t * B)
          = (g (x + t *\<^sub>R v) - g x - (H *v (t *\<^sub>R v))) \<bullet> v - t * (\<delta> * (v \<bullet> v))"
      proof -
        have m1: "(H + \<delta> *\<^sub>R mat 1) *v v = H *v v + \<delta> *\<^sub>R v"
          by (simp add: matrix_vector_mult_add_rdistrib scaleR_matrix_vector
              )
        have m2: "H *v (t *\<^sub>R v) = t *\<^sub>R (H *v v)"
          by (simp add: matrix_vector_mult_scaleR)
        show ?thesis
          unfolding A_def B_def m1 m2
          by (simp add: inner_commute
              algebra_simps)
      qed
      have small: "(g (x + t *\<^sub>R v) - g x - (H *v (t *\<^sub>R v))) \<bullet> v
          \<le> (\<delta> / 2) * (t * norm v) * norm v"
      proof -
        have "norm (t *\<^sub>R v) < d"
          using ntv nv by (simp add: r_def)
        moreover have "(x + t *\<^sub>R v) - x = t *\<^sub>R v" by simp
        ultimately have nb: "norm (g (x + t *\<^sub>R v) - g x - (H *v (t *\<^sub>R v)))
            \<le> (\<delta> / 2) * norm (t *\<^sub>R v)"
          using bnd[of "x + t *\<^sub>R v"] by simp
        have "(g (x + t *\<^sub>R v) - g x - (H *v (t *\<^sub>R v))) \<bullet> v
            \<le> norm (g (x + t *\<^sub>R v) - g x - (H *v (t *\<^sub>R v))) * norm v"
          by (rule norm_cauchy_schwarz)
        also have "\<dots> \<le> ((\<delta> / 2) * norm (t *\<^sub>R v)) * norm v"
          by (rule mult_right_mono[OF nb norm_ge_zero])
        also have "\<dots> = (\<delta> / 2) * (t * norm v) * norm v"
          using t by simp
        finally show ?thesis .
      qed
      have vv: "v \<bullet> v = norm v * norm v"
        by (simp add: dot_square_norm power2_eq_square)
      have "g (x + t *\<^sub>R v) \<bullet> v - (A + t * B)
          \<le> (\<delta> / 2) * (t * norm v) * norm v - t * (\<delta> * (norm v * norm v))"
        unfolding expand vv by (rule diff_right_mono[OF small])
      also have "\<dots> = - (\<delta> / 2) * t * (norm v * norm v)"
        by (simp add: field_simps)
      also have "\<dots> \<le> 0"
        using d0 t by simp
      finally show ?thesis using df by blast
    qed
    have "f 1 \<le> f 0"
      by (rule DERIV_nonpos_imp_nonincreasing[of 0 1 f])
        (use deriv in auto)
    then have "\<phi> (x + 1 *\<^sub>R v) \<le> \<phi> x + 1 * A + 1\<^sup>2 * B / 2"
      using f0 by (simp add: f_def)
    then show ?thesis by (simp add: v_def A_def B_def)
  qed
  show ?thesis by (rule that[OF r0 main])
qed

text \<open>The mirror for subsolutions: adding a quartic deepens a local
  maximum and, for a large enough coefficient, makes it global over \<open>K\<close>,
  reusing @{thm [source] test_fun_at_quartic_shift} with a negative
  coefficient.\<close>

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
proof -
  have r40: "0 < r ^ 4" using r0 by simp
  define C where "C = max 0 ((Bu - B\<phi> - (u x - \<phi> x)) / r ^ 4)"
  have C0: "0 \<le> C" unfolding C_def by simp
  have Cbig: "Bu - B\<phi> - (u x - \<phi> x) \<le> C * r ^ 4"
  proof -
    have "(Bu - B\<phi> - (u x - \<phi> x)) / r ^ 4 \<le> C" unfolding C_def by simp
    then have "(Bu - B\<phi> - (u x - \<phi> x)) / r ^ 4 * r ^ 4 \<le> C * r ^ 4"
      by (rule mult_right_mono) (use r40 in linarith)
    then show ?thesis using r40 by simp
  qed
  define \<psi> where
    "\<psi> = (\<lambda>z. \<phi> z - (- C) * ((z - x) \<bullet> (z - x))\<^sup>2)"
  define gg where
    "gg = (\<lambda>z. g z - (4 * (- C) * ((z - x) \<bullet> (z - x))) *\<^sub>R (z - x))"
  have tf': "test_fun_at \<psi> gg H x"
    unfolding \<psi>_def gg_def by (rule test_fun_at_quartic_shift[OF tf])
  have ggx: "gg x = g x" unfolding gg_def by simp
  have psix: "\<psi> x = \<phi> x" unfolding \<psi>_def by simp
  have glob: "u y - \<psi> y \<le> u x - \<psi> x" if yK: "y \<in> K" for y
  proof (cases "y \<in> ball x r")
    case True
    have nn: "0 \<le> C * ((y - x) \<bullet> (y - x))\<^sup>2"
      by (rule mult_nonneg_nonneg[OF C0]) simp
    show ?thesis using lm[OF True] nn unfolding \<psi>_def psix[unfolded \<psi>_def]
      by simp
  next
    case False
    then have dxy: "r \<le> dist x y" by simp
    have sq: "r\<^sup>2 \<le> (y - x) \<bullet> (y - x)"
    proof -
      have "r \<le> norm (y - x)"
        using dxy by (simp add: dist_norm norm_minus_commute)
      then have "r\<^sup>2 \<le> (norm (y - x))\<^sup>2" using r0 by (intro power_mono) auto
      then show ?thesis by (simp add: dot_square_norm)
    qed
    have q4: "r ^ 4 \<le> ((y - x) \<bullet> (y - x))\<^sup>2"
    proof -
      have "(r\<^sup>2)\<^sup>2 \<le> ((y - x) \<bullet> (y - x))\<^sup>2" using sq by (intro power_mono) auto
      then show ?thesis by (simp add: power_even_eq)
    qed
    have cq: "C * r ^ 4 \<le> C * ((y - x) \<bullet> (y - x))\<^sup>2"
      by (rule mult_left_mono[OF q4 C0])
    have hi: "u y \<le> Bu" by (rule uhi[OF yK])
    have lo: "B\<phi> \<le> \<phi> y" by (rule phi[OF yK])
    show ?thesis unfolding \<psi>_def using Cbig cq hi lo by simp
  qed
  have "ell_op_lsc k L (gg x) H \<le> 1"
    using sub[unfolded visc_subsol_env_def] x\<Omega> tf' glob by blast
  then show ?thesis unfolding ggx .
qed

corollary ell_op_usc_eq_at_nonzero:
  fixes p :: "real^'n::finite" and M :: "real^'n^'n"
  assumes k1: "1 \<le> k" and kn: "k < CARD('n)" and L1: "1 \<le> L"
    and p0: "p \<noteq> 0"
  shows "ell_op_usc k L p M = ereal (ell_op k L p M)"
proof (rule antisym)
  show "ell_op_usc k L p M \<le> ereal (ell_op k L p M)"
    by (rule ell_op_usc_le_at_nonzero[OF k1 kn L1 p0])
  show "ereal (ell_op k L p M) \<le> ell_op_usc k L p M"
    by (rule ell_op_le_ell_op_usc)
qed

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
proof -
  have Bc0: "0 < real (CARD('n) * CARD('n)) * L / 2" using LL by simp
  have Bcne: "real (CARD('n) * CARD('n)) * L / 2 \<noteq> 0"
  proof
    assume "real (CARD('n) * CARD('n)) * L / 2 = 0"
    then show False using Bc0 by simp
  qed
  define ee where "ee = 1 / (2 * (real (CARD('n) * CARD('n)) * L / 2))"
  have e0: "0 < ee" unfolding ee_def using Bc0 by simp
  have "ell_op_usc k L (0 :: real^'n) (0 :: real^'n^'n)
      \<le> ereal (real (CARD('n) * CARD('n)) * L / 2
          * (norm (0 :: real^'n^'n) + ee))"
    by (rule ell_op_usc_le_scaled_norm[OF kk(1) kk(2) LL e0])
  also have "real (CARD('n) * CARD('n)) * L / 2 * (norm (0 :: real^'n^'n) + ee)
      = 1 / 2"
  proof -
    have "real (CARD('n) * CARD('n)) * L / 2 * (norm (0 :: real^'n^'n) + ee)
        = (real (CARD('n) * CARD('n)) * L / 2) * ee" by simp
    also have "\<dots> = 1 / 2" unfolding ee_def using Bcne by (simp add: field_simps)
    finally show ?thesis .
  qed
  finally have "ell_op_usc k L (0 :: real^'n) (0 :: real^'n^'n) \<le> ereal (1 / 2)" .
  also have "ereal (1 / 2 :: real) < 1" by (simp add: one_ereal_def)
  finally show ?thesis .
qed

subsection \<open>The invariances of \<open>F\<close> --- the paper's display (4.4)\<close>

text \<open>\<open>cInf_mult_pos\<close> lives in @{theory Continuous_Time_Martingales.Integrability_Criteria}.\<close>


lemma ell_op_scale:
  fixes p :: "real^'n::finite" and M :: "real^'n^'n"
  assumes c0: "0 < c"
  shows "ell_op k L (c *\<^sub>R p) M = ell_op k L p M"
proof -
  have cne: "c \<noteq> 0" using c0 by simp
  have "feasible k L (c *\<^sub>R p) = feasible k L p" by (rule feasible_scale[OF cne])
  then show ?thesis unfolding ell_op_def by simp
qed

text \<open>\<open>trace_matrix_commute\<close> lives in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


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
      by (rule trace_matrix_commute)
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

text \<open>\<open>matvec_diff_right\<close>, \<open>matvec_scaleR_right\<close> live in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


text \<open>\<open>matrix_mul_diff_right\<close> and \<open>matrix_mul_diff_left\<close> live in
  @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>

text \<open>\<open>matvec_orth_inv\<close>, \<open>conj_orth_inv\<close>, \<open>norm_orthogonal_matrix_vector\<close>, \<open>norm_matrix_sq_trace\<close>, \<open>norm_conj_orthogonal\<close> live in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


text \<open>The transfer lemma: if \<open>\<Psi>\<close> leaves \<open>F\<close> invariant and distorts balls around
  \<open>z\<close> by at most fixed factors in both directions, then it leaves the upper
  envelope at \<open>z\<close> invariant.  Purely a statement about \<open>INF\<close>/\<open>SUP\<close> reindexing.\<close>

lemma pos_image_scale:
  assumes r0: "0 < r"
  shows "(\<lambda>e. e / r) ` {0<..} = {(0::real)<..}"
proof
  show "(\<lambda>e. e / r) ` {0<..} \<subseteq> {(0::real)<..}" using r0 by auto
  show "{(0::real)<..} \<subseteq> (\<lambda>e. e / r) ` {0<..}"
  proof
    fix x :: real assume "x \<in> {0<..}"
    then have x0: "0 < x" by simp
    have xe: "x = (x * r) / r" using r0 by simp
    have "x * r \<in> {0<..}" using x0 r0 by simp
    then show "x \<in> (\<lambda>e. e / r) ` {0<..}" using xe by (metis image_eqI)
  qed
qed

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
    unfolding \<Psi>_def ell_op_pair_def by (simp add: ell_op_scale[OF c0])
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
      by (rule matvec_diff_right[symmetric])
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

text \<open>\<open>open_orth_image\<close>, \<open>open_affine_image\<close>, \<open>affine_interior_sub\<close>, \<open>affine_inv_shape\<close>, \<open>affine_inv_left\<close>, \<open>affine_inv_right\<close>, \<open>affine_interior_image\<close> live in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


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
