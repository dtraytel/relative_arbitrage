(*
  Title:   Envelopes.thy
  Content: The semicontinuous envelopes F_* and F^* of Eq. (1.9), and
           Definition 3.1 of arXiv:2512.17702 stated with them.

  Definition 3.1 of the paper does NOT use F itself: a subsolution must
  satisfy  F_*(grad phi, Hess phi) <= 1  and a supersolution
  F^*(grad phi, Hess phi) >= 1,  where F_* and F^* are the lower and upper
  semicontinuous envelopes of F in the pair (p, M).  The envelopes matter
  precisely at p = 0, where F is discontinuous.

  What is proved here:
  * the envelopes exist as ereal-valued functions with no side conditions
    (ereal is a complete lattice, so Sup/Inf are total);
  * the sandwich  F_* <= F <= F^*  (ell_op_lsc_le, ell_op_le_usc);
  * Definition 3.1 in envelope form, with the paper's GLOBAL touching
    condition (max over K, not a local max on a small ball);
  * that the envelope-free notions of Relative_Arbitrage_PDE imply the
    envelope ones (visc_subsol_imp_env, visc_supersol_imp_env) -- both
    because F_* <= F <= F^* and because a global max is a local max;
  * hence Example 3.1 satisfies Definition 3.1 as the paper states it
    (ball_v_visc_sol_env).

  * the clause of Lemma 3.1 at the degenerate point:  F_* = F  on
    {0} x S^n  (ell_op_lsc_at_zero).  This is the clause the paper states
    separately, and it needs no eigenvalue theory: at p = 0 the constraint
    a p = 0 is vacuous, so feasible 0 is the LARGEST feasible set and
    F(0,.) the smallest value of F (ell_op_zero_le); and F is Lipschitz in
    M uniformly in p because the feasible set is entrywise bounded by L
    (trace_mult_feasible_bound, ell_op_M_gap, mgap_le_norm).  Together
    these make the infimum over any neighbourhood of (0,M) converge to
    F(0,M).

  What is NOT proved: the OTHER two clauses of Lemma 3.1, i.e.
  F_* = F^* = F on (R^n - {0}) x S^n, and the closed formula (3.6) for
  F^*(0,M).  Both need ordered eigenvalues lambda_(i), which this
  development has deliberately avoided in favour of the variational
  conditions eigen_lb/eigen_ub, plus Ky Fan's maximum principle and the
  Poincare separation theorem (Eq. (3.8)).  See the note at the end of
  this theory for the reduction that makes (3.6) precise.  Consequently
  the implication visc_sol --> visc_sol_env is still only one way on the
  supersolution side; on the SUBSOLUTION side at p = 0 the two conditions
  now provably coincide, by ell_op_lsc_at_zero.
*)

theory Envelopes
  imports Relative_Arbitrage_Comparison
begin

unbundle inner_syntax

section \<open>The operator of Eq. (1.9) on pairs\<close>

text \<open>The envelopes are taken in the pair \<open>(p, M)\<close> jointly, as in the
  paper, so we first package \<open>F\<close> as a function on the product metric
  space.  Values are put in \<open>ereal\<close> so that the suprema and infima below
  are unconditionally defined.\<close>

definition ell_op_pair ::
  "nat \<Rightarrow> real \<Rightarrow> (real^'n::finite) \<times> (real^'n^'n) \<Rightarrow> ereal"
  where
  "ell_op_pair k L z = ereal (ell_op k L (fst z) (snd z))"

section \<open>The semicontinuous envelopes \<open>F\<^sub>*\<close> and \<open>F\<^sup>*\<close>\<close>

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

text \<open>Every ball around \<open>z\<close> contains \<open>z\<close>, which gives the sandwich
  \<open>F\<^sub>* \<le> F \<le> F\<^sup>*\<close>.  This is all that is needed to see that the
  envelope-free conditions are the stronger ones.\<close>

lemma mem_ball_self: "0 < e \<Longrightarrow> z \<in> ball z e"
  by simp

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
  \<open>\<ge> 1\<close> passes through limits in \<open>(p, M)\<close>.  Both the Case-2 reduction of
  \<section>3.2 and the envelope re-basing of the comparison proof use this to
  move a conclusion obtained at PERTURBED jets back to the jet of
  interest.\<close>

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
    then have "dist ((ps j, Ms j)) w < e / 2" by (simp add: mem_ball)
    then have "dist ((p0, M0)) w < e"
      using j dist_triangle[of "(p0, M0)" w "(ps j, Ms j)"]
      by (simp add: dist_commute)
    then show "w \<in> ball ((p0, M0)) e" by (simp add: mem_ball)
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
  feasible set is the largest one and \<open>F(0, \<sqdot>)\<close> is the smallest value of \<open>F\<close>.
  Since \<open>F\<close> is moreover Lipschitz in \<open>M\<close> uniformly in \<open>p\<close> (the feasible set is
  entrywise bounded by \<open>L\<close>), the infimum over any neighbourhood of \<open>(0, M)\<close> is
  attained in the limit at \<open>(0, M)\<close> itself, which is exactly \<open>F\<^sub>*(0,M) = F(0,M)\<close>.
  No eigenvalue theory is needed for this clause.\<close>

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

text \<open>At \<open>M = 0\<close> the operator is \<open>0\<close> whatever the gradient, because every
  feasible \<open>a\<close> gives \<open>- trace (0 a)/2 = 0\<close>.  Combined with the Lipschitz
  bound @{thm [source] ell_op_M_gap} this makes \<open>F\<close> small whenever \<open>M\<close> is
  small, UNIFORMLY in \<open>p\<close> --- and a bound uniform in \<open>p\<close> survives the
  supremum over a ball, hence passes to \<open>F\<^sup>*\<close>.

  This is what the paper's Theorem 4.2(a) uses to close the diagonal case:
  when the doubled maximiser has \<open>x\<^sup>\<epsilon> = y\<^sup>\<epsilon>\<close> the test function has a
  VANISHING two-jet at \<open>y\<^sup>\<epsilon>\<close>, and the supersolution property would give
  \<open>1 \<le> F\<^sup>*(0,0) = 0\<close>.  The envelope changes nothing here: \<open>F\<^sup>*(0,0)\<close> is \<open>0\<close>
  for the same reason \<open>F(0,0)\<close> is.\<close>

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

text \<open>The form the diagonal case consumes: for a small enough shift the
  UPPER envelope at \<open>-\<delta>I\<close> is below \<open>1\<close>, whatever the gradient.\<close>

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

text \<open>Consequence: at the degenerate gradient the subsolution inequality of
  Definition 3.1 and the envelope-free one are the SAME condition.  This is
  the point of the clause: without it, \<open>F\<^sub>*(0,H) \<le> 1\<close> could conceivably be
  strictly weaker than \<open>F(0,H) \<le> 1\<close>.\<close>

corollary ell_op_lsc_at_zero_iff:
  fixes M :: "real^'n::finite^'n"
  assumes k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L"
  shows "ell_op_lsc k L (0 :: real^'n) M \<le> 1 \<longleftrightarrow> ell_op k L (0 :: real^'n) M \<le> 1"
  unfolding ell_op_lsc_at_zero[OF k L] by (simp add: one_ereal_def)

section \<open>Definition 3.1 in envelope form\<close>

text \<open>The paper's touching condition is global: \<open>(u - \<phi>)(x)\<close> is the maximum
  of \<open>u - \<phi>\<close> over all of \<open>K\<close> (resp. the minimum, for supersolutions).  The
  test-function data \<open>(\<phi>, g, H)\<close> is the same as in
  Relative\_Arbitrage\_PDE, i.e. \<open>g\<close> is the gradient and \<open>H\<close> the Hessian.\<close>

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

section \<open>The envelope-free notions are the stronger ones\<close>

text \<open>Two independent reasons.  First, \<open>F\<^sub>* \<le> F \<le> F\<^sup>*\<close>, so the envelope
  inequalities are weaker at each test function.  Second, a global maximum
  over \<open>K\<close> is in particular a local maximum on any ball around \<open>x\<close> that
  stays inside \<open>K\<close>, so the envelope notion constrains fewer test
  functions.  Both point the same way.\<close>

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

lemma visc_sol_imp_env:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes u: "visc_sol k L \<Omega> u" and sub_K: "\<Omega> \<subseteq> K" and op: "open \<Omega>"
  shows "visc_sol_env k L K \<Omega> u"
  unfolding visc_sol_env_def
proof (intro conjI)
  have s: "visc_subsol k L \<Omega> u" and t: "visc_supersol k L \<Omega> u"
    using u by (simp_all add: visc_sol_def)
  show "visc_subsol_env k L K \<Omega> u"
    by (rule visc_subsol_imp_env[OF s sub_K op])
  show "visc_supersol_env k L K \<Omega> u"
    by (rule visc_supersol_imp_env[OF t sub_K op])
qed

section \<open>Example 3.1 satisfies Definition 3.1 as stated in the paper\<close>

text \<open>Putting \<open>K = cball 0 r\<close> and \<open>\<Omega> = ball 0 r = K\<^sup>\<circ>\<close>: the explicit
  function of Eq. (3.9) is a viscosity solution in the envelope sense of
  Definition 3.1, with zero boundary values on the sphere.\<close>

theorem ball_v_visc_sol_env:
  fixes r :: real and k :: nat and L :: real
  assumes k: "1 \<le> k" "k < CARD('n::finite)" and L: "1 \<le> L"
  shows "visc_sol_env k L (cball 0 r) (ball 0 r)
           (ball_v r k :: real^'n \<Rightarrow> real)"
    and "\<And>x :: real^'n. norm x = r \<Longrightarrow> ball_v r k x = 0"
proof -
  show "visc_sol_env k L (cball 0 r) (ball 0 r)
      (ball_v r k :: real^'n \<Rightarrow> real)"
  proof (rule visc_sol_imp_env)
    show "visc_sol k L (ball 0 r) (ball_v r k :: real^'n \<Rightarrow> real)"
      by (rule ball_v_solves_pde_viscosity(1)[OF k L])
    show "ball (0::real^'n) r \<subseteq> cball 0 r"
      by (rule ball_subset_cball)
    show "open (ball (0::real^'n) r)"
      by (rule open_ball)
  qed
  show "\<And>x :: real^'n. norm x = r \<Longrightarrow> ball_v r k x = 0"
    by (rule ball_v_boundary)
qed

section \<open>Note: what Eq. (3.6) still needs\<close>

text \<open>For the record, the route to Eq. (3.6), following the paper's own
  proof, so that the remaining work is precisely delimited.

  The key definition is Eq. (3.4).  It is NOT a compression to an
  \<open>(n-1)\<close>-dimensional space --- it is an \<open>n \<times> n\<close> matrix:

    \<open>M\<^sub>p = (I - p p\<^sup>T/|p|²) M (I - p p\<^sup>T/|p|²) + min (\<lambda>\<^sub>(\<^sub>n\<^sub>)(M), 0) * p p\<^sup>T/|p|²\<close>
    for \<open>p \<noteq> 0\<close>, and \<open>M\<^sub>0 = M\<close>.

  So no change of dimension is involved anywhere, and \<open>real^'n^'n\<close> is
  exactly the right type.  The correction term \<open>min (\<lambda>\<^sub>(\<^sub>n\<^sub>)(M), 0)\<close> in the
  \<open>p\<close>-direction is chosen so that this eigenvalue sorts to the BOTTOM of the
  spectrum of \<open>M\<^sub>p\<close>; that is what makes Eq. (3.5) a clean sum over
  \<open>i = 1..n\<close> and what produces the index shift in Eq. (3.6).

  \<^item> Step 1 (Eq. (3.5)).  Since \<open>trace (M ** a) = trace (M\<^sub>p ** a)\<close> for psd
    \<open>a\<close> with \<open>a p = 0\<close>, diagonalising \<open>M\<^sub>p\<close> gives
      \<open>F(p,M) = -(1/2) * bracket (n-k) L M\<^sub>p\<close>
    with \<open>bracket\<close> as in Eigenvalues.thy, i.e.
      \<open>bracket m L a = L * possum n a + (kyfan m a - possum m a)\<close>.
    This is exactly the bracket of Eq. (3.5).

  \<^item> Step 2 (\<open>F\<^sup>*\<close> at \<open>p = 0\<close>, upper bound).  Only the ONE-SIDED Poincare
    bound is used: \<open>\<lambda>\<^sub>(\<^sub>i\<^sub>)(M\<^sub>p) \<ge> \<lambda>\<^sub>(\<^sub>i\<^sub>+\<^sub>1\<^sub>)(M)\<close> for \<open>i = 1..n-1\<close>.  Since
    \<open>\<lambda> \<mapsto> L \<lambda>\<^sup>+ + \<lambda> 1\<^sub>{\<^sub>\<lambda>\<^sub>\<le>\<^sub>0\<^sub>}\<close> and \<open>\<lambda> \<mapsto> L \<lambda>\<^sup>+\<close> are nondecreasing, this bounds
    \<open>F(p\<^sup>m, M\<^sup>m)\<close> above by the shifted-index expression, and continuity of
    \<open>M \<mapsto> (\<lambda>\<^sub>(\<^sub>1\<^sub>), \<dots>, \<lambda>\<^sub>(\<^sub>n\<^sub>))\<close> passes to the limit.

  \<^item> Step 3 (lower bound).  NOT an optimisation: evaluate \<open>F\<close> along the
    single sequence \<open>(q\<^sub>1/m, M)\<close> with \<open>q\<^sub>1\<close> a TOP eigenvector of \<open>M\<close>.  Then
    \<open>F(q\<^sub>1/m, M)\<close> is constant in \<open>m\<close> and equals the right-hand side of
    Eq. (3.6) exactly.

  \<^item> Step 4 (the clause off \<open>p = 0\<close>).  \<open>F\<close> is continuous there because
    \<open>(p,M) \<mapsto> M\<^sub>p\<close> is (pure algebra off \<open>p = 0\<close>) and \<open>M \<mapsto> \<lambda>\<^sub>(\<^sub>i\<^sub>)(M)\<close> is.

  What Eigenvalues.thy already supplies: ordered eigenvalues \<open>eigval\<close> with
  \<open>eigval_antimono\<close>, Ky Fan's maximum principle, and the positive/negative
  part sums \<open>possum\<close> --- so no functional calculus \<open>A\<^sup>\<plusminus>\<close> is needed, and
  Courant--Fischer is not needed either.  Continuity of \<open>M \<mapsto> \<lambda>\<^sub>(\<^sub>i\<^sub>)(M)\<close> is
  also cheap there: \<open>eigval\<close> is a difference of \<open>kyfan\<close>s and \<open>kyfan\<close> is
  Lipschitz in the matrix by the same argument as \<open>ell_op_M_gap\<close> above.

  Only \<open>ell_op_lsc_at_zero\<close> is independent of all of this, which is why it
  is the clause that is proved here.\<close>

subsection \<open>Householder reflections and the rotation between two directions\<close>

text \<open>Towards \<open>F\<^sup>* = F\<close> away from \<open>p = 0\<close>, which is what the
  Crandall--Ishii touchpoints of the comparison principle need in order
  to accept an envelope-form supersolution.  That proof transports a
  near-optimal feasible witness for \<open>p\<close> to one for a nearby \<open>p'\<close> by an
  ORTHOGONAL conjugation, so what it needs is an orthogonal map carrying
  \<open>p\<close>'s direction to \<open>p'\<close>'s AND tending to the identity as \<open>p' \<rightarrow> p\<close>.

  A single Householder reflection carries one direction to the other but
  does NOT tend to the identity --- its axis \<open>u - v\<close> normalises to a unit
  vector with no limit.  The composition of two does: \<open>hh (u+v) \<circ> hh u\<close>
  sends \<open>u \<mapsto> -u \<mapsto> v\<close>, and at \<open>v = u\<close> it is \<open>hh u ** hh u = 1\<close> exactly.
  (@{thm [source] orthogonal_transformation_exists} supplies an
  orthogonal map between vectors of equal norm but with no control near
  the identity, so it does not serve here.)

  The reflection is defined without normalising its axis, which makes it
  invariant under rescaling and keeps the computations division-free
  apart from the single coefficient.  Everything is proved on VECTORS
  through @{thm [source] matrix_eq} rather than on matrix entries.\<close>

definition hh :: "real^'n::finite \<Rightarrow> real^'n^'n"
  where "hh w = mat 1 - (2 / (w \<bullet> w)) *\<^sub>R outer_prod w w"

lemma matvec_minus_right:
  fixes A :: "real^'n::finite^'n"
  shows "A *v (- x) = - (A *v x)"
  by (simp add: matrix_vector_mult_def vec_eq_iff sum_negf)

lemma hh_sym: "transpose (hh w) = hh w"
  unfolding hh_def
  by (simp add: transpose_def outer_prod_def mat_def vec_eq_iff mult_ac)

lemma hh_mv: "hh w *v x = x - (2 * (w \<bullet> x) / (w \<bullet> w)) *\<^sub>R w"
proof -
  have "hh w *v x = mat 1 *v x - ((2 / (w \<bullet> w)) *\<^sub>R outer_prod w w) *v x"
    unfolding hh_def by (rule matrix_vector_mult_diff_rdistrib)
  also have "mat 1 *v x = x" by (rule matrix_vector_mul_lid)
  also have "((2 / (w \<bullet> w)) *\<^sub>R outer_prod w w) *v x
      = (2 / (w \<bullet> w)) *\<^sub>R (outer_prod w w *v x)"
    by (rule scaleR_matrix_vector)
  also have "outer_prod w w *v x = (w \<bullet> x) *\<^sub>R w"
    by (rule outer_prod_mv)
  finally show ?thesis by simp
qed

lemma hh_self:
  fixes w :: "real^'n::finite"
  assumes w0: "w \<noteq> 0"
  shows "hh w *v w = - w"
proof -
  have ww: "w \<bullet> w \<noteq> 0" using w0 by simp
  have cw: "2 * (w \<bullet> w) / (w \<bullet> w) = 2" using ww by simp
  have "hh w *v w = w - (2 * (w \<bullet> w) / (w \<bullet> w)) *\<^sub>R w" by (rule hh_mv)
  also have "\<dots> = w - (2::real) *\<^sub>R w" unfolding cw by (rule refl)
  also have "\<dots> = - w" by (simp add: vec_eq_iff)
  finally show ?thesis .
qed

lemma hh_bisect:
  fixes u v :: "real^'n::finite"
  assumes u1: "norm u = 1" and v1: "norm v = 1" and ne: "u + v \<noteq> 0"
  shows "hh (u + v) *v u = - v"
proof -
  have uu: "u \<bullet> u = 1" using u1 by (metis norm_eq_1)
  have vv: "v \<bullet> v = 1" using v1 by (metis norm_eq_1)
  have s1: "(u + v) \<bullet> u = 1 + u \<bullet> v"
  proof -
    have a: "(u + v) \<bullet> u = u \<bullet> u + v \<bullet> u" by (rule inner_add_left)
    have b: "v \<bullet> u = u \<bullet> v" by (rule inner_commute)
    show ?thesis unfolding a b uu by (rule refl)
  qed
  have s2: "(u + v) \<bullet> (u + v) = 2 * (1 + u \<bullet> v)"
  proof -
    have a: "(u + v) \<bullet> (u + v) = u \<bullet> (u + v) + v \<bullet> (u + v)"
      by (rule inner_add_left)
    have b: "u \<bullet> (u + v) = u \<bullet> u + u \<bullet> v" by (rule inner_add_right)
    have d: "v \<bullet> (u + v) = v \<bullet> u + v \<bullet> v" by (rule inner_add_right)
    have e: "v \<bullet> u = u \<bullet> v" by (rule inner_commute)
    show ?thesis unfolding a b d e uu vv by simp
  qed
  have nz: "(u + v) \<bullet> (u + v) \<noteq> 0" using ne by simp
  have c1: "1 + u \<bullet> v \<noteq> 0" using nz unfolding s2 by simp
  have "hh (u + v) *v u
      = u - (2 * ((u + v) \<bullet> u) / ((u + v) \<bullet> (u + v))) *\<^sub>R (u + v)"
    by (rule hh_mv)
  also have "2 * ((u + v) \<bullet> u) / ((u + v) \<bullet> (u + v)) = 1"
    unfolding s1 s2 using c1 by simp
  finally show ?thesis by simp
qed

lemma hh_sq:
  fixes w :: "real^'n::finite"
  assumes w0: "w \<noteq> 0"
  shows "hh w ** hh w = mat 1"
proof -
  have ww: "w \<bullet> w \<noteq> 0" using w0 by simp
  have key: "(hh w ** hh w) *v x = mat 1 *v x" for x
  proof -
    define k where "k = 2 * (w \<bullet> x) / (w \<bullet> w)"
    have h1: "hh w *v x = x - k *\<^sub>R w" unfolding k_def by (rule hh_mv)
    have wk: "w \<bullet> (x - k *\<^sub>R w) = - (w \<bullet> x)"
    proof -
      have "w \<bullet> (x - k *\<^sub>R w) = w \<bullet> x - k * (w \<bullet> w)"
        by (simp add: inner_diff_right)
      also have "k * (w \<bullet> w) = 2 * (w \<bullet> x)"
        unfolding k_def using ww by simp
      finally show ?thesis by simp
    qed
    have coeff: "2 * (w \<bullet> (x - k *\<^sub>R w)) / (w \<bullet> w) = - k"
    proof -
      have "2 * (w \<bullet> (x - k *\<^sub>R w)) / (w \<bullet> w)
          = 2 * (- (w \<bullet> x)) / (w \<bullet> w)" by (simp add: wk)
      also have "\<dots> = - (2 * (w \<bullet> x) / (w \<bullet> w))" by simp
      finally show ?thesis unfolding k_def .
    qed
    have h2: "hh w *v (x - k *\<^sub>R w)
        = (x - k *\<^sub>R w) - (2 * (w \<bullet> (x - k *\<^sub>R w)) / (w \<bullet> w)) *\<^sub>R w"
      by (rule hh_mv)
    have "(hh w ** hh w) *v x = hh w *v (hh w *v x)"
      by (metis matrix_vector_mul_assoc)
    also have "\<dots> = hh w *v (x - k *\<^sub>R w)" unfolding h1 by (rule refl)
    also have "\<dots> = (x - k *\<^sub>R w) - (- k) *\<^sub>R w"
      unfolding h2 coeff by (rule refl)
    also have "\<dots> = x" by simp
    finally show ?thesis by (simp add: matrix_vector_mul_lid)
  qed
  have "\<forall>x. (hh w ** hh w) *v x = mat 1 *v x" using key by blast
  then show ?thesis using matrix_eq[of "hh w ** hh w" "mat 1"] by blast
qed

lemma hh_orth:
  fixes w :: "real^'n::finite"
  assumes w0: "w \<noteq> 0"
  shows "transpose (hh w) ** hh w = mat 1"
  unfolding hh_sym by (rule hh_sq[OF w0])

lemma hh_scale:
  fixes w :: "real^'n::finite"
  assumes r0: "r \<noteq> 0"
  shows "hh (r *\<^sub>R w) = hh w"
proof -
  have key: "hh (r *\<^sub>R w) *v x = hh w *v x" for x
  proof -
    have "hh (r *\<^sub>R w) *v x
        = x - (2 * ((r *\<^sub>R w) \<bullet> x) / ((r *\<^sub>R w) \<bullet> (r *\<^sub>R w))) *\<^sub>R (r *\<^sub>R w)"
      by (rule hh_mv)
    also have "\<dots> = x - (2 * (w \<bullet> x) / (w \<bullet> w)) *\<^sub>R w"
    proof (cases "w \<bullet> w = 0")
      case True
      then have "w = 0" by simp
      then show ?thesis by simp
    next
      case False
      have e1: "(2 * ((r *\<^sub>R w) \<bullet> x) / ((r *\<^sub>R w) \<bullet> (r *\<^sub>R w))) *\<^sub>R (r *\<^sub>R w)
          = ((2 * (r * (w \<bullet> x)) / (r * r * (w \<bullet> w))) * r) *\<^sub>R w"
        by (simp add: mult_ac)
      have e2: "(2 * (r * (w \<bullet> x)) / (r * r * (w \<bullet> w))) * r
          = 2 * (w \<bullet> x) / (w \<bullet> w)"
        using r0 False by (simp add: field_simps)
      show ?thesis unfolding e1 e2 by (rule refl)
    qed
    also have "\<dots> = hh w *v x" by (rule hh_mv[symmetric])
    finally show ?thesis .
  qed
  have "\<forall>x. hh (r *\<^sub>R w) *v x = hh w *v x" using key by blast
  then show ?thesis using matrix_eq[of "hh (r *\<^sub>R w)" "hh w"] by blast
qed

definition rotv :: "real^'n::finite \<Rightarrow> real^'n \<Rightarrow> real^'n^'n"
  where "rotv u v = hh (u + v) ** hh u"

lemma rotv_orth:
  fixes u v :: "real^'n::finite"
  assumes u0: "u \<noteq> 0" and ne: "u + v \<noteq> 0"
  shows "transpose (rotv u v) ** rotv u v = mat 1"
proof -
  have s1: "transpose (rotv u v) ** rotv u v
      = (hh u ** hh (u + v)) ** (hh (u + v) ** hh u)"
    unfolding rotv_def matrix_transpose_mul hh_sym by (rule refl)
  have mid: "(hh u ** hh (u + v)) ** hh (u + v) = hh u"
  proof -
    have "(hh u ** hh (u + v)) ** hh (u + v)
        = hh u ** (hh (u + v) ** hh (u + v))"
      by (rule matrix_mul_assoc[symmetric])
    also have "\<dots> = hh u ** mat 1" using hh_sq[OF ne] by simp
    also have "\<dots> = hh u" by (rule matrix_mul_rid)
    finally show ?thesis .
  qed
  have "(hh u ** hh (u + v)) ** (hh (u + v) ** hh u)
      = ((hh u ** hh (u + v)) ** hh (u + v)) ** hh u"
    by (rule matrix_mul_assoc)
  also have "\<dots> = hh u ** hh u" unfolding mid by (rule refl)
  also have "\<dots> = mat 1" by (rule hh_sq[OF u0])
  finally show ?thesis unfolding s1 .
qed

lemma rotv_apply:
  fixes u v :: "real^'n::finite"
  assumes u1: "norm u = 1" and v1: "norm v = 1" and ne: "u + v \<noteq> 0"
  shows "rotv u v *v u = v"
proof -
  have u0: "u \<noteq> 0" using u1 by auto
  have "rotv u v *v u = hh (u + v) *v (hh u *v u)"
    unfolding rotv_def by (metis matrix_vector_mul_assoc)
  also have "hh u *v u = - u" by (rule hh_self[OF u0])
  also have "hh (u + v) *v (- u) = - (hh (u + v) *v u)"
    by (rule matvec_minus_right)
  also have "hh (u + v) *v u = - v" by (rule hh_bisect[OF u1 v1 ne])
  finally show ?thesis by simp
qed

lemma rotv_self:
  fixes u :: "real^'n::finite"
  assumes u0: "u \<noteq> 0"
  shows "rotv u u = mat 1"
proof -
  have e: "u + u = (2::real) *\<^sub>R u" by (simp add: vec_eq_iff)
  have "hh (u + u) = hh u" unfolding e by (rule hh_scale) simp
  then show ?thesis unfolding rotv_def by (simp add: hh_sq[OF u0])
qed

subsection \<open>Feasibility is invariant under orthogonal conjugation\<close>

text \<open>The transport step itself: an orthogonal \<open>R\<close> carries the feasible
  set of \<open>p\<close> onto the feasible set of \<open>R p\<close>.  Every clause is the change
  of variables \<open>x \<mapsto> R\<^sup>T x\<close>: definiteness and the eigenvalue cap because
  the map is an isometry, the annihilation because \<open>R\<^sup>T R = 1\<close>, and the
  eigenvalue floor by moving the witnessing subspace along \<open>R\<close>.

  For the dimension of the moved subspace only the INEQUALITY
  @{thm [source] dim_image_le} is needed, applied to \<open>R\<^sup>T\<close>: since
  \<open>S = R\<^sup>T(R(S))\<close>, it gives \<open>dim S \<le> dim (R(S))\<close>, which is the direction
  required --- so the locale-qualified \<open>dim_image_eq\<close> is never invoked.\<close>

lemma orth_preserves_inner:
  fixes R :: "real^'n::finite^'n"
  assumes orth: "transpose R ** R = mat 1"
  shows "(R *v x) \<bullet> (R *v y) = x \<bullet> y"
proof -
  have e: "transpose R *v (R *v x) = x"
  proof -
    have "transpose R *v (R *v x) = (transpose R ** R) *v x"
      by (metis matrix_vector_mul_assoc)
    also have "\<dots> = mat 1 *v x" unfolding orth by (rule refl)
    also have "\<dots> = x" by (rule matrix_vector_mul_lid)
    finally show ?thesis .
  qed
  have "(R *v x) \<bullet> (R *v y) = (transpose R *v (R *v x)) \<bullet> y"
    by (rule inner_transpose_matrix)
  then show ?thesis unfolding e .
qed

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

lemma rotv_orth':
  fixes u v :: "real^'n::finite"
  assumes u0: "u \<noteq> 0" and ne: "u + v \<noteq> 0"
  shows "rotv u v ** transpose (rotv u v) = mat 1"
proof -
  have s1: "rotv u v ** transpose (rotv u v)
      = (hh (u + v) ** hh u) ** (hh u ** hh (u + v))"
    unfolding rotv_def matrix_transpose_mul hh_sym by (rule refl)
  have mid: "(hh (u + v) ** hh u) ** hh u = hh (u + v)"
  proof -
    have "(hh (u + v) ** hh u) ** hh u = hh (u + v) ** (hh u ** hh u)"
      by (rule matrix_mul_assoc[symmetric])
    also have "\<dots> = hh (u + v) ** mat 1" using hh_sq[OF u0] by simp
    also have "\<dots> = hh (u + v)" by (rule matrix_mul_rid)
    finally show ?thesis .
  qed
  have "(hh (u + v) ** hh u) ** (hh u ** hh (u + v))
      = ((hh (u + v) ** hh u) ** hh u) ** hh (u + v)"
    by (rule matrix_mul_assoc)
  also have "\<dots> = hh (u + v) ** hh (u + v)" unfolding mid by (rule refl)
  also have "\<dots> = mat 1" by (rule hh_sq[OF ne])
  finally show ?thesis unfolding s1 .
qed

subsection \<open>Continuity of the transport\<close>

text \<open>The plumbing for \<open>F\<^sup>* = F\<close> at \<open>p \<noteq> 0\<close>: the rotation, and hence the
  conjugated witness and its pairing with the Hessian, depends
  continuously on the direction it is built from.  Everything is
  assembled from four reusable helpers, so that no proof below ever
  descends to matrix entries more than once.

  The domain is \<open>{q. 0 < u \<bullet> q}\<close> --- an open half space containing \<open>p\<close>
  when \<open>u\<close> is \<open>p\<close>'s direction.  It rules out both degeneracies at once:
  \<open>q \<noteq> 0\<close>, and \<open>u + q/|q| \<noteq> 0\<close>, since the latter would force
  \<open>u \<bullet> q/|q| = -1\<close>.\<close>

lemma continuous_on_matrix_entry:
  fixes F :: "'a::topological_space \<Rightarrow> real^'n::finite^'n"
  assumes cF: "continuous_on S F"
  shows "continuous_on S (\<lambda>z. F z $ i $ j)"
proof -
  have bl: "bounded_linear (\<lambda>A :: real^'n^'n. A $ i $ j)"
    using bounded_linear_vec_nth bounded_linear_compose by blast
  show ?thesis
    by (rule continuous_on_compose2[OF linear_continuous_on[OF bl] cF]) auto
qed

lemma continuous_on_matrix_mult:
  fixes F G :: "'a::topological_space \<Rightarrow> real^'n::finite^'n"
  assumes cF: "continuous_on S F" and cG: "continuous_on S G"
  shows "continuous_on S (\<lambda>z. F z ** G z)"
proof -
  have eq: "(\<lambda>z. F z ** G z)
      = (\<lambda>z. \<chi> i j. (\<Sum>l\<in>UNIV. F z $ i $ l * G z $ l $ j))"
    by (rule ext) (simp add: matrix_matrix_mult_def)
  show ?thesis unfolding eq
    by (intro continuous_on_vec_lambda continuous_on_sum continuous_on_mult
        continuous_on_matrix_entry cF cG)
qed

lemma continuous_on_matrix_transpose:
  fixes F :: "'a::topological_space \<Rightarrow> real^'n::finite^'n"
  assumes cF: "continuous_on S F"
  shows "continuous_on S (\<lambda>z. transpose (F z))"
proof -
  have eq: "(\<lambda>z. transpose (F z)) = (\<lambda>z. \<chi> i j. F z $ j $ i)"
    by (rule ext) (simp add: transpose_def)
  show ?thesis unfolding eq
    by (intro continuous_on_vec_lambda continuous_on_matrix_entry cF)
qed

lemma continuous_on_hh:
  fixes F :: "'a::topological_space \<Rightarrow> real^'n::finite"
  assumes cF: "continuous_on S F" and nz: "\<And>z. z \<in> S \<Longrightarrow> F z \<noteq> 0"
  shows "continuous_on S (\<lambda>z. hh (F z))"
proof -
  have entF: "continuous_on S (\<lambda>z. F z $ i)" for i
    by (rule continuous_on_compose2[OF
        linear_continuous_on[OF bounded_linear_vec_nth] cF]) auto
  have cip: "continuous_on S (\<lambda>z. F z \<bullet> F z)"
    by (rule bounded_bilinear.continuous_on[OF bounded_bilinear_inner cF cF])
  have nz': "F z \<bullet> F z \<noteq> 0" if "z \<in> S" for z using nz[OF that] by simp
  have eq: "(\<lambda>z. hh (F z)) = (\<lambda>z. \<chi> i j. (if i = j then 1 else 0)
      - 2 / (F z \<bullet> F z) * (F z $ i * F z $ j))"
    by (rule ext) (simp add: hh_def mat_def outer_prod_def vec_eq_iff)
  show ?thesis unfolding eq
    by (intro continuous_on_vec_lambda continuous_on_diff continuous_on_const
        continuous_on_mult continuous_on_divide cip entF)
      (use nz' in auto)
qed

lemma continuous_on_rotv:
  fixes u :: "real^'n::finite" and F :: "'a::topological_space \<Rightarrow> real^'n"
  assumes cF: "continuous_on S F" and nz: "\<And>z. z \<in> S \<Longrightarrow> u + F z \<noteq> 0"
  shows "continuous_on S (\<lambda>z. rotv u (F z))"
proof -
  have c1: "continuous_on S (\<lambda>z. hh (u + F z))"
  proof (rule continuous_on_hh)
    show "continuous_on S (\<lambda>z. u + F z)"
      by (intro continuous_on_add continuous_on_const cF)
    show "\<And>z. z \<in> S \<Longrightarrow> u + F z \<noteq> 0" by (rule nz)
  qed
  have c2: "continuous_on S (\<lambda>z :: 'a. hh u)" by (rule continuous_on_const)
  show ?thesis unfolding rotv_def
    by (rule continuous_on_matrix_mult[OF c1 c2])
qed

text \<open>The half space, and what it rules out.\<close>

lemma halfspace_open: "open {q :: real^'n::finite. 0 < u \<bullet> q}"
proof -
  have "continuous_on UNIV (\<lambda>q :: real^'n. u \<bullet> q)"
    by (rule linear_continuous_on[OF bounded_linear_inner_right])
  then have "open {q :: real^'n. 0 < u \<bullet> q}"
    by (rule open_Collect_less[OF continuous_on_const])
  then show ?thesis .
qed

lemma halfspace_nonzero:
  fixes q :: "real^'n::finite"
  assumes "0 < u \<bullet> q" shows "q \<noteq> 0"
  using assms by auto

lemma halfspace_not_antipodal:
  fixes u q :: "real^'n::finite"
  assumes u1: "norm u = 1" and hq: "0 < u \<bullet> q"
  shows "u + q /\<^sub>R norm q \<noteq> 0"
proof
  assume z: "u + q /\<^sub>R norm q = 0"
  have q0: "q \<noteq> 0" using hq by auto
  have nq: "0 < norm q" using q0 by simp
  have "u \<bullet> (q /\<^sub>R norm q) = (u \<bullet> q) / norm q"
    by (simp add: divide_inverse)
  then have pos: "0 < u \<bullet> (q /\<^sub>R norm q)" using hq nq by simp
  have "q /\<^sub>R norm q = - u" using z by (metis add_eq_0_iff)
  then have "u \<bullet> (q /\<^sub>R norm q) = - (u \<bullet> u)" by simp
  also have "u \<bullet> u = 1" using u1 by (metis norm_eq_1)
  finally have "u \<bullet> (q /\<^sub>R norm q) = - 1" by simp
  then show False using pos by simp
qed

lemma continuous_on_rotv_dir:
  fixes u :: "real^'n::finite"
  assumes u1: "norm u = 1"
  shows "continuous_on {q :: real^'n. 0 < u \<bullet> q}
      (\<lambda>q. rotv u (q /\<^sub>R norm q))"
proof (rule continuous_on_rotv)
  show "continuous_on {q :: real^'n. 0 < u \<bullet> q} (\<lambda>q. q /\<^sub>R norm q)"
  proof -
    have nz: "norm q \<noteq> 0" if "q \<in> {q :: real^'n. 0 < u \<bullet> q}" for q
      using that by auto
    have "continuous_on {q :: real^'n. 0 < u \<bullet> q}
        (\<lambda>q. (1 / norm q) *\<^sub>R q)"
      by (intro continuous_on_scaleR continuous_on_divide continuous_on_const
          continuous_on_norm continuous_on_id) (use nz in auto)
    then show ?thesis by (simp add: divide_inverse)
  qed
next
  show "\<And>q. q \<in> {q :: real^'n. 0 < u \<bullet> q} \<Longrightarrow> u + q /\<^sub>R norm q \<noteq> 0"
    using halfspace_not_antipodal[OF u1] by blast
qed

text \<open>And the real-valued functional the assembly actually needs: the
  Hessian paired with the conjugated witness.\<close>

lemma continuous_on_conj_trace:
  fixes a :: "real^'n::finite^'n"
    and R M :: "'b::topological_space \<Rightarrow> real^'n^'n"
  assumes cR: "continuous_on S R" and cM: "continuous_on S M"
  shows "continuous_on S (\<lambda>z. trace (M z ** (R z ** a ** transpose (R z))))"
proof -
  have c1: "continuous_on S (\<lambda>z. R z ** a)"
    by (rule continuous_on_matrix_mult[OF cR continuous_on_const])
  have c2: "continuous_on S (\<lambda>z. transpose (R z))"
    by (rule continuous_on_matrix_transpose[OF cR])
  have c3: "continuous_on S (\<lambda>z. R z ** a ** transpose (R z))"
    by (rule continuous_on_matrix_mult[OF c1 c2])
  have c4: "continuous_on S (\<lambda>z. M z ** (R z ** a ** transpose (R z)))"
    by (rule continuous_on_matrix_mult[OF cM c3])
  have tr: "(\<lambda>B :: real^'n^'n. trace B) = (\<lambda>B. \<Sum>i\<in>UNIV. B $ i $ i)"
    by (rule ext) (simp add: trace_def)
  show ?thesis
    unfolding tr
    by (intro continuous_on_sum continuous_on_matrix_entry c4)
qed

subsection \<open>\<open>F\<^sup>* = F\<close> away from the origin\<close>

text \<open>The assembly.  Feasibility depends on the gradient only through
  its DIRECTION, so the rotation carrying \<open>p\<close>'s direction to \<open>p'\<close>'s
  carries the whole feasible set across; a near-optimal witness for
  \<open>(p, M)\<close> therefore supplies a competitor for every nearby \<open>(p', M')\<close>,
  and continuity of the pairing makes the competitor's value beat
  \<open>F(p, M) + \<epsilon>\<close> on a whole ball.  That bounds the supremum defining the
  upper envelope, and the infimum over radii finishes it.\<close>

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
      also have "\<dots> = norm p * (u \<bullet> u)" by (simp add: inner_scaleR_right)
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
        by (simp add: matrix_mul_lid matrix_mul_rid)
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
        using zb by (simp add: mem_ball)
      have zW: "z \<in> W"
      proof -
        have "dist ((p, M) :: (real^'n) \<times> (real^'n^'n)) z < d1"
          using dz unfolding e_def by simp
        then have "z \<in> ball ((p, M) :: (real^'n) \<times> (real^'n^'n)) d1"
          by (simp add: mem_ball)
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
      have Rorth: "transpose R ** R = mat 1"
        unfolding R_def by (rule rotv_orth[OF u0 neuv])
      have Rorth': "R ** transpose R = mat 1"
        unfolding R_def by (rule rotv_orth'[OF u0 neuv])
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

text \<open>Definition 3.1 constrains only test functions whose touching is
  GLOBAL over \<open>K\<close>, while the Crandall--Ishii machinery produces LOCAL
  touchings from jet data.  The gap is closed by subtracting a quartic:
  \<open>\<psi> := \<phi> - C\<bar>z - x\<bar>\<^sup>4\<close> has the same two-jet at \<open>x\<close> (a quartic vanishes to
  second order), it only DEEPENS the touching inside the ball, and outside
  the ball the quartic is bounded below by \<open>Cr\<^sup>4\<close>, which for large \<open>C\<close>
  overwhelms the oscillation of \<open>w - \<phi>\<close> on \<open>K\<close>.

  The two boundedness hypotheses are exactly what a genuine \<open>C\<^sup>2\<close> test
  function on a compact \<open>K\<close> supplies, and they are what keeps the step
  honest: without a bound on \<open>\<phi>\<close> over \<open>K\<close> one could simply truncate \<open>\<phi>\<close>
  far from \<open>x\<close>, which \<^const>\<open>test_fun_at\<close> would tolerate but the paper's
  \<open>C\<^sup>2(\<real>\<^sup>n)\<close> would not.\<close>

text \<open>A test function is minorised near \<open>x\<close> by its two-jet quadratic,
  once the Hessian is shifted down by any \<open>\<delta> > 0\<close>.  This is what lets a
  touching by an ARBITRARY test function be replaced by a touching by a
  genuine quadratic --- which, unlike the original, is bounded on a
  bounded set.\<close>

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
      using z by (simp add: v_def mem_ball dist_norm norm_minus_commute)
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
        using ntv nv by (simp add: mem_ball dist_norm r_def)
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
            (simp add: inner_scaleR_right ac_simps)
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
              matrix_vector_mul_lid)
        have m2: "H *v (t *\<^sub>R v) = t *\<^sub>R (H *v v)"
          by (simp add: matrix_vector_mult_scaleR)
        show ?thesis
          unfolding A_def B_def m1 m2
          by (simp add: inner_diff_left inner_add_right inner_scaleR_left
              inner_scaleR_right inner_commute algebra_simps)
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
          using t by (simp add: abs_of_nonneg)
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
        using d0 t by (simp add: mult_nonneg_nonneg)
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

lemma inner_scaleR_diff_eq:
  fixes q v h :: "real^'n::finite" and c :: real
  shows "q \<bullet> h - c * (v \<bullet> h) = (q - c *\<^sub>R v) \<bullet> h"
  by (simp add: inner_diff_left)

lemma quartic_coeff_assoc:
  fixes c u w :: real
  shows "c * (2 * u * (2 * w)) = 4 * c * u * w"
  by (simp add: field_simps)

text \<open>Shifting a symmetric matrix by a multiple of the identity keeps it
  symmetric.\<close>

lemma transpose_shift_add:
  fixes A :: "real^'n::finite^'n"
  assumes s: "transpose A = A"
  shows "transpose (A + \<delta> *\<^sub>R mat 1) = A + \<delta> *\<^sub>R mat 1"
proof -
  have "transpose (A + \<delta> *\<^sub>R mat 1) $ i $ j = (A + \<delta> *\<^sub>R mat 1) $ i $ j"
    for i j
  proof -
    have "transpose (A + \<delta> *\<^sub>R mat 1) $ i $ j
        = A $ j $ i + \<delta> * (if j = i then 1 else 0)"
      by (simp add: transpose_def mat_def)
    also have "A $ j $ i = transpose A $ i $ j"
      by (simp add: transpose_def)
    also have "transpose A $ i $ j = A $ i $ j"
      using s by simp
    finally show ?thesis
      by (simp add: mat_def)
  qed
  then show ?thesis
    by (simp add: vec_eq_iff)
qed

lemma transpose_shift_diff:
  fixes A :: "real^'n::finite^'n"
  assumes s: "transpose A = A"
  shows "transpose (A - \<delta> *\<^sub>R mat 1) = A - \<delta> *\<^sub>R mat 1"
proof -
  have "A - \<delta> *\<^sub>R mat 1 = A + (- \<delta>) *\<^sub>R mat 1"
    by simp
  then show ?thesis
    using transpose_shift_add[OF s, of "- \<delta>"] by simp
qed

lemma test_fun_at_add_const:
  fixes \<phi> :: "real^'n::finite \<Rightarrow> real" and c :: real
  assumes tf: "test_fun_at \<phi> g H x"
  shows "test_fun_at (\<lambda>z. c + \<phi> z) g H x"
  unfolding test_fun_at_def
proof (intro conjI)
  show "transpose H = H" using tf unfolding test_fun_at_def by blast
next
  obtain e where e0: "0 < e"
    and d: "\<And>y. y \<in> ball x e \<Longrightarrow> (\<phi> has_derivative (\<lambda>h. g y \<bullet> h)) (at y)"
    using tf unfolding test_fun_at_def by blast
  have "((\<lambda>z. c + \<phi> z) has_derivative (\<lambda>h. g y \<bullet> h)) (at y)"
    if y: "y \<in> ball x e" for y
    using d[OF y] by (auto intro!: derivative_eq_intros)
  then show "\<exists>e>0. \<forall>y \<in> ball x e.
      ((\<lambda>z. c + \<phi> z) has_derivative (\<lambda>h. g y \<bullet> h)) (at y)"
    using e0 by blast
next
  show "(g has_derivative (\<lambda>h. H *v h)) (at x)"
    using tf unfolding test_fun_at_def by blast
qed

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
      using z by (simp add: v_def mem_ball dist_norm norm_minus_commute)
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
        using ntv nv by (simp add: mem_ball dist_norm r_def)
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
            (simp add: inner_scaleR_right ac_simps)
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
              matrix_vector_mul_lid)
        have m2: "H *v (t *\<^sub>R v) = t *\<^sub>R (H *v v)"
          by (simp add: matrix_vector_mult_scaleR)
        show ?thesis
          unfolding A_def B_def m1 m2
          by (simp add: inner_diff_left inner_add_right inner_scaleR_left
              inner_scaleR_right inner_commute algebra_simps)
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
          using t by (simp add: abs_of_nonneg)
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
        using d0 t by (simp add: mult_nonneg_nonneg)
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

theorem visc_supersol_env_local:
  fixes K :: "(real^'n::finite) set" and w \<phi> :: "real^'n \<Rightarrow> real"
    and g :: "real^'n \<Rightarrow> real^'n" and H :: "real^'n^'n"
  assumes sup: "visc_supersol_env k L K \<Omega> w"
    and x\<Omega>: "x \<in> \<Omega>"
    and tf: "test_fun_at \<phi> g H x"
    and wlo: "\<And>y. y \<in> K \<Longrightarrow> Bw \<le> w y"
    and phi: "\<And>y. y \<in> K \<Longrightarrow> \<phi> y \<le> B\<phi>"
    and r0: "0 < r"
    and lm: "\<And>y. y \<in> ball x r \<Longrightarrow> w x - \<phi> x \<le> w y - \<phi> y"
  shows "1 \<le> ell_op_usc k L (g x) H"
proof -
  have r40: "0 < r ^ 4" using r0 by simp
  define C where "C = max 0 ((w x - \<phi> x - Bw + B\<phi>) / r ^ 4)"
  have C0: "0 \<le> C" unfolding C_def by simp
  have Cbig: "w x - \<phi> x - Bw + B\<phi> \<le> C * r ^ 4"
  proof -
    have "(w x - \<phi> x - Bw + B\<phi>) / r ^ 4 \<le> C" unfolding C_def by simp
    then have "(w x - \<phi> x - Bw + B\<phi>) / r ^ 4 * r ^ 4 \<le> C * r ^ 4"
      by (rule mult_right_mono) (use r40 in linarith)
    then show ?thesis using r40 by simp
  qed
  define \<psi> where "\<psi> = (\<lambda>z. \<phi> z - C * ((z - x) \<bullet> (z - x))\<^sup>2)"
  define gg where
    "gg = (\<lambda>z. g z - (4 * C * ((z - x) \<bullet> (z - x))) *\<^sub>R (z - x))"
  have tf': "test_fun_at \<psi> gg H x"
    unfolding \<psi>_def gg_def by (rule test_fun_at_quartic_shift[OF tf])
  have ggx: "gg x = g x" unfolding gg_def by simp
  have psix: "\<psi> x = \<phi> x" unfolding \<psi>_def by simp
  have glob: "w x - \<psi> x \<le> w y - \<psi> y" if yK: "y \<in> K" for y
  proof (cases "y \<in> ball x r")
    case True
    have nn: "0 \<le> C * ((y - x) \<bullet> (y - x))\<^sup>2"
      by (rule mult_nonneg_nonneg[OF C0]) simp
    show ?thesis using lm[OF True] nn unfolding \<psi>_def psix[unfolded \<psi>_def] by simp
  next
    case False
    then have dxy: "r \<le> dist x y" by simp
    have sq: "r\<^sup>2 \<le> (y - x) \<bullet> (y - x)"
    proof -
      have "r \<le> norm (y - x)"
        using dxy by (simp add: dist_norm norm_minus_commute)
      then have "r\<^sup>2 \<le> (norm (y - x))\<^sup>2"
        using r0 by (intro power_mono) auto
      then show ?thesis by (simp add: dot_square_norm)
    qed
    have q4: "r ^ 4 \<le> ((y - x) \<bullet> (y - x))\<^sup>2"
    proof -
      have "(r\<^sup>2)\<^sup>2 \<le> ((y - x) \<bullet> (y - x))\<^sup>2"
        using sq by (intro power_mono) auto
      then show ?thesis by (simp add: power_even_eq)
    qed
    have cq: "C * r ^ 4 \<le> C * ((y - x) \<bullet> (y - x))\<^sup>2"
      by (rule mult_left_mono[OF q4 C0])
    have lo: "Bw \<le> w y" by (rule wlo[OF yK])
    have hi: "\<phi> y \<le> B\<phi>" by (rule phi[OF yK])
    show ?thesis
      unfolding \<psi>_def using Cbig cq lo hi by simp
  qed
  have "1 \<le> ell_op_usc k L (gg x) H"
    using sup[unfolded visc_supersol_env_def] x\<Omega> tf' glob by blast
  then show ?thesis unfolding ggx .
qed


text \<open>The mirror for subsolutions: ADDING a quartic deepens a local
  MAXIMUM and, for a large enough coefficient, makes it global over \<open>K\<close>.
  Reusing @{thm [source] test_fun_at_quartic_shift} with a negative
  coefficient means no new derivative computation is needed.\<close>

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


section \<open>P0: semicontinuity toolbox and the invariances of \<open>F\<close> (UNVERIFIED)\<close>

text \<open>Written 2026-08-11 WITHOUT verification (end-of-context batch); a
  fixer model repairs errors.  NOTE for the fixer: \<open>lsc_env\<close> and several
  of its lemmas below DUPLICATE Paper_Viscosity; DELETE the copies there
  (the planned P0 move).  Style: explicit rules, no linarith on compound
  divisions, no blast on obtains-elimination.\<close>

definition lsc_env :: "(real^'n::finite \<Rightarrow> real) \<Rightarrow> real^'n \<Rightarrow> real" where
  "lsc_env u x = (SUP e \<in> {0<..}. INF y \<in> ball x e. u y)"

definition usc_env :: "(real^'n::finite \<Rightarrow> real) \<Rightarrow> real^'n \<Rightarrow> real" where
  "usc_env u x = - lsc_env (\<lambda>y. - u y) x"

lemma lsc_env_bdd_above:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes B: "\<And>y. B \<le> u y"
  shows "bdd_above ((\<lambda>e. INF y \<in> ball x e. u y) ` {0<..})"
proof (rule bdd_aboveI[of _ "u x"])
  fix t assume "t \<in> (\<lambda>e. INF y \<in> ball x e. u y) ` {0<..}"
  then obtain e where e0: "0 < e" and te: "t = (INF y \<in> ball x e. u y)" by auto
  have "(INF y \<in> ball x e. u y) \<le> u x"
    by (rule cInf_lower) (use e0 B bdd_belowI[of _ B] in auto)
  then show "t \<le> u x" unfolding te .
qed

lemma lsc_env_le_self:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes B: "\<And>y. B \<le> u y"
  shows "lsc_env u x \<le> u x"
  unfolding lsc_env_def
proof (rule cSup_least)
  show "(\<lambda>e. INF y \<in> ball x e. u y) ` {0<..} \<noteq> {}" by auto
next
  fix t assume "t \<in> (\<lambda>e. INF y \<in> ball x e. u y) ` {0<..}"
  then obtain e where e0: "0 < e" and te: "t = (INF y \<in> ball x e. u y)" by auto
  show "t \<le> u x"
    unfolding te by (rule cInf_lower) (use e0 B bdd_belowI[of _ B] in auto)
qed

lemma lsc_env_ge:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes B: "\<And>y. B \<le> u y"
  shows "B \<le> lsc_env u x"
proof -
  have "B \<le> (INF y \<in> ball x 1. u y)"
    by (rule cInf_greatest) (use B in auto)
  also have "\<dots> \<le> lsc_env u x"
    unfolding lsc_env_def
    by (rule cSup_upper[OF _ lsc_env_bdd_above[OF B]]) auto
  finally show ?thesis .
qed

lemma usc_env_ge_self:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> B"
  shows "u x \<le> usc_env u x"
proof -
  have "lsc_env (\<lambda>y. - u y) x \<le> - u x"
    by (rule lsc_env_le_self[of "- B"]) (use B in auto)
  then show ?thesis unfolding usc_env_def by linarith
qed

lemma usc_env_le:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> B"
  shows "usc_env u x \<le> B"
proof -
  have "- B \<le> lsc_env (\<lambda>y. - u y) x"
    by (rule lsc_env_ge[of "- B"]) (use B in auto)
  then show ?thesis unfolding usc_env_def by linarith
qed

text \<open>The limsup bound Theorem 4.3's \<open>\<iota> \<downarrow> 1\<close> step consumes: values of \<open>u\<close>
  along a sequence tending to \<open>x\<close> are eventually below \<open>usc_env u x + \<epsilon>\<close>.\<close>

lemma usc_env_limsup_bound:
  fixes u :: "real^'n::finite \<Rightarrow> real" and zs :: "nat \<Rightarrow> real^'n"
  assumes B: "\<And>y. u y \<le> B" and lim: "zs \<longlonglongrightarrow> x"
    and lo: "\<And>j. c \<le> u (zs j)"
  shows "c \<le> usc_env u x"
proof (rule ccontr)
  assume "\<not> c \<le> usc_env u x"
  then have lt: "usc_env u x < c" by simp
  have "- c < lsc_env (\<lambda>y. - u y) x" using lt unfolding usc_env_def by simp
  then have "- c < (SUP e \<in> {0<..}. INF y \<in> ball x e. - u y)"
    unfolding lsc_env_def .
  then obtain t where tmem: "t \<in> (\<lambda>e. INF y \<in> ball x e. - u y) ` {0<..}"
    and tc: "- c < t"
    using less_cSup_iff[OF _ lsc_env_bdd_above[of "- B" "\<lambda>y. - u y" x]]
    by (auto simp del: mem_ball) (use B in force)
  from tmem obtain e where e0: "0 < e"
    and te: "t = (INF y \<in> ball x e. - u y)" by auto
  obtain N where N: "\<And>j. N \<le> j \<Longrightarrow> dist (zs j) x < e"
    using lim e0 unfolding lim_sequentially by blast
  have zin: "zs N \<in> ball x e" using N[of N] by (simp add: dist_commute)
  have "t \<le> - u (zs N)"
    unfolding te
    by (rule cInf_lower) (use zin bdd_belowI[of _ "- B"] B in auto)
  moreover have "c \<le> u (zs N)" by (rule lo)
  ultimately show False using tc by linarith
qed

subsection \<open>Attainment and extension for semicontinuous functions\<close>

lemma lsc_attains_inf_gen:
  fixes f :: "real^'n::finite \<Rightarrow> real" and S :: "(real^'n) set"
  assumes lsc: "\<And>c z. c < f z \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> c < f y"
    and B: "\<And>y. y \<in> S \<Longrightarrow> B \<le> f y"
    and cS: "compact S" and neS: "S \<noteq> {}"
  obtains z where "z \<in> S" and "\<And>y. y \<in> S \<Longrightarrow> f z \<le> f y"
proof -
  define m where "m = (INF y \<in> S. f y)"
  have bdd: "bdd_below (f ` S)" by (rule bdd_belowI[of _ B]) (use B in auto)
  have mlow: "\<And>y. y \<in> S \<Longrightarrow> m \<le> f y"
    unfolding m_def by (rule cInf_lower[OF _ bdd]) auto
  have "\<forall>j. \<exists>zz. zz \<in> S \<and> f zz < m + 1 / real (Suc j)"
  proof
    fix j :: nat
    have "m < m + 1 / real (Suc j)" by simp
    then have "\<exists>t \<in> f ` S. t < m + 1 / real (Suc j)"
      unfolding m_def using cInf_less_iff[OF _ bdd] neS by auto
    then show "\<exists>zz. zz \<in> S \<and> f zz < m + 1 / real (Suc j)" by auto
  qed
  then obtain zs where zsS: "\<And>j. zs j \<in> S"
    and zsm: "\<And>j. f (zs j) < m + 1 / real (Suc j)" by metis
  obtain z r where zS: "z \<in> S" and rm: "strict_mono r"
    and lim: "(zs \<circ> r) \<longlonglongrightarrow> z"
    using compact_eq_seq_compact_metric[THEN iffD1, OF cS]
      zsS unfolding seq_compact_def by blast
  have zle: "f z \<le> m"
  proof (rule ccontr)
    assume "\<not> f z \<le> m"
    then have mlt: "m < f z" by simp
    define c where "c = (m + f z) / 2"
    have c2: "2 * c = m + f z" unfolding c_def by simp
    have cm: "m < c" and cz: "c < f z" using mlt c2 by linarith+
    obtain e where e0: "0 < e"
      and en: "\<forall>y. dist z y < e \<longrightarrow> c < f y" using lsc[OF cz] by blast
    obtain N1 where N1: "\<And>l. N1 \<le> l \<Longrightarrow> dist ((zs \<circ> r) l) z < e"
      using lim e0 unfolding lim_sequentially by blast
    have "(\<lambda>l. 1 / real (Suc (r l))) \<longlonglongrightarrow> 0"
      using LIMSEQ_subseq_LIMSEQ[OF _ rm] LIMSEQ_inverse_real_of_nat
      by (simp add: o_def divide_inverse)
    then obtain N2 where N2: "\<And>l. N2 \<le> l \<Longrightarrow> 1 / real (Suc (r (l))) < c - m"
      using cm order_tendstoD(2)[of _ 0 sequentially "c - m"]
      unfolding eventually_sequentially by fastforce
    define l where "l = max N1 N2"
    have "c < f (zs (r l))"
      using en N1[of l] unfolding l_def by (simp add: o_def dist_commute)
    moreover have "f (zs (r l)) < m + 1 / real (Suc (r l))" by (rule zsm)
    moreover have "1 / real (Suc (r l)) < c - m"
      using N2[of l] unfolding l_def by simp
    ultimately show False by linarith
  qed
  show ?thesis
  proof (rule that[OF zS])
    fix y assume yS: "y \<in> S"
    show "f z \<le> f y" using zle mlow[OF yS] by linarith
  qed
qed

lemma usc_attains_sup_gen:
  fixes f :: "real^'n::finite \<Rightarrow> real" and S :: "(real^'n) set"
  assumes usc: "\<And>c z. f z < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> f y < c"
    and B: "\<And>y. y \<in> S \<Longrightarrow> f y \<le> B"
    and cS: "compact S" and neS: "S \<noteq> {}"
  obtains z where "z \<in> S" and "\<And>y. y \<in> S \<Longrightarrow> f y \<le> f z"
proof -
  have lsc': "\<And>c z. c < - f z \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> c < - f y"
  proof -
    fix c z assume "c < - f z"
    then have "f z < - c" by linarith
    from usc[OF this] obtain e where "0 < e"
      and "\<forall>y. dist z y < e \<longrightarrow> f y < - c" by blast
    then show "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> c < - f y" by force
  qed
  obtain z where zS: "z \<in> S" and zm: "\<And>y. y \<in> S \<Longrightarrow> - f z \<le> - f y"
  proof (rule lsc_attains_inf_gen[OF lsc' _ cS neS, of "- B"])
    fix y assume "y \<in> S" then show "- B \<le> - f y" using B by simp
  qed (rule that)
  show ?thesis
  proof (rule that[OF zS])
    fix y assume "y \<in> S" then show "f y \<le> f z" using zm by simp
  qed
qed

text \<open>Extension by a constant BELOW the minimum is usc (extension by \<open>0\<close>
  is NOT — recorded trap).  Sequential form of usc, matching the repo.\<close>

lemma usc_extension_bounded:
  fixes u :: "real^'n::finite \<Rightarrow> real" and K :: "(real^'n) set"
  assumes cl: "closed K"
    and usc: "\<And>c z. z \<in> K \<Longrightarrow> u z < c \<Longrightarrow>
      \<exists>e>0. \<forall>y \<in> K. dist z y < e \<longrightarrow> u y < c"
    and Bd: "\<And>y. y \<in> K \<Longrightarrow> \<bar>u y\<bar> \<le> B"
  obtains u' where "\<And>y. y \<in> K \<Longrightarrow> u' y = u y"
    and "\<And>y. \<bar>u' y\<bar> \<le> B"
    and "\<And>c z. u' z < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> u' y < c"
proof -
  define u' where "u' = (\<lambda>y. if y \<in> K then u y else - B)"
  have agree: "\<And>y. y \<in> K \<Longrightarrow> u' y = u y" unfolding u'_def by simp
  have B0: "0 \<le> B"
  proof (cases "K = {}")
    case True then show ?thesis
      using abs_ge_zero Bd by (cases "0 \<le> B") auto
  next
    case False
    then obtain y where "y \<in> K" by blast
    from Bd[OF this] show ?thesis by linarith
  qed
  have bnd: "\<And>y. \<bar>u' y\<bar> \<le> B"
    unfolding u'_def using Bd B0 by auto
  have ue: "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> u' y < c"
    if lt: "u' z < c" for c z
  proof (cases "z \<in> K")
    case True
    have uzc: "u z < c" using lt agree[OF True] by simp
    obtain e where e0: "0 < e"
      and eK: "\<forall>y \<in> K. dist z y < e \<longrightarrow> u y < c"
      using usc[OF True uzc] by blast
    have "- B \<le> u z" using Bd[OF True] by linarith
    then have mBc: "- B < c" using uzc by linarith
    have "u' y < c" if "dist z y < e" for y
      using eK that mBc unfolding u'_def by (cases "y \<in> K") auto
    then show ?thesis using e0 by blast
  next
    case False
    then have "0 < infdist z K \<or> K = {}"
      using cl infdist_pos_not_in_closed by auto
    then obtain d where d0: "0 < d" and dK: "\<And>y. y \<in> K \<Longrightarrow> d \<le> dist z y"
      using infdist_le2
      by (metis all_not_in_conv dual_order.strict_iff_not
          infdist_le zero_less_one)
    have mBc: "- B < c" using lt False unfolding u'_def by simp
    have "u' y < c" if dy: "dist z y < d" for y
    proof -
      have "y \<notin> K" using dK dy by fastforce
      then show ?thesis using mBc unfolding u'_def by simp
    qed
    then show ?thesis using d0 by blast
  qed
  show ?thesis by (rule that[OF agree bnd ue])
qed

subsection \<open>The invariances of \<open>F\<close> — the paper's display (4.4)\<close>

lemma ell_op_scale:
  fixes p :: "real^'n::finite" and M :: "real^'n^'n"
  assumes c0: "0 < c"
  shows "ell_op k L (c *\<^sub>R p) M = ell_op k L p M"
proof -
  have "feasible k L (c *\<^sub>R p) = feasible k L p"
    by (rule feasible_scale[OF c0])
  then show ?thesis unfolding ell_op_def by simp
qed

lemma ell_op_hess_scale:
  fixes p :: "real^'n::finite" and M :: "real^'n^'n"
  assumes c0: "0 < c"
  shows "ell_op k L p (c *\<^sub>R M) = c * ell_op k L p M"
proof -
  have tr: "\<And>a. - trace ((c *\<^sub>R M) ** a) / 2 = c * (- trace (M ** a) / 2)"
  proof -
    fix a :: "real^'n^'n"
    have "(c *\<^sub>R M) ** a = c *\<^sub>R (M ** a)"
      by (simp add: matrix_scaleR_ac scaleR_matrix_mult_left)
    then have "trace ((c *\<^sub>R M) ** a) = c * trace (M ** a)"
      by (simp add: trace_scaleR)
    then show "- trace ((c *\<^sub>R M) ** a) / 2 = c * (- trace (M ** a) / 2)"
      by simp
  qed
  have img: "(\<lambda>a. - trace ((c *\<^sub>R M) ** a) / 2) ` feasible k L p
      = (\<lambda>t. c * t) ` (\<lambda>a. - trace (M ** a) / 2) ` feasible k L p"
    unfolding image_image by (rule image_cong[OF refl]) (rule tr)
  show ?thesis
    unfolding ell_op_def img
    by (rule cInf_scale_pos) (rule c0)
qed

text \<open>Fixer note: if \<open>cInf_scale_pos\<close>, \<open>trace_scaleR\<close> or
  \<open>scaleR_matrix_mult_left\<close> do not exist under these names, prove them
  inline (all are one-liners over \<open>Inf ((*) c ` A) = c * Inf A\<close> for
  \<open>c > 0\<close> — \<open>Inf\<close> version of \<open>cSup_scale\<close> — and entrywise trace algebra).\<close>

lemma ell_op_conj_rot:
  fixes p :: "real^'n::finite" and M :: "real^'n^'n" and R :: "real^'n^'n"
  assumes orth: "orthogonal_matrix R"
  shows "ell_op k L (R *v p) (R ** M ** transpose R) = ell_op k L p M"
proof -
  have bij: "(\<lambda>a. R ** a ** transpose R) ` feasible k L p
      = feasible k L (R *v p)"
    by (rule feasible_conj[OF orth])
  have tr: "\<And>a. - trace ((R ** M ** transpose R) ** (R ** a ** transpose R)) / 2
      = - trace (M ** a) / 2"
  proof -
    fix a :: "real^'n^'n"
    have RtR: "transpose R ** R = mat 1"
      using orth unfolding orthogonal_matrix_def by blast
    have "(R ** M ** transpose R) ** (R ** a ** transpose R)
        = R ** (M ** a) ** transpose R"
      by (metis RtR matrix_mul_assoc matrix_mul_rid)
    then have "trace ((R ** M ** transpose R) ** (R ** a ** transpose R))
        = trace (M ** a)"
      by (metis orth orthogonal_matrix_def trace_conj_orth)
    then show "- trace ((R ** M ** transpose R) ** (R ** a ** transpose R)) / 2
        = - trace (M ** a) / 2" by simp
  qed
  have "(\<lambda>a. - trace ((R ** M ** transpose R) ** a) / 2) ` feasible k L (R *v p)
      = (\<lambda>a. - trace (M ** a) / 2) ` feasible k L p"
    unfolding bij[symmetric] image_image
    by (rule image_cong[OF refl]) (rule tr)
  then show ?thesis unfolding ell_op_def by simp
qed

text \<open>Fixer notes.  (1) Check \<open>feasible_conj\<close>'s exact statement (Envelopes
  1029): it may be stated with two orthogonality hypotheses or with the
  image in the other direction; adapt \<open>bij\<close> accordingly.  (2) If
  \<open>trace_conj_orth\<close> is absent: \<open>trace (R ** N ** transpose R) = trace N\<close>
  follows from cyclicity \<open>trace (A ** B) = trace (B ** A)\<close> (the repo has a
  form of this near the mgap material) and \<open>transpose R ** R = mat 1\<close>.
  (3) The envelope versions \<open>ell_op_usc\<close>/\<open>ell_op_lsc\<close> of both invariances
  are P0's remaining item: the transform \<open>(p, M) \<mapsto> (R *v p, R ** M ** R\<^sup>T)\<close>
  is an isometry of the product (orthogonal matrices preserve the norms
  entrywise up to the fixed constants), so it maps \<open>ball z e\<close> BIJECTIVELY
  onto \<open>ball (f z) e\<close>; conjugate the INF/SUP through the bijection exactly
  as \<open>ball_prod_shift_snd\<close> does for translations.\<close>

end
