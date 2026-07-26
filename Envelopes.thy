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

end
