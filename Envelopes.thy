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

end
