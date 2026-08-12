(*
  Title:   Eigenvalues.thy
  Content: Ky Fan partial sums and ordered eigenvalues of a real symmetric
           matrix, developed basis-free, towards Eq. (3.6) of
           arXiv:2512.17702 (Lai/Shkolnikov/Soner).

  Design.  Relative_Arbitrage_Convexity already defines

    Pi_proj a m = Inf {trace (a ** P) | is_proj P, trace P = m}

  which is the sum of the m SMALLEST eigenvalues of a -- basis-free by
  construction, so no well-definedness argument is needed.  Dually,

    kyfan m a = Sup {trace (a ** P) | is_proj P, trace P = m}

  is the sum of the m LARGEST, and the i-th largest eigenvalue is the
  difference  lam i a = kyfan i a - kyfan (i-1) a.  This route avoids
  defining eigenvalues by sorting a multiset and then having to prove
  independence of the eigenbasis: here basis-independence is free, and the
  Courant--Fischer / Ky Fan theorems become EVALUATION lemmas rather than
  well-definedness obligations.

  The one genuinely combinatorial ingredient is the linear program in
  Section 1: maximising a linear functional over the vectors t with
  0 <= t <= 1 and sum t = m puts the mass on the m largest coefficients.
  That is what turns "trace (a ** P) for an arbitrary rank-m projection P"
  into "a sum of m eigenvalues".
*)

theory Eigenvalues
  imports Lemma_2_1_Exact
begin

section \<open>The linear program on the simplex inside a box\<close>

text \<open>Among the \<open>m\<close>-element subsets of a finite set there is one whose
  \<open>f\<close>-values all dominate those outside it: take a subset maximising the
  \<open>f\<close>-sum, and swap.\<close>

lemma exists_top_subset:
  fixes f :: "'a \<Rightarrow> real"
  assumes finU: "finite U" and m: "m \<le> card U"
  obtains T where "T \<subseteq> U" "card T = m"
    and "\<And>i j. i \<in> T \<Longrightarrow> j \<in> U - T \<Longrightarrow> f j \<le> f i"
proof -
  define Sub where "Sub = {T. T \<subseteq> U \<and> card T = m}"
  have finSub: "finite Sub"
  proof (rule finite_subset)
    show "Sub \<subseteq> Pow U" by (auto simp: Sub_def)
    show "finite (Pow U)" using finU by simp
  qed
  have neSub: "Sub \<noteq> {}"
  proof -
    obtain T where "T \<subseteq> U" "card T = m"
      using obtain_subset_with_card_n[OF m] by metis
    then show ?thesis by (auto simp: Sub_def)
  qed
  define g where "g = (\<lambda>T. \<Sum>i\<in>T. f i)"
  have "Max (g ` Sub) \<in> g ` Sub"
    by (rule Max_in) (use finSub neSub in auto)
  then obtain T where T: "T \<in> Sub" and gT: "g T = Max (g ` Sub)"
    by (metis imageE)
  have Tmax: "g T' \<le> g T" if "T' \<in> Sub" for T'
    unfolding gT using that finSub by (intro Max_ge) auto
  have Tsub: "T \<subseteq> U" and cardT: "card T = m"
    using T by (auto simp: Sub_def)
  have finT: "finite T"
    using Tsub finU by (rule finite_subset)
  have thresh: "f j \<le> f i" if i: "i \<in> T" and j: "j \<in> U - T" for i j
  proof -
    have jT: "j \<notin> T" and jU: "j \<in> U"
      using j by auto
    have finTi: "finite (T - {i})"
      using finT by simp
    have jTi: "j \<notin> T - {i}"
      using jT by simp
    have m_pos: "0 < m"
      using i cardT finT by (metis card_gt_0_iff empty_iff)
    define T' where "T' = insert j (T - {i})"
    have cardT': "card T' = m"
    proof -
      have "card T' = Suc (card (T - {i}))"
        unfolding T'_def using jTi finTi by simp
      also have "card (T - {i}) = m - 1"
        using finT i cardT by simp
      also have "Suc (m - 1) = m"
        using m_pos by simp
      finally show ?thesis .
    qed
    have T'sub: "T' \<subseteq> U"
      unfolding T'_def using jU Tsub by auto
    have "g T' = f j + (\<Sum>u\<in>T - {i}. f u)"
      unfolding g_def T'_def using jTi finTi by simp
    moreover have "g T = f i + (\<Sum>u\<in>T - {i}. f u)"
      unfolding g_def using finT i by (simp add: sum.remove)
    moreover have "g T' \<le> g T"
      using cardT' T'sub by (intro Tmax) (simp add: Sub_def)
    ultimately show ?thesis
      by simp
  qed
  show thesis
    by (rule that[OF Tsub cardT thresh])
qed

text \<open>The linear program: if \<open>0 \<le> t \<le> 1\<close> pointwise and \<open>\<Sum> t = m\<close>, then
  \<open>\<Sum> f t\<close> is dominated by the sum of \<open>f\<close> over some \<open>m\<close>-element set. The
  proof needs no vertex enumeration --- subtracting the threshold value
  \<open>\<theta>\<close> makes both halves one-line monotonicity steps.\<close>

lemma sum_weighted_le_top_subset:
  fixes f t :: "'a \<Rightarrow> real"
  assumes finU: "finite U" and m: "m \<le> card U"
    and t0: "\<And>i. i \<in> U \<Longrightarrow> 0 \<le> t i" and t1: "\<And>i. i \<in> U \<Longrightarrow> t i \<le> 1"
    and tsum: "(\<Sum>i\<in>U. t i) = real m"
  obtains T where "T \<subseteq> U" "card T = m"
    and "(\<Sum>i\<in>U. f i * t i) \<le> (\<Sum>i\<in>T. f i)"
proof (cases "m = 0")
  case True
  have "t i = 0" if i: "i \<in> U" for i
  proof -
    have "(\<Sum>i\<in>U. t i) = 0"
      using tsum True by simp
    then show ?thesis
      using finU t0 i by (simp add: sum_nonneg_eq_0_iff)
  qed
  then have "(\<Sum>i\<in>U. f i * t i) = 0"
    by simp
  then show thesis
    using True by (intro that[of "{}"]) auto
next
  case False
  then have m_pos: "0 < m" by simp
  obtain T where Tsub: "T \<subseteq> U" and cardT: "card T = m"
    and thresh: "\<And>i j. i \<in> T \<Longrightarrow> j \<in> U - T \<Longrightarrow> f j \<le> f i"
    using exists_top_subset[OF finU m] by metis
  have finT: "finite T"
    using Tsub finU by (rule finite_subset)
  have Tne: "T \<noteq> {}"
    using cardT m_pos by auto
  define \<theta> where "\<theta> = Min (f ` T)"
  have lowT: "\<theta> \<le> f i" if "i \<in> T" for i
    unfolding \<theta>_def using finT that by simp
  have highD: "f j \<le> \<theta>" if j: "j \<in> U - T" for j
    unfolding \<theta>_def using finT Tne thresh[OF _ j] by (subst Min_ge_iff) auto
  have inT: "(\<Sum>i\<in>T. (f i - \<theta>) * t i) \<le> (\<Sum>i\<in>T. f i - \<theta>)"
  proof (rule sum_mono)
    fix i assume i: "i \<in> T"
    have "(f i - \<theta>) * t i \<le> (f i - \<theta>) * 1"
      using lowT[OF i] t1[OF subsetD[OF Tsub i]] by (intro mult_left_mono) auto
    then show "(f i - \<theta>) * t i \<le> f i - \<theta>" by simp
  qed
  have outT: "(\<Sum>i\<in>U - T. (f i - \<theta>) * t i) \<le> 0"
  proof (rule sum_nonpos)
    fix i assume i: "i \<in> U - T"
    have "f i - \<theta> \<le> 0"
      using highD[OF i] by simp
    then show "(f i - \<theta>) * t i \<le> 0"
      using t0[OF DiffD1[OF i]] by (simp add: mult_nonpos_nonneg)
  qed
  have "(\<Sum>i\<in>U. f i * t i) = (\<Sum>i\<in>U. (f i - \<theta>) * t i) + \<theta> * (\<Sum>i\<in>U. t i)"
    by (simp add: sum.distrib[symmetric] algebra_simps sum_distrib_left)
  also have "(\<Sum>i\<in>U. (f i - \<theta>) * t i)
      = (\<Sum>i\<in>U - T. (f i - \<theta>) * t i) + (\<Sum>i\<in>T. (f i - \<theta>) * t i)"
    using Tsub finU by (rule sum.subset_diff)
  also have "\<dots> \<le> 0 + (\<Sum>i\<in>T. f i - \<theta>)"
    using outT inT by (rule add_mono)
  finally have "(\<Sum>i\<in>U. f i * t i) \<le> (\<Sum>i\<in>T. f i - \<theta>) + \<theta> * real m"
    using tsum by simp
  also have "(\<Sum>i\<in>T. f i - \<theta>) = (\<Sum>i\<in>T. f i) - \<theta> * real m"
    using cardT by (simp add: sum_subtractf algebra_simps)
  finally have "(\<Sum>i\<in>U. f i * t i) \<le> (\<Sum>i\<in>T. f i)"
    by simp
  then show thesis
    by (rule that[OF Tsub cardT])
qed

section \<open>The quadratic form of an orthogonal projection lies in \<open>[0,1]\<close>\<close>

text \<open>These are the two facts that make the coefficients \<open>t\<^sub>u = u \<bullet> P u\<close> of
  the next section admissible for the linear program above.\<close>

lemma proj_quadform_self:
  assumes P: "is_proj P"
  shows "u \<bullet> (P *v u) = (P *v u) \<bullet> (P *v u)"
proof -
  have "u \<bullet> (P *v u) = u \<bullet> ((P ** P) *v u)"
    using P by (simp add: is_proj_def)
  also have "\<dots> = u \<bullet> (P *v (P *v u))"
    by (simp add: matrix_vector_mul_assoc)
  also have "\<dots> = (transpose P *v u) \<bullet> (P *v u)"
    by (rule inner_transpose_matrix)
  also have "\<dots> = (P *v u) \<bullet> (P *v u)"
    using P by (simp add: is_proj_def)
  finally show ?thesis .
qed

lemma proj_quadform_nonneg:
  assumes P: "is_proj P"
  shows "0 \<le> u \<bullet> (P *v u)"
  unfolding proj_quadform_self[OF P] by simp

lemma proj_quadform_le_self:
  assumes P: "is_proj P"
  shows "u \<bullet> (P *v u) \<le> u \<bullet> u"
proof -
  define x where "x = P *v u"
  define y where "y = u - P *v u"
  have u_eq: "u = x + y"
    by (simp add: x_def y_def)
  have q: "u \<bullet> x = x \<bullet> x"
    unfolding x_def by (rule proj_quadform_self[OF P])
  have xy: "x \<bullet> y = 0"
  proof -
    have "x \<bullet> y = x \<bullet> u - x \<bullet> x"
      by (simp add: y_def x_def inner_diff_right)
    also have "x \<bullet> u = u \<bullet> x"
      by (rule inner_commute)
    finally show ?thesis
      using q by simp
  qed
  have "u \<bullet> u = (x + y) \<bullet> (x + y)"
    by (simp add: u_eq)
  also have "\<dots> = x \<bullet> x + x \<bullet> y + (y \<bullet> x + y \<bullet> y)"
    by (simp add: inner_add_left inner_add_right)
  also have "\<dots> = x \<bullet> x + y \<bullet> y"
    using xy by (simp add: inner_commute[of y x])
  finally have "u \<bullet> u = x \<bullet> x + y \<bullet> y" .
  then show ?thesis
    using q by (simp add: x_def)
qed

lemma proj_quadform_le_one:
  assumes P: "is_proj P" and B: "onormal B" and u: "u \<in> B"
  shows "u \<bullet> (P *v u) \<le> 1"
  using proj_quadform_le_self[OF P, of u] B u by simp

section \<open>The trace against a projection, read off in an eigenbasis\<close>

text \<open>If \<open>B\<close> is an orthonormal eigenbasis of the symmetric matrix \<open>a\<close> with
  eigenvalues \<open>\<lambda>\<^sub>u = u \<bullet> a u\<close>, then for every matrix \<open>P\<close>

    \<open>trace (a ** P) = \<Sum>\<^sub>u \<lambda>\<^sub>u * (u \<bullet> P u)\<close>,

  so that a projection of trace \<open>m\<close> produces exactly the weights of the
  linear program: in \<open>[0,1]\<close> and summing to \<open>m\<close>.\<close>

lemma trace_mult_eigen_weights:
  fixes a :: "real^'n::finite^'n"
  assumes B: "onormal B" "span B = UNIV"
    and sym: "transpose a = a"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
  shows "trace (a ** P) = (\<Sum>u\<in>B. (u \<bullet> (a *v u)) * (u \<bullet> (P *v u)))"
proof -
  have "trace (a ** P) = (\<Sum>u\<in>B. u \<bullet> ((a ** P) *v u))"
    by (rule trace_onormal_basis[OF B])
  also have "\<dots> = (\<Sum>u\<in>B. (u \<bullet> (a *v u)) * (u \<bullet> (P *v u)))"
  proof (rule sum.cong[OF refl])
    fix u assume u: "u \<in> B"
    text \<open>Name the eigenvalue: \<open>eig\<close> rewrites \<open>a u\<close> into a term that again
      contains \<open>a u\<close>, so it must not be handed to the simplifier directly.\<close>
    define c where "c = u \<bullet> (a *v u)"
    have au: "a *v u = c *\<^sub>R u"
      unfolding c_def by (rule eig[OF u])
    have "u \<bullet> ((a ** P) *v u) = u \<bullet> (a *v (P *v u))"
      by (simp add: matrix_vector_mul_assoc)
    also have "\<dots> = (P *v u) \<bullet> (a *v u)"
      by (rule sym_inner_swap[OF sym])
    also have "\<dots> = (P *v u) \<bullet> (c *\<^sub>R u)"
      by (simp add: au)
    also have "\<dots> = c * ((P *v u) \<bullet> u)"
      by simp
    also have "\<dots> = (u \<bullet> (a *v u)) * (u \<bullet> (P *v u))"
      unfolding c_def by (simp add: inner_commute)
    finally show "u \<bullet> ((a ** P) *v u) = (u \<bullet> (a *v u)) * (u \<bullet> (P *v u))" .
  qed
  finally show ?thesis .
qed

text \<open>The weights of a trace-\<open>m\<close> projection sum to \<open>m\<close>.\<close>

lemma proj_weights_sum:
  fixes P :: "real^'n::finite^'n"
  assumes B: "onormal B" "span B = UNIV" and P: "trace P = real m"
  shows "(\<Sum>u\<in>B. u \<bullet> (P *v u)) = real m"
  using trace_onormal_basis[OF B, of P] P by simp

section \<open>Ky Fan partial sums: the sum of the \<open>m\<close> largest eigenvalues\<close>

text \<open>The dual of \<open>Pi_proj\<close> of Eq. (2.1). Like \<open>Pi_proj\<close> it is manifestly
  independent of any choice of basis; unlike a definition by sorting a
  multiset of eigenvalues, it needs no well-definedness proof.\<close>

definition kyfan :: "nat \<Rightarrow> real^'n::finite^'n \<Rightarrow> real" where
  "kyfan m a = Sup {trace (a ** P) | P. is_proj P \<and> trace P = real m}"

text \<open>The set of \<open>m\<close>-element subsets of the eigenbasis, and the largest
  \<open>m\<close>-fold eigenvalue sum. Both are used only inside the proof of
  \<open>kyfan_attained\<close>; they are auxiliary to the basis-free \<open>kyfan\<close>.\<close>

lemma spectral_proj_trace:
  fixes a :: "real^'n::finite^'n"
  assumes B: "onormal B" and T: "T \<subseteq> B" "card T = m"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
  shows "is_proj (\<Sum>u\<in>T. outer_prod u u)"
    and "trace (\<Sum>u\<in>T. outer_prod u u) = real m"
    and "trace (a ** (\<Sum>u\<in>T. outer_prod u u)) = (\<Sum>u\<in>T. u \<bullet> (a *v u))"
proof -
  have onT: "onormal T"
    by (rule onormal_subset[OF B T(1)])
  show "is_proj (\<Sum>u\<in>T. outer_prod u u)"
    by (rule onormal_proj(1)[OF onT])
  show "trace (\<Sum>u\<in>T. outer_prod u u) = real m"
    using onormal_proj(2)[OF onT] T(2) by simp
  show "trace (a ** (\<Sum>u\<in>T. outer_prod u u)) = (\<Sum>u\<in>T. u \<bullet> (a *v u))"
    by (rule trace_mult_spectral_proj[OF B T(1) eig])
qed

text \<open>Ky Fan's maximum principle, in the form needed here: the supremum
  defining \<open>kyfan m a\<close> is attained at a spectral projection, i.e. it is a
  sum of \<open>m\<close> eigenvalues --- necessarily the \<open>m\<close> largest ones, since every
  other \<open>m\<close>-element subset of the eigenbasis competes in the same
  supremum.\<close>

theorem kyfan_attained:
  fixes a :: "real^'n::finite^'n"
  assumes B: "onormal B" "span B = UNIV"
    and sym: "transpose a = a"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
    and m: "m \<le> CARD('n)"
  obtains T where "T \<subseteq> B" "card T = m"
    and "kyfan m a = (\<Sum>u\<in>T. u \<bullet> (a *v u))"
    and "\<And>T'. T' \<subseteq> B \<Longrightarrow> card T' = m
           \<Longrightarrow> (\<Sum>u\<in>T'. u \<bullet> (a *v u)) \<le> (\<Sum>u\<in>T. u \<bullet> (a *v u))"
proof -
  define lam where "lam = (\<lambda>u :: real^'n. u \<bullet> (a *v u))"
  define Subs where "Subs = {T. T \<subseteq> B \<and> card T = m}"
  define S where "S = {trace (a ** P) | P :: real^'n^'n. is_proj P \<and> trace P = real m}"
  have finB: "finite B"
    by (rule onormal_finite[OF B(1)])
  have cardB: "card B = CARD('n)"
    by (rule onormal_span_card[OF B])
  have m_le: "m \<le> card B"
    using m cardB by simp
  have finSubs: "finite Subs"
  proof (rule finite_subset)
    show "Subs \<subseteq> Pow B" by (auto simp: Subs_def)
    show "finite (Pow B)" using finB by simp
  qed
  have neSubs: "Subs \<noteq> {}"
  proof -
    obtain T where "T \<subseteq> B" "card T = m"
      using obtain_subset_with_card_n[OF m_le] by metis
    then show ?thesis by (auto simp: Subs_def)
  qed
  define g where "g = (\<lambda>T. \<Sum>u\<in>T. lam u)"
  have "Max (g ` Subs) \<in> g ` Subs"
    by (rule Max_in) (use finSubs neSubs in auto)
  then obtain T0 where T0: "T0 \<in> Subs" and gT0: "g T0 = Max (g ` Subs)"
    by (metis imageE)
  have T0sub: "T0 \<subseteq> B" and cardT0: "card T0 = m"
    using T0 by (auto simp: Subs_def)
  have T0max: "g T' \<le> g T0" if "T' \<in> Subs" for T'
    unfolding gT0 using that finSubs by (intro Max_ge) auto
  text \<open>Every competitor in the supremum is dominated by \<open>g T0\<close>: expand the
    trace in the eigenbasis and apply the linear program.\<close>
  have upper: "v \<le> g T0" if v: "v \<in> S" for v
  proof -
    obtain P :: "real^'n^'n" where P: "is_proj P" "trace P = real m"
      and vP: "v = trace (a ** P)"
      using v by (auto simp: S_def)
    define t where "t = (\<lambda>u :: real^'n. u \<bullet> (P *v u))"
    have t0: "0 \<le> t u" for u
      unfolding t_def by (rule proj_quadform_nonneg[OF P(1)])
    have t1: "t u \<le> 1" if "u \<in> B" for u
      unfolding t_def by (rule proj_quadform_le_one[OF P(1) B(1) that])
    have tsum: "(\<Sum>u\<in>B. t u) = real m"
      unfolding t_def by (rule proj_weights_sum[OF B P(2)])
    have vexp: "v = (\<Sum>u\<in>B. lam u * t u)"
      unfolding vP lam_def t_def
      by (rule trace_mult_eigen_weights[OF B sym eig])
    obtain T where T: "T \<subseteq> B" "card T = m"
      and le: "(\<Sum>u\<in>B. lam u * t u) \<le> (\<Sum>u\<in>T. lam u)"
      using sum_weighted_le_top_subset[OF finB m_le t0 t1 tsum] by metis
    have "v \<le> g T"
      unfolding vexp g_def by (rule le)
    also have "g T \<le> g T0"
      using T by (intro T0max) (simp add: Subs_def)
    finally show ?thesis .
  qed
  text \<open>And \<open>g T0\<close> is itself attained, by the spectral projection onto \<open>T0\<close>.\<close>
  have member: "g T0 \<in> S"
  proof -
    define P0 where "P0 = (\<Sum>u\<in>T0. outer_prod u u)"
    have p1: "is_proj P0" and p2: "trace P0 = real m"
      and tr: "trace (a ** P0) = (\<Sum>u\<in>T0. lam u)"
      unfolding P0_def lam_def
      using spectral_proj_trace[OF B(1) T0sub cardT0 eig] by blast+
    have "g T0 = trace (a ** P0)"
      unfolding g_def using tr by simp
    then show ?thesis
      unfolding S_def using p1 p2 by blast
  qed
  have kf: "kyfan m a = g T0"
  proof -
    have "Sup S = g T0"
    proof (rule antisym)
      show "Sup S \<le> g T0"
        using member upper by (intro cSup_least) auto
      show "g T0 \<le> Sup S"
        using member upper by (intro cSup_upper bdd_aboveI[of _ "g T0"]) auto
    qed
    then show ?thesis
      by (simp add: kyfan_def S_def)
  qed
  show thesis
  proof (rule that[OF T0sub cardT0])
    show "kyfan m a = (\<Sum>u\<in>T0. u \<bullet> (a *v u))"
      using kf by (simp add: g_def lam_def)
    fix T' assume "T' \<subseteq> B" "card T' = m"
    then show "(\<Sum>u\<in>T'. u \<bullet> (a *v u)) \<le> (\<Sum>u\<in>T0. u \<bullet> (a *v u))"
      using T0max[of T'] by (simp add: Subs_def g_def lam_def)
  qed
qed

section \<open>Boundedness, and \<open>kyfan\<close> as a genuine supremum\<close>

text \<open>The defining set is bounded above by \<open>\<Sum>\<^sub>u |\<lambda>\<^sub>u|\<close>, again by the weight
  representation: the weights lie in \<open>[0,1]\<close>. This is what licenses the
  \<open>cSup\<close> rules below.\<close>

lemma kyfan_bdd_above:
  fixes a :: "real^'n::finite^'n"
  assumes sym: "transpose a = a"
  shows "bdd_above {trace (a ** P) | P :: real^'n^'n. is_proj P \<and> trace P = real m}"
proof -
  obtain B where B: "onormal B" "span B = UNIV"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
    using symmetric_eigenbasis[OF sym] by metis
  show ?thesis
  proof (rule bdd_aboveI)
    fix x
    assume "x \<in> {trace (a ** P) | P :: real^'n^'n. is_proj P \<and> trace P = real m}"
    then obtain P :: "real^'n^'n" where P: "is_proj P" and x: "x = trace (a ** P)"
      by blast
    have "x = (\<Sum>u\<in>B. (u \<bullet> (a *v u)) * (u \<bullet> (P *v u)))"
      unfolding x by (rule trace_mult_eigen_weights[OF B sym eig])
    also have "\<dots> \<le> (\<Sum>u\<in>B. \<bar>u \<bullet> (a *v u)\<bar>)"
    proof (intro sum_mono)
      fix u assume u: "u \<in> B"
      have t0: "0 \<le> u \<bullet> (P *v u)"
        by (rule proj_quadform_nonneg[OF P])
      have t1: "u \<bullet> (P *v u) \<le> 1"
        by (rule proj_quadform_le_one[OF P B(1) u])
      have "(u \<bullet> (a *v u)) * (u \<bullet> (P *v u)) \<le> \<bar>u \<bullet> (a *v u)\<bar> * (u \<bullet> (P *v u))"
        using t0 by (intro mult_right_mono) auto
      also have "\<dots> \<le> \<bar>u \<bullet> (a *v u)\<bar> * 1"
        using t1 by (intro mult_left_mono) auto
      finally show "(u \<bullet> (a *v u)) * (u \<bullet> (P *v u)) \<le> \<bar>u \<bullet> (a *v u)\<bar>"
        by simp
    qed
    finally show "x \<le> (\<Sum>u\<in>B. \<bar>u \<bullet> (a *v u)\<bar>)" .
  qed
qed

lemma kyfan_ge_trace_mult:
  fixes a :: "real^'n::finite^'n"
  assumes sym: "transpose a = a" and P: "is_proj P" "trace P = real m"
  shows "trace (a ** P) \<le> kyfan m a"
  unfolding kyfan_def
  by (intro cSup_upper kyfan_bdd_above[OF sym]) (use P in blast)

section \<open>\<open>kyfan\<close> against the spectral constraints of Eq. (1.9)\<close>

text \<open>The two bridges to \<open>eigen_lb\<close> / \<open>eigen_ub\<close>. Together they say that on
  the feasible set of Eq. (1.9) the \<open>m\<close>-fold eigenvalue sums are pinned
  between \<open>m\<close> and \<open>m L\<close> --- exactly the input the extremal computation
  behind Eq. (3.5) needs.\<close>

text \<open>\<open>eigen_lb a m\<close> provides an \<open>m\<close>-dimensional subspace on which the form
  dominates \<open>|x|²\<close>. Testing the supremum at the orthogonal projection onto
  it gives the lower bound; no eigenbasis of \<open>a\<close> is involved.\<close>

lemma kyfan_ge_of_eigen_lb:
  fixes a :: "real^'n::finite^'n"
  assumes sym: "transpose a = a" and lb: "eigen_lb a m"
  shows "real m \<le> kyfan m a"
proof -
  obtain S where S: "subspace S" "m \<le> dim S"
    and quad: "\<And>x. x \<in> S \<Longrightarrow> x \<bullet> x \<le> x \<bullet> (a *v x)"
    using lb by (auto simp: eigen_lb_def)
  obtain B0 where B0: "B0 \<subseteq> S" "pairwise orthogonal B0"
    "\<And>x. x \<in> B0 \<Longrightarrow> norm x = 1" "independent B0"
    "card B0 = dim S" "span B0 = S"
    using orthonormal_basis_subspace[OF S(1)] by metis
  have onB0: "onormal B0"
    using B0 by (auto simp: onormal_def intro: pairwise_orthogonal_imp_finite)
  obtain C where C: "C \<subseteq> B0" "card C = m"
    using S(2) B0(5) obtain_subset_with_card_n[of m B0] by metis
  have onC: "onormal C"
    by (rule onormal_subset[OF onB0 C(1)])
  define P where "P = (\<Sum>u\<in>C. outer_prod u u)"
  have Pproj: "is_proj P"
    unfolding P_def by (rule onormal_proj(1)[OF onC])
  have Ptr: "trace P = real m"
    unfolding P_def using onormal_proj(2)[OF onC] C(2) by simp
  have "real m = (\<Sum>u\<in>C. (1::real))"
    using C(2) by simp
  also have "\<dots> \<le> (\<Sum>u\<in>C. u \<bullet> (a *v u))"
  proof (intro sum_mono)
    fix u assume u: "u \<in> C"
    then have uS: "u \<in> S"
      using C(1) B0(1) by auto
    have "u \<bullet> u = 1"
      using onC u by simp
    then show "1 \<le> u \<bullet> (a *v u)"
      using quad[OF uS] by simp
  qed
  also have "\<dots> = trace (a ** P)"
    unfolding P_def by (simp add: trace_mult_outer_sum)
  also have "\<dots> \<le> kyfan m a"
    by (rule kyfan_ge_trace_mult[OF sym Pproj Ptr])
  finally show ?thesis .
qed

text \<open>Dually, \<open>eigen_ub a L\<close> caps every eigenvalue, hence every \<open>m\<close>-fold
  sum. Here the bound holds for each competing projection separately, so
  no eigenbasis and no symmetry assumption are needed.\<close>

lemma kyfan_le_of_eigen_ub:
  fixes a :: "real^'n::finite^'n"
  assumes ub: "eigen_ub a L" and m: "m \<le> CARD('n)"
  shows "kyfan m a \<le> real m * L"
  unfolding kyfan_def
proof (rule cSup_least)
  show "{trace (a ** P) | P :: real^'n^'n. is_proj P \<and> trace P = real m} \<noteq> {}"
    using proj_with_trace_exists[OF m] by force
next
  fix x
  assume "x \<in> {trace (a ** P) | P :: real^'n^'n. is_proj P \<and> trace P = real m}"
  then obtain P :: "real^'n^'n" where P: "is_proj P" "trace P = real m"
    and x: "x = trace (a ** P)"
    by blast
  obtain C where C: "onormal C" "P = (\<Sum>u\<in>C. outer_prod u u)"
    "real (card C) = trace P"
    using is_proj_decomp[OF P(1)] by metis
  have cardC: "card C = m"
    using C(3) P(2) by simp
  have "x = (\<Sum>u\<in>C. u \<bullet> (a *v u))"
    unfolding x C(2) by (simp add: trace_mult_outer_sum)
  also have "\<dots> \<le> (\<Sum>u\<in>C. L)"
  proof (intro sum_mono)
    fix u assume u: "u \<in> C"
    have "u \<bullet> (a *v u) \<le> L * (u \<bullet> u)"
      using ub by (simp add: eigen_ub_def)
    then show "u \<bullet> (a *v u) \<le> L"
      using C(1) u by simp
  qed
  also have "\<dots> = real m * L"
    using cardC by simp
  finally show "x \<le> real m * L" .
qed

section \<open>Ordered eigenvalues as differences of Ky Fan sums\<close>

text \<open>Only the rank-\<open>0\<close> projection has trace \<open>0\<close>, so the \<open>0\<close>-th Ky Fan sum
  vanishes and the differences below telescope.\<close>

lemma is_proj_trace_zero:
  fixes P :: "real^'n::finite^'n"
  assumes P: "is_proj P" and tr: "trace P = 0"
  shows "P = 0"
proof -
  obtain C where C: "onormal C" "P = (\<Sum>u\<in>C. outer_prod u u)"
    "real (card C) = trace P"
    using is_proj_decomp[OF P] by metis
  have "card C = 0"
    using C(3) tr by simp
  then have "C = {}"
    using onormal_finite[OF C(1)] by simp
  then show ?thesis
    using C(2) by simp
qed

lemma kyfan_0:
  fixes a :: "real^'n::finite^'n"
  shows "kyfan 0 a = 0"
proof -
  have trz: "trace (a ** (0 :: real^'n^'n)) = 0"
    by (simp add: trace_def matrix_matrix_mult_def)
  have pz: "is_proj (0 :: real^'n^'n)"
    by (auto simp: is_proj_def transpose_def matrix_matrix_mult_def vec_eq_iff)
  have "{trace (a ** P) | P :: real^'n^'n. is_proj P \<and> trace P = real (0::nat)}
      = {0}"
  proof (rule equalityI, rule subsetI)
    fix x
    assume "x \<in> {trace (a ** P) | P :: real^'n^'n. is_proj P \<and> trace P = real (0::nat)}"
    then obtain P :: "real^'n^'n" where P: "is_proj P" "trace P = real (0::nat)"
      and x: "x = trace (a ** P)"
      by blast
    have "P = 0"
      using is_proj_trace_zero[OF P(1)] P(2) by simp
    then show "x \<in> {0}"
      using x trz by simp
  next
    show "{0} \<subseteq> {trace (a ** P) | P :: real^'n^'n. is_proj P \<and> trace P = real (0::nat)}"
      using pz trz by (auto intro!: exI[of _ "0 :: real^'n^'n"])
  qed
  then show ?thesis
    by (simp add: kyfan_def)
qed

text \<open>The \<open>i\<close>-th largest eigenvalue of a symmetric matrix, \<open>1 \<le> i \<le> n\<close>.
  This is the \<open>\<lambda>\<^sub>(\<^sub>i\<^sub>)\<close> of the paper. Being a difference of two basis-free
  quantities it is itself basis-free, with no well-definedness obligation.\<close>

definition eigval :: "nat \<Rightarrow> real^'n::finite^'n \<Rightarrow> real" where
  "eigval i a = kyfan i a - kyfan (i - 1) a"

lemma eigval_1: "eigval 1 (a :: real^'n::finite^'n) = kyfan 1 a"
  by (simp add: eigval_def kyfan_0)

lemma eigval_Suc: "eigval (Suc i) (a :: real^'n::finite^'n) = kyfan (Suc i) a - kyfan i a"
  by (simp add: eigval_def)

text \<open>The Ky Fan sums are exactly the partial sums of the ordered
  eigenvalues --- so nothing is lost by taking the sums as primitive.\<close>

lemma kyfan_eq_sum_eigval:
  fixes a :: "real^'n::finite^'n"
  shows "kyfan m a = (\<Sum>i\<in>{1..m}. eigval i a)"
proof (induction m)
  case 0
  show ?case by (simp add: kyfan_0)
next
  case (Suc m)
  have "(\<Sum>i\<in>{1..Suc m}. eigval i a) = (\<Sum>i\<in>{1..m}. eigval i a) + eigval (Suc m) a"
    by simp
  also have "\<dots> = kyfan m a + (kyfan (Suc m) a - kyfan m a)"
    using Suc.IH by (simp add: eigval_Suc)
  finally show ?case by simp
qed

section \<open>Monotonicity: \<open>\<lambda>\<^sub>(\<^sub>1\<^sub>) \<ge> \<lambda>\<^sub>(\<^sub>2\<^sub>) \<ge> \<dots>\<close>\<close>

text \<open>\<open>kyfan_attained\<close> produces a maximiser for each \<open>m\<close> separately, which
  is not enough: monotonicity needs the maximisers to nest. Call
  \<open>T \<subseteq> B\<close> with \<open>card T = m\<close> a \<^emph>\<open>threshold set\<close> when every value inside
  dominates every value outside; deleting a minimal element leaves a
  threshold set one size down, and iterating produces the nested chain.\<close>

text \<open>A minimiser of a real-valued function on a finite nonempty set.\<close>

lemma finite_arg_min_on:
  fixes f :: "'a \<Rightarrow> real"
  assumes fin: "finite T" and ne: "T \<noteq> {}"
  obtains w where "w \<in> T" and "\<And>u. u \<in> T \<Longrightarrow> f w \<le> f u"
proof -
  have "Min (f ` T) \<in> f ` T"
    using fin ne by (intro Min_in) auto
  then obtain w where w: "w \<in> T" and fw: "f w = Min (f ` T)"
    by (metis imageE)
  have wmin: "f w \<le> f u" if u: "u \<in> T" for u
    unfolding fw using fin u by simp
  show thesis
    by (rule that[OF w wmin])
qed


lemma threshold_sum_maximal:
  fixes lam :: "'a \<Rightarrow> real"
  assumes finB: "finite B" and T: "T \<subseteq> B" "card T = m"
    and thresh: "\<And>u v. u \<in> T \<Longrightarrow> v \<in> B - T \<Longrightarrow> lam v \<le> lam u"
    and T': "T' \<subseteq> B" "card T' = m"
  shows "(\<Sum>u\<in>T'. lam u) \<le> (\<Sum>u\<in>T. lam u)"
proof -
  have finT: "finite T"
    using T(1) finB by (rule finite_subset)
  have finT': "finite T'"
    using T'(1) finB by (rule finite_subset)
  have splitT: "(\<Sum>u\<in>T. lam u) = (\<Sum>u\<in>T - T'. lam u) + (\<Sum>u\<in>T \<inter> T'. lam u)"
  proof -
    have e1: "T - (T \<inter> T') = T - T'" by auto
    have "(\<Sum>u\<in>T. lam u) = (\<Sum>u\<in>T - (T \<inter> T'). lam u) + (\<Sum>u\<in>T \<inter> T'. lam u)"
      using finT by (intro sum.subset_diff) auto
    then show ?thesis by (simp only: e1)
  qed
  have splitT': "(\<Sum>u\<in>T'. lam u) = (\<Sum>u\<in>T' - T. lam u) + (\<Sum>u\<in>T \<inter> T'. lam u)"
  proof -
    have e2: "T' \<inter> T = T \<inter> T'" by auto
    have e1: "T' - (T \<inter> T') = T' - T" by auto
    have "(\<Sum>u\<in>T'. lam u) = (\<Sum>u\<in>T' - (T' \<inter> T). lam u) + (\<Sum>u\<in>T' \<inter> T. lam u)"
      using finT' by (intro sum.subset_diff) auto
    then show ?thesis by (simp only: e2 e1)
  qed
  have cT: "card (T - T') = m - card (T \<inter> T')"
  proof -
    have e: "T - T' = T - (T \<inter> T')" by auto
    have "card (T - (T \<inter> T')) = card T - card (T \<inter> T')"
      using finT by (intro card_Diff_subset) auto
    then show ?thesis using T(2) by (simp add: e)
  qed
  have cT': "card (T' - T) = m - card (T \<inter> T')"
  proof -
    have e: "T' - T = T' - (T' \<inter> T)" by auto
    have e2: "T' \<inter> T = T \<inter> T'" by auto
    have "card (T' - (T' \<inter> T)) = card T' - card (T' \<inter> T)"
      using finT' by (intro card_Diff_subset) auto
    then show ?thesis using T'(2) by (simp add: e e2)
  qed
  show ?thesis
  proof (cases "T - T' = {}")
    case True
    then have "T \<subseteq> T'" by blast
    then have "T = T'"
      using finT' T(2) T'(2) by (metis card_subset_eq)
    then show ?thesis by simp
  next
    case False
    have finD: "finite (T - T')"
      using finT by simp
    define \<theta> where "\<theta> = Min (lam ` (T - T'))"
    have "\<theta> \<in> lam ` (T - T')"
      unfolding \<theta>_def using finD False by (intro Min_in) auto
    then obtain u0 where u0: "u0 \<in> T - T'" and u0\<theta>: "lam u0 = \<theta>"
      by blast
    have low: "\<theta> \<le> lam u" if "u \<in> T - T'" for u
      unfolding \<theta>_def using finD that by simp
    have "(\<Sum>u\<in>T' - T. lam u) \<le> (\<Sum>u\<in>T' - T. \<theta>)"
    proof (intro sum_mono)
      fix v assume v: "v \<in> T' - T"
      then have vB: "v \<in> B - T"
        using T'(1) by auto
      have u0T: "u0 \<in> T" using u0 by blast
      have "lam v \<le> lam u0" by (rule thresh[OF u0T vB])
      then show "lam v \<le> \<theta>" using u0\<theta> by simp
    qed
    also have "(\<Sum>u\<in>T' - T. \<theta>) = real (card (T' - T)) * \<theta>"
      by simp
    also have "\<dots> = real (card (T - T')) * \<theta>"
      using cT cT' by simp
    also have "\<dots> = (\<Sum>u\<in>T - T'. \<theta>)"
      by simp
    also have "\<dots> \<le> (\<Sum>u\<in>T - T'. lam u)"
      by (intro sum_mono low)
    finally have "(\<Sum>u\<in>T' - T. lam u) \<le> (\<Sum>u\<in>T - T'. lam u)" .
    then show ?thesis
      using splitT splitT' by simp
  qed
qed

lemma threshold_remove_min:
  fixes lam :: "'a \<Rightarrow> real"
  assumes thresh: "\<And>u v. u \<in> T \<Longrightarrow> v \<in> B - T \<Longrightarrow> lam v \<le> lam u"
    and wmin: "\<And>u. u \<in> T \<Longrightarrow> lam w \<le> lam u"
    and u: "u \<in> T - {w}" and v: "v \<in> B - (T - {w})"
  shows "lam v \<le> lam u"
proof -
  have uT: "u \<in> T"
    using u by blast
  show ?thesis
  proof (cases "v \<in> T")
    case True
    then have "v = w"
      using v by blast
    then show ?thesis
      using wmin[OF uT] by simp
  next
    case False
    then have "v \<in> B - T"
      using v by blast
    then show ?thesis
      by (rule thresh[OF uT])
  qed
qed

text \<open>Consequently a threshold set computes the Ky Fan sum.\<close>

lemma kyfan_threshold:
  fixes a :: "real^'n::finite^'n"
  assumes B: "onormal B" "span B = UNIV"
    and sym: "transpose a = a"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
    and T: "T \<subseteq> B" "card T = m"
    and thresh: "\<And>u v. u \<in> T \<Longrightarrow> v \<in> B - T \<Longrightarrow> v \<bullet> (a *v v) \<le> u \<bullet> (a *v u)"
  shows "kyfan m a = (\<Sum>u\<in>T. u \<bullet> (a *v u))"
proof -
  have finB: "finite B"
    by (rule onormal_finite[OF B(1)])
  have cardB: "card B = CARD('n)"
    by (rule onormal_span_card[OF B])
  have m: "m \<le> CARD('n)"
    using T(2) card_mono[OF finB T(1)] cardB by simp
  obtain T0 where T0: "T0 \<subseteq> B" "card T0 = m"
    and kf: "kyfan m a = (\<Sum>u\<in>T0. u \<bullet> (a *v u))"
    and T0max: "\<And>T'. T' \<subseteq> B \<Longrightarrow> card T' = m
          \<Longrightarrow> (\<Sum>u\<in>T'. u \<bullet> (a *v u)) \<le> (\<Sum>u\<in>T0. u \<bullet> (a *v u))"
    using kyfan_attained[OF B sym eig m] by metis
  have le1: "(\<Sum>u\<in>T0. u \<bullet> (a *v u)) \<le> (\<Sum>u\<in>T. u \<bullet> (a *v u))"
    by (rule threshold_sum_maximal[where lam = "\<lambda>u :: real^'n. u \<bullet> (a *v u)",
          OF finB T thresh T0])
  have le2: "(\<Sum>u\<in>T. u \<bullet> (a *v u)) \<le> (\<Sum>u\<in>T0. u \<bullet> (a *v u))"
    by (rule T0max[OF T])
  show ?thesis
    using kf le1 le2 by simp
qed

text \<open>Hence the \<open>(i+1)\<close>-st eigenvalue is the smallest value on a threshold
  set of size \<open>i+1\<close>: deleting that value drops the Ky Fan sum by exactly it.\<close>

lemma eigval_eq_min_of_threshold:
  fixes a :: "real^'n::finite^'n"
  assumes B: "onormal B" "span B = UNIV"
    and sym: "transpose a = a"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
    and T: "T \<subseteq> B" "card T = Suc i"
    and thresh: "\<And>u v. u \<in> T \<Longrightarrow> v \<in> B - T \<Longrightarrow> v \<bullet> (a *v v) \<le> u \<bullet> (a *v u)"
    and w: "w \<in> T" and wmin: "\<And>u. u \<in> T \<Longrightarrow> w \<bullet> (a *v w) \<le> u \<bullet> (a *v u)"
  shows "eigval (Suc i) a = w \<bullet> (a *v w)"
proof -
  have finB: "finite B"
    by (rule onormal_finite[OF B(1)])
  have finT: "finite T"
    using T(1) finB by (rule finite_subset)
  have T1: "T - {w} \<subseteq> B"
    using T(1) by blast
  have cardT1: "card (T - {w}) = i"
    using finT w T(2) by simp
  have th1: "v \<bullet> (a *v v) \<le> u \<bullet> (a *v u)"
    if "u \<in> T - {w}" "v \<in> B - (T - {w})" for u v
    by (rule threshold_remove_min[where lam = "\<lambda>u :: real^'n. u \<bullet> (a *v u)",
          OF thresh wmin that(1) that(2)])
  have kSuc: "kyfan (Suc i) a = (\<Sum>u\<in>T. u \<bullet> (a *v u))"
    by (rule kyfan_threshold[OF B sym eig T thresh])
  have ki: "kyfan i a = (\<Sum>u\<in>T - {w}. u \<bullet> (a *v u))"
    by (rule kyfan_threshold[OF B sym eig T1 cardT1 th1])
  have "(\<Sum>u\<in>T. u \<bullet> (a *v u)) = w \<bullet> (a *v w) + (\<Sum>u\<in>T - {w}. u \<bullet> (a *v u))"
    using finT w by (simp add: sum.remove)
  then show ?thesis
    unfolding eigval_Suc kSuc ki by simp
qed

text \<open>The ordered eigenvalues decrease. Applying the previous lemma to a
  threshold set of size \<open>i+1\<close> and then to the same set with its minimum
  deleted exhibits \<open>\<lambda>\<^sub>(\<^sub>i\<^sub>+\<^sub>1\<^sub>)\<close> and \<open>\<lambda>\<^sub>(\<^sub>i\<^sub>)\<close> as the minima of a set and of a
  subset of it, and a minimum over a subset is larger.\<close>

theorem eigval_antimono:
  fixes a :: "real^'n::finite^'n"
  assumes sym: "transpose a = a" and i: "1 \<le> i" and n: "Suc i \<le> CARD('n)"
  shows "eigval (Suc i) a \<le> eigval i a"
proof -
  obtain j where ij: "i = Suc j"
    using i by (cases i) auto
  obtain B where B: "onormal B" "span B = UNIV"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
    using symmetric_eigenbasis[OF sym] by metis
  have finB: "finite B"
    by (rule onormal_finite[OF B(1)])
  have cardB: "card B = CARD('n)"
    by (rule onormal_span_card[OF B])
  have mB: "Suc i \<le> card B"
    using n cardB by simp
  obtain T where T: "T \<subseteq> B" "card T = Suc i"
    and thresh: "\<And>u v. u \<in> T \<Longrightarrow> v \<in> B - T \<Longrightarrow> v \<bullet> (a *v v) \<le> u \<bullet> (a *v u)"
    using exists_top_subset[where f = "\<lambda>u :: real^'n. u \<bullet> (a *v u)", OF finB mB]
    by metis
  have finT: "finite T"
    using T(1) finB by (rule finite_subset)
  have Tne: "T \<noteq> {}"
    using T(2) by auto
  obtain w where w: "w \<in> T"
    and wmin: "\<And>u. u \<in> T \<Longrightarrow> w \<bullet> (a *v w) \<le> u \<bullet> (a *v u)"
    using finite_arg_min_on[where f = "\<lambda>u :: real^'n. u \<bullet> (a *v u)", OF finT Tne]
    by metis
  have e1: "eigval (Suc i) a = w \<bullet> (a *v w)"
    by (rule eigval_eq_min_of_threshold[OF B sym eig T thresh w wmin])
  text \<open>One level down, on \<open>T - {w}\<close>.\<close>
  have T1: "T - {w} \<subseteq> B"
    using T(1) by blast
  have cardT1: "card (T - {w}) = Suc j"
  proof -
    have "card (T - {w}) = card T - 1"
      using finT w by simp
    then show ?thesis
      using T(2) ij by simp
  qed
  have th1: "v \<bullet> (a *v v) \<le> u \<bullet> (a *v u)"
    if "u \<in> T - {w}" "v \<in> B - (T - {w})" for u v
    by (rule threshold_remove_min[where lam = "\<lambda>u :: real^'n. u \<bullet> (a *v u)",
          OF thresh wmin that(1) that(2)])
  have finT1: "finite (T - {w})"
    using finT by simp
  have T1ne: "T - {w} \<noteq> {}"
  proof (rule notI)
    assume z: "T - {w} = {}"
    have "card (T - {w}) = 0" unfolding z by simp
    with cardT1 show False by simp
  qed
  obtain w' where w': "w' \<in> T - {w}"
    and w'min: "\<And>u. u \<in> T - {w} \<Longrightarrow> w' \<bullet> (a *v w') \<le> u \<bullet> (a *v u)"
    using finite_arg_min_on[where f = "\<lambda>u :: real^'n. u \<bullet> (a *v u)",
        OF finT1 T1ne]
    by metis
  have e0: "eigval i a = w' \<bullet> (a *v w')"
    unfolding ij
    by (rule eigval_eq_min_of_threshold[OF B sym eig T1 cardT1 th1 w' w'min])
  have "w' \<in> T"
    using w' by blast
  then show ?thesis
    unfolding e1 e0 by (rule wmin)
qed

text \<open>The chain form, by induction: \<open>\<lambda>\<^sub>(\<^sub>i\<^sub>) \<ge> \<lambda>\<^sub>(\<^sub>j\<^sub>)\<close> whenever \<open>1 \<le> i \<le> j \<le> n\<close>.\<close>

corollary eigval_antimono_le:
  fixes a :: "real^'n::finite^'n"
  assumes sym: "transpose a = a" and i: "1 \<le> i" and ij: "i \<le> j"
    and n: "j \<le> CARD('n)"
  shows "eigval j a \<le> eigval i a"
  using ij n
proof (induction j)
  case 0
  then show ?case using i by simp
next
  case (Suc j)
  show ?case
  proof (cases "i = Suc j")
    case True
    then show ?thesis by simp
  next
    case False
    then have ijj: "i \<le> j"
      using Suc.prems(1) by simp
    have j1: "1 \<le> j"
      using i ijj by simp
    have "eigval (Suc j) a \<le> eigval j a"
      by (rule eigval_antimono[OF sym j1 Suc.prems(2)])
    also have "\<dots> \<le> eigval i a"
      using ijj Suc.prems(2) by (intro Suc.IH) simp_all
    finally show ?thesis .
  qed
qed

section \<open>Positive and negative parts, with no functional calculus\<close>

text \<open>Eq. (3.5)/(3.6) need two spectral sums:

    \<open>\<Sum>\<^sub>i\<^sub>\<le>\<^sub>m \<lambda>\<^sub>(\<^sub>i\<^sub>)\<^sup>+\<close>   and   \<open>\<Sum>\<^sub>i\<^sub>\<le>\<^sub>m min (\<lambda>\<^sub>(\<^sub>i\<^sub>), 0)\<close>.

  Neither requires the positive/negative part of the matrix: since the
  ordered eigenvalues decrease (\<open>eigval_antimono\<close>), the partial sum
  \<open>\<lambda>\<^sub>(\<^sub>1\<^sub>) + \<dots> + \<lambda>\<^sub>(\<^sub>j\<^sub>)\<close> is largest when \<open>j\<close> counts the positive
  eigenvalues, capped at \<open>m\<close>, so the first sum is the running maximum of
  the Ky Fan sums and the second the remaining difference --- all inside
  \<open>kyfan\<close>, with no spectral functional calculus.\<close>

definition possum :: "nat \<Rightarrow> real^'n::finite^'n \<Rightarrow> real" where
  "possum m a = Max ((\<lambda>j. kyfan j a) ` {..m})"

lemma possum_ge_kyfan:
  fixes a :: "real^'n::finite^'n"
  assumes jm: "j \<le> m"
  shows "kyfan j a \<le> possum m a"
  unfolding possum_def using jm by (intro Max_ge) auto

lemma possum_0: "possum 0 (a :: real^'n::finite^'n) = 0"
  by (simp add: possum_def kyfan_0)

lemma possum_Suc:
  fixes a :: "real^'n::finite^'n"
  shows "possum (Suc m) a = max (kyfan (Suc m) a) (possum m a)"
proof -
  have fin: "finite ((\<lambda>j. kyfan j a) ` {..m})" by simp
  have ne: "(\<lambda>j. kyfan j a) ` {..m} \<noteq> {}" by simp
  have "(\<lambda>j. kyfan j a) ` {..Suc m}
      = insert (kyfan (Suc m) a) ((\<lambda>j. kyfan j a) ` {..m})"
    by (simp add: atMost_Suc)
  then show ?thesis
    unfolding possum_def using fin ne by simp
qed

text \<open>If the first \<open>m\<close> eigenvalues are all nonnegative then the Ky Fan sums
  increase up to \<open>m\<close>.\<close>

lemma kyfan_mono_of_nonneg:
  fixes a :: "real^'n::finite^'n"
  assumes nn: "\<And>i. 1 \<le> i \<Longrightarrow> i \<le> m \<Longrightarrow> 0 \<le> eigval i a" and jm: "j \<le> m"
  shows "kyfan j a \<le> kyfan m a"
  unfolding kyfan_eq_sum_eigval
proof (rule sum_mono2)
  show "finite {1..m}" by simp
  show "{1..j} \<subseteq> {1..m}" using jm by auto
  fix i assume "i \<in> {1..m} - {1..j}"
  then show "0 \<le> eigval i a" using nn by auto
qed

text \<open>The evaluation lemma: the running maximum of the Ky Fan sums is the
  sum of the positive parts of the first \<open>m\<close> eigenvalues.\<close>

theorem possum_eq_sum_pos:
  fixes a :: "real^'n::finite^'n"
  assumes sym: "transpose a = a" and m: "m \<le> CARD('n)"
  shows "possum m a = (\<Sum>i\<in>{1..m}. max (eigval i a) 0)"
  using m
proof (induction m)
  case 0
  show ?case by (simp add: possum_0)
next
  case (Suc m)
  have m_le: "m \<le> CARD('n)"
    using Suc.prems by simp
  have IH: "possum m a = (\<Sum>i\<in>{1..m}. max (eigval i a) 0)"
    by (rule Suc.IH[OF m_le])
  have kSuc: "kyfan (Suc m) a = kyfan m a + eigval (Suc m) a"
    by (simp add: eigval_Suc)
  have main: "possum (Suc m) a = (\<Sum>i\<in>{1..Suc m}. max (eigval i a) 0)"
  proof (cases "0 \<le> eigval (Suc m) a")
    case True
    text \<open>All earlier eigenvalues dominate \<open>\<lambda>\<^sub>(\<^sub>m\<^sub>+\<^sub>1\<^sub>) \<ge> 0\<close>, so up to \<open>m\<close> the Ky
      Fan sums increase and the running maximum has not yet bitten.\<close>
    have nn: "0 \<le> eigval i a" if i: "1 \<le> i" "i \<le> m" for i
    proof -
      have "eigval (Suc m) a \<le> eigval i a"
        using i Suc.prems by (intro eigval_antimono_le[OF sym]) auto
      then show ?thesis
        using True by simp
    qed
    have possum_m: "possum m a = kyfan m a"
    proof (rule antisym)
      have "\<forall>x \<in> (\<lambda>j. kyfan j a) ` {..m}. x \<le> kyfan m a"
        using kyfan_mono_of_nonneg[OF nn] by auto
      then show "possum m a \<le> kyfan m a"
        unfolding possum_def by (subst Max_le_iff) auto
      show "kyfan m a \<le> possum m a"
        by (rule possum_ge_kyfan) simp
    qed
    have "possum (Suc m) a = max (kyfan (Suc m) a) (possum m a)"
      by (rule possum_Suc)
    also have "\<dots> = possum m a + max (eigval (Suc m) a) 0"
      unfolding possum_m kSuc using True by simp
    also have "\<dots> = (\<Sum>i\<in>{1..Suc m}. max (eigval i a) 0)"
      unfolding IH by simp
    finally show ?thesis .
  next
    case False
    text \<open>Otherwise the new Ky Fan sum decreases, so the maximum is unchanged
      --- and the new positive part contributes \<open>0\<close>.\<close>
    have le: "kyfan (Suc m) a \<le> possum m a"
    proof -
      have "kyfan (Suc m) a \<le> kyfan m a"
        unfolding kSuc using False by simp
      also have "\<dots> \<le> possum m a"
        by (rule possum_ge_kyfan) simp
      finally show ?thesis .
    qed
    have "possum (Suc m) a = possum m a"
      using le by (simp add: possum_Suc)
    also have "\<dots> = possum m a + max (eigval (Suc m) a) 0"
      using False by simp
    also have "\<dots> = (\<Sum>i\<in>{1..Suc m}. max (eigval i a) 0)"
      unfolding IH by simp
    finally show ?thesis .
  qed
  then show ?case .
qed

text \<open>And the companion: the gap between the Ky Fan sum and its running
  maximum is the sum of the negative parts. This is the \<open>\<Sum> min (\<mu>\<^sub>i, 0)\<close> term
  of the bracket in Eq. (3.5).\<close>

corollary kyfan_minus_possum:
  fixes a :: "real^'n::finite^'n"
  assumes sym: "transpose a = a" and m: "m \<le> CARD('n)"
  shows "kyfan m a - possum m a = (\<Sum>i\<in>{1..m}. min (eigval i a) 0)"
proof -
  have step: "eigval i a - max (eigval i a) 0 = min (eigval i a) 0" for i
    by (simp add: min_def max_def)
  have "kyfan m a - possum m a
      = (\<Sum>i\<in>{1..m}. eigval i a) - (\<Sum>i\<in>{1..m}. max (eigval i a) 0)"
    using kyfan_eq_sum_eigval[of m a] possum_eq_sum_pos[OF sym m] by simp
  also have "\<dots> = (\<Sum>i\<in>{1..m}. eigval i a - max (eigval i a) 0)"
    by (simp add: sum_subtractf)
  also have "\<dots> = (\<Sum>i\<in>{1..m}. min (eigval i a) 0)"
    using step by simp
  finally show ?thesis .
qed

text \<open>Consequently the whole bracket of Eq. (3.5),

    \<open>L * (\<Sum>\<^sub>i \<lambda>\<^sub>i\<^sup>+) + \<Sum>\<^sub>i\<^sub>\<le>\<^sub>m min (\<lambda>\<^sub>i, 0)\<close>,

  is a function of the Ky Fan sums alone:

    \<open>L * possum n a + (kyfan m a - possum m a)\<close>.

  What remains for Eq. (3.6) is the geometry: the Poincare separation
  theorem relating the eigenvalues of the compression of \<open>M\<close> to \<open>p\<^sup>\<bottom>\<close> with
  those of \<open>M\<close>, and the extremal computation identifying the bracket with the
  supremum over the feasible set of Eq. (1.9).\<close>

definition bracket :: "nat \<Rightarrow> real \<Rightarrow> real^'n::finite^'n \<Rightarrow> real" where
  "bracket m L a = L * possum CARD('n) a + (kyfan m a - possum m a)"

lemma bracket_eq_sum:
  fixes a :: "real^'n::finite^'n"
  assumes sym: "transpose a = a" and m: "m \<le> CARD('n)"
  shows "bracket m L a
      = L * (\<Sum>i\<in>{1..CARD('n)}. max (eigval i a) 0)
      + (\<Sum>i\<in>{1..m}. min (eigval i a) 0)"
  using possum_eq_sum_pos[OF sym order_refl] kyfan_minus_possum[OF sym m]
  by (simp add: bracket_def)

section \<open>Evaluating \<open>possum\<close> in an eigenbasis\<close>

text \<open>The extremal construction behind Eq. (3.5) needs a concrete feasible
  \<open>a\<close>, built from an eigenbasis of \<open>M\<close>, evaluating \<open>trace (M ** a)\<close> ---
  which needs the positive-part sum expressed over the eigenbasis rather
  than the index range \<open>1..n\<close>.

  The set \<open>T = {u \<in> B. 0 < u \<bullet> M u}\<close> of positive directions is
  automatically a threshold set, so \<open>kyfan_threshold\<close> evaluates
  \<open>kyfan (card T) M\<close> at it, and that value is already the maximum.\<close>

lemma possum_nonneg:
  fixes a :: "real^'n::finite^'n"
  shows "0 \<le> possum m a"
proof -
  have "kyfan 0 a \<le> possum m a"
    by (rule possum_ge_kyfan) simp
  then show ?thesis
    by (simp add: kyfan_0)
qed

lemma possum_full_eq_sum_basis:
  fixes a :: "real^'n::finite^'n"
  assumes B: "onormal B" "span B = UNIV"
    and sym: "transpose a = a"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
  shows "possum CARD('n) a = (\<Sum>u\<in>B. max (u \<bullet> (a *v u)) 0)"
proof -
  have finB: "finite B"
    by (rule onormal_finite[OF B(1)])
  have cardB: "card B = CARD('n)"
    by (rule onormal_span_card[OF B])
  define T where "T = {u \<in> B. 0 < u \<bullet> (a *v u)}"
  have Tsub: "T \<subseteq> B"
    by (auto simp: T_def)
  have cardT: "card T \<le> CARD('n)"
    using card_mono[OF finB Tsub] cardB by simp
  text \<open>The positive directions form a threshold set.\<close>
  have thresh: "v \<bullet> (a *v v) \<le> u \<bullet> (a *v u)" if "u \<in> T" "v \<in> B - T" for u v
  proof -
    have "0 < u \<bullet> (a *v u)"
      using that(1) by (simp add: T_def)
    moreover have "v \<bullet> (a *v v) \<le> 0"
      using that(2) by (auto simp: T_def)
    ultimately show ?thesis by simp
  qed
  have kT: "kyfan (card T) a = (\<Sum>u\<in>T. u \<bullet> (a *v u))"
    by (rule kyfan_threshold[OF B sym eig Tsub refl thresh])
  have sumT: "(\<Sum>u\<in>B. max (u \<bullet> (a *v u)) 0) = (\<Sum>u\<in>T. u \<bullet> (a *v u))"
  proof -
    have split: "(\<Sum>u\<in>B. max (u \<bullet> (a *v u)) 0)
        = (\<Sum>u\<in>B - T. max (u \<bullet> (a *v u)) 0) + (\<Sum>u\<in>T. max (u \<bullet> (a *v u)) 0)"
      using Tsub finB by (rule sum.subset_diff)
    have out: "(\<Sum>u\<in>B - T. max (u \<bullet> (a *v u)) 0) = 0"
      by (intro sum.neutral ballI) (auto simp: T_def)
    have inn: "(\<Sum>u\<in>T. max (u \<bullet> (a *v u)) 0) = (\<Sum>u\<in>T. u \<bullet> (a *v u))"
      by (intro sum.cong refl) (auto simp: T_def)
    show ?thesis
      using split out inn by simp
  qed
  show ?thesis
  proof (rule antisym)
    text \<open>Every Ky Fan sum is a sum of eigenvalues over some subset of \<open>B\<close>,
      hence at most the sum of all the positive parts.\<close>
    have bound: "\<forall>x \<in> (\<lambda>j. kyfan j a) ` {..CARD('n)}.
        x \<le> (\<Sum>u\<in>B. max (u \<bullet> (a *v u)) 0)"
    proof
      fix x assume "x \<in> (\<lambda>j. kyfan j a) ` {..CARD('n)}"
      then obtain j where j: "j \<le> CARD('n)" and x: "x = kyfan j a"
        by auto
      obtain T' where T': "T' \<subseteq> B" "card T' = j"
        and kf: "kyfan j a = (\<Sum>u\<in>T'. u \<bullet> (a *v u))"
        using kyfan_attained[OF B sym eig j] by metis
      have "(\<Sum>u\<in>T'. u \<bullet> (a *v u)) \<le> (\<Sum>u\<in>T'. max (u \<bullet> (a *v u)) 0)"
        by (intro sum_mono) simp
      also have "\<dots> \<le> (\<Sum>u\<in>B. max (u \<bullet> (a *v u)) 0)"
        using finB T'(1) by (intro sum_mono2) auto
      finally show "x \<le> (\<Sum>u\<in>B. max (u \<bullet> (a *v u)) 0)"
        unfolding x kf .
    qed
    show "possum CARD('n) a \<le> (\<Sum>u\<in>B. max (u \<bullet> (a *v u)) 0)"
      using bound unfolding possum_def by (subst Max_le_iff) auto
  next
    have "(\<Sum>u\<in>B. max (u \<bullet> (a *v u)) 0) = kyfan (card T) a"
      using kT sumT by simp
    also have "\<dots> \<le> possum CARD('n) a"
      by (rule possum_ge_kyfan[OF cardT])
    finally show "(\<Sum>u\<in>B. max (u \<bullet> (a *v u)) 0) \<le> possum CARD('n) a" .
  qed
qed

text \<open>The companion statement for the negative-part term,

    \<open>kyfan m a - possum m a = (\<Sum>u\<in>S. min (u \<bullet> a u) 0)\<close>  for a threshold set
    \<open>S \<subseteq> B\<close> of size \<open>m\<close>,

  which would express \<open>bracket m L a\<close> entirely over an eigenbasis, is not
  established here. The positive-part half above goes through because
  \<open>{u \<in> B. 0 < u \<bullet> a u}\<close> is itself a threshold set of \<open>B\<close>; the restricted
  version is harder, needing for every \<open>j \<le> m\<close> a threshold subset of
  \<open>S\<close> of size \<open>j\<close> --- i.e. that \<open>\<lambda>\<^sub>(\<^sub>1\<^sub>), \<dots>, \<lambda>\<^sub>(\<^sub>m\<^sub>)\<close> are exactly the
  \<open>S\<close>-eigenvalues in decreasing order, true by iterating
  \<open>threshold_remove_min\<close> downwards from \<open>S\<close>, but a separate induction.\<close>


end
