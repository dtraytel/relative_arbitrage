
(*<*)
theory Ky_Fan
  imports Symmetric_Spectral
begin

(*>*)

text \<open>
  Ky Fan partial sums and ordered eigenvalues of a real symmetric matrix,
  developed basis-free.

    Design.  For an orthogonal projection matrix \<open>P\<close>,

      \<open>kyfan m a = Sup {trace (a ** P) | is_proj P, trace P = m}\<close>

    is the sum of the \<open>m\<close> LARGEST eigenvalues of \<open>a\<close>, by Ky Fan's maximum
    principle \<^cite>\<open>Fan1949\<close> -- basis-free by
    construction, so no well-definedness argument is needed. The \<open>i\<close>-th
    largest eigenvalue is the difference \<open>eigval i a = kyfan i a - kyfan
    (i-1) a\<close>. This route avoids defining eigenvalues by sorting a multiset
    and then having to prove independence of the eigenbasis: here
    basis-independence is free, and the Courant--Fischer / Ky Fan theorems
    become EVALUATION lemmas rather than well-definedness obligations.

    The one genuinely combinatorial ingredient is the linear program on the
    simplex inside a box: maximising a linear functional over the vectors \<open>t\<close> with
    \<open>0 \<le> t \<le> 1\<close> and \<open>\<Sum> t = m\<close> puts the mass on the \<open>m\<close> largest
    coefficients.  That is what turns "\<open>trace (a ** P)\<close> for an arbitrary
    rank-\<open>m\<close> projection \<open>P\<close>" into "a sum of \<open>m\<close> eigenvalues".\<close>

unbundle inner_syntax

section \<open>Orthogonal projections\<close>

definition is_proj :: "real^'n^'n \<Rightarrow> bool" where
  "is_proj P \<longleftrightarrow> transpose P = P \<and> P ** P = P"

text \<open>Basis projections are orthogonal projections.\<close>

lemma onormal_proj:
  assumes C: "onormal C"
  shows "is_proj (\<Sum>u\<in>C. outer_prod u u)"
    and "trace (\<Sum>u\<in>C. outer_prod u u) = real (card C)"
proof -
  show "is_proj (\<Sum>u\<in>C. outer_prod u u)"
    unfolding is_proj_def
  proof
    show "transpose (\<Sum>u\<in>C. outer_prod u u) = (\<Sum>u\<in>C. outer_prod u u)"
      by (simp add: transpose_matrix_sum)
    have "(\<Sum>u\<in>C. outer_prod u u) ** (\<Sum>v\<in>C. outer_prod v v)
        = (\<Sum>v\<in>C. \<Sum>u\<in>C. (u \<bullet> v) *\<^sub>R outer_prod u v)"
      by (simp add: matrix_mult_sum_left matrix_mult_sum_right outer_prod_mult)
    also have "\<dots> = (\<Sum>u\<in>C. \<Sum>v\<in>C. (u \<bullet> v) *\<^sub>R outer_prod u v)"
      by (rule sum.swap)
    also have "\<dots> = (\<Sum>u\<in>C. \<Sum>v\<in>C. if v = u then outer_prod u u else 0)"
      by (intro sum.cong refl)
        (use C in \<open>auto dest: onormal_inner_distinct
          simp: outer_prod_scaleR_left\<close>)
    also have "\<dots> = (\<Sum>u\<in>C. outer_prod u u)"
      using C by (simp add: onormal_def)
    finally show "(\<Sum>u\<in>C. outer_prod u u) ** (\<Sum>u\<in>C. outer_prod u u)
        = (\<Sum>u\<in>C. outer_prod u u)" .
  qed
  have "trace (\<Sum>u\<in>C. outer_prod u u) = (\<Sum>u\<in>C. u \<bullet> u)"
    by (simp add: trace_matrix_sum)
  also have "\<dots> = (\<Sum>u\<in>C. (1::real))"
    by (intro sum.cong refl) (use C in \<open>simp\<close>)
  finally show "trace (\<Sum>u\<in>C. outer_prod u u) = real (card C)"
    by simp
qed

text \<open>Conversely, every orthogonal projection is the basis-projection onto its
  range: in an orthonormal eigenbasis its eigenvalues are \<open>0\<close> or \<open>1\<close>, and the
  spectral decomposition keeps the eigenvectors of eigenvalue \<open>1\<close>.\<close>

lemma is_proj_decomp:
  assumes P: "is_proj P"
  obtains C where "onormal C" "P = (\<Sum>u\<in>C. outer_prod u u)"
    "real (card C) = trace P"
proof -
  have symP: "transpose P = P" and idem: "P ** P = P"
    using P by (auto simp: is_proj_def)
  obtain B where B: "onormal B" "span B = UNIV"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> P *v u = (u \<bullet> (P *v u)) *\<^sub>R u"
    using symmetric_eigenbasis[OF symP] by metis
  have mu01: "u \<bullet> (P *v u) = 0 \<or> u \<bullet> (P *v u) = 1" if u: "u \<in> B" for u
  proof -
    define \<mu> where "\<mu> = u \<bullet> (P *v u)"
    have Pu: "P *v u = \<mu> *\<^sub>R u"
      unfolding \<mu>_def using eig[OF u] .
    have "P *v (P *v u) = P *v u"
      by (simp add: matrix_vector_mul_assoc idem)
    then have "(\<mu> * \<mu>) *\<^sub>R u = \<mu> *\<^sub>R u"
      by (simp add: Pu matrix_vector_mult_scaleR)
    moreover have "u \<noteq> 0"
      using B(1) u by (auto simp: onormal_def)
    ultimately have "\<mu> * (\<mu> - 1) = 0"
      by (simp add: algebra_simps)
    then show ?thesis
      unfolding \<mu>_def[symmetric] by auto
  qed
  define C where "C = {u \<in> B. u \<bullet> (P *v u) = 1}"
  have onC: "onormal C"
    by (rule onormal_subset[OF B(1)]) (auto simp: C_def)
  have "P = (\<Sum>u\<in>B. (u \<bullet> (P *v u)) *\<^sub>R outer_prod u u)"
    by (rule spectral_decomposition[OF B eig])
  also have "\<dots> = (\<Sum>u\<in>B. if u \<bullet> (P *v u) = 1 then outer_prod u u else 0)"
    by (intro sum.cong refl) (use mu01 in fastforce)
  also have "\<dots> = (\<Sum>u\<in>C. outer_prod u u)"
    using onormal_finite[OF B(1)] by (simp add: C_def sum.inter_filter)
  finally have Peq: "P = (\<Sum>u\<in>C. outer_prod u u)" .
  show thesis
    by (rule that[OF onC Peq]) (simp add: Peq onormal_proj(2)[OF onC])
qed

lemma proj_with_trace_exists:
  assumes m: "m \<le> CARD('n::finite)"
  obtains P :: "real^'n^'n" where "is_proj P" "trace P = real m"
proof -
  obtain B :: "(real^'n) set" where B: "onormal B" "span B = UNIV"
    using onormal_extension[OF onormal_empty] by auto
  have "card B = CARD('n)"
    using onormal_card_dim_span[OF B(1)] B(2)
    by simp
  with m obtain T where T: "T \<subseteq> B" "card T = m" "finite T"
    by (metis obtain_subset_with_card_n)
  have onT: "onormal T"
    using T B(1) by (auto simp: onormal_def elim: pairwise_subset)
  show thesis
    using onormal_proj[OF onT] T(2) by (intro that[of "\<Sum>u\<in>T. outer_prod u u"]) auto
qed

text \<open>If one coefficient is strictly between \<open>0\<close> and \<open>1\<close> then so is a second
  one: otherwise the total would be that coefficient plus an integer, forcing
  it to be an integer itself.\<close>

lemma two_fractional:
  fixes B :: "'a set" and c :: "'a \<Rightarrow> real"
  assumes fin: "finite B" and i: "i \<in> B" and fi: "c i \<notin> {0, 1}"
    and c0: "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> c u" and c1: "\<And>u. u \<in> B \<Longrightarrow> c u \<le> 1"
    and isum: "(\<Sum>u\<in>B. c u) = real (N :: nat)"
  shows "\<exists>j \<in> B. j \<noteq> i \<and> c j \<notin> {0, 1}"
proof (rule ccontr)
  assume "\<not> (\<exists>j \<in> B. j \<noteq> i \<and> c j \<notin> {0, 1})"
  then have all01: "c u \<in> {0, 1}" if "u \<in> B" "u \<noteq> i" for u
    using that by blast
  define D where "D = B - {i}"
  have finD: "finite D"
    using fin by (simp add: D_def)
  define M where "M = card {u \<in> D. c u = 1}"
  have sumD: "(\<Sum>u\<in>D. c u) = real M"
  proof -
    have "(\<Sum>u\<in>D. c u) = (\<Sum>u\<in>{u \<in> D. c u = 1}. c u)"
      by (rule sum.mono_neutral_right[OF finD])
        (use all01 in \<open>auto simp: D_def\<close>)
    also have "\<dots> = real M"
      by (simp add: M_def)
    finally show ?thesis .
  qed
  have "(\<Sum>u\<in>B. c u) = c i + (\<Sum>u\<in>D. c u)"
    unfolding D_def using fin i by (simp add: sum.remove)
  then have ci_eq: "c i = real N - real M"
    using isum sumD by simp
  have "0 < c i" and "c i < 1"
    using fi c0[OF i] c1[OF i] by auto
  then have "real M < real N" and "real N < real M + 1"
    using ci_eq by simp_all
  then have "M < N" and "N < M + 1"
    by simp_all
  then show False
    by simp
qed

section \<open>The linear program on the simplex inside a box\<close>

text \<open>Among the \<open>m\<close>-element subsets of a finite set, one maximises the
  \<open>f\<close>-sum.\<close>

lemma exists_max_sum_subset:
  fixes f :: "'a \<Rightarrow> real"
  assumes finU: "finite U" and m: "m \<le> card U"
  obtains T where "T \<subseteq> U" "card T = m"
    and "\<And>T'. T' \<subseteq> U \<Longrightarrow> card T' = m \<Longrightarrow> (\<Sum>i\<in>T'. f i) \<le> (\<Sum>i\<in>T. f i)"
proof -
  define Sub where "Sub = {T. T \<subseteq> U \<and> card T = m}"
  have "finite Sub"
    using finU by (intro finite_subset[of Sub "Pow U"]) (auto simp: Sub_def)
  moreover have "Sub \<noteq> {}"
    using obtain_subset_with_card_n[OF m] by (auto simp: Sub_def)
  ultimately obtain T where "is_arg_min (\<lambda>T. - (\<Sum>i\<in>T. f i)) (\<lambda>T. T \<in> Sub) T"
    using ex_is_arg_min_if_finite by blast
  then show thesis
    by (intro that[of T]) (auto simp: is_arg_min_def Sub_def not_less)
qed

text \<open>Among the \<open>m\<close>-element subsets of a finite set there is one whose
  \<open>f\<close>-values all dominate those outside it: take a subset maximising the
  \<open>f\<close>-sum, and swap.\<close>

lemma exists_top_subset:
  fixes f :: "'a \<Rightarrow> real"
  assumes finU: "finite U" and m: "m \<le> card U"
  obtains T where "T \<subseteq> U" "card T = m"
    and "\<And>i j. i \<in> T \<Longrightarrow> j \<in> U - T \<Longrightarrow> f j \<le> f i"
proof -
  define g where "g = (\<lambda>T. \<Sum>i\<in>T. f i)"
  obtain T where Tsub: "T \<subseteq> U" and cardT: "card T = m"
    and Tmax: "\<And>T'. T' \<subseteq> U \<Longrightarrow> card T' = m \<Longrightarrow> g T' \<le> g T"
    unfolding g_def using exists_max_sum_subset[OF finU m] by blast
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
      by (rule Tmax[OF T'sub cardT'])
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

lemma is_proj_norm_le:
  assumes P: "is_proj P"
  shows "norm (P *v w) \<le> norm w"
  unfolding norm_le using proj_quadform_le_self[OF P, of w] proj_quadform_self[OF P, of w]
  by linarith

lemma is_proj_psd:
  assumes P: "is_proj P"
  shows "psd P"
  using P proj_quadform_nonneg[OF P] by (simp add: psd_def is_proj_def)

lemma trace_proj_psd_nonneg:
  assumes a: "psd a" and P: "is_proj P"
  shows "0 \<le> trace (a ** P)"
  by (rule trace_mult_psd_nonneg[OF a is_proj_psd[OF P]])

lemma proj_quadform_le_one:
  assumes P: "is_proj P" and B: "onormal B" and u: "u \<in> B"
  shows "u \<bullet> (P *v u) \<le> 1"
  using proj_quadform_le_self[OF P, of u] B u by simp

section \<open>The trace against a projection, read off in an eigenbasis\<close>

text \<open>If \<open>B\<close> is an orthonormal eigenbasis of the symmetric matrix \<open>a\<close> with
  eigenvalues \<open>\<lambda>\<^sub>u = u \<bullet> a u\<close>, then for every matrix \<open>P\<close>

    \<open>trace (a ** P) = \<Sum>\<^sub>u \<lambda>\<^sub>u * (u \<bullet> P u)\<close>

  (\<open>trace_mult_eigen_weights\<close>), so that a projection of trace \<open>m\<close>
  produces exactly the weights of the linear program: in \<open>[0,1]\<close> and
  summing to \<open>m\<close>.  The weights of a trace-\<open>m\<close> projection sum to \<open>m\<close>:\<close>

lemma proj_weights_sum:
  fixes P :: "real^'n::finite^'n"
  assumes B: "onormal B" "span B = UNIV" and P: "trace P = real m"
  shows "(\<Sum>u\<in>B. u \<bullet> (P *v u)) = real m"
  using trace_onormal_basis[OF B, of P] P by simp

section \<open>Ky Fan partial sums: the sum of the \<open>m\<close> largest eigenvalues\<close>

text \<open>As a supremum over projections, \<open>kyfan\<close> is manifestly
  independent of any choice of basis; unlike a definition by sorting a
  multiset of eigenvalues, it needs no well-definedness proof.\<close>

definition kyfan :: "nat \<Rightarrow> real^'n::finite^'n \<Rightarrow> real" where
  "kyfan m a = Sup {trace (a ** P) | P. is_proj P \<and> trace P = real m}"

text \<open>The spectral projection onto \<open>m\<close> members of an orthonormal family is
  a projection of trace \<open>m\<close>, and the trace of \<open>a\<close> against it is the sum of
  the quadratic forms of \<open>a\<close> at those members.\<close>

lemma spectral_proj_trace:
  fixes a :: "real^'n::finite^'n"
  assumes B: "onormal B" and T: "T \<subseteq> B" "card T = m"
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
    by (rule trace_mult_outer_sum)
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
  define S where "S = {trace (a ** P) | P :: real^'n^'n. is_proj P \<and> trace P = real m}"
  have finB: "finite B"
    by (rule onormal_finite[OF B(1)])
  have m_le: "m \<le> card B"
    using m onormal_span_card[OF B] by simp
  define g where "g = (\<lambda>T. \<Sum>u\<in>T. lam u)"
  obtain T0 where T0sub: "T0 \<subseteq> B" and cardT0: "card T0 = m"
    and T0max: "\<And>T'. T' \<subseteq> B \<Longrightarrow> card T' = m \<Longrightarrow> g T' \<le> g T0"
    unfolding g_def using exists_max_sum_subset[OF finB m_le] by blast
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
      by (rule T0max[OF T])
    finally show ?thesis .
  qed
  text \<open>And \<open>g T0\<close> is itself attained, by the spectral projection onto \<open>T0\<close>.\<close>
  have member: "g T0 \<in> S"
  proof -
    define P0 where "P0 = (\<Sum>u\<in>T0. outer_prod u u)"
    have p1: "is_proj P0" and p2: "trace P0 = real m"
      and tr: "trace (a ** P0) = (\<Sum>u\<in>T0. lam u)"
      unfolding P0_def lam_def
      using spectral_proj_trace[OF B(1) T0sub cardT0] by blast+
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
      using T0max[of T'] by (simp add: g_def lam_def)
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
  have pz: "is_proj (0 :: real^'n^'n)"
    by (auto simp: is_proj_def transpose_def matrix_matrix_mult_def vec_eq_iff)
  have "{trace (a ** P) | P :: real^'n^'n. is_proj P \<and> trace P = real (0::nat)} = {0}"
  proof (intro set_eqI iffI)
    fix x assume "x \<in> {trace (a ** P) | P :: real^'n^'n. is_proj P \<and> trace P = real (0::nat)}"
    then obtain P :: "real^'n^'n" where "is_proj P" "trace P = 0" "x = trace (a ** P)"
      by auto
    then show "x \<in> {0}"
      using is_proj_trace_zero[of P] by (simp add: trace_mult_zero_right)
  next
    have "trace (0 :: real^'n^'n) = real (0::nat)"
      by (simp add: trace_def)
    then show "x \<in> {trace (a ** P) | P :: real^'n^'n. is_proj P \<and> trace P = real (0::nat)}"
      if "x \<in> {0}" for x
      using that pz trace_mult_zero_right[of a] by (auto intro!: exI[of _ "0 :: real^'n^'n"])
  qed
  then show ?thesis by (simp add: kyfan_def)
qed

text \<open>The \<open>i\<close>-th largest eigenvalue of a symmetric matrix, \<open>1 \<le> i \<le> n\<close>.
  Being a difference of two basis-free quantities it is itself basis-free,
  with no well-definedness obligation.\<close>

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

text \<open>Every threshold set of positive size \<open>m\<close> attains \<open>eigval m a\<close> at its
  minimum, and an eigenbasis has such a set of every size up to \<open>n\<close>.\<close>

lemma eigval_threshold_min:
  fixes a :: "real^'n::finite^'n"
  assumes B: "onormal B" "span B = UNIV"
    and sym: "transpose a = a"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
    and T: "T \<subseteq> B" "card T = m" and m: "0 < m"
    and thresh: "\<And>u v. u \<in> T \<Longrightarrow> v \<in> B - T \<Longrightarrow> v \<bullet> (a *v v) \<le> u \<bullet> (a *v u)"
  obtains w where "w \<in> T" "\<And>u. u \<in> T \<Longrightarrow> w \<bullet> (a *v w) \<le> u \<bullet> (a *v u)"
    "eigval m a = w \<bullet> (a *v w)"
proof -
  have finT: "finite T"
    using T(1) onormal_finite[OF B(1)] by (rule finite_subset)
  have Tne: "T \<noteq> {}"
    using T(2) m by auto
  obtain w where w: "w \<in> T"
    and wmin: "\<And>u. u \<in> T \<Longrightarrow> w \<bullet> (a *v w) \<le> u \<bullet> (a *v u)"
    using arg_min_if_finite(1)[OF finT Tne, of "\<lambda>u :: real^'n. u \<bullet> (a *v u)"]
        arg_min_least[OF finT Tne, of _ "\<lambda>u :: real^'n. u \<bullet> (a *v u)"] by metis
  obtain i where mi: "m = Suc i"
    using m by (cases m) auto
  have cardT: "card T = Suc i"
    using T(2) mi by simp
  have "eigval m a = w \<bullet> (a *v w)"
    unfolding mi
    by (rule eigval_eq_min_of_threshold[OF B sym eig T(1) cardT thresh w wmin])
  with w wmin show thesis
    by (rule that)
qed

lemma eigval_threshold_witness:
  fixes a :: "real^'n::finite^'n"
  assumes B: "onormal B" "span B = UNIV"
    and sym: "transpose a = a"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
    and m: "0 < m" "m \<le> CARD('n)"
  obtains T w where "T \<subseteq> B" "card T = m"
    "\<And>u v. u \<in> T \<Longrightarrow> v \<in> B - T \<Longrightarrow> v \<bullet> (a *v v) \<le> u \<bullet> (a *v u)"
    "w \<in> T" "\<And>u. u \<in> T \<Longrightarrow> w \<bullet> (a *v w) \<le> u \<bullet> (a *v u)"
    "eigval m a = w \<bullet> (a *v w)"
proof -
  have mB: "m \<le> card B"
    using m(2) onormal_span_card[OF B] by simp
  obtain T where T: "T \<subseteq> B" "card T = m"
    and thresh: "\<And>u v. u \<in> T \<Longrightarrow> v \<in> B - T \<Longrightarrow> v \<bullet> (a *v v) \<le> u \<bullet> (a *v u)"
    using exists_top_subset[where f = "\<lambda>u :: real^'n. u \<bullet> (a *v u)",
        OF onormal_finite[OF B(1)] mB] by metis
  obtain w where w: "w \<in> T" "\<And>u. u \<in> T \<Longrightarrow> w \<bullet> (a *v w) \<le> u \<bullet> (a *v u)"
    "eigval m a = w \<bullet> (a *v w)"
    using eigval_threshold_min[OF B sym eig T m(1) thresh] by blast
  with T thresh show thesis
    by (rule that)
qed

text \<open>Every ordered eigenvalue is attained by a unit eigenvector.\<close>

lemma exists_eigenvector_eigval:
  fixes M :: "real^'n::finite^'n"
  assumes sym: "transpose M = M" and i: "1 \<le> i" "i \<le> CARD('n)"
  shows "\<exists>q. norm q = 1 \<and> M *v q = (q \<bullet> (M *v q)) *\<^sub>R q \<and> q \<bullet> (M *v q) = eigval i M"
proof -
  obtain B where B: "onormal B" "span B = UNIV"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> M *v u = (u \<bullet> (M *v u)) *\<^sub>R u"
    using symmetric_eigenbasis[OF sym] by metis
  obtain T w where "T \<subseteq> B" "w \<in> T" "eigval i M = w \<bullet> (M *v w)"
    using eigval_threshold_witness[OF B sym eig _ i(2)] i(1) by (metis less_eq_Suc_le One_nat_def)
  then show ?thesis using B(1) eig by (metis onormal_def subsetD)
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
  obtain B where B: "onormal B" "span B = UNIV"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
    using symmetric_eigenbasis[OF sym] by metis
  obtain T w where T: "T \<subseteq> B" "card T = Suc i"
    and thresh: "\<And>u v. u \<in> T \<Longrightarrow> v \<in> B - T \<Longrightarrow> v \<bullet> (a *v v) \<le> u \<bullet> (a *v u)"
    and w: "w \<in> T" and wmin: "\<And>u. u \<in> T \<Longrightarrow> w \<bullet> (a *v w) \<le> u \<bullet> (a *v u)"
    and e1: "eigval (Suc i) a = w \<bullet> (a *v w)"
    using eigval_threshold_witness[OF B sym eig zero_less_Suc n] by blast
  text \<open>One level down, on \<open>T - {w}\<close>.\<close>
  have finT: "finite T"
    using T(1) onormal_finite[OF B(1)] by (rule finite_subset)
  have th1: "v \<bullet> (a *v v) \<le> u \<bullet> (a *v u)"
    if "u \<in> T - {w}" "v \<in> B - (T - {w})" for u v
    by (rule threshold_remove_min[where lam = "\<lambda>u :: real^'n. u \<bullet> (a *v u)",
          OF thresh wmin that(1) that(2)])
  have T1: "T - {w} \<subseteq> B" "card (T - {w}) = i" "0 < i"
    using T finT w i by auto
  obtain w' where w': "w' \<in> T - {w}"
    and "\<And>u. u \<in> T - {w} \<Longrightarrow> w' \<bullet> (a *v w') \<le> u \<bullet> (a *v u)"
    and e0: "eigval i a = w' \<bullet> (a *v w')"
    using eigval_threshold_min[OF B sym eig T1 th1] by blast
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

text \<open>Two spectral sums are of general interest:

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
  maximum is the sum of the negative parts.\<close>

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

text \<open>Consequently the bracket

    \<open>L * (\<Sum>\<^sub>i \<lambda>\<^sub>i\<^sup>+) + \<Sum>\<^sub>i\<^sub>\<le>\<^sub>m min (\<lambda>\<^sub>i, 0)\<close>

  is a function of the Ky Fan sums alone:

    \<open>L * possum n a + (kyfan m a - possum m a)\<close>.\<close>

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

section \<open>The positive-part sum inside a threshold set\<close>

text \<open>On a threshold set \<open>S\<close> of size \<open>m\<close>, \<open>possum m a\<close> is the sum of the
  positive eigenvalues occurring in \<open>S\<close>, and consequently
  \<open>kyfan m a - possum m a\<close> is the sum of the nonpositive ones.

  The \<open>\<le>\<close> half uses \<open>kyfan_within_threshold\<close> for each \<open>j \<le> m\<close>; the \<open>\<ge>\<close> half
  observes that the positive part of \<open>S\<close> is again a threshold set of \<open>B\<close>, so
  \<open>kyfan_threshold\<close> evaluates it, and its size is at most \<open>m\<close>.\<close>

lemma threshold_shrink_one:
  fixes lam :: "'a \<Rightarrow> real"
  assumes finS: "finite S" and Sne: "S \<noteq> {}"
    and thresh: "\<And>u v. u \<in> S \<Longrightarrow> v \<in> B - S \<Longrightarrow> lam v \<le> lam u"
  shows "\<exists>T. T \<subseteq> S \<and> card T = card S - 1
          \<and> (\<forall>u \<in> T. \<forall>v \<in> B - T. lam v \<le> lam u)"
proof -
  obtain w where w: "w \<in> S"
    and wmin: "\<And>u. u \<in> S \<Longrightarrow> lam w \<le> lam u"
    using arg_min_if_finite(1)[OF finS Sne, of lam]
        arg_min_least[OF finS Sne, of _ lam] by metis
  have sub: "S - {w} \<subseteq> S"
    by blast
  have cardw: "card (S - {w}) = card S - 1"
    using finS w by simp
  have th: "\<forall>u \<in> S - {w}. \<forall>v \<in> B - (S - {w}). lam v \<le> lam u"
  proof (intro ballI)
    fix u v assume uv: "u \<in> S - {w}" "v \<in> B - (S - {w})"
    show "lam v \<le> lam u"
      by (rule threshold_remove_min[where lam = lam and T = S and B = B and w = w,
            OF thresh wmin uv(1) uv(2)])
  qed
  show ?thesis
    by (rule exI[of _ "S - {w}"]) (intro conjI sub cardw th)
qed

text \<open>The descending chain, by induction on \<open>n = card S\<close>, where the measure
  decreases visibly.  The step splits on whether \<open>j\<close> is already \<open>card S\<close>.\<close>

lemma threshold_chain_aux:
  fixes lam :: "'a \<Rightarrow> real"
  assumes finB: "finite B"
  shows "\<And>S j. card S = n \<Longrightarrow> S \<subseteq> B
     \<Longrightarrow> (\<forall>u \<in> S. \<forall>v \<in> B - S. lam v \<le> lam u) \<Longrightarrow> j \<le> n
     \<Longrightarrow> \<exists>T. T \<subseteq> S \<and> card T = j
             \<and> (\<forall>u \<in> T. \<forall>v \<in> B - T. lam v \<le> lam u)"
proof (induction n)
  case 0
  then have j0: "j = 0" by simp
  show ?case
    by (rule exI[of _ "{}"]) (simp add: j0)
next
  case (Suc n)
  have finS: "finite S"
    using Suc.prems(2) finB by (rule finite_subset)
  show ?case
  proof (cases "j = Suc n")
    case True
    have c: "card S = j"
      using Suc.prems(1) True by simp
    show ?thesis
      by (rule exI[of _ S]) (intro conjI subset_refl c Suc.prems(3))
  next
    case False
    then have jn: "j \<le> n"
      using Suc.prems(4) by simp
    have Sne: "S \<noteq> {}"
      using Suc.prems(1) by auto
    have thr: "lam v \<le> lam u" if "u \<in> S" "v \<in> B - S" for u v
      using Suc.prems(3) that by blast
    have ex1: "\<exists>T. T \<subseteq> S \<and> card T = card S - 1
            \<and> (\<forall>u \<in> T. \<forall>v \<in> B - T. lam v \<le> lam u)"
      by (rule threshold_shrink_one[OF finS Sne thr])
    obtain S' where S'P: "S' \<subseteq> S \<and> card S' = card S - 1
            \<and> (\<forall>u \<in> S'. \<forall>v \<in> B - S'. lam v \<le> lam u)"
      using ex1 by (rule exE)
    have S'sub: "S' \<subseteq> S"
      using S'P by simp
    have S'card: "card S' = n"
      using S'P Suc.prems(1) by simp
    have S'th: "\<forall>u \<in> S'. \<forall>v \<in> B - S'. lam v \<le> lam u"
      using S'P by simp
    have S'B: "S' \<subseteq> B"
      using S'sub Suc.prems(2) by blast
    have ex2: "\<exists>T. T \<subseteq> S' \<and> card T = j
            \<and> (\<forall>u \<in> T. \<forall>v \<in> B - T. lam v \<le> lam u)"
      by (rule Suc.IH[OF S'card S'B S'th jn])
    obtain T where TP: "T \<subseteq> S' \<and> card T = j
            \<and> (\<forall>u \<in> T. \<forall>v \<in> B - T. lam v \<le> lam u)"
      using ex2 by (rule exE)
    have TS: "T \<subseteq> S"
      using TP S'sub by auto
    have Tcard: "card T = j"
      using TP by simp
    have Tth: "\<forall>u \<in> T. \<forall>v \<in> B - T. lam v \<le> lam u"
      using TP by simp
    show ?thesis
      by (rule exI[of _ T]) (intro conjI TS Tcard Tth)
  qed
qed

lemma threshold_chain:
  fixes lam :: "'a \<Rightarrow> real"
  assumes finB: "finite B" and S: "S \<subseteq> B"
    and thresh: "\<And>u v. u \<in> S \<Longrightarrow> v \<in> B - S \<Longrightarrow> lam v \<le> lam u"
    and j: "j \<le> card S"
  shows "\<exists>T. T \<subseteq> S \<and> card T = j
          \<and> (\<forall>u \<in> T. \<forall>v \<in> B - T. lam v \<le> lam u)"
proof -
  have th: "\<forall>u \<in> S. \<forall>v \<in> B - S. lam v \<le> lam u"
  proof (intro ballI)
    fix u v assume "u \<in> S" "v \<in> B - S"
    then show "lam v \<le> lam u" by (rule thresh)
  qed
  show ?thesis
    by (rule threshold_chain_aux[OF finB refl S th j])
qed

text \<open>Specialised to an eigenbasis: for every \<open>j \<le> m\<close> the Ky Fan sum
  \<open>kyfan j a\<close> is already computed inside a threshold set \<open>S\<close> of size \<open>m\<close>,
  which lets \<open>possum m a\<close> be identified with the positive-part sum over
  \<open>S\<close>.\<close>

lemma kyfan_within_threshold:
  fixes a :: "real^'n::finite^'n"
  assumes B: "onormal B" "span B = UNIV"
    and sym: "transpose a = a"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
    and S: "S \<subseteq> B" "card S = m"
    and thresh: "\<And>u v. u \<in> S \<Longrightarrow> v \<in> B - S \<Longrightarrow> v \<bullet> (a *v v) \<le> u \<bullet> (a *v u)"
    and j: "j \<le> m"
  shows "\<exists>T. T \<subseteq> S \<and> card T = j \<and> kyfan j a = (\<Sum>u\<in>T. u \<bullet> (a *v u))"
proof -
  have finB: "finite B"
    by (rule onormal_finite[OF B(1)])
  have jc: "j \<le> card S"
    using j S(2) by simp
  have ex: "\<exists>T. T \<subseteq> S \<and> card T = j
          \<and> (\<forall>u \<in> T. \<forall>v \<in> B - T. v \<bullet> (a *v v) \<le> u \<bullet> (a *v u))"
    by (rule threshold_chain[where lam = "\<lambda>u :: real^'n. u \<bullet> (a *v u)",
          OF finB S(1) thresh jc])
  obtain T where TP: "T \<subseteq> S \<and> card T = j
          \<and> (\<forall>u \<in> T. \<forall>v \<in> B - T. v \<bullet> (a *v v) \<le> u \<bullet> (a *v u))"
    using ex by (rule exE)
  have T1: "T \<subseteq> S"
    using TP by simp
  have T2: "card T = j"
    using TP by simp
  have thT: "\<forall>u \<in> T. \<forall>v \<in> B - T. v \<bullet> (a *v v) \<le> u \<bullet> (a *v u)"
    using TP by simp
  have TB: "T \<subseteq> B"
    using T1 S(1) by blast
  have thT': "v \<bullet> (a *v v) \<le> u \<bullet> (a *v u)" if "u \<in> T" "v \<in> B - T" for u v
    using thT that by blast
  have kf: "kyfan j a = (\<Sum>u\<in>T. u \<bullet> (a *v u))"
    by (rule kyfan_threshold[OF B sym eig TB T2 thT'])
  show ?thesis
    by (rule exI[of _ T]) (intro conjI T1 T2 kf)
qed

lemma possum_within_threshold:
  fixes a :: "real^'n::finite^'n"
  assumes B: "onormal B" "span B = UNIV"
    and sym: "transpose a = a"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
    and S: "S \<subseteq> B" "card S = m"
    and thresh: "\<And>u v. u \<in> S \<Longrightarrow> v \<in> B - S \<Longrightarrow> v \<bullet> (a *v v) \<le> u \<bullet> (a *v u)"
  shows "possum m a = (\<Sum>u\<in>S. max (u \<bullet> (a *v u)) 0)"
proof (rule antisym)
  have finB: "finite B"
    by (rule onormal_finite[OF B(1)])
  have finS: "finite S"
    using S(1) finB by (rule finite_subset)
  have bound: "\<forall>x \<in> (\<lambda>j. kyfan j a) ` {..m}. x \<le> (\<Sum>u\<in>S. max (u \<bullet> (a *v u)) 0)"
  proof (intro ballI)
    fix x assume "x \<in> (\<lambda>j. kyfan j a) ` {..m}"
    then obtain j where j: "j \<le> m" and x: "x = kyfan j a"
      by auto
    have exj: "\<exists>T. T \<subseteq> S \<and> card T = j \<and> kyfan j a = (\<Sum>u\<in>T. u \<bullet> (a *v u))"
      by (rule kyfan_within_threshold[OF B sym eig S thresh j])
    obtain T where TP: "T \<subseteq> S \<and> card T = j
            \<and> kyfan j a = (\<Sum>u\<in>T. u \<bullet> (a *v u))"
      using exj by (rule exE)
    have T1: "T \<subseteq> S"
      using TP by simp
    have kf: "kyfan j a = (\<Sum>u\<in>T. u \<bullet> (a *v u))"
      using TP by simp
    have "(\<Sum>u\<in>T. u \<bullet> (a *v u)) \<le> (\<Sum>u\<in>T. max (u \<bullet> (a *v u)) 0)"
      by (intro sum_mono) simp
    also have "\<dots> \<le> (\<Sum>u\<in>S. max (u \<bullet> (a *v u)) 0)"
      using finS T1 by (intro sum_mono2) auto
    finally show "x \<le> (\<Sum>u\<in>S. max (u \<bullet> (a *v u)) 0)"
      unfolding x kf .
  qed
  show "possum m a \<le> (\<Sum>u\<in>S. max (u \<bullet> (a *v u)) 0)"
    using bound unfolding possum_def by (subst Max_le_iff) auto
next
  have finB: "finite B"
    by (rule onormal_finite[OF B(1)])
  have finS: "finite S"
    using S(1) finB by (rule finite_subset)
  define P where "P = {u \<in> S. 0 < u \<bullet> (a *v u)}"
  have Psub: "P \<subseteq> S"
    by (auto simp: P_def)
  have PB: "P \<subseteq> B"
    using Psub S(1) by blast
  have cardP: "card P \<le> m"
    using S(2) card_mono[OF finS Psub] by simp
  text \<open>The positive part of a threshold set is again a threshold set: a
    point outside it is either inside \<open>S\<close> with a nonpositive value, or
    outside \<open>S\<close> and hence dominated already.\<close>
  have threshP: "v \<bullet> (a *v v) \<le> u \<bullet> (a *v u)" if u: "u \<in> P" and v: "v \<in> B - P" for u v
  proof -
    have upos: "0 < u \<bullet> (a *v u)"
      using u by (simp add: P_def)
    have uS: "u \<in> S"
      using u by (simp add: P_def)
    show ?thesis
    proof (cases "v \<in> S")
      case True
      then have "v \<bullet> (a *v v) \<le> 0"
        using v by (auto simp: P_def)
      then show ?thesis
        using upos by simp
    next
      case False
      then have "v \<in> B - S"
        using v by blast
      then show ?thesis
        by (rule thresh[OF uS])
    qed
  qed
  have kP: "kyfan (card P) a = (\<Sum>u\<in>P. u \<bullet> (a *v u))"
    by (rule kyfan_threshold[OF B sym eig PB refl threshP])
  have sumP: "(\<Sum>u\<in>S. max (u \<bullet> (a *v u)) 0) = (\<Sum>u\<in>P. u \<bullet> (a *v u))"
  proof -
    have split: "(\<Sum>u\<in>S. max (u \<bullet> (a *v u)) 0)
        = (\<Sum>u\<in>S - P. max (u \<bullet> (a *v u)) 0) + (\<Sum>u\<in>P. max (u \<bullet> (a *v u)) 0)"
      using Psub finS by (rule sum.subset_diff)
    have out: "(\<Sum>u\<in>S - P. max (u \<bullet> (a *v u)) 0) = 0"
      by (intro sum.neutral ballI) (auto simp: P_def)
    have inn: "(\<Sum>u\<in>P. max (u \<bullet> (a *v u)) 0) = (\<Sum>u\<in>P. u \<bullet> (a *v u))"
      by (intro sum.cong refl) (auto simp: P_def)
    show ?thesis
      using split out inn by simp
  qed
  have "(\<Sum>u\<in>S. max (u \<bullet> (a *v u)) 0) = kyfan (card P) a"
    using kP sumP by simp
  also have "\<dots> \<le> possum m a"
    by (rule possum_ge_kyfan[OF cardP])
  finally show "(\<Sum>u\<in>S. max (u \<bullet> (a *v u)) 0) \<le> possum m a" .
qed

text \<open>And the negative-part companion.\<close>

corollary kyfan_minus_possum_threshold:
  fixes a :: "real^'n::finite^'n"
  assumes B: "onormal B" "span B = UNIV"
    and sym: "transpose a = a"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
    and S: "S \<subseteq> B" "card S = m"
    and thresh: "\<And>u v. u \<in> S \<Longrightarrow> v \<in> B - S \<Longrightarrow> v \<bullet> (a *v v) \<le> u \<bullet> (a *v u)"
  shows "kyfan m a - possum m a = (\<Sum>u\<in>S. min (u \<bullet> (a *v u)) 0)"
proof -
  have kS: "kyfan m a = (\<Sum>u\<in>S. u \<bullet> (a *v u))"
    by (rule kyfan_threshold[OF B sym eig S thresh])
  have pS: "possum m a = (\<Sum>u\<in>S. max (u \<bullet> (a *v u)) 0)"
    by (rule possum_within_threshold[OF B sym eig S thresh])
  have step: "u \<bullet> (a *v u) - max (u \<bullet> (a *v u)) 0 = min (u \<bullet> (a *v u)) 0" for u
    by (simp add: min_def max_def)
  have "kyfan m a - possum m a
      = (\<Sum>u\<in>S. u \<bullet> (a *v u)) - (\<Sum>u\<in>S. max (u \<bullet> (a *v u)) 0)"
    unfolding kS pS by (rule refl)
  also have "\<dots> = (\<Sum>u\<in>S. u \<bullet> (a *v u) - max (u \<bullet> (a *v u)) 0)"
    by (simp add: sum_subtractf)
  also have "\<dots> = (\<Sum>u\<in>S. min (u \<bullet> (a *v u)) 0)"
    using step by simp
  finally show ?thesis .
qed

text \<open>Over a whole eigenbasis the threshold condition is vacuous, so
  \<open>possum CARD('n) a\<close> is the sum of the positive parts of all eigenvalues.\<close>

lemma possum_full_eq_sum_basis:
  fixes a :: "real^'n::finite^'n"
  assumes B: "onormal B" "span B = UNIV"
    and sym: "transpose a = a"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
  shows "possum CARD('n) a = (\<Sum>u\<in>B. max (u \<bullet> (a *v u)) 0)"
  by (rule possum_within_threshold[OF B sym eig subset_refl onormal_span_card[OF B]]) auto

section \<open>The linear program with an approximate weight sum\<close>

lemma reduce_weights_to_exact:
  fixes t :: "'a \<Rightarrow> real"
  assumes finB: "finite B"
    and t0: "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> t u"
    and tsum: "real m \<le> (\<Sum>u\<in>B. t u)"
  shows "\<exists>t'. (\<forall>u\<in>B. 0 \<le> t' u \<and> t' u \<le> t u) \<and> (\<Sum>u\<in>B. t' u) = real m"
proof (cases "m = 0")
  case True
  show ?thesis
    by (rule exI[of _ "\<lambda>_. 0"]) (simp add: True t0)
next
  case False
  have mpos: "0 < real m"
    using False by simp
  have pos: "0 < (\<Sum>u\<in>B. t u)"
    using mpos tsum by simp
  define r where "r = real m / (\<Sum>u\<in>B. t u)"
  have r0: "0 \<le> r"
    unfolding r_def using mpos pos by simp
  have r1: "r \<le> 1"
    unfolding r_def using tsum pos by simp
  have bounds: "0 \<le> r * t u \<and> r * t u \<le> t u" if u: "u \<in> B" for u
  proof
    show "0 \<le> r * t u"
      using r0 t0[OF u] by simp
    have "r * t u \<le> 1 * t u"
      using r1 t0[OF u] by (intro mult_right_mono) auto
    then show "r * t u \<le> t u"
      by simp
  qed
  have "(\<Sum>u\<in>B. r * t u) = r * (\<Sum>u\<in>B. t u)"
    by (rule sum_distrib_left[symmetric])
  also have "\<dots> = real m"
    unfolding r_def using pos by simp
  finally have rsum: "(\<Sum>u\<in>B. r * t u) = real m" .
  show ?thesis
    by (rule exI[of _ "\<lambda>u. r * t u"]) (intro conjI ballI bounds rsum)
qed

text \<open>The box program with \<open>(\<Sum>t) \<ge> real m\<close> rather than equality: the
  positive part uses \<open>t \<le> 1\<close> directly, and the negative part is pushed onto
  the scaled-down weights before applying \<open>sum_weighted_le_top_subset\<close>.\<close>


theorem box_program_bound:
  fixes lam t :: "'a \<Rightarrow> real"
  assumes finB: "finite B" and m: "m \<le> card B"
    and t0: "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> t u" and t1: "\<And>u. u \<in> B \<Longrightarrow> t u \<le> 1"
    and tsum: "real m \<le> (\<Sum>u\<in>B. t u)"
  shows "\<exists>T. T \<subseteq> B \<and> card T = m
      \<and> (\<Sum>u\<in>B. lam u * t u)
          \<le> (\<Sum>u\<in>B. max (lam u) 0) + (\<Sum>u\<in>T. min (lam u) 0)"
proof -
  obtain t' where t': "\<forall>u\<in>B. 0 \<le> t' u \<and> t' u \<le> t u"
    and t'sum: "(\<Sum>u\<in>B. t' u) = real m"
    using reduce_weights_to_exact[OF finB t0 tsum] by blast
  have t'0: "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> t' u"
    using t' by blast
  have t'1: "\<And>u. u \<in> B \<Longrightarrow> t' u \<le> 1"
    using t' t1 by force
  obtain T where T: "T \<subseteq> B" "card T = m"
    and neg': "(\<Sum>u\<in>B. min (lam u) 0 * t' u) \<le> (\<Sum>u\<in>T. min (lam u) 0)"
    using sum_weighted_le_top_subset[where f = "\<lambda>u. min (lam u) 0" and t = t',
        OF finB m t'0 t'1 t'sum] by metis
  have negmono: "(\<Sum>u\<in>B. min (lam u) 0 * t u) \<le> (\<Sum>u\<in>B. min (lam u) 0 * t' u)"
  proof (rule sum_mono)
    fix u assume u: "u \<in> B"
    have "t' u \<le> t u"
      using t' u by blast
    then show "min (lam u) 0 * t u \<le> min (lam u) 0 * t' u"
      by (intro mult_left_mono_neg) auto
  qed
  have pos: "(\<Sum>u\<in>B. max (lam u) 0 * t u) \<le> (\<Sum>u\<in>B. max (lam u) 0)"
  proof (rule sum_mono)
    fix u assume u: "u \<in> B"
    have "max (lam u) 0 * t u \<le> max (lam u) 0 * 1"
      using t1[OF u] by (intro mult_left_mono) auto
    then show "max (lam u) 0 * t u \<le> max (lam u) 0"
      by simp
  qed
  have split: "lam u * t u = max (lam u) 0 * t u + min (lam u) 0 * t u" for u
    by (simp add: min_def max_def)
  have "(\<Sum>u\<in>B. lam u * t u)
      = (\<Sum>u\<in>B. max (lam u) 0 * t u) + (\<Sum>u\<in>B. min (lam u) 0 * t u)"
    unfolding split by (rule sum.distrib)
  also have "\<dots> \<le> (\<Sum>u\<in>B. max (lam u) 0) + (\<Sum>u\<in>T. min (lam u) 0)"
    using pos negmono neg' by (intro add_mono) auto
  finally have le: "(\<Sum>u\<in>B. lam u * t u)
      \<le> (\<Sum>u\<in>B. max (lam u) 0) + (\<Sum>u\<in>T. min (lam u) 0)" .
  show ?thesis
    by (rule exI[of _ T]) (intro conjI T(1) T(2) le)
qed

text \<open>The linear program with weights in \<open>[0, L]\<close>, \<open>1 \<le> L\<close>, whose values
  clipped at \<open>1\<close> sum to at least \<open>m\<close>: writing \<open>w = t + s\<close> with
  \<open>t u = min (w u) 1\<close> and \<open>s u = max (w u - 1) 0\<close>, the \<open>t\<close>-part is the box
  program and the \<open>s\<close>-part contributes \<open>\<le> (L-1) * (\<Sum> max (lam u) 0)\<close>,
  giving the bracket \<open>L * (\<Sum> max (lam u) 0) + \<Sum>\<^sub>u\<^sub>\<in>\<^sub>T min (lam u) 0\<close>
  for some \<open>m\<close>-element \<open>T\<close>.\<close>


theorem lp_upper_bound:
  fixes lam w :: "'a \<Rightarrow> real"
  assumes finB: "finite B" and m: "m \<le> card B" and L: "1 \<le> L"
    and w0: "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> w u" and wL: "\<And>u. u \<in> B \<Longrightarrow> w u \<le> L"
    and wsum: "real m \<le> (\<Sum>u\<in>B. min (w u) 1)"
  shows "\<exists>T. T \<subseteq> B \<and> card T = m
      \<and> (\<Sum>u\<in>B. lam u * w u)
          \<le> L * (\<Sum>u\<in>B. max (lam u) 0) + (\<Sum>u\<in>T. min (lam u) 0)"
proof -
  have t0: "0 \<le> min (w u) 1" if u: "u \<in> B" for u
    using w0[OF u] by simp
  have t1: "min (w u) 1 \<le> 1" for u
    by simp
  obtain T where T: "T \<subseteq> B" "card T = m"
    and tpart: "(\<Sum>u\<in>B. lam u * min (w u) 1)
        \<le> (\<Sum>u\<in>B. max (lam u) 0) + (\<Sum>u\<in>T. min (lam u) 0)"
    using box_program_bound[where lam = lam and t = "\<lambda>u. min (w u) 1",
        OF finB m t0 t1 wsum] by blast
  have spart: "(\<Sum>u\<in>B. lam u * (w u - min (w u) 1))
      \<le> (L - 1) * (\<Sum>u\<in>B. max (lam u) 0)"
  proof -
    have "(\<Sum>u\<in>B. lam u * (w u - min (w u) 1))
        \<le> (\<Sum>u\<in>B. max (lam u) 0 * (L - 1))"
    proof (rule sum_mono)
      fix u assume u: "u \<in> B"
      have s0: "0 \<le> w u - min (w u) 1"
        by simp
      have sL: "w u - min (w u) 1 \<le> L - 1"
        using wL[OF u] L by (simp add: min_def)
      have "lam u * (w u - min (w u) 1) \<le> max (lam u) 0 * (w u - min (w u) 1)"
        using s0 by (intro mult_right_mono) auto
      also have "\<dots> \<le> max (lam u) 0 * (L - 1)"
        using sL by (intro mult_left_mono) auto
      finally show "lam u * (w u - min (w u) 1) \<le> max (lam u) 0 * (L - 1)" .
    qed
    also have "\<dots> = (L - 1) * (\<Sum>u\<in>B. max (lam u) 0)"
      by (simp add: sum_distrib_left mult.commute)
    finally show ?thesis .
  qed
  have decomp: "lam u * w u
      = lam u * min (w u) 1 + lam u * (w u - min (w u) 1)" for u
    by (simp add: algebra_simps)
  have "(\<Sum>u\<in>B. lam u * w u)
      = (\<Sum>u\<in>B. lam u * min (w u) 1) + (\<Sum>u\<in>B. lam u * (w u - min (w u) 1))"
    unfolding decomp by (rule sum.distrib)
  also have "\<dots> \<le> ((\<Sum>u\<in>B. max (lam u) 0) + (\<Sum>u\<in>T. min (lam u) 0))
      + (L - 1) * (\<Sum>u\<in>B. max (lam u) 0)"
    using tpart spart by (rule add_mono)
  also have "\<dots> = L * (\<Sum>u\<in>B. max (lam u) 0) + (\<Sum>u\<in>T. min (lam u) 0)"
    by (simp add: algebra_simps)
  finally have le: "(\<Sum>u\<in>B. lam u * w u)
      \<le> L * (\<Sum>u\<in>B. max (lam u) 0) + (\<Sum>u\<in>T. min (lam u) 0)" .
  show ?thesis
    by (rule exI[of _ T]) (intro conjI T(1) T(2) le)
qed

text \<open>The box program returns an arbitrary size-\<open>m\<close> set \<open>T\<close>, whereas
  \<open>kyfan m - possum m\<close> sums over a threshold set.  Since \<open>min (\<cdot>) 0\<close> is
  monotone, a threshold set for \<open>lam\<close> is also one for
  \<open>\<lambda>u. min (lam u) 0\<close>, and \<open>threshold_sum_maximal\<close> gives the inequality.\<close>


lemma sum_min_le_threshold:
  fixes lam :: "'a \<Rightarrow> real"
  assumes finB: "finite B"
    and T0: "T0 \<subseteq> B" "card T0 = m"
    and thresh: "\<And>u v. u \<in> T0 \<Longrightarrow> v \<in> B - T0 \<Longrightarrow> lam v \<le> lam u"
    and T: "T \<subseteq> B" "card T = m"
  shows "(\<Sum>u\<in>T. min (lam u) 0) \<le> (\<Sum>u\<in>T0. min (lam u) 0)"
proof -
  have threshmin: "min (lam v) 0 \<le> min (lam u) 0"
    if u: "u \<in> T0" and v: "v \<in> B - T0" for u v
    using thresh[OF u v] by (simp add: min_def)
  show ?thesis
    by (rule threshold_sum_maximal[where lam = "\<lambda>u. min (lam u) 0",
          OF finB T0(1) T0(2) threshmin T(1) T(2)])
qed

text \<open>The upper bound in bracket form.  For a symmetric \<open>N\<close> with eigenbasis
  \<open>B\<close>, and weights \<open>u \<bullet> (a *v u)\<close> in \<open>[0, L]\<close> whose values clipped at \<open>1\<close>
  sum to at least \<open>m\<close>, the weighted sum of the Rayleigh quotients of \<open>N\<close> is
  bounded by \<open>bracket m L N\<close>.  The two conversions are
  \<open>possum_full_eq_sum_basis\<close> (the positive part) and
  \<open>kyfan_minus_possum_threshold\<close> (the negative part, via
  \<open>sum_min_le_threshold\<close>).\<close>

theorem bracket_upper_bound:
  fixes N a :: "real^'n::finite^'n"
  assumes symN: "transpose N = N"
    and B: "onormal B" "span B = UNIV"
    and eigN: "\<And>u. u \<in> B \<Longrightarrow> N *v u = (u \<bullet> (N *v u)) *\<^sub>R u"
    and m: "m \<le> CARD('n)" and L: "1 \<le> L"
    and w0: "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> u \<bullet> (a *v u)"
    and wL: "\<And>u. u \<in> B \<Longrightarrow> u \<bullet> (a *v u) \<le> L"
    and wsum: "real m \<le> (\<Sum>u\<in>B. min (u \<bullet> (a *v u)) 1)"
  shows "(\<Sum>u\<in>B. (u \<bullet> (N *v u)) * (u \<bullet> (a *v u))) \<le> bracket m L N"
proof -
  have finB: "finite B"
    by (rule onormal_finite[OF B(1)])
  have cardB: "card B = CARD('n)"
    by (rule onormal_span_card[OF B])
  have mB: "m \<le> card B"
    using m cardB by simp
  obtain T where T: "T \<subseteq> B" "card T = m"
    and lp: "(\<Sum>u\<in>B. (u \<bullet> (N *v u)) * (u \<bullet> (a *v u)))
        \<le> L * (\<Sum>u\<in>B. max (u \<bullet> (N *v u)) 0)
          + (\<Sum>u\<in>T. min (u \<bullet> (N *v u)) 0)"
    using lp_upper_bound[where lam = "\<lambda>u :: real^'n. u \<bullet> (N *v u)"
        and w = "\<lambda>u :: real^'n. u \<bullet> (a *v u)", OF finB mB L w0 wL wsum]
    by blast
  text \<open>Pass to a threshold set, where the negative part becomes
    \<open>kyfan m - possum m\<close>.\<close>
  obtain T0 where T0: "T0 \<subseteq> B" "card T0 = m"
    and thresh: "\<And>u v. u \<in> T0 \<Longrightarrow> v \<in> B - T0
        \<Longrightarrow> v \<bullet> (N *v v) \<le> u \<bullet> (N *v u)"
    using exists_top_subset[where f = "\<lambda>u :: real^'n. u \<bullet> (N *v u)", OF finB mB]
    by metis
  have negle: "(\<Sum>u\<in>T. min (u \<bullet> (N *v u)) 0)
      \<le> (\<Sum>u\<in>T0. min (u \<bullet> (N *v u)) 0)"
    by (rule sum_min_le_threshold[where lam = "\<lambda>u :: real^'n. u \<bullet> (N *v u)",
          OF finB T0(1) T0(2) thresh T(1) T(2)])
  have negeq: "(\<Sum>u\<in>T0. min (u \<bullet> (N *v u)) 0) = kyfan m N - possum m N"
    by (rule kyfan_minus_possum_threshold[OF B symN eigN T0(1) T0(2) thresh,
          symmetric])
  have poseq: "(\<Sum>u\<in>B. max (u \<bullet> (N *v u)) 0) = possum CARD('n) N"
    by (rule possum_full_eq_sum_basis[OF B symN eigN, symmetric])
  have "(\<Sum>u\<in>B. (u \<bullet> (N *v u)) * (u \<bullet> (a *v u)))
      \<le> L * (\<Sum>u\<in>B. max (u \<bullet> (N *v u)) 0)
        + (\<Sum>u\<in>T0. min (u \<bullet> (N *v u)) 0)"
    using lp negle by simp
  also have "\<dots> = L * possum CARD('n) N + (kyfan m N - possum m N)"
    unfolding poseq negeq by (rule refl)
  also have "\<dots> = bracket m L N"
    by (simp add: bracket_def)
  finally show ?thesis .
qed

subsection \<open>Selecting a subset minimal for a weight\<close>

text \<open>The mirror image of \<open>exists_top_subset\<close>: some \<open>m\<close>-element subset
  carries the \<open>m\<close> smallest values of \<open>w\<close>.\<close>

lemma exists_min_subset:
  fixes w :: "'a \<Rightarrow> real"
  assumes finB: "finite B"
  shows "m \<le> card B \<Longrightarrow> \<exists>S. S \<subseteq> B \<and> card S = m
      \<and> (\<forall>u\<in>S. \<forall>v\<in>B - S. w u \<le> w v)"
  using exists_top_subset[where f = "\<lambda>u. - w u", OF finB] by (metis neg_le_iff_le)

text \<open>For weights \<open>c\<close> in \<open>[0, 1]\<close> summing to at least \<open>m\<close>, some subset of
  \<open>B\<close> with at least \<open>m\<close> elements has a \<open>w\<close>-sum no larger than the
  \<open>c\<close>-weighted sum of \<open>w\<close>.\<close>

lemma weighted_min_value:
  fixes w c :: "'a \<Rightarrow> real"
  assumes finB: "finite B" and m1: "1 \<le> m" and mB: "m \<le> card B"
    and c0: "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> c u" and c1: "\<And>u. u \<in> B \<Longrightarrow> c u \<le> 1"
    and csum: "real m \<le> (\<Sum>u\<in>B. c u)"
  obtains S where "S \<subseteq> B" and "m \<le> card S"
    and "(\<Sum>u\<in>S. w u) \<le> (\<Sum>u\<in>B. c u * w u)"
proof -
  obtain S0 where S0: "S0 \<subseteq> B" and cS0: "card S0 = m"
    and least: "\<forall>u\<in>S0. \<forall>v\<in>B - S0. w u \<le> w v"
    using exists_min_subset[OF finB mB] by blast
  have finS0: "finite S0" using S0 finB by (rule finite_subset)
  have neS0: "S0 \<noteq> {}" using cS0 m1 by auto
  define Neg where "Neg = {u \<in> B. w u < 0}"
  have finNeg: "finite Neg" unfolding Neg_def using finB by simp
  define \<tau> where "\<tau> = Max (w ` S0)"
  have tauS0: "\<And>u. u \<in> S0 \<Longrightarrow> w u \<le> \<tau>"
    unfolding \<tau>_def by (intro Max_ge finite_imageI finS0) blast
  have tauout: "\<And>v. v \<in> B - S0 \<Longrightarrow> \<tau> \<le> w v"
    unfolding \<tau>_def
    by (intro Max.boundedI finite_imageI finS0)
      (use neS0 least in blast)+
  show ?thesis
  proof (cases "Neg \<subseteq> S0")
    case True
    \<comment> \<open>the threshold is \<open>max \<tau> 0\<close>; every term is compared against it\<close>
    define tp where "tp = max \<tau> 0"
    have tp0: "0 \<le> tp" by (simp add: tp_def)
    have key: "0 \<le> (\<Sum>u\<in>B. c u * w u) - (\<Sum>u\<in>S0. w u)"
    proof -
      have split: "(\<Sum>u\<in>B. c u * w u)
          = (\<Sum>u\<in>S0. c u * w u) + (\<Sum>u\<in>B - S0. c u * w u)"
        using sum.subset_diff[OF S0 finB, of "\<lambda>u. c u * w u"] by simp
      have inS: "\<And>u. u \<in> S0 \<Longrightarrow> (c u - 1) * tp \<le> (c u - 1) * w u"
      proof -
        fix u assume u: "u \<in> S0"
        have wle: "w u \<le> tp" using tauS0[OF u] by (simp add: tp_def)
        have cle: "c u - 1 \<le> 0" using c1 S0 u by auto
        show "(c u - 1) * tp \<le> (c u - 1) * w u"
          using mult_left_mono_neg[OF wle cle] by simp
      qed
      have outS: "\<And>u. u \<in> B - S0 \<Longrightarrow> c u * tp \<le> c u * w u"
      proof -
        fix u assume u: "u \<in> B - S0"
        have w0: "0 \<le> w u" using True u unfolding Neg_def by auto
        have wge: "tp \<le> w u"
          using tauout[OF u] w0 by (simp add: tp_def)
        have c0': "0 \<le> c u" using c0 u by auto
        show "c u * tp \<le> c u * w u"
          by (rule mult_left_mono[OF wge c0'])
      qed
      have "(\<Sum>u\<in>B. c u * w u) - (\<Sum>u\<in>S0. w u)
          = (\<Sum>u\<in>S0. (c u - 1) * w u) + (\<Sum>u\<in>B - S0. c u * w u)"
        unfolding split by (simp add: sum_subtractf algebra_simps)
      moreover have "(\<Sum>u\<in>S0. (c u - 1) * tp) + (\<Sum>u\<in>B - S0. c u * tp)
          \<le> (\<Sum>u\<in>S0. (c u - 1) * w u) + (\<Sum>u\<in>B - S0. c u * w u)"
        by (intro add_mono sum_mono inS outS)
      moreover have "(\<Sum>u\<in>S0. (c u - 1) * tp) + (\<Sum>u\<in>B - S0. c u * tp)
          = tp * ((\<Sum>u\<in>B. c u) - real m)"
      proof -
        have h1: "(\<Sum>u\<in>S0. (c u - 1) * tp)
            = (\<Sum>u\<in>S0. c u * tp) - real m * tp"
          by (simp add: sum_subtractf cS0 algebra_simps)
        have h2: "(\<Sum>u\<in>S0. c u * tp) + (\<Sum>u\<in>B - S0. c u * tp)
            = (\<Sum>u\<in>B. c u * tp)"
          using sum.subset_diff[OF S0 finB, of "\<lambda>u. c u * tp"] by simp
        have h3: "(\<Sum>u\<in>B. c u * tp) = (\<Sum>u\<in>B. c u) * tp"
          by (simp add: sum_distrib_right)
        show ?thesis using h1 h2 h3 by (simp add: algebra_simps)
      qed
      moreover have "0 \<le> tp * ((\<Sum>u\<in>B. c u) - real m)"
        using tp0 csum by simp
      ultimately show ?thesis by linarith
    qed
    show ?thesis
      by (rule that[of S0]) (use S0 cS0 key in auto)
  next
    case False
    \<comment> \<open>a negative weight escaped the minimal set, so \<open>\<tau> < 0\<close> and taking all
      negatives on top of \<open>S0\<close> costs nothing\<close>
    obtain vn where vn: "vn \<in> Neg" "vn \<notin> S0" using False by blast
    have tneg: "\<tau> < 0"
    proof -
      have "\<tau> \<le> w vn"
        using tauout vn unfolding Neg_def by auto
      also have "w vn < 0" using vn unfolding Neg_def by auto
      finally show ?thesis .
    qed
    define S where "S = S0 \<union> Neg"
    have SB: "S \<subseteq> B" unfolding S_def Neg_def using S0 by auto
    have finS: "finite S" using SB finB by (rule finite_subset)
    have cardS: "m \<le> card S"
      unfolding S_def using cS0 card_mono[OF finS[unfolded S_def], of S0]
      by simp
    have inS: "\<And>u. u \<in> S \<Longrightarrow> w u \<le> 0"
    proof -
      fix u assume "u \<in> S"
      then consider "u \<in> S0" | "u \<in> Neg" unfolding S_def by blast
      then show "w u \<le> 0"
      proof cases
        case 1 then show ?thesis using tauS0 tneg by fastforce
      next
        case 2 then show ?thesis unfolding Neg_def by auto
      qed
    qed
    have key: "0 \<le> (\<Sum>u\<in>B. c u * w u) - (\<Sum>u\<in>S. w u)"
    proof -
      have split: "(\<Sum>u\<in>B. c u * w u)
          = (\<Sum>u\<in>S. c u * w u) + (\<Sum>u\<in>B - S. c u * w u)"
        using sum.subset_diff[OF SB finB, of "\<lambda>u. c u * w u"] by simp
      have t1: "0 \<le> (\<Sum>u\<in>S. (c u - 1) * w u)"
      proof (rule sum_nonneg)
        fix u assume u: "u \<in> S"
        have c1': "c u - 1 \<le> 0" using c1 SB u by auto
        have w0: "w u \<le> 0" by (rule inS[OF u])
        show "0 \<le> (c u - 1) * w u" by (rule mult_nonpos_nonpos[OF c1' w0])
      qed
      have t2: "0 \<le> (\<Sum>u\<in>B - S. c u * w u)"
      proof (rule sum_nonneg)
        fix u assume u: "u \<in> B - S"
        have "0 \<le> w u" using u unfolding S_def Neg_def by auto
        then show "0 \<le> c u * w u" using c0 u by auto
      qed
      have "(\<Sum>u\<in>B. c u * w u) - (\<Sum>u\<in>S. w u)
          = (\<Sum>u\<in>S. (c u - 1) * w u) + (\<Sum>u\<in>B - S. c u * w u)"
        unfolding split by (simp add: sum_subtractf algebra_simps)
      with t1 t2 show ?thesis by linarith
    qed
    show ?thesis
      by (rule that[of S]) (use SB cardS key in auto)
  qed
qed

(*<*)
end
(*>*)
