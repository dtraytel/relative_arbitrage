

(*<*)
theory Eigenvalue_Continuity
  imports Eigenvalues
begin

(*>*)

text \<open>
  Lipschitz dependence of the Ky Fan sums, hence of the ordered
             eigenvalues, on the matrix.

    The paper's proof of Lemma 3.1 uses the continuity of
    M |-> (lambda_(1)(M), ..., lambda_(n)(M)) twice: to pass to the limit in
    (3.8), and for the continuity of F off p = 0.

    In this development that is cheap.  Each kyfan m is a supremum of traces
    against orthogonal projections, and the quadratic form of a unit vector
    against D is bounded by the entrywise sum of |D|; so kyfan m moves by at
    most m * entrysum (A - B) when M moves from B to A.  Since eigval is a
    difference of two Ky Fan sums, it inherits the bound.  No eigenvalue
    perturbation theory is needed.\<close>
section \<open>The entrywise sum\<close>

definition entrysum :: "real^'n::finite^'n \<Rightarrow> real" where
  "entrysum D = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>D $ i $ j\<bar>)"

lemma entrysum_nonneg: "0 \<le> entrysum D"
  unfolding entrysum_def by (intro sum_nonneg) auto

lemma entrysum_sym: "entrysum (A - B) = entrysum (B - A)"
  unfolding entrysum_def by (intro sum.cong refl) (simp add: abs_minus_commute)

section \<open>The quadratic form of a unit vector\<close>

lemma inner_quadform_bound:
  fixes D :: "real^'n::finite^'n"
  assumes u: "norm u = 1"
  shows "\<bar>u \<bullet> (D *v u)\<bar> \<le> entrysum D"
proof -
  have ub: "\<bar>u $ i\<bar> \<le> 1" for i
    using component_le_norm_cart[of u i] u by simp
  have expand: "u \<bullet> (D *v u) = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. u $ i * (D $ i $ j * u $ j))"
    by (simp add: inner_vec_def matrix_vector_mult_def sum_distrib_left)
  have inner_le: "\<bar>\<Sum>j\<in>(UNIV::'n set). u $ i * (D $ i $ j * u $ j)\<bar>
      \<le> (\<Sum>j\<in>(UNIV::'n set). \<bar>D $ i $ j\<bar>)" for i
  proof -
    have "\<bar>\<Sum>j\<in>(UNIV::'n set). u $ i * (D $ i $ j * u $ j)\<bar>
        \<le> (\<Sum>j\<in>(UNIV::'n set). \<bar>u $ i * (D $ i $ j * u $ j)\<bar>)"
      by (rule sum_abs)
    also have "\<dots> \<le> (\<Sum>j\<in>(UNIV::'n set). \<bar>D $ i $ j\<bar>)"
    proof (rule sum_mono)
      fix j :: 'n
      have "\<bar>u $ i * (D $ i $ j * u $ j)\<bar> = \<bar>u $ i\<bar> * \<bar>D $ i $ j\<bar> * \<bar>u $ j\<bar>"
        by (simp add: abs_mult mult.assoc)
      also have "\<dots> \<le> 1 * \<bar>D $ i $ j\<bar> * 1"
        using ub[of i] ub[of j] by (intro mult_mono) auto
      finally show "\<bar>u $ i * (D $ i $ j * u $ j)\<bar> \<le> \<bar>D $ i $ j\<bar>"
        by simp
    qed
    finally show ?thesis .
  qed
  have "\<bar>u \<bullet> (D *v u)\<bar>
      \<le> (\<Sum>i\<in>UNIV. \<bar>\<Sum>j\<in>UNIV. u $ i * (D $ i $ j * u $ j)\<bar>)"
    unfolding expand by (rule sum_abs)
  also have "\<dots> \<le> (\<Sum>i\<in>(UNIV::'n set). \<Sum>j\<in>(UNIV::'n set). \<bar>D $ i $ j\<bar>)"
    by (intro sum_mono inner_le)
  finally show ?thesis
    unfolding entrysum_def .
qed

section \<open>The trace against a projection\<close>

lemma trace_mult_proj_bound:
  fixes D :: "real^'n::finite^'n"
  assumes P: "is_proj P" "trace P = real m"
  shows "\<bar>trace (D ** P)\<bar> \<le> real m * entrysum D"
proof -
  obtain C where C: "onormal C" "P = (\<Sum>u\<in>C. outer_prod u u)"
    "real (card C) = trace P"
    using is_proj_decomp[OF P(1)] by metis
  have cardC: "card C = m"
    using C(3) P(2) by simp
  have finC: "finite C"
    using C(1) by (rule onormal_finite)
  have "trace (D ** P) = (\<Sum>u\<in>C. u \<bullet> (D *v u))"
    by (simp add: C(2) trace_mult_outer_sum)
  then have "\<bar>trace (D ** P)\<bar> \<le> (\<Sum>u\<in>C. \<bar>u \<bullet> (D *v u)\<bar>)"
    by simp
  also have "\<dots> \<le> (\<Sum>u\<in>C. entrysum D)"
  proof (rule sum_mono)
    fix u assume "u \<in> C"
    then have "norm u = 1"
      using C(1) by (simp add: onormal_def)
    then show "\<bar>u \<bullet> (D *v u)\<bar> \<le> entrysum D"
      by (rule inner_quadform_bound)
  qed
  also have "\<dots> = real m * entrysum D"
    using cardC by simp
  finally show ?thesis .
qed

section \<open>The Ky Fan sums are Lipschitz in the matrix\<close>

lemma kyfan_gap:
  fixes A B :: "real^'n::finite^'n"
  assumes symB: "transpose B = B" and m: "m \<le> CARD('n)"
  shows "kyfan m A \<le> kyfan m B + real m * entrysum (A - B)"
  unfolding kyfan_def[of m A]
proof (rule cSup_least)
  show "{trace (A ** P) | P :: real^'n^'n. is_proj P \<and> trace P = real m} \<noteq> {}"
    using proj_with_trace_exists[OF m] by force
next
  fix x
  assume "x \<in> {trace (A ** P) | P :: real^'n^'n. is_proj P \<and> trace P = real m}"
  then obtain P :: "real^'n^'n" where P: "is_proj P" "trace P = real m"
    and x: "x = trace (A ** P)"
    by blast
  have split: "trace (A ** P) = trace (B ** P) + trace ((A - B) ** P)"
  proof -
    have "B ** P + (A - B) ** P = A ** P"
      by (simp add: matrix_add_rdistrib[symmetric])
    then show ?thesis
      by (metis trace_add)
  qed
  have le1: "trace (B ** P) \<le> kyfan m B"
    by (rule kyfan_ge_trace_mult[OF symB P(1) P(2)])
  have le2: "trace ((A - B) ** P) \<le> real m * entrysum (A - B)"
  proof -
    have "trace ((A - B) ** P) \<le> \<bar>trace ((A - B) ** P)\<bar>"
      by (rule abs_ge_self)
    also have "\<dots> \<le> real m * entrysum (A - B)"
      by (rule trace_mult_proj_bound[OF P(1) P(2)])
    finally show ?thesis .
  qed
  show "x \<le> kyfan m B + real m * entrysum (A - B)"
  proof -
    have "x = trace (B ** P) + trace ((A - B) ** P)"
      using x split by simp
    also have "\<dots> \<le> kyfan m B + real m * entrysum (A - B)"
      using le1 le2 by (rule add_mono)
    finally show ?thesis .
  qed
qed

theorem kyfan_lipschitz:
  fixes A B :: "real^'n::finite^'n"
  assumes symA: "transpose A = A" and symB: "transpose B = B"
    and m: "m \<le> CARD('n)"
  shows "\<bar>kyfan m A - kyfan m B\<bar> \<le> real m * entrysum (A - B)"
proof -
  have up: "kyfan m A - kyfan m B \<le> real m * entrysum (A - B)"
    using kyfan_gap[OF symB m, of A] by simp
  have dn: "kyfan m B - kyfan m A \<le> real m * entrysum (A - B)"
    using kyfan_gap[OF symA m, of B] by (simp add: entrysum_sym)
  show ?thesis
    using up dn by simp
qed

text \<open>Hence each ordered eigenvalue is Lipschitz too, being a difference of
  two Ky Fan sums.  This is the continuity of
  \<open>M \<mapsto> (\<lambda>\<^sub>(\<^sub>1\<^sub>)(M), \<dots>, \<lambda>\<^sub>(\<^sub>n\<^sub>)(M))\<close> that the proof of Lemma 3.1 needs.\<close>

corollary eigval_lipschitz:
  fixes A B :: "real^'n::finite^'n"
  assumes symA: "transpose A = A" and symB: "transpose B = B"
    and i: "i \<le> CARD('n)"
  shows "\<bar>eigval i A - eigval i B\<bar> \<le> 2 * real i * entrysum (A - B)"
proof -
  have i1: "i - 1 \<le> CARD('n)"
    using i by simp
  have a: "\<bar>kyfan i A - kyfan i B\<bar> \<le> real i * entrysum (A - B)"
    by (rule kyfan_lipschitz[OF symA symB i])
  have b: "\<bar>kyfan (i - 1) A - kyfan (i - 1) B\<bar>
      \<le> real (i - 1) * entrysum (A - B)"
    by (rule kyfan_lipschitz[OF symA symB i1])
  have le: "real (i - 1) \<le> real i"
    by simp
  have nn: "0 \<le> entrysum (A - B)"
    by (rule entrysum_nonneg)
  have "\<bar>eigval i A - eigval i B\<bar>
      \<le> \<bar>kyfan i A - kyfan i B\<bar> + \<bar>kyfan (i - 1) A - kyfan (i - 1) B\<bar>"
    unfolding eigval_def by simp
  also have "\<dots> \<le> real i * entrysum (A - B) + real (i - 1) * entrysum (A - B)"
    using a b by simp
  also have "\<dots> \<le> real i * entrysum (A - B) + real i * entrysum (A - B)"
    using le nn by (simp add: mult_right_mono)
  also have "\<dots> = 2 * real i * entrysum (A - B)"
    by simp
  finally show ?thesis .
qed


(*<*)
end
(*>*)
