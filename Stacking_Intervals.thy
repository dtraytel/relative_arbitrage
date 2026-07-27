section \<open>Stacking a mass sequence into consecutive intervals\<close>

text \<open>
  Layer 4 of the Skorokhod representation development (open task 25, needed by
  Lemma 2.3 of arXiv:2512.17702).

  Recall the shape of the Billingsley construction. Layers 1-3, in
  \<open>Measure_Continuity_Sets\<close>, produce a countable Borel partition of the Polish
  space into small pieces with null boundaries. The coupling is then built on
  \<open>[0,1)\<close> under Lebesgue measure: the unit interval is cut into CONSECUTIVE
  intervals whose lengths are the masses the measure assigns to the partition
  pieces, and each such interval is mapped into the corresponding piece. Weak
  convergence makes the masses converge, so the cut points converge, and the
  resulting maps converge almost everywhere.

  This theory supplies the cutting: given a summable sequence of nonnegative
  masses, the consecutive intervals delimited by its partial sums are disjoint,
  have exactly those masses under Lebesgue measure, and exhaust
  \<open>[0, suminf p)\<close>. Nothing here is probabilistic, and nothing depends on
  stochastic integration (open task 15).
\<close>

theory Stacking_Intervals
  imports "HOL-Probability.Probability"
begin

subsection \<open>Partial sums and the slabs they delimit\<close>

definition psum :: "(nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real" where
  "psum p n = (\<Sum>i<n. p i)"

definition slab :: "(nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real set" where
  "slab p n = {psum p n ..< psum p (Suc n)}"

lemma psum_0 [simp]: "psum p 0 = 0"
  by (simp add: psum_def)

lemma psum_Suc: "psum p (Suc n) = psum p n + p n"
  by (simp add: psum_def)

lemma psum_mono:
  assumes "\<And>i. 0 \<le> p i" and "m \<le> n"
  shows "psum p m \<le> psum p n"
  unfolding psum_def using assms by (intro sum_mono2) auto

lemma psum_nonneg:
  assumes "\<And>i. 0 \<le> p i"
  shows "0 \<le> psum p n"
  using psum_mono[OF assms, of 0 n] by simp

subsection \<open>The slab of index @{term n} has measure @{term "p n"}\<close>

lemma measure_slab:
  assumes p: "0 \<le> p n"
  shows "measure lborel (slab p n) = p n"
proof -
  have "emeasure lborel (slab p n) = ennreal (p n)"
    unfolding slab_def using p by (simp add: psum_Suc)
  thus ?thesis using p by (simp add: measure_def)
qed

subsection \<open>The slabs are pairwise disjoint\<close>

lemma slab_disjoint:
  assumes p: "\<And>i. 0 \<le> p i" and mn: "m < n"
  shows "slab p m \<inter> slab p n = {}"
proof -
  have "psum p (Suc m) \<le> psum p n" using p mn by (intro psum_mono) auto
  thus ?thesis unfolding slab_def by auto
qed

lemma disjoint_family_slab:
  assumes p: "\<And>i. 0 \<le> p i"
  shows "disjoint_family (slab p)"
  unfolding disjoint_family_on_def
proof (intro ballI impI)
  fix m n :: nat assume mn: "m \<noteq> n"
  show "slab p m \<inter> slab p n = {}"
  proof (cases "m < n")
    case True
    show ?thesis by (rule slab_disjoint[OF p True])
  next
    case False
    with mn have "n < m" by simp
    then have "slab p n \<inter> slab p m = {}" by (rule slab_disjoint[OF p])
    thus ?thesis by (simp add: Int_commute)
  qed
qed

subsection \<open>The slabs exhaust @{term "{0 ..< suminf p}"}\<close>

lemma slab_subset:
  assumes p: "\<And>i. 0 \<le> p i" and sp: "summable p"
  shows "slab p n \<subseteq> {0 ..< suminf p}"
proof -
  have lo: "0 \<le> psum p n" by (rule psum_nonneg[OF p])
  have hi: "psum p (Suc n) \<le> suminf p"
    unfolding psum_def using sp p by (intro sum_le_suminf) auto
  show ?thesis unfolding slab_def using lo hi by auto
qed

lemma slab_UN:
  assumes p: "\<And>i. 0 \<le> p i" and sp: "summable p"
  shows "(\<Union>n. slab p n) = {0 ..< suminf p}"
proof (intro equalityI subsetI)
  fix x assume "x \<in> (\<Union>n. slab p n)"
  thus "x \<in> {0 ..< suminf p}" using slab_subset[OF p sp] by blast
next
  fix x assume x: "x \<in> {0 ..< suminf p}"
  then have x0: "0 \<le> x" and xL: "x < suminf p" by auto
  have "\<exists>n. x < psum p n"
  proof -
    have "(\<lambda>n. psum p n) \<longlonglongrightarrow> suminf p"
      unfolding psum_def by (rule summable_LIMSEQ[OF sp])
    from this xL obtain n where "x < psum p n"
      by (metis order_tendstoD(1) eventually_sequentially order_refl)
    thus ?thesis by blast
  qed
  then obtain n where n: "x < psum p n" by blast
  define k where "k = (LEAST m. x < psum p m)"
  have kn: "x < psum p k" unfolding k_def using n by (rule LeastI)
  have kpos: "k \<noteq> 0"
  proof
    assume "k = 0"
    with kn show False using x0 by simp
  qed
  then obtain j where kj: "k = Suc j" by (cases k) auto
  have "\<not> x < psum p j"
    using kj unfolding k_def by (metis lessI not_less_Least)
  hence "psum p j \<le> x" by simp
  moreover have "x < psum p (Suc j)" using kn kj by simp
  ultimately have "x \<in> slab p j" unfolding slab_def by simp
  thus "x \<in> (\<Union>n. slab p n)" by (rule UN_I[OF UNIV_I])qed

end
