
(*<*)
theory Orthonormal_Families
  imports Outer_Products Matrix_Algebra
begin

(*>*)

text \<open>
  Finite orthonormal families of vectors: the completeness relation and the
  trace formula it gives in an orthonormal basis, and the extension of any
  orthonormal family to an orthonormal basis of the whole space.
\<close>

unbundle inner_syntax

section \<open>Orthonormal families\<close>

definition onormal :: "(real^'n) set \<Rightarrow> bool" where
  "onormal B \<longleftrightarrow> finite B \<and> pairwise orthogonal B \<and> (\<forall>u\<in>B. norm u = 1)"

lemma onormal_inner_self [simp]: "onormal B \<Longrightarrow> u \<in> B \<Longrightarrow> u \<bullet> u = 1"
  by (metis onormal_def norm_eq_1)

lemma onormal_inner_distinct: "onormal B \<Longrightarrow> u \<in> B \<Longrightarrow> v \<in> B \<Longrightarrow> u \<noteq> v \<Longrightarrow> u \<bullet> v = 0"
  by (auto simp: onormal_def pairwise_def orthogonal_def)

lemma onormal_inner_sums:
  assumes B: "onormal B"
  shows "(\<Sum>u\<in>B. f u *\<^sub>R u) \<bullet> (\<Sum>v\<in>B. g v *\<^sub>R v) = (\<Sum>u\<in>B. f u * g u)"
proof -
  have "(\<Sum>u\<in>B. f u *\<^sub>R u) \<bullet> (\<Sum>v\<in>B. g v *\<^sub>R v)
      = (\<Sum>v\<in>B. \<Sum>u\<in>B. f u * g v * (u \<bullet> v))"
    by (simp add: inner_sum_left inner_sum_right sum_distrib_left ac_simps)
  also have "\<dots> = (\<Sum>u\<in>B. \<Sum>v\<in>B. f u * g v * (u \<bullet> v))"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>u\<in>B. \<Sum>v\<in>B. if v = u then f u * g u else 0)"
    by (intro sum.cong refl)
      (use B in \<open>auto dest: onormal_inner_distinct\<close>)
  also have "\<dots> = (\<Sum>u\<in>B. f u * g u)"
    using B by (simp add: onormal_def)
  finally show ?thesis .
qed

lemma onormal_expand:
  assumes B: "onormal B" and x: "x \<in> span B"
  shows "(\<Sum>u\<in>B. (u \<bullet> x) *\<^sub>R u) = x"
proof -
  from x B obtain c where c: "x = (\<Sum>v\<in>B. c v *\<^sub>R v)"
    by (auto simp: span_finite onormal_def)
  have "u \<bullet> x = c u" if u: "u \<in> B" for u
  proof -
    have "u \<bullet> x = (\<Sum>v\<in>B. c v * (u \<bullet> v))"
      by (simp add: c inner_sum_right ac_simps)
    also have "\<dots> = (\<Sum>v\<in>B. if v = u then c u else 0)"
      by (intro sum.cong refl)
        (use B u in \<open>auto dest: onormal_inner_distinct simp: ac_simps\<close>)
    also have "\<dots> = c u"
      using B u by (simp add: onormal_def)
    finally show ?thesis .
  qed
  then show ?thesis
    by (simp add: c cong: sum.cong)
qed

lemma onormal_bessel:
  assumes B: "onormal B"
  shows "(\<Sum>u\<in>B. (u \<bullet> x)\<^sup>2) \<le> x \<bullet> x"
proof -
  define s where "s = (\<Sum>u\<in>B. (u \<bullet> x) *\<^sub>R u)"
  have ss: "s \<bullet> s = (\<Sum>u\<in>B. (u \<bullet> x)\<^sup>2)"
    by (simp add: s_def onormal_inner_sums[OF B] power2_eq_square)
  have xs: "x \<bullet> s = (\<Sum>u\<in>B. (u \<bullet> x)\<^sup>2)"
    by (simp add: s_def inner_sum_right power2_eq_square inner_commute)
  have "0 \<le> (x - s) \<bullet> (x - s)"
    by simp
  also have "(x - s) \<bullet> (x - s) = x \<bullet> x - 2 * (x \<bullet> s) + s \<bullet> s"
    by (simp add: inner_diff_left inner_diff_right inner_commute)
  finally show ?thesis
    using ss xs by simp
qed

section \<open>Completeness relation and traces in orthonormal bases\<close>

lemma onormal_complete:
  assumes B: "onormal B" and U: "span B = UNIV"
  shows "(\<Sum>u\<in>B. outer_prod u u) = mat 1"
proof -
  have "(\<Sum>u\<in>B. outer_prod u u) *v x = mat 1 *v x" for x
  proof -
    have "(\<Sum>u\<in>B. outer_prod u u) *v x = (\<Sum>u\<in>B. (u \<bullet> x) *\<^sub>R u)"
      by (simp add: matrix_vector_mult_sum)
    also have "\<dots> = x"
      by (rule onormal_expand[OF B]) (simp add: U)
    finally show ?thesis
      by simp
  qed
  then show ?thesis
    by (auto simp: matrix_eq)
qed

lemma trace_onormal_basis:
  assumes B: "onormal B" and U: "span B = UNIV"
  shows "trace A = (\<Sum>u\<in>B. u \<bullet> (A *v u))"
proof -
  have "trace A = trace (A ** (\<Sum>u\<in>B. outer_prod u u))"
    by (simp add: onormal_complete[OF B U])
  also have "\<dots> = (\<Sum>u\<in>B. trace (A ** outer_prod u u))"
    by (simp add: matrix_mult_sum_right trace_matrix_sum)
  also have "\<dots> = (\<Sum>u\<in>B. u \<bullet> (A *v u))"
    by (simp add: mult_outer_prod inner_commute)
  finally show ?thesis .
qed

section \<open>Extension of orthonormal families to orthonormal bases\<close>

lemma onormal_extension:
  assumes B: "onormal B"
  obtains C where "onormal C" "B \<subseteq> C" "span C = UNIV"
proof -
  have orthB: "pairwise orthogonal B"
    using B by (simp add: onormal_def)
  obtain U where U: "pairwise orthogonal (B \<union> U)"
    "span (B \<union> U) = span (B \<union> Basis)"
    using orthogonal_extension[OF orthB, where T = Basis] by blast
  define C where "C = (\<lambda>u. u /\<^sub>R norm u) ` ((B \<union> U) - {0})"
  have C_norm: "norm u = 1" if "u \<in> C" for u
    using that
    by (auto simp: C_def sgn_div_norm[symmetric] norm_sgn split: if_splits)
  have C_orth: "pairwise orthogonal C"
  proof (rule pairwiseI)
    fix x y assume "x \<in> C" "y \<in> C" "x \<noteq> y"
    then obtain u v where uv: "u \<in> (B \<union> U) - {0}" "v \<in> (B \<union> U) - {0}"
      "x = u /\<^sub>R norm u" "y = v /\<^sub>R norm v"
      by (auto simp: C_def)
    with \<open>x \<noteq> y\<close> have "u \<noteq> v" by auto
    with U(1) uv have "orthogonal u v"
      by (auto simp: pairwise_def)
    then show "orthogonal x y"
      by (simp add: uv orthogonal_def)
  qed
  have C_fin: "finite C"
    using C_orth C_norm
    by (intro pairwise_orthogonal_imp_finite) auto
  have BC: "B \<subseteq> C"
  proof
    fix b assume b: "b \<in> B"
    with B have "norm b = 1"
      by (simp add: onormal_def)
    with b show "b \<in> C"
      by (force simp: C_def intro: rev_image_eqI)
  qed
  have C_sub: "C \<subseteq> span (B \<union> U)"
  proof
    fix y assume "y \<in> C"
    then obtain u where u: "u \<in> (B \<union> U) - {0}" "y = u /\<^sub>R norm u"
      by (auto simp: C_def)
    then show "y \<in> span (B \<union> U)"
      by (metis DiffD1 span_base span_scale)
  qed
  have sub_C: "B \<union> U \<subseteq> span C"
  proof
    fix u assume u: "u \<in> B \<union> U"
    show "u \<in> span C"
    proof (cases "u = 0")
      case True
      then show ?thesis
        by (simp add: span_zero)
    next
      case False
      with u have "u /\<^sub>R norm u \<in> C"
        by (auto simp: C_def)
      then have "norm u *\<^sub>R (u /\<^sub>R norm u) \<in> span C"
        by (intro span_scale span_base)
      with False show ?thesis
        by simp
    qed
  qed
  have "span C = span (B \<union> U)"
    using C_sub sub_C by (simp add: span_eq)
  also have "\<dots> = span (B \<union> Basis)"
    by (fact U(2))
  also have "\<dots> = UNIV"
  proof -
    have "(UNIV :: (real^'n) set) = span Basis"
      by simp
    also have "\<dots> \<subseteq> span (B \<union> Basis)"
      by (intro span_mono) auto
    finally show ?thesis
      by auto
  qed
  finally have C_span: "span C = UNIV" .
  show thesis
    by (rule that[of C]) (use C_fin C_orth C_norm BC C_span in \<open>auto simp: onormal_def\<close>)
qed

section \<open>The trace lower bound (Courant--Fischer/Ky Fan argument)\<close>

lemma trace_ge_dim:
  fixes a :: "real^'n^'n"
  assumes psd: "\<And>x. 0 \<le> x \<bullet> (a *v x)"
    and S: "subspace S"
    and ray: "\<And>x. x \<in> S \<Longrightarrow> x \<bullet> x \<le> x \<bullet> (a *v x)"
  shows "real (dim S) \<le> trace a"
proof -
  obtain B where B: "B \<subseteq> S" "pairwise orthogonal B" "\<And>x. x \<in> B \<Longrightarrow> norm x = 1"
    "independent B" "card B = dim S" "span B = S"
    using orthonormal_basis_subspace[OF S] by metis
  have onB: "onormal B"
    using B by (auto simp: onormal_def intro: pairwise_orthogonal_imp_finite)
  obtain C where C: "onormal C" "B \<subseteq> C" "span C = UNIV"
    using onormal_extension[OF onB] by blast
  have "real (dim S) = (\<Sum>u\<in>B. u \<bullet> u)"
    using B(5) onB by (simp add: onormal_def)
  also have "\<dots> \<le> (\<Sum>u\<in>B. u \<bullet> (a *v u))"
    by (intro sum_mono ray) (use B(1) in auto)
  also have "\<dots> \<le> (\<Sum>u\<in>C. u \<bullet> (a *v u))"
    using C by (intro sum_mono2 psd) (auto simp: onormal_def)
  also have "\<dots> = trace a"
    by (simp add: trace_onormal_basis[OF C(1,3)])
  finally show ?thesis .
qed

section \<open>More orthonormal-family facts\<close>

lemma onormal_empty: "onormal {}"
  by (simp add: onormal_def pairwise_def)

lemma onormal_subset:
  assumes "onormal B" and "S \<subseteq> B"
  shows "onormal S"
  using assms unfolding onormal_def
  by (auto elim: pairwise_subset intro: finite_subset)

lemma onormal_finite:
  assumes "onormal B"
  shows "finite B"
  using assms by (simp add: onormal_def)

lemma onormal_independent:
  assumes "onormal B"
  shows "independent B"
  using assms
  by (intro pairwise_orthogonal_independent) (auto simp: onormal_def)

lemma onormal_card_dim_span:
  assumes "onormal B"
  shows "card B = dim (span B)"
  using onormal_independent[OF assms]
  by (simp add: dim_eq_card_independent)

text \<open>An orthonormal spanning family is a basis, so it has \<open>n\<close> elements.\<close>

lemma onormal_span_card:
  fixes B :: "(real^'n::finite) set"
  assumes B: "onormal B" and sp: "span B = UNIV"
  shows "card B = CARD('n)"
proof -
  have nz: "0 \<notin> B"
    using B by (auto simp: onormal_def)
  have ind: "independent B"
    using B nz by (intro pairwise_orthogonal_independent) (auto simp: onormal_def)
  have "card B = dim B"
    using ind by (simp add: dim_eq_card_independent)
  also have "dim B = dim (UNIV :: (real^'n) set)"
    using sp dim_span[of B] by simp
  also have "\<dots> = CARD('n)"
    by simp
  finally show ?thesis .
qed

lemma onormal_extension_within:
  assumes B: "onormal B" and W: "subspace W" and BW: "B \<subseteq> W"
  obtains C where "onormal C" "B \<subseteq> C" "C \<subseteq> W" "span C = W"
proof -
  have orthB: "pairwise orthogonal B"
    using B by (simp add: onormal_def)
  obtain D where D: "D \<subseteq> W" "pairwise orthogonal D"
    "\<And>x. x \<in> D \<Longrightarrow> norm x = 1" "independent D" "card D = dim W" "span D = W"
    using orthonormal_basis_subspace[OF W] by metis
  obtain U where U: "pairwise orthogonal (B \<union> U)"
    "span (B \<union> U) = span (B \<union> D)"
    using orthogonal_extension[OF orthB, where T = D] by blast
  have spanBU: "span (B \<union> U) = W"
  proof -
    have "span (B \<union> D) \<subseteq> W"
      using BW D(1) W by (intro span_minimal) auto
    moreover have "W \<subseteq> span (B \<union> D)"
      using D(6) by (metis Un_upper2 span_mono)
    ultimately show ?thesis
      using U(2) by auto
  qed
  have BUW: "B \<union> U \<subseteq> W"
    by (metis spanBU span_superset)
  define C where "C = (\<lambda>u. u /\<^sub>R norm u) ` ((B \<union> U) - {0})"
  have C_norm: "norm u = 1" if "u \<in> C" for u
    using that
    by (auto simp: C_def sgn_div_norm[symmetric] norm_sgn split: if_splits)
  have C_orth: "pairwise orthogonal C"
  proof (rule pairwiseI)
    fix x y assume "x \<in> C" "y \<in> C" "x \<noteq> y"
    then obtain u v where uv: "u \<in> (B \<union> U) - {0}" "v \<in> (B \<union> U) - {0}"
      "x = u /\<^sub>R norm u" "y = v /\<^sub>R norm v"
      by (auto simp: C_def)
    with \<open>x \<noteq> y\<close> have "u \<noteq> v" by auto
    with U(1) uv have "orthogonal u v"
      by (auto simp: pairwise_def)
    then show "orthogonal x y"
      by (simp add: uv orthogonal_def)
  qed
  have C_fin: "finite C"
    using C_orth by (rule pairwise_orthogonal_imp_finite)
  have BC: "B \<subseteq> C"
  proof
    fix b assume b: "b \<in> B"
    with B have "norm b = 1"
      by (simp add: onormal_def)
    with b show "b \<in> C"
      by (force simp: C_def intro: rev_image_eqI)
  qed
  have CW: "C \<subseteq> W"
  proof
    fix y assume "y \<in> C"
    then obtain u where u: "u \<in> (B \<union> U) - {0}" "y = u /\<^sub>R norm u"
      by (auto simp: C_def)
    then have "u \<in> W"
      using BUW by auto
    then show "y \<in> W"
      using u(2) W by (simp add: subspace_scale)
  qed
  have C_sub: "C \<subseteq> span (B \<union> U)"
  proof
    fix y assume "y \<in> C"
    then obtain u where u: "u \<in> (B \<union> U) - {0}" "y = u /\<^sub>R norm u"
      by (auto simp: C_def)
    then show "y \<in> span (B \<union> U)"
      by (metis DiffD1 span_base span_scale)
  qed
  have sub_C: "B \<union> U \<subseteq> span C"
  proof
    fix u assume u: "u \<in> B \<union> U"
    show "u \<in> span C"
    proof (cases "u = 0")
      case True
      then show ?thesis
        by (simp add: span_zero)
    next
      case False
      with u have "u /\<^sub>R norm u \<in> C"
        by (auto simp: C_def)
      then have "norm u *\<^sub>R (u /\<^sub>R norm u) \<in> span C"
        by (intro span_scale span_base)
      with False show ?thesis
        by simp
    qed
  qed
  have "span C = span (B \<union> U)"
    using C_sub sub_C by (simp add: span_eq)
  then have C_span: "span C = W"
    by (simp add: spanBU)
  show thesis
    by (rule that[of C])
      (use C_fin C_orth C_norm BC CW C_span in \<open>auto simp: onormal_def\<close>)
qed

lemma onormal_outer_sum_eq:
  assumes B1: "onormal B1" and B2: "onormal B2" and sp: "span B1 = span B2"
  shows "(\<Sum>u\<in>B1. outer_prod u u) = (\<Sum>u\<in>B2. outer_prod u u)"
proof -
  have act: "(\<Sum>u\<in>B. outer_prod u u) *v x = y"
    if B: "onormal B" "span B = span B1"
      and yz: "y \<in> span B1" "\<And>w. w \<in> span B1 \<Longrightarrow> orthogonal z w" "x = y + z"
    for B x y z
  proof -
    have "(\<Sum>u\<in>B. outer_prod u u) *v x = (\<Sum>u\<in>B. (u \<bullet> x) *\<^sub>R u)"
      by (simp add: matrix_vector_mult_sum)
    also have "\<dots> = (\<Sum>u\<in>B. (u \<bullet> y) *\<^sub>R u)"
    proof (intro sum.cong refl)
      fix u assume u: "u \<in> B"
      then have "u \<in> span B1"
        using B(2) span_base by fastforce
      then have "orthogonal z u"
        by (rule yz(2))
      then have "u \<bullet> z = 0"
        by (simp add: orthogonal_def inner_commute)
      then show "(u \<bullet> x) *\<^sub>R u = (u \<bullet> y) *\<^sub>R u"
        by (simp add: yz(3) inner_add_right)
    qed
    also have "\<dots> = y"
      using B yz(1) by (intro onormal_expand) auto
    finally show ?thesis .
  qed
  have "(\<Sum>u\<in>B1. outer_prod u u) *v x = (\<Sum>u\<in>B2. outer_prod u u) *v x" for x
  proof -
    obtain y z where yz: "y \<in> span B1"
      "\<And>w. w \<in> span B1 \<Longrightarrow> orthogonal z w" "x = y + z"
      using orthogonal_subspace_decomp_exists[of B1 x] by metis
    show ?thesis
      using act[OF B1 refl yz] act[OF B2 sp[symmetric] yz] by simp
  qed
  then show ?thesis
    by (auto simp: matrix_eq)
qed

lemma trace_on_subspace_eq:
  assumes "onormal B1" "onormal B2" "span B1 = span B2"
  shows "(\<Sum>u\<in>B1. u \<bullet> (a *v u)) = (\<Sum>u\<in>B2. u \<bullet> (a *v u))"
proof -
  have "(\<Sum>u\<in>B1. u \<bullet> (a *v u)) = trace (a ** (\<Sum>u\<in>B1. outer_prod u u))"
    by (simp add: trace_mult_outer_sum)
  also have "\<dots> = trace (a ** (\<Sum>u\<in>B2. outer_prod u u))"
    by (simp add: onormal_outer_sum_eq[OF assms])
  also have "\<dots> = (\<Sum>u\<in>B2. u \<bullet> (a *v u))"
    by (simp add: trace_mult_outer_sum)
  finally show ?thesis .
qed

(*<*)
end
(*>*)
