
(*<*)
theory Outer_Products
  imports Matrix_Algebra
begin

(*>*)

text \<open>
  The outer product \<open>u v\<^sup>T\<close> of two vectors, as a rank-one matrix: the basic
  algebra of forming it, applying it, and summing it against an orthonormal
  family, and its Frobenius norm.  Last, the outer square \<open>x x\<^sup>T\<close> as a
  constant of its own, with its algebra, traces and norm.
\<close>

unbundle inner_syntax

section \<open>Outer products\<close>

definition outer_prod :: "real^'n \<Rightarrow> real^'n \<Rightarrow> real^'n^'n" where
  "outer_prod u v = (\<chi> i j. u $ i * v $ j)"

lemma outer_prod_mv [simp]: "outer_prod u v *v x = (v \<bullet> x) *\<^sub>R u"
  unfolding outer_prod_def matrix_vector_mult_def inner_vec_def
  by (simp add: vec_eq_iff sum_distrib_left ac_simps)

lemma transpose_outer_prod [simp]: "transpose (outer_prod u v) = outer_prod v u"
  by (simp add: outer_prod_def transpose_def vec_eq_iff)

lemma trace_outer_prod [simp]: "trace (outer_prod u v) = u \<bullet> v"
  by (simp add: outer_prod_def trace_def inner_vec_def)

lemma mult_outer_prod: "A ** outer_prod u v = outer_prod (A *v u) v"
  unfolding outer_prod_def matrix_matrix_mult_def matrix_vector_mult_def
  by (simp add: vec_eq_iff sum_distrib_left sum_distrib_right ac_simps)

lemma outer_prod_scaleR_left: "outer_prod (c *\<^sub>R u) v = c *\<^sub>R outer_prod u v"
  by (simp add: outer_prod_def vec_eq_iff)

lemma outer_prod_scaleR_right:
  fixes u v :: "real^'n::finite"
  shows "outer_prod u (c *\<^sub>R v) = c *\<^sub>R outer_prod u v"
proof -
  have "outer_prod u (c *\<^sub>R v) = transpose (outer_prod (c *\<^sub>R v) u)"
    by simp
  also have "\<dots> = transpose (c *\<^sub>R outer_prod v u)"
    by (simp add: outer_prod_scaleR_left)
  also have "\<dots> = c *\<^sub>R outer_prod u v"
    by (simp add: transpose_scalar)
  finally show ?thesis .
qed

lemma outer_prod_diff_left:
  fixes u v w :: "real^'n::finite"
  shows "outer_prod (u - v) w = outer_prod u w - outer_prod v w"
  unfolding outer_prod_def by (simp add: vec_eq_iff left_diff_distrib)

lemma outer_prod_diff_right:
  fixes u v w :: "real^'n::finite"
  shows "outer_prod u (v - w) = outer_prod u v - outer_prod u w"
  unfolding outer_prod_def by (simp add: vec_eq_iff right_diff_distrib)

lemma outer_prod_mult: "outer_prod u v ** outer_prod w z = (v \<bullet> w) *\<^sub>R outer_prod u z"
  by (simp add: mult_outer_prod outer_prod_scaleR_left)

lemma trace_mult_outer_sum:
  "trace (A ** (\<Sum>u\<in>B. outer_prod u u)) = (\<Sum>u\<in>B. u \<bullet> (A *v u))"
  by (simp add: matrix_mult_sum_right trace_matrix_sum mult_outer_prod
      inner_commute)

lemma traceM_sum_outer:
  fixes S :: "(real^'n::finite) set" and c :: "real^'n \<Rightarrow> real"
    and M :: "real^'n^'n"
  shows "trace (M ** (\<Sum>u\<in>S. c u *\<^sub>R outer_prod u u))
      = (\<Sum>u\<in>S. c u * (u \<bullet> (M *v u)))"
  by (simp add: matrix_mult_sum_right trace_matrix_sum trace_mult_scaleR mult_outer_prod
      inner_commute)

lemma matvec_sum_outer:
  fixes S :: "(real^'n::finite) set" and c :: "real^'n \<Rightarrow> real"
  assumes finS: "finite S"
  shows "(\<Sum>u\<in>S. c u *\<^sub>R outer_prod u u) *v z = (\<Sum>u\<in>S. (c u * (u \<bullet> z)) *\<^sub>R u)"
  by (simp add: matrix_vector_mult_sum scaleR_matrix_vector_assoc[symmetric])

text \<open>A weighted sum of outer squares annihilates every vector orthogonal to
  each member that carries a nonzero weight.\<close>

lemma weighted_outer_sum_annihilates:
  fixes c :: "real^'n::finite \<Rightarrow> real"
  assumes finB: "finite B"
    and van: "\<And>u. u \<in> B \<Longrightarrow> c u = 0 \<or> p \<bullet> u = 0"
  shows "(\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u) *v p = 0"
proof -
  have "(\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u) *v p = (\<Sum>u\<in>B. c u *\<^sub>R ((u \<bullet> p) *\<^sub>R u))"
    by (simp add: matrix_vector_mult_sum scaleR_matrix_vector_assoc[symmetric])
  also have "\<dots> = (\<Sum>u\<in>B. 0)"
  proof (intro sum.cong refl)
    fix u assume u: "u \<in> B"
    show "c u *\<^sub>R ((u \<bullet> p) *\<^sub>R u) = 0"
      using van[OF u] by (auto simp: inner_commute)
  qed
  also have "\<dots> = 0"
    by simp
  finally show ?thesis .
qed


subsection \<open>The projector \<open>u u\<^sup>T\<close> as an operator\<close>

lemma op_matvec: "outer_prod u u *v h = (u \<bullet> h) *\<^sub>R (u :: real^'n::finite)"
  by (simp add: outer_prod_def matrix_vector_mult_def vec_eq_iff inner_vec_def
      sum_distrib_left mult.assoc mult.commute mult.left_commute)

lemma op_transpose: "transpose (outer_prod u u) = outer_prod (u :: real^'n::finite) u"
  by (simp add: outer_prod_def transpose_def vec_eq_iff mult.commute)

lemma op_continuous:
  "continuous_on UNIV (\<lambda>y :: real^'n::finite. outer_prod (y - x) (y - x))"
  unfolding outer_prod_def
  by (intro continuous_on_vec_lambda continuous_intros)

subsection \<open>Norms of outer products\<close>

text \<open>In the Frobenius norm, which is the norm of \<open>real^'n^'n\<close>, the outer
  product is multiplicative: \<open>\<parallel>u v\<^sup>T\<parallel> = \<parallel>u\<parallel> \<parallel>v\<parallel>\<close>.  Two bounds that
  estimates on rank-one projections need come along: normalisation is
  Lipschitz away from the origin, and the identity matrix has norm \<open>\<surd>n\<close>.\<close>

lemma inner_outer_prod_self:
  fixes u v :: "real^'n::finite"
  shows "outer_prod u v \<bullet> outer_prod u v = (u \<bullet> u) * (v \<bullet> v)"
proof -
  have "outer_prod u v \<bullet> outer_prod u v
      = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. (u $ i * v $ j) * (u $ i * v $ j))"
    unfolding outer_prod_def inner_vec_def by simp
  also have "\<dots> = (\<Sum>i\<in>(UNIV :: 'n set).
      (u $ i * u $ i) * (\<Sum>j\<in>(UNIV :: 'n set). v $ j * v $ j))"
    by (intro sum.cong refl) (simp add: sum_distrib_left algebra_simps)
  also have "\<dots> = (\<Sum>i\<in>(UNIV :: 'n set). u $ i * u $ i)
      * (\<Sum>j\<in>(UNIV :: 'n set). v $ j * v $ j)"
    by (simp add: sum_distrib_right)
  also have "\<dots> = (u \<bullet> u) * (v \<bullet> v)"
    unfolding inner_vec_def by simp
  finally show ?thesis .
qed


lemma norm_outer_prod:
  fixes u v :: "real^'n::finite"
  shows "norm (outer_prod u v) = norm u * norm v"
proof -
  have "norm (outer_prod u v) = sqrt (outer_prod u v \<bullet> outer_prod u v)"
    by (simp add: norm_eq_sqrt_inner)
  also have "\<dots> = sqrt ((u \<bullet> u) * (v \<bullet> v))"
    by (simp add: inner_outer_prod_self)
  also have "\<dots> = sqrt (u \<bullet> u) * sqrt (v \<bullet> v)"
    by (simp add: real_sqrt_mult)
  also have "\<dots> = norm u * norm v"
    by (simp add: norm_eq_sqrt_inner)
  finally show ?thesis .
qed

lemma norm_unit_diff_le:
  fixes p p' :: "real^'n::finite"
  assumes p: "p \<noteq> 0" and p': "p' \<noteq> 0"
  shows "norm (p' /\<^sub>R norm p' - p /\<^sub>R norm p) \<le> 2 * norm (p' - p) / norm p"
proof -
  have np: "0 < norm p"
    using p by simp
  have np': "0 < norm p'"
    using p' by simp
  have split: "p' /\<^sub>R norm p' - p /\<^sub>R norm p
      = (p' - p) /\<^sub>R norm p + (inverse (norm p') - inverse (norm p)) *\<^sub>R p'"
    by (simp add:
        algebra_simps)
  have t1: "norm ((p' - p) /\<^sub>R norm p) = norm (p' - p) / norm p"
    using np by (simp add: divide_inverse mult.commute)
  have t2: "norm ((inverse (norm p') - inverse (norm p)) *\<^sub>R p')
      \<le> norm (p' - p) / norm p"
  proof -
    have "\<bar>inverse (norm p') - inverse (norm p)\<bar>
        = \<bar>norm p - norm p'\<bar> / (norm p' * norm p)"
      using np np' by (simp add: field_simps abs_mult_pos abs_minus_commute)
    then have "norm ((inverse (norm p') - inverse (norm p)) *\<^sub>R p')
        = \<bar>norm p - norm p'\<bar> / (norm p' * norm p) * norm p'"
      by simp
    also have "\<dots> = \<bar>norm p - norm p'\<bar> / norm p"
      using np' by simp
    also have "\<dots> \<le> norm (p' - p) / norm p"
      using np norm_triangle_ineq3[of p p'] 
      by (simp add: divide_right_mono abs_minus_commute norm_minus_commute)
    finally show ?thesis .
  qed
  have "norm (p' /\<^sub>R norm p' - p /\<^sub>R norm p)
      \<le> norm ((p' - p) /\<^sub>R norm p)
        + norm ((inverse (norm p') - inverse (norm p)) *\<^sub>R p')"
    unfolding split by (rule norm_triangle_ineq)
  also have "\<dots> \<le> norm (p' - p) / norm p + norm (p' - p) / norm p"
    using t1 t2 by simp
  also have "\<dots> = 2 * norm (p' - p) / norm p"
    by simp
  finally show ?thesis .
qed

lemma norm_mat_1:
  shows "norm (mat 1 :: real^'n::finite^'n) = sqrt (real CARD('n))"
proof -
  have "(mat 1 :: real^'n^'n) \<bullet> (mat 1 :: real^'n^'n)
      = (\<Sum>i\<in>(UNIV :: 'n set). \<Sum>j\<in>(UNIV :: 'n set).
          (if i = j then 1 else 0) * (if i = j then (1 :: real) else 0))"
    unfolding inner_vec_def mat_def by simp
  also have "\<dots> = (\<Sum>i\<in>(UNIV :: 'n set). (1 :: real))"
  proof (intro sum.cong refl)
    fix i :: 'n
    have "(\<Sum>j\<in>(UNIV :: 'n set).
            (if i = j then 1 else 0) * (if i = j then (1 :: real) else 0))
        = (\<Sum>j\<in>(UNIV :: 'n set). (if i = j then (1 :: real) else 0))"
      by (intro sum.cong refl) simp
    also have "\<dots> = 1"
      by simp
    finally show "(\<Sum>j\<in>(UNIV :: 'n set).
        (if i = j then 1 else 0) * (if i = j then (1 :: real) else 0)) = 1" .
  qed
  also have "\<dots> = real CARD('n)"
    by simp
  finally have "(mat 1 :: real^'n^'n) \<bullet> (mat 1 :: real^'n^'n) = real CARD('n)" .
  then show ?thesis
    by (simp add: norm_eq_sqrt_inner)
qed

section \<open>The outer square \<open>outerp\<close>\<close>

definition outerp :: "real^'n::finite \<Rightarrow> real^'n^'n" where
  "outerp x = (\<chi> i j. x $ i * x $ j)"

text \<open>\<open>outerp x\<close> is the outer square \<open>x x\<^sup>T\<close>: the \<open>outer_prod\<close> of this
  theory at equal arguments (\<open>outerp_eq_outer_prod\<close> below).  This theory's
  \<open>outer_prod\<close> shadows an identical constant of HOL-Analysis
  (\<open>Higher_Differentiability_Multi\<close>).  \<open>outerp\<close> stays a definition of its own
  because making it an abbreviation unfolds it in every simp set that
  mentions it, and proofs that rely on it as a unit then diverge.\<close>

lemma outerp_eq_outer_prod:
  fixes v :: "real^'n::finite"
  shows "outerp v = outer_prod v v"
  by (simp add: outerp_def outer_prod_def)

lemma outerp_scale_self:
  fixes u :: "real^'n::finite"
  shows "outerp (c *\<^sub>R u) = (c * c) *\<^sub>R outer_prod u u"
  by (simp add: vec_eq_iff outerp_def outer_prod_def)

lemma outerp_zero: "outerp (0 :: real^'n::finite) = 0"
  by (simp add: outerp_def vec_eq_iff)

lemma outerp_add:
  fixes a b :: "real^'n::finite"
  shows "outerp (a + b) = outerp a + outerp b
      + ((\<chi> i j. a $ i * b $ j) + (\<chi> i j. b $ i * a $ j))"
  by (simp add: outerp_def vec_eq_iff algebra_simps)

lemma outerp_diff:
  fixes a b :: "real^'n::finite"
  shows "outerp (a - b) = outerp a - ((\<chi> i j. a $ i * b $ j)
      + (\<chi> i j. b $ i * a $ j)) + outerp b"
  by (simp add: outerp_def vec_eq_iff algebra_simps)

lemma outerp_matvec_image:
  fixes S :: "real^'n::finite^'n" and w :: "real^'n"
  shows "outerp (S *v w) = S ** outerp w ** transpose S"
proof -
  have "outerp (S *v w) $ i $ j
      = (\<Sum>l\<in>UNIV. (\<Sum>k\<in>UNIV. S $ i $ k * (w $ k * w $ l)) * S $ j $ l)"
    for i j
  proof -
    have "outerp (S *v w) $ i $ j
        = (\<Sum>k\<in>UNIV. S $ i $ k * w $ k) * (\<Sum>l\<in>UNIV. S $ j $ l * w $ l)"
      by (simp add: outerp_def matrix_vector_mult_def)
    also have "\<dots> = (\<Sum>l\<in>UNIV. (\<Sum>k\<in>UNIV. S $ i $ k * w $ k)
        * (S $ j $ l * w $ l))"
      by (rule sum_distrib_left)
    also have "\<dots> = (\<Sum>l\<in>UNIV. (\<Sum>k\<in>UNIV. S $ i $ k * (w $ k * w $ l))
        * S $ j $ l)"
    proof (rule sum.cong[OF refl])
      fix l :: 'n
      have "(\<Sum>k\<in>UNIV. S $ i $ k * w $ k) * (S $ j $ l * w $ l)
          = (\<Sum>k\<in>UNIV. S $ i $ k * w $ k * (S $ j $ l * w $ l))"
        by (rule sum_distrib_right)
      also have "\<dots> = (\<Sum>k\<in>UNIV. S $ i $ k * (w $ k * w $ l) * S $ j $ l)"
        by (rule sum.cong[OF refl]) (simp only: mult_ac)
      also have "\<dots> = (\<Sum>k\<in>UNIV. S $ i $ k * (w $ k * w $ l)) * S $ j $ l"
        by (rule sum_distrib_right[symmetric])
      finally show "(\<Sum>k\<in>UNIV. S $ i $ k * w $ k) * (S $ j $ l * w $ l)
          = (\<Sum>k\<in>UNIV. S $ i $ k * (w $ k * w $ l)) * S $ j $ l" .
    qed
    finally show ?thesis .
  qed
  moreover have "(S ** outerp w ** transpose S) $ i $ j
      = (\<Sum>l\<in>UNIV. (\<Sum>k\<in>UNIV. S $ i $ k * (w $ k * w $ l)) * S $ j $ l)"
    for i j
    by (simp add: matrix_matrix_mult_def transpose_def outerp_def)
  ultimately show ?thesis by (simp add: vec_eq_iff)
qed

lemma cols_mult_transpose:
  fixes w :: "'m::finite \<Rightarrow> real^'n::finite"
  shows "(\<chi> i j. w j $ i) ** transpose (\<chi> i j. w j $ i)
       = (\<Sum>j\<in>UNIV. outerp (w j))"
proof -
  have "((\<chi> i j. w j $ i) ** transpose (\<chi> i j. w j $ i)) $ i $ l
      = (\<Sum>j\<in>UNIV. w j $ i * w j $ l)" for i l
    by (simp add: matrix_matrix_mult_def transpose_def)
  moreover have "(\<Sum>j\<in>UNIV. outerp (w j)) $ i $ l
      = (\<Sum>j\<in>UNIV. w j $ i * w j $ l)" for i l
    by (induction "UNIV :: 'm set" rule: infinite_finite_induct)
      (simp_all add: outerp_def)
  ultimately show ?thesis by (simp add: vec_eq_iff)
qed

lemma trace_outerp:
  fixes v :: "real^'n::finite"
  shows "trace (outerp v) = v \<bullet> v"
  by (simp add: outerp_eq_outer_prod)

lemma trace_mult_outerp:
  fixes M :: "real^'n::finite^'n" and v :: "real^'n"
  shows "trace (M ** outerp v) = v \<bullet> (M *v v)"
  by (simp add: outerp_eq_outer_prod mult_outer_prod inner_commute)

lemma trace_outerp_mult:
  fixes B :: "real^'n::finite^'n" and v :: "real^'n"
  shows "trace (outerp v ** B) = v \<bullet> (B *v v)"
  by (subst trace_mul_sym) (rule trace_mult_outerp)

lemma trace_mult_outerp_sum:
  fixes M :: "real^'n::finite^'n" and w :: "'b \<Rightarrow> real^'n" and F :: "'b set"
  assumes finF: "finite F"
  shows "trace (M ** (\<Sum>u\<in>F. outerp (w u))) = (\<Sum>u\<in>F. w u \<bullet> (M *v w u))"
  by (simp add: matrix_mult_sum_right trace_matrix_sum trace_mult_outerp)

lemma quadform_outerp:
  fixes q z :: "real^'n::finite"
  shows "z \<bullet> (outerp q *v z) = (q \<bullet> z)\<^sup>2"
  by (simp add: outerp_eq_outer_prod power2_eq_square inner_commute)

lemma norm_outerp: "norm (outerp (v :: real^'n::finite)) = norm v * norm v"
  by (simp add: outerp_eq_outer_prod norm_outer_prod)

(*<*)
end
(*>*)
