
(*<*)
theory Outer_Products
  imports Matrix_Algebra
begin

(*>*)

text \<open>
  The outer product \<open>u v\<^sup>T\<close> of two vectors, as a rank-one matrix: the basic
  algebra of forming it, applying it, and summing it against an orthonormal
  family.
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

lemma outer_prod_mult: "outer_prod u v ** outer_prod w z = (v \<bullet> w) *\<^sub>R outer_prod u z"
  by (simp add: mult_outer_prod outer_prod_scaleR_left)

lemma trace_mult_outer_sum:
  "trace (A ** (\<Sum>u\<in>B. outer_prod u u)) = (\<Sum>u\<in>B. u \<bullet> (A *v u))"
  by (simp add: matrix_mult_sum_right trace_matrix_sum mult_outer_prod
      inner_commute)


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

text \<open>The Hessian field of the quartic \<open>C|z-x|\<^sup>4\<close>, which is what
  \<open>test_fun_at\<close> never had to record.\<close>

(*<*)
end
(*>*)
