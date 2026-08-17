
(*<*)
theory Matrix_Algebra
  imports "HOL-Analysis.Analysis"
begin

(*>*)

text \<open>
  The elementary calculus of \<open>trace\<close>, \<open>transpose\<close>, \<open>**\<close> and \<open>*v\<close> that
  HOL-Analysis leaves to be reproved at every use site: distributivity over
  sums and differences, \<open>scaleR\<close>, and their interaction.
\<close>

section \<open>Sums of matrices\<close>

lemma trace_matrix_sum: "trace (\<Sum>x\<in>S. f x) = (\<Sum>x\<in>S. trace (f x))"
proof -
  have "trace (\<Sum>x\<in>S. f x) = (\<Sum>i\<in>UNIV. \<Sum>x\<in>S. f x $ i $ i)"
    by (simp add: trace_def)
  also have "\<dots> = (\<Sum>x\<in>S. \<Sum>i\<in>UNIV. f x $ i $ i)"
    by (rule sum.swap)
  finally show ?thesis
    by (simp add: trace_def)
qed

lemma transpose_matrix_sum: "transpose (\<Sum>x\<in>S. f x) = (\<Sum>x\<in>S. transpose (f x))"
  by (simp add: transpose_def vec_eq_iff)

lemma matrix_vector_mult_sum: "(\<Sum>x\<in>S. f x) *v y = (\<Sum>x\<in>S. f x *v y)"
proof -
  have "((\<Sum>x\<in>S. f x) *v y) $ i = (\<Sum>x\<in>S. f x *v y) $ i" for i
  proof -
    have "((\<Sum>x\<in>S. f x) *v y) $ i = (\<Sum>j\<in>UNIV. \<Sum>x\<in>S. f x $ i $ j * y $ j)"
      by (simp add: matrix_vector_mult_def sum_distrib_right)
    also have "\<dots> = (\<Sum>x\<in>S. \<Sum>j\<in>UNIV. f x $ i $ j * y $ j)"
      by (rule sum.swap)
    finally show ?thesis
      by (simp add: matrix_vector_mult_def)
  qed
  then show ?thesis
    by (simp add: vec_eq_iff)
qed

lemma matrix_mult_sum_right: "A ** (\<Sum>x\<in>S. f x) = (\<Sum>x\<in>S. A ** f x)"
proof -
  have "(A ** (\<Sum>x\<in>S. f x)) $ i $ j = (\<Sum>x\<in>S. A ** f x) $ i $ j" for i j
  proof -
    have "(A ** (\<Sum>x\<in>S. f x)) $ i $ j = (\<Sum>k\<in>UNIV. \<Sum>x\<in>S. A $ i $ k * f x $ k $ j)"
      by (simp add: matrix_matrix_mult_def sum_distrib_left)
    also have "\<dots> = (\<Sum>x\<in>S. \<Sum>k\<in>UNIV. A $ i $ k * f x $ k $ j)"
      by (rule sum.swap)
    finally show ?thesis
      by (simp add: matrix_matrix_mult_def)
  qed
  then show ?thesis
    by (simp add: vec_eq_iff)
qed

lemma scaleR_matrix_mult:
  fixes A :: "real^'m^'n" and B :: "real^'p^'m"
  shows "(r *\<^sub>R A) ** B = r *\<^sub>R (A ** B)"
  by (simp add: matrix_matrix_mult_def vec_eq_iff sum_distrib_left ac_simps)

lemma trace_scaleR: "trace (r *\<^sub>R A) = r * trace A"
  by (simp add: trace_def sum_distrib_left)

lemma scaleR_matrix_vector:
  fixes A :: "real^'m^'n"
  shows "(r *\<^sub>R A) *v x = r *\<^sub>R (A *v x)"
  by (simp add: matrix_vector_mult_def vec_eq_iff sum_distrib_left ac_simps)

lemma neg_matrix_vector:
  fixes A :: "real^'m^'n"
  shows "(- A) *v x = - (A *v x)"
  by (simp add: matrix_vector_mult_def vec_eq_iff sum_negf)

lemma matrix_mul_diff_right:
  fixes A B C :: "real^'n::finite^'n"
  shows "A ** (B - C) = A ** B - A ** C"
  by (simp add: matrix_matrix_mult_def vec_eq_iff algebra_simps sum_subtractf)

lemma matrix_mul_diff_left:
  fixes A B C :: "real^'n::finite^'n"
  shows "(A - B) ** C = A ** C - B ** C"
  by (simp add: matrix_matrix_mult_def vec_eq_iff algebra_simps sum_subtractf)

lemma matvec_add_right:
  fixes A :: "real^'n::finite^'n"
  shows "A *v (x + y) = A *v x + A *v y"
  by (simp add: matrix_vector_mult_def vec_eq_iff algebra_simps sum.distrib)

lemma matrix_vector_mult_diff:
  fixes A B :: "real^'n::finite^'n"
  shows "(A - B) *v x = A *v x - B *v x"
proof -
  have "((A - B) *v x) $ i = (A *v x) $ i - (B *v x) $ i" for i
  proof -
    have "((A - B) *v x) $ i = (\<Sum>j\<in>UNIV. (A $ i $ j - B $ i $ j) * x $ j)"
      by (simp add: matrix_vector_mult_def)
    also have "\<dots> = (\<Sum>j\<in>UNIV. A $ i $ j * x $ j - B $ i $ j * x $ j)"
      by (intro sum.cong refl) (simp add: left_diff_distrib)
    also have "\<dots> = (\<Sum>j\<in>UNIV. A $ i $ j * x $ j) - (\<Sum>j\<in>UNIV. B $ i $ j * x $ j)"
      by (rule sum_subtractf)
    also have "\<dots> = (A *v x) $ i - (B *v x) $ i"
      by (simp add: matrix_vector_mult_def)
    finally show ?thesis .
  qed
  then show ?thesis
    by (simp add: vec_eq_iff)
qed

lemma transpose_diff_matrix: "transpose (A - B) = transpose A - transpose B"
  by (simp add: transpose_def vec_eq_iff)

lemma matrix_add_rdistrib: "(A + B) ** C = A ** C + B ** C"
  by (simp add: matrix_matrix_mult_def vec_eq_iff sum.distrib
      algebra_simps)

lemma matrix_vector_mult_vsum: "A *v (\<Sum>x\<in>S. f x) = (\<Sum>x\<in>S. A *v f x)"
proof -
  have "(A *v (\<Sum>x\<in>S. f x)) $ i = (\<Sum>x\<in>S. A *v f x) $ i" for i
  proof -
    have "(A *v (\<Sum>x\<in>S. f x)) $ i = (\<Sum>j\<in>UNIV. \<Sum>x\<in>S. A $ i $ j * f x $ j)"
      by (simp add: matrix_vector_mult_def sum_distrib_left)
    also have "\<dots> = (\<Sum>x\<in>S. \<Sum>j\<in>UNIV. A $ i $ j * f x $ j)"
      by (rule sum.swap)
    finally show ?thesis
      by (simp add: matrix_vector_mult_def)
  qed
  then show ?thesis
    by (simp add: vec_eq_iff)
qed

lemma matrix_mult_sum_left: "(\<Sum>x\<in>S. f x) ** A = (\<Sum>x\<in>S. f x ** A)"
proof -
  have "((\<Sum>x\<in>S. f x) ** A) $ i $ j = (\<Sum>x\<in>S. f x ** A) $ i $ j" for i j
  proof -
    have "((\<Sum>x\<in>S. f x) ** A) $ i $ j = (\<Sum>k\<in>UNIV. \<Sum>x\<in>S. f x $ i $ k * A $ k $ j)"
      by (simp add: matrix_matrix_mult_def sum_distrib_right)
    also have "\<dots> = (\<Sum>x\<in>S. \<Sum>k\<in>UNIV. f x $ i $ k * A $ k $ j)"
      by (rule sum.swap)
    finally show ?thesis
      by (simp add: matrix_matrix_mult_def)
  qed
  then show ?thesis
    by (simp add: vec_eq_iff)
qed

lemma transpose_scaleR: "transpose (c *\<^sub>R A) = c *\<^sub>R transpose A"
  by (simp add: transpose_def vec_eq_iff)

lemma transpose_add: "transpose (A + B) = transpose A + transpose B"
  by (simp add: transpose_def vec_eq_iff)

section \<open>Continuity of matrix-valued maps\<close>

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

section \<open>Sums, transpose, matrix-vector multiplication\<close>

lemma inner_transpose_matrix:
  fixes A :: "real^'m^'n" and x :: "real^'n" and y :: "real^'m"
  shows "x \<bullet> (A *v y) = (transpose A *v x) \<bullet> y"
proof -
  have "x \<bullet> (A *v y) = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. x $ i * (A $ i $ j * y $ j))"
    by (simp add: inner_vec_def matrix_vector_mult_def sum_distrib_left)
  also have "\<dots> = (\<Sum>j\<in>UNIV. \<Sum>i\<in>UNIV. x $ i * (A $ i $ j * y $ j))"
    by (rule sum.swap)
  also have "\<dots> = (transpose A *v x) \<bullet> y"
    by (simp add: inner_vec_def matrix_vector_mult_def transpose_def
        sum_distrib_left sum_distrib_right ac_simps)
  finally show ?thesis .
qed

(*<*)
end
(*>*)
