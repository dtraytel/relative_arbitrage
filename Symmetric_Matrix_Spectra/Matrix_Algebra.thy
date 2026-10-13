
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

lemma trace_scaleR: "trace (r *\<^sub>R A) = r * trace A"
  by (simp add: trace_def sum_distrib_left)

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

lemma transpose_diff_matrix: "transpose (A - B) = transpose A - transpose B"
  by (simp add: transpose_def vec_eq_iff)

lemma matrix_add_rdistrib: "(A + B) ** C = A ** C + B ** C"
  by (simp add: matrix_matrix_mult_def vec_eq_iff sum.distrib
      algebra_simps)

lemma matrix_vector_mult_vsum: "A *v (\<Sum>x\<in>S. f x) = (\<Sum>x\<in>S. A *v f x)"
  by (induct S rule: infinite_finite_induct) (simp_all add: matrix_vector_right_distrib)

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

section \<open>Sums, transpose, matrix-vector multiplication\<close>

lemma inner_transpose_matrix:
  fixes A :: "real^'m^'n" and x :: "real^'n" and y :: "real^'m"
  shows "x \<bullet> (A *v y) = (transpose A *v x) \<bullet> y"
  by (simp add: dot_lmul_matrix)

lemma sym_inner_swap:
  fixes a :: "real^'n^'n"
  assumes "transpose a = a"
  shows "x \<bullet> (a *v y) = y \<bullet> (a *v x)"
  by (metis assms inner_transpose_matrix inner_commute)

subsection \<open>Shifts by a multiple of the identity, and bounds from a basis\<close>

text \<open>These arrived with the doubling toolbox, which needs the quadratic
  form of a matrix shifted by \<open>\<delta> I\<close>, the entrywise reading of a linear
  map through \<open>axis\<close>, and the crude operator bound that follows from a
  uniform bound on the coordinates.\<close>

lemma quad_form_shift_identity:
  fixes A :: "real^'n::finite^'n" and k :: "real^'n"
  shows "k \<bullet> ((A + \<delta> *\<^sub>R mat 1) *v k) = k \<bullet> (A *v k) + \<delta> * (norm k)\<^sup>2"
proof -
  have "(A + \<delta> *\<^sub>R mat 1) *v k = A *v k + \<delta> *\<^sub>R k"
    by (simp add: matrix_vector_mult_add_rdistrib
        scaleR_matrix_vector_assoc[symmetric])
  then have "k \<bullet> ((A + \<delta> *\<^sub>R mat 1) *v k) = k \<bullet> (A *v k) + k \<bullet> (\<delta> *\<^sub>R k)"
    by (simp add: inner_add_right)
  then show ?thesis
    by (simp add: dot_square_norm)
qed

lemma quad_form_shift_identity_neg:
  fixes A :: "real^'n::finite^'n" and k :: "real^'n"
  shows "k \<bullet> ((A - \<delta> *\<^sub>R mat 1) *v k) = k \<bullet> (A *v k) - \<delta> * (norm k)\<^sup>2"
proof -
  have "(A - \<delta> *\<^sub>R mat 1) *v k = A *v k - \<delta> *\<^sub>R k"
    by (simp add: matrix_vector_mult_diff_rdistrib
        scaleR_matrix_vector_assoc[symmetric])
  then have "k \<bullet> ((A - \<delta> *\<^sub>R mat 1) *v k) = k \<bullet> (A *v k) - k \<bullet> (\<delta> *\<^sub>R k)"
    by (simp add: inner_diff_right)
  then show ?thesis
    by (simp add: dot_square_norm)
qed

lemma norm_le_card_Basis_bound:
  fixes M :: "'a::euclidean_space"
  assumes b: "\<And>e. e \<in> Basis \<Longrightarrow> \<bar>M \<bullet> e\<bar> \<le> c"
  shows "norm M \<le> real (card (Basis :: 'a set)) * c"
  using order_trans[OF norm_le_l1 sum_mono[OF b]] by simp

lemma matrix_Basis_cases:
  fixes e :: "real^'n::finite^'n"
  assumes "e \<in> Basis"
  shows "\<exists>i j. e = axis i (axis j 1)"
proof -
  from assms obtain i u where eu: "e = axis i u"
    and uB: "u \<in> (Basis :: (real^'n) set)"
    unfolding Basis_vec_def by blast
  from uB obtain j v where uv: "u = axis j v"
    and vB: "v \<in> (Basis :: real set)"
    unfolding Basis_vec_def by blast
  from vB have "v = 1" by simp
  with eu uv show ?thesis by blast
qed

lemma inner_matrix_axis:
  fixes W :: "real^'n::finite \<Rightarrow> real^'n"
  assumes lin: "linear W"
  shows "matrix W \<bullet> axis i (axis j 1) = (axis i 1 :: real^'n) \<bullet> W (axis j 1)"
proof -
  have "matrix W \<bullet> axis i (axis j 1) = matrix W $ i $ j"
    by (simp add: inner_axis)
  also have "\<dots> = (W (axis j 1)) $ i"
    by (simp add: matrix_def)
  also have "\<dots> = (axis i 1 :: real^'n) \<bullet> W (axis j 1)"
    by (simp add: inner_axis')
  finally show ?thesis .
qed

subsection \<open>The calculus the doubling and comparison arguments consume\<close>

text \<open>Trace, transpose, matrix-vector and matrix-matrix identities, the
  bounded-linear and continuity facts that go with them, and the affine and
  quadratic-form bookkeeping around them.  All of it was written as steps of
  a viscosity-comparison proof and none of it is about one.\<close>

text \<open>Conjugation preserves each defining condition of the feasible set.
  Orthogonality is HOL-Analysis's own \<open>orthogonal_matrix\<close>.\<close>

lemma trace_conjugate:
  fixes M Q a :: "real^'n^'n"
  shows "trace (M ** (transpose Q ** a ** Q)) = trace ((Q ** M ** transpose Q) ** a)"
proof -
  have "trace (M ** (transpose Q ** a ** Q))
      = trace ((M ** transpose Q ** a) ** Q)"
    by (simp add: matrix_mul_assoc)
  also have "\<dots> = trace (Q ** (M ** transpose Q ** a))"
    using trace_mul_sym[of "M ** transpose Q ** a" Q] by simp
  also have "\<dots> = trace ((Q ** M ** transpose Q) ** a)"
    by (simp add: matrix_mul_assoc)
  finally show ?thesis .
qed

text \<open>Lemma 2.2 of \<^cite>\<open>LaiShkolnikovSoner\<close> of the paper assumes the set \<open>S\<close> of admissible covariances is
  bounded.  For the paper's \<open>S\<close> that is a purely linear-algebraic fact,
  provable without any probability: \<open>psd a\<close> bounds the diagonal below by
  \<open>0\<close> and \<open>eigen_ub a L\<close> bounds it above by \<open>L\<close>, testing the quadratic form
  at the coordinate vectors.\<close>

text \<open>The off-diagonal entries are bounded too.  Testing the psd quadratic form
  at \<open>axis i 1 \<plusminus> axis j 1\<close> gives \<open>a\<^sub>i\<^sub>i + a\<^sub>j\<^sub>j \<plusminus> 2 a\<^sub>i\<^sub>j \<ge> 0\<close>, i.e.
  \<open>2 \<bar>a\<^sub>i\<^sub>j\<bar> \<le> a\<^sub>i\<^sub>i + a\<^sub>j\<^sub>j \<le> 2 L\<close>.  (For \<open>i = j\<close> the same bound is the diagonal
  one.)\<close>

lemma quadform_axis_pair:
  fixes a :: "real^'n::finite^'n"
  assumes sym: "transpose a = a"
  shows "(axis i (1::real) + axis j 1) \<bullet> (a *v (axis i (1::real) + axis j 1))
       = a $ i $ i + a $ j $ j + 2 * a $ i $ j"
proof -
  have aji: "a $ j $ i = a $ i $ j"
    by (metis sym transpose_def vec_lambda_beta)
  have mv: "(a *v (axis i (1::real) + axis j 1))
      = (a *v axis i (1::real)) + (a *v axis j 1)"
    by (simp add: matrix_vector_right_distrib)
  have "(axis i (1::real) + axis j 1) \<bullet> (a *v (axis i (1::real) + axis j 1))
      = (a *v axis i (1::real)) $ i + (a *v axis j (1::real)) $ i
        + ((a *v axis i (1::real)) $ j + (a *v axis j (1::real)) $ j)"
    unfolding mv by (simp add: inner_add_left inner_axis')
  also have "\<dots> = a $ i $ i + a $ i $ j + (a $ j $ i + a $ j $ j)"
    by (simp add: matrix_vector_mult_basis column_def)
  also have "\<dots> = a $ i $ i + a $ j $ j + 2 * a $ i $ j"
    unfolding aji by simp
  finally show ?thesis .
qed

lemma quadform_axis_pair_minus:
  fixes a :: "real^'n::finite^'n"
  assumes sym: "transpose a = a"
  shows "(axis i (1::real) - axis j 1) \<bullet> (a *v (axis i (1::real) - axis j 1))
       = a $ i $ i + a $ j $ j - 2 * a $ i $ j"
proof -
  have aji: "a $ j $ i = a $ i $ j"
    by (metis sym transpose_def vec_lambda_beta)
  have mv: "(a *v (axis i (1::real) - axis j 1))
      = (a *v axis i (1::real)) - (a *v axis j 1)"
    by (rule matrix_vector_mult_diff_distrib)
  have "(axis i (1::real) - axis j 1) \<bullet> (a *v (axis i (1::real) - axis j 1))
      = (a *v axis i (1::real)) $ i - (a *v axis j (1::real)) $ i
        - ((a *v axis i (1::real)) $ j - (a *v axis j (1::real)) $ j)"
    unfolding mv by (simp add: inner_diff_left inner_axis')
  also have "\<dots> = a $ i $ i - a $ i $ j - (a $ j $ i - a $ j $ j)"
    by (simp add: matrix_vector_mult_basis column_def)
  also have "\<dots> = a $ i $ i + a $ j $ j - 2 * a $ i $ j"
    unfolding aji by simp
  finally show ?thesis .
qed

text \<open>\<open>p\<close> itself is an eigenvector of \<open>M\<^sub>p\<close>, with eigenvalue
  \<open>min (\<lambda>\<^sub>(\<^sub>n\<^sub>)(M)) 0\<close>: the conjugation kills it and the correction term
  scales it.  This is the first half of the "sorts to the bottom of the
  spectrum" claim after Eq. (3.4) of \<^cite>\<open>LaiShkolnikovSoner\<close>; the second half is the Poincare bound
  \<open>\<lambda>\<^sub>(\<^sub>i\<^sub>)(M\<^sub>p) \<ge> \<lambda>\<^sub>(\<^sub>i\<^sub>+\<^sub>1\<^sub>)(M)\<close>, which is what still remains for Eq. (3.5).\<close>

text \<open>An orthogonal \<open>R\<close> carries the feasible set of \<open>p\<close> onto that of \<open>Rp\<close>:
  each clause is the change of variables \<open>x \<mapsto> R\<^sup>T x\<close>, using that \<open>R\<close> is
  an isometry with \<open>R\<^sup>T R = 1\<close>, and moving the witnessing subspace along
  \<open>R\<close> for the eigenvalue floor.  The dimension of the moved subspace needs
  only \<open>dim_image_le\<close> applied to \<open>R\<^sup>T\<close>, since
  \<open>S = R\<^sup>T(R(S))\<close> gives \<open>dim S \<le> dim (R(S))\<close>.\<close>

lemma orth_preserves_inner:
  fixes R :: "real^'n::finite^'n"
  assumes orth: "transpose R ** R = mat 1"
  shows "(R *v x) \<bullet> (R *v y) = x \<bullet> y"
  by (metis orth inner_transpose_matrix matrix_vector_mul_assoc matrix_vector_mul_lid)

lemma inner_scaleR_diff_eq:
  fixes q v h :: "real^'n::finite" and c :: real
  shows "q \<bullet> h - c * (v \<bullet> h) = (q - c *\<^sub>R v) \<bullet> h"
  by (simp add: inner_diff_left)

text \<open>Shifting a symmetric matrix by a multiple of the identity keeps it
  symmetric.\<close>

lemma transpose_shift_add:
  fixes A :: "real^'n::finite^'n"
  assumes s: "transpose A = A"
  shows "transpose (A + \<delta> *\<^sub>R mat 1) = A + \<delta> *\<^sub>R mat 1"
  using s by (simp add: transpose_add transpose_scalar)

lemma transpose_shift_diff:
  fixes A :: "real^'n::finite^'n"
  assumes s: "transpose A = A"
  shows "transpose (A - \<delta> *\<^sub>R mat 1) = A - \<delta> *\<^sub>R mat 1"
  using s by (simp add: transpose_diff_matrix transpose_scalar)

text \<open>\<open>inner_matrix_transpose\<close> is the square case of \<open>inner_transpose_matrix\<close>
  from \<open>Symmetric_Spectral\<close>, general at
  \<open>real^'m^'n\<close>.\<close>

lemma matvec_orth_inv:
  fixes R :: "real^'n::finite^'n" and q :: "real^'n"
  assumes orth: "orthogonal_matrix R"
  shows "R *v (transpose R *v q) = q"
proof -
  have o2: "R ** transpose R = mat 1" using orth unfolding orthogonal_matrix_def by blast
  have "R *v (transpose R *v q) = (R ** transpose R) *v q"
    by (metis matrix_vector_mul_assoc)
  also have "\<dots> = q" unfolding o2 by (rule matrix_vector_mul_lid)
  finally show ?thesis .
qed

lemma conj_orth_inv:
  fixes R N :: "real^'n::finite^'n"
  assumes orth: "orthogonal_matrix R"
  shows "R ** (transpose R ** N ** R) ** transpose R = N"
proof -
  have o2: "R ** transpose R = mat 1" using orth unfolding orthogonal_matrix_def by blast
  have "R ** (transpose R ** N ** R) ** transpose R
      = (R ** transpose R) ** N ** (R ** transpose R)"
    by (simp add: matrix_mul_assoc)
  also have "\<dots> = N" unfolding o2 by simp
  finally show ?thesis .
qed

lemma norm_orthogonal_matrix_vector:
  fixes R :: "real^'n::finite^'n" and v :: "real^'n"
  assumes orth: "orthogonal_matrix R"
  shows "norm (R *v v) = norm v"
  using orth orthogonal_transformation_matrix[of "(*v) R"]
  by (simp add: orthogonal_transformation)

lemma norm_matrix_sq_trace:
  fixes M :: "real^'n::finite^'n"
  shows "(norm M)\<^sup>2 = trace (transpose M ** M)"
proof -
  have "trace (transpose M ** M) = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. M $ j $ i * M $ j $ i)"
    by (simp add: trace_def matrix_matrix_mult_def transpose_def)
  also have "\<dots> = (\<Sum>j\<in>UNIV. \<Sum>i\<in>UNIV. M $ j $ i * M $ j $ i)"
    by (rule sum.swap)
  also have "\<dots> = (norm M)\<^sup>2"
    by (simp add: power2_norm_eq_inner inner_vec_def)
  finally show ?thesis by (rule sym)
qed

lemma trace_transpose:
  fixes A :: "'a::comm_ring_1^'n::finite^'n"
  shows "trace (transpose A) = trace A"
  by (simp add: trace_def transpose_def)

lemma norm_transpose_matrix:
  fixes M :: "real^'n::finite^'n"
  shows "norm (transpose M) = norm M"
proof -
  have "(norm (transpose M))\<^sup>2 = trace (M ** transpose M)"
    using norm_matrix_sq_trace[of "transpose M"] by simp
  also have "\<dots> = trace (transpose M ** M)" by (rule trace_mul_sym)
  also have "\<dots> = (norm M)\<^sup>2" by (rule norm_matrix_sq_trace[symmetric])
  finally show ?thesis by simp
qed

lemma trace_transpose_mult_sym:
  fixes M a :: "real^'n::finite^'n"
  assumes "transpose a = a"
  shows "trace (transpose M ** a) = trace (M ** a)"
proof -
  have "trace (transpose M ** a) = trace (transpose (transpose a ** M))"
    by (simp add: matrix_transpose_mul)
  also have "\<dots> = trace (transpose a ** M)" by (simp only: trace_transpose)
  also have "\<dots> = trace (M ** a)" using assms trace_mul_sym[of a M] by simp
  finally show ?thesis .
qed

lemma norm_conj_orthogonal:
  fixes R M :: "real^'n::finite^'n"
  assumes orth: "orthogonal_matrix R"
  shows "norm (R ** M ** transpose R) = norm M"
proof -
  have o1: "transpose R ** R = mat 1" using orth unfolding orthogonal_matrix_def by blast
  have tt: "transpose (R ** M ** transpose R) = R ** transpose M ** transpose R"
    by (simp add: matrix_transpose_mul matrix_mul_assoc)
  have "transpose (R ** M ** transpose R) ** (R ** M ** transpose R)
      = R ** transpose M ** transpose R ** (R ** M ** transpose R)"
    unfolding tt by (rule refl)
  also have "\<dots> = R ** transpose M ** (transpose R ** R) ** M ** transpose R"
    by (simp add: matrix_mul_assoc)
  also have "\<dots> = R ** (transpose M ** M) ** transpose R"
    unfolding o1 by (simp add: matrix_mul_assoc)
  finally have eq: "transpose (R ** M ** transpose R) ** (R ** M ** transpose R)
      = R ** (transpose M ** M) ** transpose R" .
  have "trace (R ** (transpose M ** M) ** transpose R)
      = trace (transpose R ** (R ** (transpose M ** M)))"
    by (rule trace_mul_sym)
  also have "\<dots> = trace ((transpose R ** R) ** (transpose M ** M))"
    by (simp add: matrix_mul_assoc)
  also have "\<dots> = trace (transpose M ** M)" unfolding o1 by simp
  finally have tr: "trace (R ** (transpose M ** M) ** transpose R)
      = trace (transpose M ** M)" .
  have sq: "(norm (R ** M ** transpose R))\<^sup>2 = (norm M)\<^sup>2"
    unfolding norm_matrix_sq_trace eq tr by (rule refl)
  show ?thesis by (rule power2_eq_imp_eq[OF sq norm_ge_zero norm_ge_zero])
qed

lemma dist_prod_scale_fst:
  fixes v z :: "(real^'n::finite) \<times> (real^'n^'n)"
  assumes c0: "0 < c"
  shows "dist (c *\<^sub>R fst v, snd v) (c *\<^sub>R fst z, snd z) \<le> max c 1 * dist v z"
    and "min c 1 * dist v z \<le> dist (c *\<^sub>R fst v, snd v) (c *\<^sub>R fst z, snd z)"
proof -
  define dp where "dp = dist (fst v) (fst z)"
  define dm where "dm = dist (snd v) (snd z)"
  have dp0: "0 \<le> dp" and dm0: "0 \<le> dm" unfolding dp_def dm_def by simp_all
  have dv: "dist v z = sqrt (dp\<^sup>2 + dm\<^sup>2)"
    unfolding dp_def dm_def by (simp add: dist_prod_def)
  have dsp: "dist (c *\<^sub>R fst v) (c *\<^sub>R fst z) = c * dp"
    unfolding dp_def dist_norm using c0
    by (simp add: scaleR_right_diff_distrib[symmetric])
  have ds: "dist (c *\<^sub>R fst v, snd v) (c *\<^sub>R fst z, snd z) = sqrt ((c * dp)\<^sup>2 + dm\<^sup>2)"
    unfolding dm_def by (simp add: dist_prod_def dsp)
  have mx0: "0 \<le> max c 1" using c0 by simp
  have mn0: "0 < min c 1" using c0 by simp
  show "dist (c *\<^sub>R fst v, snd v) (c *\<^sub>R fst z, snd z) \<le> max c 1 * dist v z"
  proof -
    have cle: "c\<^sup>2 \<le> (max c 1)\<^sup>2" using c0 by (simp add: power_mono)
    have one: "(1::real) \<le> (max c 1)\<^sup>2" using c0 by (simp add: max_def)
    have m1: "c\<^sup>2 * dp\<^sup>2 \<le> (max c 1)\<^sup>2 * dp\<^sup>2"
      using cle by (simp add: mult_right_mono)
    have m2: "dm\<^sup>2 \<le> (max c 1)\<^sup>2 * dm\<^sup>2"
      using mult_right_mono[OF one zero_le_power2, of dm] by simp
    have "(c * dp)\<^sup>2 + dm\<^sup>2 = c\<^sup>2 * dp\<^sup>2 + dm\<^sup>2" by (simp add: power_mult_distrib)
    also have "\<dots> \<le> (max c 1)\<^sup>2 * dp\<^sup>2 + (max c 1)\<^sup>2 * dm\<^sup>2" using m1 m2 by linarith
    also have "\<dots> = (max c 1)\<^sup>2 * (dp\<^sup>2 + dm\<^sup>2)" by (simp add: algebra_simps)
    finally have "(c * dp)\<^sup>2 + dm\<^sup>2 \<le> (max c 1)\<^sup>2 * (dp\<^sup>2 + dm\<^sup>2)" .
    then have "sqrt ((c * dp)\<^sup>2 + dm\<^sup>2) \<le> sqrt ((max c 1)\<^sup>2 * (dp\<^sup>2 + dm\<^sup>2))"
      by (rule real_sqrt_le_mono)
    also have "\<dots> = max c 1 * sqrt (dp\<^sup>2 + dm\<^sup>2)"
      using mx0 by (simp add: real_sqrt_mult)
    finally show ?thesis unfolding ds dv .
  qed
  show "min c 1 * dist v z \<le> dist (c *\<^sub>R fst v, snd v) (c *\<^sub>R fst z, snd z)"
  proof -
    have cle: "(min c 1)\<^sup>2 \<le> c\<^sup>2" using c0 by (simp add: power_mono)
    have one: "(min c 1)\<^sup>2 \<le> 1" using c0 by (simp add: min_def power_le_one)
    have m1: "(min c 1)\<^sup>2 * dp\<^sup>2 \<le> c\<^sup>2 * dp\<^sup>2" using cle by (simp add: mult_right_mono)
    have m2: "(min c 1)\<^sup>2 * dm\<^sup>2 \<le> dm\<^sup>2"
      using mult_right_mono[OF one zero_le_power2, of dm] by simp
    have "(min c 1)\<^sup>2 * (dp\<^sup>2 + dm\<^sup>2) = (min c 1)\<^sup>2 * dp\<^sup>2 + (min c 1)\<^sup>2 * dm\<^sup>2"
      by (simp add: algebra_simps)
    also have "\<dots> \<le> c\<^sup>2 * dp\<^sup>2 + dm\<^sup>2" using m1 m2 by linarith
    also have "\<dots> = (c * dp)\<^sup>2 + dm\<^sup>2" by (simp add: power_mult_distrib)
    finally have "(min c 1)\<^sup>2 * (dp\<^sup>2 + dm\<^sup>2) \<le> (c * dp)\<^sup>2 + dm\<^sup>2" .
    then have step: "sqrt ((min c 1)\<^sup>2 * (dp\<^sup>2 + dm\<^sup>2)) \<le> sqrt ((c * dp)\<^sup>2 + dm\<^sup>2)"
      by (rule real_sqrt_le_mono)
    have "sqrt ((min c 1)\<^sup>2 * (dp\<^sup>2 + dm\<^sup>2)) = min c 1 * sqrt (dp\<^sup>2 + dm\<^sup>2)"
      using mn0 by (simp add: real_sqrt_mult)
    then show ?thesis using step unfolding ds dv by simp
  qed
qed

lemma affine_interior_image:
  fixes R :: "real^'n::finite^'n" and b :: "real^'n"
  assumes orth: "orthogonal_matrix R" and c0: "0 < c"
  shows "interior ((\<lambda>z. c *\<^sub>R (R *v z) + b) ` S)
       = (\<lambda>z. c *\<^sub>R (R *v z) + b) ` interior S"
proof -
  have "(\<lambda>z. c *\<^sub>R (R *v z) + b) ` A = (+) b ` (\<lambda>z. c *\<^sub>R (R *v z)) ` A" for A
    by (auto simp: image_image add.commute)
  moreover have "interior ((\<lambda>z. c *\<^sub>R (R *v z)) ` A) = (\<lambda>z. c *\<^sub>R (R *v z)) ` interior A" for A
  proof (rule interior_injective_linear_image)
    show "linear (\<lambda>z. c *\<^sub>R (R *v z))"
      unfolding linear_iff
      by (simp add: matrix_vector_right_distrib matrix_vector_mult_scaleR algebra_simps)
    show "inj (\<lambda>z. c *\<^sub>R (R *v z))"
      using c0 orth norm_orthogonal_matrix_vector[OF orth]
      by (intro injI) (metis eq_iff_diff_eq_0 matrix_vector_mult_diff_distrib norm_eq_zero
          scaleR_cancel_left less_irrefl)
  qed
  ultimately show ?thesis by (simp add: interior_translation)
qed


lemma diag_eq_inner_axis:
  fixes a :: "real^'n^'n"
  shows "a $ i $ i = axis i (1 :: real) \<bullet> (a *v axis i 1)"
proof -
  have "axis i (1 :: real) \<bullet> (a *v axis i 1) = (a *v axis i 1) $ i"
    by (simp add: inner_axis')
  also have "\<dots> = a $ i $ i"
    by (simp add: matrix_vector_mult_basis column_def)
  finally show ?thesis ..
qed

lemma trace_nonneg_psd:
  fixes a :: "real^'n^'n"
  assumes "\<And>x. 0 \<le> x \<bullet> (a *v x)"
  shows "0 \<le> trace a"
  unfolding trace_def diag_eq_inner_axis by (intro sum_nonneg assms)

text \<open>The constraint set is convex, closed and bounded, hence compact.
  Convexity comes from convexity of the constraint set and the an eigenvalue upper bound
  half-spaces, closedness from the a projection-infimum characterisation infimum characterisation,
  boundedness from the standard psd entry bound.\<close>

lemma quadform_convex_comb:
  fixes a b :: "real^'n::finite^'n"
  shows "x \<bullet> ((s *\<^sub>R a + t *\<^sub>R b) *v x)
      = s * (x \<bullet> (a *v x)) + t * (x \<bullet> (b *v x))"
  by (simp add: matrix_vector_mult_add_rdistrib
      scaleR_matrix_vector_assoc[symmetric] inner_add_right)

lemma bounded_linear_cross:
  fixes x :: "real^'n::finite"
  shows "bounded_linear
      (\<lambda>v :: real^'n. (\<chi> i j. x $ i * v $ j + v $ i * x $ j) :: real^'n^'n)"
  unfolding linear_conv_bounded_linear[symmetric]
  by (intro linearI) (simp_all add: vec_eq_iff algebra_simps)

text \<open>Tracing the compensated clause gives the submartingale statement
  Lemma 2.1 of \<^cite>\<open>LaiShkolnikovSoner\<close> runs on: \<open>|X|\<^sup>2 - trace Y\<close> is a martingale and \<open>trace Y\<close> grows
  at rate at least \<open>n - k\<close>, so \<open>E[|X\<^sub>t|\<^sup>2] - |x|\<^sup>2 \<ge> (n-k)\<sqdot>t\<close>.\<close>

lemma bounded_linear_trace:
  "bounded_linear (trace :: real^'n::finite^'n \<Rightarrow> real)"
  unfolding linear_conv_bounded_linear[symmetric]
  by (intro linearI) (simp_all add: trace_add trace_scaleR)

lemma bounded_linear_cross_pair:
  fixes c :: "real^'n::finite"
  shows "bounded_linear
      (\<lambda>v :: real^'n. (\<chi> i j. c $ i * v $ j) + (\<chi> i j. v $ i * c $ j))"
  unfolding linear_conv_bounded_linear[symmetric]
  by (intro linearI) (simp_all add: vec_eq_iff algebra_simps)

lemma trace_mult_sum:
  fixes M a :: "real^'n::finite^'n"
  shows "trace (M ** a) = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. M $ i $ j * a $ j $ i)"
  by (simp add: trace_def matrix_matrix_mult_def)

lemma bounded_linear_trace_mult_left:
  fixes M :: "real^'n::finite^'n"
  shows "bounded_linear (\<lambda>a :: real^'n^'n. trace (M ** a))"
  unfolding linear_conv_bounded_linear[symmetric]
proof (rule linearI)
  fix a b :: "real^'n^'n"
  show "trace (M ** (a + b)) = trace (M ** a) + trace (M ** b)"
    by (simp add: trace_mult_sum sum.distrib algebra_simps)
next
  fix r :: real and a :: "real^'n^'n"
  show "trace (M ** (r *\<^sub>R a)) = r *\<^sub>R trace (M ** a)"
    by (simp add: trace_mult_sum sum_distrib_left algebra_simps)
qed

lemma bounded_linear_trace_mult_right:
  fixes P :: "real^'n::finite^'n"
  shows "bounded_linear (\<lambda>a :: real^'n^'n. trace (a ** P))"
  unfolding linear_conv_bounded_linear[symmetric]
proof (rule linearI)
  fix a b :: "real^'n^'n"
  show "trace ((a + b) ** P) = trace (a ** P) + trace (b ** P)"
    by (simp add: trace_mult_sum sum.distrib algebra_simps)
next
  fix r :: real and a :: "real^'n^'n"
  show "trace ((r *\<^sub>R a) ** P) = r *\<^sub>R trace (a ** P)"
    by (simp add: trace_mult_sum sum_distrib_left algebra_simps)
qed

lemma bounded_linear_quadform:
  fixes z :: "real^'n::finite"
  shows "bounded_linear (\<lambda>a :: real^'n^'n. z \<bullet> (a *v z))"
  unfolding linear_conv_bounded_linear[symmetric]
proof (rule linearI)
  fix a b :: "real^'n^'n"
  show "z \<bullet> ((a + b) *v z) = z \<bullet> (a *v z) + z \<bullet> (b *v z)"
    by (simp add: matrix_vector_mult_def inner_vec_def sum.distrib
        algebra_simps)
next
  fix r :: real and a :: "real^'n^'n"
  show "z \<bullet> ((r *\<^sub>R a) *v z) = r *\<^sub>R (z \<bullet> (a *v z))"
    by (simp add: matrix_vector_mult_def inner_vec_def sum_distrib_left
        algebra_simps)
qed

lemma continuous_on_trace_mult_right:
  fixes P :: "real^'n::finite^'n"
  shows "continuous_on UNIV (\<lambda>a :: real^'n^'n. trace (a ** P))"
  by (rule linear_continuous_on[OF bounded_linear_trace_mult_right])

lemma closed_trace_proj_halfspace:
  fixes P :: "real^'n::finite^'n"
  shows "closed {a :: real^'n^'n. c \<le> trace (a ** P)}"
  by (intro closed_Collect_le continuous_on_const continuous_on_trace_mult_right)

lemma trace_mult_diff:
  fixes M A B :: "real^'n::finite^'n"
  shows "trace (M ** (A - B)) = trace (M ** A) - trace (M ** B)"
  by (simp add: trace_mult_sum sum_subtractf right_diff_distrib)

lemma trace_mult_scaleR:
  fixes M A :: "real^'n::finite^'n"
  shows "trace (M ** (r *\<^sub>R A)) = r * trace (M ** A)"
  by (simp add: trace_mult_sum sum_distrib_left algebra_simps)

lemma trace_mult_add:
  fixes M A B :: "real^'n::finite^'n"
  shows "trace (M ** (A + B)) = trace (M ** A) + trace (M ** B)"
  by (simp add: trace_mult_sum sum.distrib algebra_simps)

lemma quadform_abs_le:
  fixes M :: "real^'n::finite^'n" and v :: "real^'n"
  shows "\<bar>v \<bullet> (M *v v)\<bar> \<le> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>) * (norm v)\<^sup>2"
proof -
  have e: "v \<bullet> (M *v v) = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. v $ i * (M $ i $ j * v $ j))"
    by (simp add: inner_vec_def matrix_vector_mult_def sum_distrib_left)
  have "\<bar>v \<bullet> (M *v v)\<bar> \<le> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>v $ i * (M $ i $ j * v $ j)\<bar>)"
    unfolding e by (intro order_trans[OF sum_abs] sum_mono sum_abs)
  also have "\<dots> \<le> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar> * (norm v)\<^sup>2)"
  proof (intro sum_mono)
    fix i j :: 'n
    have vi: "\<bar>v $ i\<bar> \<le> norm v" by (rule component_le_norm_cart)
    have vj: "\<bar>v $ j\<bar> \<le> norm v" by (rule component_le_norm_cart)
    have "\<bar>v $ i * (M $ i $ j * v $ j)\<bar> = \<bar>M $ i $ j\<bar> * (\<bar>v $ i\<bar> * \<bar>v $ j\<bar>)"
      by (simp add: abs_mult algebra_simps)
    also have "\<dots> \<le> \<bar>M $ i $ j\<bar> * (norm v * norm v)"
      by (intro mult_left_mono mult_mono vi vj) auto
    finally show "\<bar>v $ i * (M $ i $ j * v $ j)\<bar>
        \<le> \<bar>M $ i $ j\<bar> * (norm v)\<^sup>2"
      by (simp add: power2_eq_square)
  qed
  also have "\<dots> = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>) * (norm v)\<^sup>2"
    by (simp add: sum_distrib_right)
  finally show ?thesis .
qed

subsection \<open>The entrywise sum\<close>

text \<open>The sum of the absolute values of the entries bounds the quadratic form
  above and is itself bounded by a multiple of the norm.\<close>

definition entrysum :: "real^'n::finite^'n \<Rightarrow> real" where
  "entrysum D = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>D $ i $ j\<bar>)"

lemma entrysum_nonneg: "0 \<le> entrysum D"
  unfolding entrysum_def by (intro sum_nonneg) auto

lemma entrysum_sym: "entrysum (A - B) = entrysum (B - A)"
  unfolding entrysum_def by (intro sum.cong refl) (simp add: abs_minus_commute)

lemma entry_abs_le_norm:
  fixes D :: "real^'n::finite^'n"
  shows "\<bar>D $ i $ j\<bar> \<le> norm D"
  by (metis component_le_norm_cart Finite_Cartesian_Product.norm_nth_le order_trans)

lemma entrysum_le_norm:
  fixes D :: "real^'n::finite^'n"
  shows "entrysum D \<le> real (CARD('n) * CARD('n)) * norm D"
proof -
  have "entrysum D \<le> (\<Sum>i\<in>(UNIV :: 'n set). \<Sum>j\<in>(UNIV :: 'n set). norm D)"
    unfolding entrysum_def by (intro sum_mono entry_abs_le_norm)
  then show ?thesis by simp
qed

lemma matvec_norm_le:
  fixes M :: "real^'n::finite^'n"
  shows "norm (M *v w) \<le> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>) * norm w"
  using onorm[OF matrix_vector_mul_bounded_linear, of M w]
    onorm_le_matrix_component_sum[of M]
  by (meson mult_right_mono norm_ge_zero order_trans)

text \<open>The covariance field is \<open>\<Sum>\<^sub>u outerp (w u)\<close> for columns \<open>w u\<close>, and the
  Euler machinery reads it only through its trace against the Hessian.  That
  pairing is exact, whatever the columns: the trace of \<open>M\<close> against the sum is
  the sum of the quadratic forms \<open>w u \<bullet> (M *v w u)\<close>.\<close>

lemma trace_mult_zero_right: "trace (M ** (0 :: real^'n::finite^'n)) = 0"
  by (simp add: matrix_matrix_mult_def trace_def vec_eq_iff)

lemma matmul_sandwich_blin:
  fixes S :: "real^'n::finite^'n"
  shows "bounded_linear (\<lambda>A :: real^'n^'n. S ** A ** transpose S)"
  unfolding linear_conv_bounded_linear[symmetric]
proof (intro linearI)
  fix A B :: "real^'n^'n"
  show "S ** (A + B) ** transpose S = S ** A ** transpose S
      + S ** B ** transpose S"
    by (simp add: matrix_matrix_mult_def vec_eq_iff
        sum.distrib algebra_simps)
next
  fix c :: real and A :: "real^'n^'n"
  show "S ** (c *\<^sub>R A) ** transpose S = c *\<^sub>R (S ** A ** transpose S)"
    by (simp add: matrix_matrix_mult_def vec_eq_iff
        sum_distrib_left algebra_simps)
qed

lemma sandwich_mat1:
  fixes S :: "real^'n::finite^'n"
  shows "S ** (c *\<^sub>R mat 1) ** transpose S = c *\<^sub>R (S ** transpose S)"
  by (simp add: matrix_scalar_ac scalar_matrix_assoc[symmetric] scalar_matrix_assoc[symmetric])

text \<open>The Euler analysis needs exactly two facts per step: the compensated
  quadratic increment has mean zero (an instance of
  a mean-zero compensated-increment fact in the application, since the member's
  second component is deterministic), and its variance is \<open>O(h\<^sup>2)\<close>.  The
  variance bound needs no Wick calculus and no coordinate independence:
  the pointwise AM--GM bound \<open>a\<^sup>2b\<^sup>2 \<le> (a\<^sup>4 + b\<^sup>4)/2\<close> reduces everything
  to the fourth marginal moment \<open>3h\<^sup>2\<close> of one Brownian coordinate.\<close>

lemma quad_taylor_step:
  fixes M :: "real^'n::finite^'n" and q x a b :: "real^'n"
  assumes sym: "transpose M = M"
  shows "q \<bullet> (b - x) + (1/2) * ((b - x) \<bullet> (M *v (b - x)))
       - (q \<bullet> (a - x) + (1/2) * ((a - x) \<bullet> (M *v (a - x))))
     = (q + M *v (a - x)) \<bullet> (b - a)
       + (1/2) * ((b - a) \<bullet> (M *v (b - a)))"
proof -
  define u where "u = a - x"
  define d where "d = b - a"
  have bx: "b - x = u + d" unfolding u_def d_def by simp
  have swap: "d \<bullet> (M *v u) = u \<bullet> (M *v d)"
  proof -
    have "d \<bullet> (M *v u) = (transpose M *v d) \<bullet> u"
      by (rule inner_transpose_matrix)
    also have "\<dots> = (M *v d) \<bullet> u" by (simp add: sym)
    also have "\<dots> = u \<bullet> (M *v d)" by (rule inner_commute)
    finally show ?thesis .
  qed
  have e12: "(b - x) \<bullet> (M *v (b - x))
      = u \<bullet> (M *v u) + 2 * (u \<bullet> (M *v d)) + d \<bullet> (M *v d)"
  proof -
    have "(b - x) \<bullet> (M *v (b - x)) = (u + d) \<bullet> (M *v (u + d))"
      unfolding bx by (rule refl)
    also have "\<dots> = u \<bullet> (M *v u) + u \<bullet> (M *v d)
        + (d \<bullet> (M *v u) + d \<bullet> (M *v d))"
      by (simp add: matrix_vector_right_distrib inner_add_left
          inner_add_right)
    also have "d \<bullet> (M *v u) = u \<bullet> (M *v d)" by (rule swap)
    finally show ?thesis by simp
  qed
  have e0: "q \<bullet> (b - x) = q \<bullet> u + q \<bullet> d"
    unfolding bx by (simp add: inner_add_right)
  have e3: "q \<bullet> (a - x) = q \<bullet> u" unfolding u_def by (rule refl)
  have e4: "(a - x) \<bullet> (M *v (a - x)) = u \<bullet> (M *v u)"
    unfolding u_def by (rule refl)
  have e5: "(q + M *v (a - x)) \<bullet> (b - a) = q \<bullet> d + u \<bullet> (M *v d)"
  proof -
    have "(q + M *v (a - x)) \<bullet> (b - a) = (q + M *v u) \<bullet> d"
      unfolding u_def d_def by (rule refl)
    also have "\<dots> = q \<bullet> d + (M *v u) \<bullet> d" by (simp add: inner_add_left)
    also have "(M *v u) \<bullet> d = d \<bullet> (M *v u)" by (rule inner_commute)
    also have "d \<bullet> (M *v u) = u \<bullet> (M *v d)" by (rule swap)
    finally show ?thesis .
  qed
  have e6: "(b - a) \<bullet> (M *v (b - a)) = d \<bullet> (M *v d)"
    unfolding d_def by (rule refl)
  show ?thesis using e0 e12 e3 e4 e5 e6 by linarith
qed

text \<open>The quadratic is Lipschitz on the ball, with explicit constant
  \<open>norm q + 2 C\<^sub>M rb\<close>, via the one-step Taylor identity
  \<open>quad_taylor_step\<close>.\<close>

text \<open>Small independent pieces the contradiction assembles: algebra for the
  softened Hessian, a generic small-radius chooser, the witness extraction
  from a failed operator inequality, the value bound \<open>v(x) < T\<close> forced by a
  nonzero touching gradient, and the exit-time identity on paths that never
  leave \<open>K\<close>.\<close>

lemma trace_msub_mat:
  fixes H a :: "real^'n::finite^'n" and s :: real
  shows "trace ((H - s *\<^sub>R mat 1) ** a) = trace (H ** a) - s * trace a"
proof -
  have e1: "(H - s *\<^sub>R mat 1) ** a = H ** a - (s *\<^sub>R mat 1) ** a"
    by (simp add: matrix_matrix_mult_def vec_eq_iff sum_subtractf
        left_diff_distrib)
  have e2: "(s *\<^sub>R mat 1) ** a = s *\<^sub>R a"
    by (simp add: scalar_matrix_assoc[symmetric])
  have e3: "trace (H ** a - s *\<^sub>R a) = trace (H ** a) - s * trace a"
    by (simp add: trace_def sum_subtractf sum_distrib_left)
  show ?thesis unfolding e1 e2 by (rule e3)
qed

lemma quad_soften_split:
  fixes H :: "real^'n::finite^'n" and v :: "real^'n" and \<gamma> \<delta> :: real
  shows "v \<bullet> ((H - \<delta> *\<^sub>R mat 1) *v v)
      = v \<bullet> ((H - (2 * \<gamma> + \<delta>) *\<^sub>R mat 1) *v v) + 2 * \<gamma> * (v \<bullet> v)"
proof -
  have e1: "(H - \<delta> *\<^sub>R mat 1) *v v = H *v v - \<delta> *\<^sub>R v"
    by (simp add: matrix_vector_mult_diff_rdistrib
        scaleR_matrix_vector_assoc[symmetric])
  have e2: "(H - (2 * \<gamma> + \<delta>) *\<^sub>R mat 1) *v v
      = H *v v - (2 * \<gamma> + \<delta>) *\<^sub>R v"
    by (simp add: matrix_vector_mult_diff_rdistrib
        scaleR_matrix_vector_assoc[symmetric])
  show ?thesis unfolding e1 e2
    by (simp add: algebra_simps)
qed

text \<open>The skew field above moves the witness off its own eigenframe, and the
  margins that absorb that motion are what force \<open>1 < L\<close>: at \<open>L = 1\<close> the
  feasible set of Eq. (1.9) of \<^cite>\<open>LaiShkolnikovSoner\<close> is rigid, its top \<open>n - k\<close> eigenvalues pinned to
  \<open>1\<close> from both sides, so no witness has slack to perturb.  A field of exact
  rotations needs none.  Conjugating the witness by an orthogonal matrix
  leaves its spectrum, and hence its membership of the feasible set,
  untouched; and the rotation carrying the frozen gradient \<open>q\<close> to the current
  gradient makes the conjugate annihilate the current gradient, which is all
  the Euler construction asks of the field.  The package the rotation-field package below
  therefore carries no hypothesis on \<open>L\<close> at all, and in particular is
  available at \<open>L = 1\<close>, the Ambrosio-Soner flow case of Remark 1.1(c).

  The rotation \<open>rotm q w\<close> is a product of two Householder reflections; it
  carries \<open>q\<close> onto the ray through \<open>w\<close> as soon as the two are not opposed,
  and is the identity at \<open>w = q\<close>, which is where the trace margin is read
  off: by continuity at the touching point, in place of the three explicit
  smallness estimates the skew field needs. \<open>hrefl\<close>, \<open>rotm\<close> and their
  properties, including the continuity of \<open>w \<mapsto> rotm q w\<close>
  (\<open>rotm_vec_cont\<close>), live in
  \<open>Householder_Rotation\<close>.\<close>

lemma colmat_matvec:
  fixes R :: "real^'n::finite^'n" and c :: "'n \<Rightarrow> real^'n"
  shows "(\<chi> i j. (R *v c j) $ i) = R ** (\<chi> i j. c j $ i)"
  by (simp add: vec_eq_iff matrix_matrix_mult_def matrix_vector_mult_def)

lemma rot_cone_ok:
  fixes q e :: "real^'n::finite"
  assumes q0: "q \<noteq> 0" and lt: "norm e < norm q"
  shows "0 < norm q * norm (q + e) + q \<bullet> (q + e)"
proof -
  have nq0: "0 < norm q" using q0 by simp
  have cs: "\<bar>q \<bullet> e\<bar> \<le> norm q * norm e" by (rule Cauchy_Schwarz_ineq2)
  have qq: "q \<bullet> q = norm q * norm q"
    by (simp add: dot_square_norm power2_eq_square)
  have expand: "q \<bullet> (q + e) = norm q * norm q + q \<bullet> e"
    by (simp add: inner_add_right qq)
  have "norm q * norm e < norm q * norm q"
    by (rule mult_strict_left_mono[OF lt nq0])
  then have "0 < q \<bullet> (q + e)" unfolding expand using cs by linarith
  moreover have "0 \<le> norm q * norm (q + e)" by simp
  ultimately show ?thesis by linarith
qed

text \<open>The Lipschitz bound on a quadratic and the openness of its bad
  event, re-stated with the confinement region decoupled from the
  quadratic's centre: the Lipschitz bound needs only the two norm
  bounds, and the bad event stays open for any open region, since the
  stay-condition and the quadratic no longer share a centre.  These feed
  the region versions of the vanishing-probability and limit theorems
  below.\<close>

lemma quad_diff_bound_gen:
  fixes M :: "real^'n::finite^'n" and q x a b :: "real^'n" and R :: real
  assumes sym: "transpose M = M"
    and na: "norm (a - x) \<le> R" and nb: "norm (b - x) \<le> R"
  shows "\<bar>q \<bullet> (b - x) + (1/2) * ((b - x) \<bullet> (M *v (b - x)))
       - (q \<bullet> (a - x) + (1/2) * ((a - x) \<bullet> (M *v (a - x))))\<bar>
      \<le> (norm q + 2 * (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>) * R)
          * norm (b - a)"
proof -
  let ?CM = "\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>"
  have CM0: "0 \<le> ?CM" by (auto intro!: sum_nonneg)
  have dble: "norm (b - a) \<le> 2 * R"
  proof -
    have deq: "b - a = (b - x) + (x - a)" by simp
    have "norm (b - a) \<le> norm (b - x) + norm (x - a)"
      by (subst deq) (rule norm_triangle_ineq)
    moreover have "norm (x - a) \<le> R"
      using na by (simp add: norm_minus_commute)
    ultimately show ?thesis using nb by linarith
  qed
  have step: "q \<bullet> (b - x) + (1/2) * ((b - x) \<bullet> (M *v (b - x)))
      - (q \<bullet> (a - x) + (1/2) * ((a - x) \<bullet> (M *v (a - x))))
      = (q + M *v (a - x)) \<bullet> (b - a)
        + (1/2) * ((b - a) \<bullet> (M *v (b - a)))"
    by (rule quad_taylor_step[OF sym])
  have t1: "\<bar>(q + M *v (a - x)) \<bullet> (b - a)\<bar>
      \<le> (norm q + ?CM * R) * norm (b - a)"
  proof -
    have cs: "\<bar>(q + M *v (a - x)) \<bullet> (b - a)\<bar>
        \<le> norm (q + M *v (a - x)) * norm (b - a)"
      by (rule Cauchy_Schwarz_ineq2)
    have "norm (q + M *v (a - x)) \<le> norm q + ?CM * R"
    proof -
      have "norm (q + M *v (a - x)) \<le> norm q + norm (M *v (a - x))"
        by (rule norm_triangle_ineq)
      moreover have "norm (M *v (a - x)) \<le> ?CM * norm (a - x)"
        by (rule matvec_norm_le)
      moreover have "?CM * norm (a - x) \<le> ?CM * R"
        by (rule mult_left_mono[OF na CM0])
      ultimately show ?thesis by linarith
    qed
    then have "norm (q + M *v (a - x)) * norm (b - a)
        \<le> (norm q + ?CM * R) * norm (b - a)"
      by (rule mult_right_mono) simp
    then show ?thesis using cs by linarith
  qed
  have t2: "\<bar>(1/2) * ((b - a) \<bullet> (M *v (b - a)))\<bar>
      \<le> ?CM * R * norm (b - a)"
  proof -
    have "\<bar>(b - a) \<bullet> (M *v (b - a))\<bar>
        \<le> norm (b - a) * norm (M *v (b - a))"
      by (rule Cauchy_Schwarz_ineq2)
    also have "\<dots> \<le> norm (b - a) * (?CM * norm (b - a))"
      by (rule mult_left_mono[OF matvec_norm_le norm_ge_zero])
    finally have h: "\<bar>(b - a) \<bullet> (M *v (b - a))\<bar>
        \<le> ?CM * norm (b - a) * norm (b - a)"
      by (simp add: mult_ac)
    have h2: "?CM * norm (b - a) * norm (b - a)
        \<le> ?CM * (2 * R) * norm (b - a)"
      by (rule mult_right_mono[OF mult_left_mono[OF dble CM0] norm_ge_zero])
    have "\<bar>(1/2) * ((b - a) \<bullet> (M *v (b - a)))\<bar>
        = (1/2) * \<bar>(b - a) \<bullet> (M *v (b - a))\<bar>"
      by (simp add: abs_mult)
    also have "\<dots> \<le> (1/2) * (?CM * (2 * R) * norm (b - a))"
      using h h2 by linarith
    also have "\<dots> = ?CM * R * norm (b - a)" by simp
    finally show ?thesis .
  qed
  have tri: "\<bar>q \<bullet> (b - x) + (1/2) * ((b - x) \<bullet> (M *v (b - x)))
      - (q \<bullet> (a - x) + (1/2) * ((a - x) \<bullet> (M *v (a - x))))\<bar>
      \<le> \<bar>(q + M *v (a - x)) \<bullet> (b - a)\<bar>
        + \<bar>(1/2) * ((b - a) \<bullet> (M *v (b - a)))\<bar>"
    unfolding step by (rule abs_triangle_ineq)
  have fin: "(norm q + ?CM * R) * norm (b - a)
      + ?CM * R * norm (b - a)
      = (norm q + 2 * ?CM * R) * norm (b - a)"
    by (simp add: algebra_simps)
  show ?thesis using tri t1 t2 fin by linarith
qed

text \<open>The two facts that make the envelope argument affordable.  A
  quadratic centred at \<open>x\<close> is, up to the additive constant of its value
  at \<open>y\<close>, the quadratic centred at \<open>y\<close> with gradient \<open>q + M(y-x)\<close>, and
  the two have the same gradient field \<open>q + M(\<sqdot> - x)\<close>, so the kill
  hypothesis is unchanged.  Consequently every verified theorem about a
  process started at its quadratic's centre applies verbatim to a
  process started at \<open>y\<close> with the quadratic centred at \<open>x\<close>.\<close>

lemma quad_grad_shift:
  fixes M :: "real^'n::finite^'n" and q x y z :: "real^'n"
  shows "(q + M *v (y - x)) + M *v (z - y) = q + M *v (z - x)"
proof -
  have "M *v (z - x) = M *v ((y - x) + (z - y))"
    by (rule arg_cong[where f = "\<lambda>v. M *v v"]) simp
  also have "\<dots> = M *v (y - x) + M *v (z - y)"
    by (rule matrix_vector_right_distrib)
  finally show ?thesis by simp
qed

lemma quad_shift:
  fixes M :: "real^'n::finite^'n" and q x y z :: "real^'n"
  assumes sym: "transpose M = M"
  shows "q \<bullet> (z - x) + (1/2) * ((z - x) \<bullet> (M *v (z - x)))
      = (q \<bullet> (y - x) + (1/2) * ((y - x) \<bullet> (M *v (y - x))))
        + ((q + M *v (y - x)) \<bullet> (z - y)
           + (1/2) * ((z - y) \<bullet> (M *v (z - y))))"
  using quad_taylor_step[OF sym, where q = q and x = x and a = y and b = z]
  by linarith

text \<open>The tilted test function of Case 2 is a quadratic plus a linear
  term, so it is continuous.\<close>

lemma continuous_on_quad_tilt:
  fixes M :: "real^'n::finite^'n" and x \<eta> :: "real^'n"
  shows "continuous_on S (\<lambda>z. ((z - x) \<bullet> (M *v (z - x))) / 2 + \<eta> \<bullet> (z - x))"
proof -
  have c1: "continuous_on S (\<lambda>z. z - x)" by (intro continuous_intros)
  have c2: "continuous_on S (\<lambda>z. M *v (z - x))"
    by (rule continuous_on_compose2[OF
          linear_continuous_on[OF matrix_vector_mul_bounded_linear] c1]) auto
  show ?thesis using c1 c2 by (intro continuous_intros) auto
qed

text \<open>Finally the quantitative part of the tilt.  If \<open>W\<close> is bounded
  below by \<open>W x + Q\<close> with a quadratic surplus \<open>c|z - x|\<^sup>2\<close>, and \<open>y\<close>
  minimises \<open>W - Q - \<langle>\<eta>, \<cdot> - x\<rangle>\<close> over the ball, then \<open>y\<close> is within
  \<open>\<bar>\<eta>\<bar>/c\<close> of \<open>x\<close>.  The paper only records that the minimisers converge
  to the touching point; the explicit rate is what makes them interior
  to the ball for small \<open>\<eta>\<close>, which is what the now-local Case 1 needs.\<close>

lemma tilted_minimiser_close:
  fixes W Q :: "real^'n::finite \<Rightarrow> real" and x y \<eta> :: "real^'n"
  assumes sep: "\<And>z. z \<in> cball x \<rho> \<Longrightarrow>
      W x + Q z + c * ((z - x) \<bullet> (z - x)) \<le> W z"
    and Qx: "Q x = 0" and c0: "0 < c"
    and xin: "x \<in> cball x \<rho>" and yin: "y \<in> cball x \<rho>"
    and mn: "\<And>z. z \<in> cball x \<rho> \<Longrightarrow>
      W y - Q y - \<eta> \<bullet> (y - x) \<le> W z - Q z - \<eta> \<bullet> (z - x)"
  shows "norm (y - x) \<le> norm \<eta> / c"
proof -
  have a1: "W y - Q y - \<eta> \<bullet> (y - x) \<le> W x"
    using mn[OF xin] Qx by simp
  have a2: "W x + Q y + c * ((y - x) \<bullet> (y - x)) \<le> W y"
    by (rule sep[OF yin])
  have step: "c * ((y - x) \<bullet> (y - x)) \<le> \<eta> \<bullet> (y - x)"
    using a1 a2 by linarith
  have cs: "\<eta> \<bullet> (y - x) \<le> norm \<eta> * norm (y - x)"
    by (rule norm_cauchy_schwarz)
  have sq: "(y - x) \<bullet> (y - x) = norm (y - x) * norm (y - x)"
    by (simp add: dot_square_norm power2_eq_square)
  show ?thesis
  proof (cases "norm (y - x) = 0")
    case True
    then show ?thesis using c0 by simp
  next
    case False
    then have pos: "0 < norm (y - x)" by simp
    have "(c * norm (y - x)) * norm (y - x) \<le> norm \<eta> * norm (y - x)"
      using step cs sq by (simp add: mult.assoc)
    then have "c * norm (y - x) \<le> norm \<eta>"
      using pos by (rule mult_right_le_imp_le)
    then show ?thesis using c0 by (simp add: pos_le_divide_eq mult.commute)
  qed
qed

text \<open>The other horn of Case 2's dichotomy is that the tilted gradient
  vanishes at every tilted minimiser.  Because the test function is
  exactly quadratic, a vanishing gradient makes the first-order terms of
  the minimality inequality cancel identically, leaving the purely
  quadratic bound

    \<open>W w - W y \<ge> \<onehalf>(w - y)\<^sup>T M (w - y) \<ge> -C\<bar>w - y\<bar>\<^sup>2\<close>

  for every \<open>w\<close> near \<open>y\<close>.  If that holds for every \<open>y\<close> in a ball ---
  which it does, once the tilted minimisers sweep out a neighbourhood ---
  then the bound is available in both directions between any two points
  of the ball, and a function whose increments are \<open>O(\<bar>\<Delta>\<bar>\<^sup>2)\<close> along
  every segment is constant: subdividing a segment into \<open>n\<close> pieces costs
  \<open>n \<cdot> C(\<bar>\<Delta>\<bar>/n)\<^sup>2 = C\<bar>\<Delta>\<bar>\<^sup>2/n\<close>, which vanishes.

  Both statements below are pure real analysis; neither mentions the
  value function or the operator.\<close>

lemma pinch_segment_bound:
  fixes W :: "real^'n::finite \<Rightarrow> real" and a b :: "real^'n"
    and S :: "(real^'n) set"
  assumes C0: "0 \<le> C" and n0: "0 < n"
    and pin: "\<And>u w. u \<in> S \<Longrightarrow> w \<in> S \<Longrightarrow>
      W u - C * (dist u w * dist u w) \<le> W w"
    and seg: "\<And>i. i \<le> n \<Longrightarrow> a + (real i / real n) *\<^sub>R (b - a) \<in> S"
  shows "W a - W b \<le> C * (dist a b * dist a b) / real n"
proof -
  define p where "p = (\<lambda>i :: nat. a + (real i / real n) *\<^sub>R (b - a))"
  define d where "d = dist a b / real n"
  have rn0: "(0 :: real) < real n" using n0 by simp
  have p0: "p 0 = a" unfolding p_def by simp
  have pn: "p n = b" unfolding p_def using rn0 by simp
  have pd: "dist (p i) (p (Suc i)) = d" for i
  proof -
    have c1: "p i - p (Suc i)
        = (real i / real n - real (Suc i) / real n) *\<^sub>R (b - a)"
      unfolding p_def by (simp add: scaleR_left_diff_distrib)
    have c2: "real i / real n - real (Suc i) / real n = - (1 / real n)"
      using rn0 by (simp add: field_simps)
    have "dist (p i) (p (Suc i)) = norm ((- (1 / real n)) *\<^sub>R (b - a))"
      unfolding dist_norm c1 c2 by (rule refl)
    also have "\<dots> = (1 / real n) * norm (b - a)"
      using rn0 by simp
    finally show ?thesis
      unfolding d_def by (simp add: dist_norm norm_minus_commute)
  qed
  have d0: "0 \<le> d" unfolding d_def using rn0 by simp
  have step: "W a - W (p j) \<le> real j * (C * (d * d))" if "j \<le> n" for j
    using that
  proof (induction j)
    case 0
    show ?case unfolding p0 by simp
  next
    case (Suc j)
    have jn: "j \<le> n" using Suc.prems by simp
    have ih: "W a - W (p j) \<le> real j * (C * (d * d))" by (rule Suc.IH[OF jn])
    have "W (p j) - C * (dist (p j) (p (Suc j)) * dist (p j) (p (Suc j)))
        \<le> W (p (Suc j))"
      unfolding p_def by (rule pin[OF seg[OF jn] seg[OF Suc.prems]])
    then have "W (p j) - W (p (Suc j)) \<le> C * (d * d)"
      unfolding pd by simp
    then show ?case using ih by (simp add: field_simps)
  qed
  have "W a - W b \<le> real n * (C * (d * d))"
    using step[OF order_refl] unfolding pn .
  also have "real n * (C * (d * d)) = C * (dist a b * dist a b) / real n"
    unfolding d_def using rn0 by (simp add: field_simps)
  finally show ?thesis .
qed

lemma pinch_implies_constant:
  fixes W :: "real^'n::finite \<Rightarrow> real" and x y :: "real^'n"
  assumes r0: "0 < r" and C0: "0 \<le> C"
    and pin: "\<And>u w. u \<in> ball x r \<Longrightarrow> w \<in> ball x r \<Longrightarrow>
      W u - C * (dist u w * dist u w) \<le> W w"
    and yb: "y \<in> ball x r"
  shows "W y = W x"
proof -
  have xb: "x \<in> ball x r" using r0 by simp
  have segb: "a + (real i / real n) *\<^sub>R (b - a) \<in> ball x r"
    if ab: "a \<in> ball x r" and bb: "b \<in> ball x r" and inn: "i \<le> n" and n0: "0 < n"
    for a b :: "real^'n" and i n :: nat
  proof -
    define t where "t = real i / real n"
    have t0: "0 \<le> t" unfolding t_def by simp
    have t1: "t \<le> 1" unfolding t_def using inn n0 by simp
    have conv: "a + t *\<^sub>R (b - a) = (1 - t) *\<^sub>R a + t *\<^sub>R b"
      by (simp add: algebra_simps)

    have "(1 - t) *\<^sub>R a + t *\<^sub>R b \<in> ball x r"
      by (rule convexD[OF convex_ball ab bb]) (use t0 t1 in auto)
    then show ?thesis unfolding t_def conv[unfolded t_def] .
  qed
  have half: "W u - W w \<le> C * (dist u w * dist u w) / real n"
    if ub: "u \<in> ball x r" and wb: "w \<in> ball x r" and n0: "0 < n"
    for u w :: "real^'n" and n :: nat
  proof (rule pinch_segment_bound[OF C0 n0 pin])
    fix i assume "i \<le> n"
    then show "u + (real i / real n) *\<^sub>R (w - u) \<in> ball x r"
      by (rule segb[OF ub wb _ n0])
  qed
  have zero: "W u \<le> W w"
    if ub: "u \<in> ball x r" and wb: "w \<in> ball x r" for u w :: "real^'n"
  proof (rule ccontr)
    assume "\<not> W u \<le> W w"
    then have pos: "0 < W u - W w" by simp
    obtain n :: nat where nn: "C * (dist u w * dist u w) / (W u - W w) < real n"
      using reals_Archimedean2 by blast
    have nneg: "0 \<le> C * (dist u w * dist u w) / (W u - W w)"
      using C0 pos by (simp add: zero_le_mult_iff)
    have n0: "0 < n" using nn nneg by simp
    have h1: "W u - W w \<le> C * (dist u w * dist u w) / real n"
      by (rule half[OF ub wb n0])
    have h2: "C * (dist u w * dist u w) / real n < W u - W w"
      using nn pos n0 by (simp add: field_simps)
    show False using h1 h2 by linarith
  qed
  show ?thesis using zero[OF yb xb] zero[OF xb yb] by linarith
qed

text \<open>Three ingredients for the second horn.

  First, a quadratic form is bounded below by a multiple of the squared
  norm --- the constant \<open>C\<close> that \<open>pinch_implies_constant\<close> consumes.

  Second, the pinch itself.  At a tilted minimiser whose gradient
  vanishes, the first-order terms of the minimality inequality cancel
  identically, because the test function is exactly quadratic: expanding
  around the minimiser, the cross term is \<open>\<langle>u, Mv\<rangle>\<close> and the tilt
  contributes \<open>\<langle>\<eta>, u\<rangle>\<close>, and \<open>Mv + \<eta> = 0\<close> is precisely the statement
  that they cancel.  What is left is purely quadratic.

  Third, the singular case is free.  If \<open>M\<close> is not invertible then it is
  not surjective, so some \<open>u\<close> is missed; a small multiple of \<open>u\<close> is then
  a tilt for which \<open>M z + \<eta> = 0\<close> has no solution at all, so the gradient
  at the tilted minimiser cannot vanish and the first horn fires
  instead.  The second horn therefore only has to be run for invertible
  \<open>M\<close>, which is what makes the tilted minimisers sweep out a whole
  neighbourhood.\<close>

lemma quad_form_bounded_below:
  fixes M :: "real^'n::finite^'n"
  obtains C where "0 \<le> C"
    and "\<And>u :: real^'n. - (C * (norm u * norm u)) \<le> (u \<bullet> (M *v u)) / 2"
proof -
  have bl: "bounded_linear ((*v) M)" by (rule matrix_vector_mul_bounded_linear)
  define C where "C = onorm ((*v) M)"
  have C0: "0 \<le> C" unfolding C_def by (rule onorm_pos_le[OF bl])
  have key: "- (C * (norm u * norm u)) \<le> (u \<bullet> (M *v u)) / 2"
    for u :: "real^'n"
  proof -
    have cs: "\<bar>u \<bullet> (M *v u)\<bar> \<le> norm u * norm (M *v u)"
      by (rule Cauchy_Schwarz_ineq2)
    have on: "norm (M *v u) \<le> C * norm u"
      unfolding C_def by (rule onorm[OF bl])
    have m: "norm u * norm (M *v u) \<le> norm u * (C * norm u)"
      by (rule mult_left_mono[OF on norm_ge_zero])
    have eq: "norm u * (C * norm u) = C * (norm u * norm u)"
      by (simp add: mult.assoc mult.left_commute)
    have ab: "\<bar>u \<bullet> (M *v u)\<bar> \<le> C * (norm u * norm u)"
      using cs m eq by linarith
    have nn: "0 \<le> C * (norm u * norm u)"
      by (rule mult_nonneg_nonneg[OF C0
            mult_nonneg_nonneg[OF norm_ge_zero norm_ge_zero]])
    show ?thesis using ab[unfolded abs_le_iff] nn by linarith
  qed
  show ?thesis by (rule that[OF C0]) (use key in blast)
qed

lemma quad_minimality_pinch:
  fixes W :: "real^'n::finite \<Rightarrow> real" and M :: "real^'n^'n"
    and x y \<eta> w :: "real^'n" and C :: real
  assumes sym: "transpose M = M"
    and Cb: "\<And>u :: real^'n. - (C * (norm u * norm u)) \<le> (u \<bullet> (M *v u)) / 2"
    and grad0: "M *v (y - x) + \<eta> = 0"
    and mn: "W y - (((y - x) \<bullet> (M *v (y - x))) / 2 + \<eta> \<bullet> (y - x))
      \<le> W w - (((w - x) \<bullet> (M *v (w - x))) / 2 + \<eta> \<bullet> (w - x))"
  shows "W y - C * (dist y w * dist y w) \<le> W w"
proof -
  define v where "v = y - x"
  define u where "u = w - y"
  have wx: "w - x = v + u" unfolding v_def u_def by simp
  have s1: "v \<bullet> (M *v u) = u \<bullet> (M *v v)"
  proof -
    have "v \<bullet> (M *v u) = (transpose M *v v) \<bullet> u"
      by (rule inner_transpose_matrix)
    also have "\<dots> = (M *v v) \<bullet> u" using sym by simp
    finally show ?thesis by (simp add: inner_commute)
  qed
  have expand: "(w - x) \<bullet> (M *v (w - x))
      = v \<bullet> (M *v v) + 2 * (u \<bullet> (M *v v)) + u \<bullet> (M *v u)"
    unfolding wx using s1
    by (simp add: matrix_vector_right_distrib inner_add_left inner_add_right)
  have etaw: "\<eta> \<bullet> (w - x) = \<eta> \<bullet> v + \<eta> \<bullet> u"
    unfolding wx by (rule inner_add_right)
  have kill: "u \<bullet> (M *v v) + \<eta> \<bullet> u = 0"
  proof -
    have z: "M *v v + \<eta> = 0" unfolding v_def by (rule grad0)
    have "u \<bullet> (M *v v) + \<eta> \<bullet> u = u \<bullet> (M *v v + \<eta>)"
      by (simp add: inner_add_right inner_commute)
    also have "\<dots> = u \<bullet> (0 :: real^'n)" using z by simp
    also have "\<dots> = 0" by simp
    finally show ?thesis .
  qed
  have main: "W y - W w \<le> - ((u \<bullet> (M *v u)) / 2)"
  proof -
    have "W y - W w \<le> (((y - x) \<bullet> (M *v (y - x))) / 2 + \<eta> \<bullet> (y - x))
        - (((w - x) \<bullet> (M *v (w - x))) / 2 + \<eta> \<bullet> (w - x))"
      using mn by linarith
    also have "\<dots> = - ((u \<bullet> (M *v u)) / 2 + (u \<bullet> (M *v v) + \<eta> \<bullet> u))"
      unfolding expand etaw v_def[symmetric] by (simp add: field_simps)
    also have "\<dots> = - ((u \<bullet> (M *v u)) / 2)" unfolding kill by simp
    finally show ?thesis .
  qed
  have cb: "- (C * (norm u * norm u)) \<le> (u \<bullet> (M *v u)) / 2" by (rule Cb)
  have dyw: "dist y w = norm u"
    unfolding u_def by (simp add: dist_norm norm_minus_commute)
  show ?thesis using main cb unfolding dyw by linarith
qed

lemma singular_matrix_avoids_range:
  fixes M :: "real^'n::finite^'n"
  assumes ni: "\<not> invertible M" and d0: "0 < \<delta>"
  obtains \<eta> where "norm \<eta> < \<delta>" and "\<And>z :: real^'n. M *v z + \<eta> \<noteq> 0"
proof -
  have ns: "\<not> surj ((*v) M)"
  proof
    assume "surj ((*v) M)"
    then have "\<exists>B. M ** B = mat 1"
      using matrix_right_invertible_surjective by blast
    then show False using ni invertible_right_inverse by blast
  qed
  obtain u :: "real^'n" where nu: "\<And>z :: real^'n. u \<noteq> M *v z"
    using ns unfolding surj_def by blast
  have u0: "u \<noteq> 0" using nu[of 0] by simp
  have nu0: "0 < norm u" using u0 by simp
  define c where "c = \<delta> / (2 * norm u)"
  have c0: "0 < c" unfolding c_def using d0 nu0 by simp
  have nrm: "norm ((- c) *\<^sub>R u) = c * norm u" using c0 by simp
  have lt: "norm ((- c) *\<^sub>R u) < \<delta>"
    unfolding nrm c_def using nu0 d0 by (simp add: field_simps)
  have nz: "M *v z + (- c) *\<^sub>R u \<noteq> 0" for z :: "real^'n"
  proof
    assume "M *v z + (- c) *\<^sub>R u = 0"
    then have mz: "M *v z = c *\<^sub>R u" by (simp add: algebra_simps)
    have "M *v ((1 / c) *\<^sub>R z) = (1 / c) *\<^sub>R (M *v z)"
      by (rule matrix_vector_mult_scaleR)
    also have "\<dots> = (1 / c) *\<^sub>R (c *\<^sub>R u)" unfolding mz by (rule refl)
    also have "\<dots> = u" using c0 by simp
    finally have "u = M *v ((1 / c) *\<^sub>R z)" by (rule sym)
    then show False using nu by blast
  qed
  show ?thesis by (rule that[OF lt]) (use nz in blast)
qed

text \<open>The sweep.  With \<open>M\<close> invertible the tilt \<open>\<eta> := -M(y - x)\<close> selects
  \<open>y\<close> itself as the tilted minimiser: whatever minimiser \<open>y'\<close> the
  machinery returns, the second horn says \<open>M(y' - x) + \<eta> = 0\<close>, i.e.
  \<open>M(y' - x) = M(y - x)\<close>, and injectivity forces \<open>y' = y\<close>.  So the pinch
  is available at every point of a neighbourhood of \<open>x\<close>, not just at the
  minimisers of one fixed tilt --- and that is exactly the hypothesis of
  \<open>pinch_implies_constant\<close>.\<close>

text \<open>\<open>trace_sum_matrix\<close> is \<open>trace_matrix_sum\<close> from
  \<open>Matrix_Algebra\<close>.\<close>

text \<open>\<open>inner_matrix_transpose\<close> is the square case of \<open>inner_transpose_matrix\<close>
  from \<open>Symmetric_Spectral\<close>.\<close>

lemma orthonormal_inj:
  fixes b :: "nat \<Rightarrow> real^'n::finite"
  assumes orth: "\<And>i j. i < m \<Longrightarrow> j < m \<Longrightarrow> b i \<bullet> b j = (if i = j then 1 else 0)"
  shows "inj_on b {..<m}"
  by (rule inj_onI) (metis lessThan_iff orth zero_neq_one)

lemma orthonormal_dim_span:
  fixes b :: "nat \<Rightarrow> real^'n::finite"
  assumes orth: "\<And>i j. i < m \<Longrightarrow> j < m \<Longrightarrow> b i \<bullet> b j = (if i = j then 1 else 0)"
  shows "dim (span (b ` {..<m})) = m"
proof -
  have "pairwise orthogonal (b ` {..<m})"
    using orth by (auto simp: pairwise_def orthogonal_def)
  moreover have "0 \<notin> b ` {..<m}"
    using orth by (metis imageE inner_zero_left lessThan_iff zero_neq_one)
  ultimately have "independent (b ` {..<m})"
    by (rule pairwise_orthogonal_independent)
  then show ?thesis
    using card_image[OF orthonormal_inj[OF orth]] by (simp add: dim_eq_card_independent)
qed

text \<open>The square of the field is again a field of the same shape with the
  direction rescaled, and the rescaled direction still has norm \<open>\<le> 1\<close> because
  \<open>(2 - a) * a = 1 - (a-1)\<^sup>2 \<le> 1\<close>.  That is what makes the clamped field
  feasible everywhere, which the Euler-limit argument in the application demands.\<close>

lemma tanpU_sq_norm_le:
  fixes u :: "real^'n::finite"
  assumes u1: "norm u \<le> 1"
  shows "norm (sqrt (2 - u \<bullet> u) *\<^sub>R u) \<le> 1"
proof -
  define a where "a = u \<bullet> u"
  have a0: "0 \<le> a" unfolding a_def by simp
  have anorm: "a = (norm u)\<^sup>2" unfolding a_def by (simp add: dot_square_norm)
  have a1: "a \<le> 1" unfolding anorm using u1 by (simp add: power_le_one)
  have a2: "0 \<le> 2 - a" using a1 by linarith
  have e1: "norm (sqrt (2 - a) *\<^sub>R u) = sqrt (2 - a) * norm u"
    using a2 by simp
  have e2: "(sqrt (2 - a) * norm u)\<^sup>2 = (2 - a) * a"
    using a2 anorm by (simp add: power_mult_distrib)
  have le1: "(2 - a) * a \<le> 1"
  proof -
    have "0 \<le> (a - 1)\<^sup>2" by simp
    then show ?thesis by (simp add: power2_eq_square algebra_simps)
  qed
  have nn: "0 \<le> sqrt (2 - a) * norm u" using a2 by simp
  have "(sqrt (2 - a) * norm u)\<^sup>2 \<le> 1\<^sup>2" using e2 le1 by simp
  then have "sqrt (2 - a) * norm u \<le> 1"
    by (rule power2_le_imp_le) simp
  then show ?thesis unfolding a_def[symmetric] e1 .
qed

lemma orthonormal_family_containing:
  fixes x0 :: "real^'n::finite"
  assumes u: "x0 \<bullet> x0 = 1" and m: "m \<le> CARD('n)" and m0: "0 < m"
  shows "\<exists>b :: nat \<Rightarrow> real^'n. b 0 = x0
      \<and> (\<forall>i < m. \<forall>j < m. b i \<bullet> b j = (if i = j then 1 else 0))"
proof -
  obtain S where S: "x0 \<in> S" "pairwise orthogonal S" "\<And>x. x \<in> S \<Longrightarrow> x \<bullet> x = 1"
    and cardS: "card S = CARD('n)"
    using vector_in_orthonormal_basis[of x0] u by (metis DIM_cart DIM_real mult.right_neutral norm_eq_1)
  have "finite S"
    using cardS by (intro card_ge_0_finite) simp
  then obtain f where f: "bij_betw f {0..<card (S - {x0})} (S - {x0})"
    using ex_bij_betw_nat_finite by blast
  have cS: "card (S - {x0}) = CARD('n) - 1"
    using cardS S(1) \<open>finite S\<close> by simp
  have fS: "f k \<in> S - {x0}" if "Suc k < CARD('n)" for k
    using that bij_betw_apply[OF f] cS by auto
  have finj: "k = l" if "f k = f l" "Suc k < CARD('n)" "Suc l < CARD('n)" for k l
    using that bij_betw_imp_inj_on[OF f] cS by (auto simp: inj_on_def)
  define b where "b = case_nat x0 f"
  have bS: "b i \<in> S" if "i < CARD('n)" for i
    using that S(1) fS by (cases i) (auto simp: b_def)
  have binj: "b i \<noteq> b j" if "i < CARD('n)" "j < CARD('n)" "i \<noteq> j" for i j
    using that fS finj by (cases i; cases j) (auto simp: b_def)
  have "b i \<bullet> b j = (if i = j then 1 else 0)" if "i < m" "j < m" for i j
    using that m bS[of i] bS[of j] binj[of i j] S(2,3)
    by (auto simp: pairwise_def orthogonal_def)
  then show ?thesis
    by (intro exI[of _ b]) (simp add: b_def)
qed

text \<open>The two envelope-form hypotheses in the shape the doubling produces:
  on an open \<open>\<Omega>\<close> inside \<open>K\<close>, a subsolution and supersolution in the
  envelope-free sense are also envelope sub/supersolutions, letting the
  doubling argument run where the \<open>\<delta> \<rightarrow> 0\<close> passage is legitimate.\<close>

text \<open>The supersolution mirror: the sup-convolution is taken of \<open>-w\<close>, the
  summand the doubled functional carries, and the transferred bound
  becomes a local minimum statement for \<open>w\<close> after negation. The
  correction runs the other way, \<open>Ym - \<delta> I\<close>, as with
  \<open>jet_imp_local_min_test_onesided\<close>.\<close>

lemma neg_shift_matrix_apply:
  fixes B :: "real^'n::finite^'n"
  shows "((- B) + \<delta> *\<^sub>R mat 1) *v h = - ((B - \<delta> *\<^sub>R mat 1) *v h)"
proof -
  have e: "(- B) + \<delta> *\<^sub>R mat 1 = - (B - \<delta> *\<^sub>R mat 1)"
    by simp
  show ?thesis
    unfolding e by (rule neg_matrix_vector)
qed

text \<open>Symmetry is a closed condition and so survives the passage to a limit
  (positive semidefiniteness likewise, \<open>closed_psd\<close>).\<close>

lemma closed_symmetric_matrices:
  "closed {a :: real^'n::finite^'n. transpose a = a}"
proof -
  have eq: "{a :: real^'n^'n. transpose a = a}
      = (\<Inter>i. \<Inter>j. {a. a $ j $ i = a $ i $ j})"
    unfolding transpose_def vec_eq_iff by auto
  have "closed {a :: real^'n^'n. a $ j $ i = a $ i $ j}" for i j
    by (intro closed_Collect_eq continuous_on_matrix_entry continuous_on_id)
  thus ?thesis unfolding eq by (intro closed_INT) auto
qed

lemma transpose_limit:
  fixes A :: "nat \<Rightarrow> real^'n::finite^'n"
  assumes conv: "A \<longlonglongrightarrow> A0" and sym: "\<And>i. transpose (A i) = A i"
  shows "transpose A0 = A0"
  using closed_sequentially[OF closed_symmetric_matrices, of A A0] conv sym by blast

text \<open>\<open>transpose_scalar\<close> is HOL-Analysis's; \<open>transpose_add\<close> lives
  further up in this theory.\<close>

text \<open>The bridge between the jets' operator-form Hessian
  \<open>\<lambda>v. f v + c *\<^sub>R v\<close> and the matrix form the family theorem wants:
  taking the matrix of the shifted operator adds \<open>cI\<close>.  Every shifted
  fact then reduces to its unshifted counterpart plus
  \<open>transpose_shift_add\<close>, the shifted positivity fact and \<open>norm_shifted_block\<close>.\<close>

lemma matrix_shift_apply:
  fixes M :: "real^'n::finite^'n"
  shows "(M + c *\<^sub>R mat 1) *v h = M *v h + c *\<^sub>R h"
  by (simp add: matrix_vector_mult_add_rdistrib scaleR_matrix_vector_assoc[symmetric])

lemma norm_shifted_block:
  fixes M :: "real^'n::finite^'n"
  shows "norm (M + c *\<^sub>R mat 1)
      \<le> norm M + \<bar>c\<bar> * norm (mat 1 :: real^'n^'n)"
proof -
  have "norm (M + c *\<^sub>R mat 1) \<le> norm M + norm (c *\<^sub>R (mat 1 :: real^'n^'n))"
    by (rule norm_triangle_ineq)
  moreover have "norm (c *\<^sub>R (mat 1 :: real^'n^'n))
      = \<bar>c\<bar> * norm (mat 1 :: real^'n^'n)"
    by simp
  ultimately show ?thesis by linarith
qed

text \<open>Shifting \<open>Y\<close> down by \<open>cI\<close> and \<open>X\<close> up by \<open>cI\<close> costs the difference
  exactly \<open>2cI\<close>, recovering \<open>Y-X\<close> on cancellation; this is the equation
  behind the asymptotic \<open>psdi\<close> hypothesis, with defect
  \<open>cs\<^sub>i=2c\<^sub>i \<rightarrow> 0\<close>.\<close>

lemma shift_cancel_matrix:
  fixes X Y :: "real^'n::finite^'n"
  shows "(Y - c *\<^sub>R mat 1) - (X + c *\<^sub>R mat 1) + (2*c) *\<^sub>R mat 1 = Y - X"
  by (simp add: vec_eq_iff mat_def axis_def algebra_simps)

lemma affine_linear:
  fixes R :: "real^'n::finite^'n"
  shows "bounded_linear (\<lambda>z :: real^'n. c *\<^sub>R (R *v z))"
proof -
  have "linear (\<lambda>z :: real^'n. c *\<^sub>R (R *v z))"
    by (simp add: linear_iff matrix_vector_right_distrib matrix_vector_mult_scaleR
        scaleR_right_distrib)
  then show ?thesis by (simp add: linear_conv_bounded_linear)
qed

text \<open>Two small facts about the inverse of the dilation, used to transfer
  lower semicontinuity and the bound to the transformed supersolution.\<close>

lemma affine_inv_dist:
  fixes R :: "real^'n::finite^'n" and b :: "real^'n"
  assumes orth: "orthogonal_matrix R" and c0: "0 < c"
  shows "dist ((1/c) *\<^sub>R (transpose R *v (X - b)))
             ((1/c) *\<^sub>R (transpose R *v (Y - b))) = (1/c) * dist X Y"
proof -
  have "orthogonal_matrix (transpose R)"
    using orth by (simp add: orthogonal_matrix_transpose)
  then show ?thesis
    using c0 norm_orthogonal_matrix_vector[of "transpose R" "X - Y"]
    by (simp add: dist_norm matrix_vector_mult_diff_distrib[symmetric]
        scaleR_right_diff_distrib[symmetric] del: transpose_matrix_vector)
qed

text \<open>On \<open>real^'n\<close> compactness is closedness together with a ball bound, so
  one hypothesis supplies both of the ones the transfer needs.  The radius is
  named only where it appears in a conclusion, which is clause (0).\<close>

lemma compact_cball_bound:
  fixes K :: "(real^'n::finite) set"
  assumes cK: "compact K"
  shows "\<exists>rK. 0 \<le> rK \<and> K \<subseteq> cball 0 rK"
  using bounded_pos[THEN iffD1, OF compact_imp_bounded[OF cK]]
  by (auto simp: subset_eq intro: less_imp_le)

subsection \<open>An abstract linear map read through its matrix\<close>

text \<open>Viscosity-solution notions speak of a matrix \<open>H\<close> acting by
  \<open>H *v h\<close> with \<open>transpose H = H\<close>, while the results above produce a
  bounded linear \<open>X\<close> with the abstract symmetry \<open>v \<cdot> X w = w \<cdot> X v\<close>.
  HOL-Analysis's \<open>matrix\<close> bridges the two: it represents \<open>X\<close> faithfully,
  and the abstract symmetry is exactly matrix symmetry, since
  \<open>v \<cdot> (transpose A *v w) = w \<cdot> (A *v v)\<close>.\<close>

lemma matrix_of_symmetric:
  fixes X :: "(real^'n::finite) \<Rightarrow> (real^'n)"
  assumes lin: "linear X" and sym: "\<And>v w. v \<bullet> X w = w \<bullet> X v"
  shows "transpose (matrix X) = matrix X"
proof (subst matrix_eq, rule allI)
  fix w :: "real^'n"
  have pt: "v \<bullet> (transpose (matrix X) *v w) = v \<bullet> (matrix X *v w)"
    for v :: "real^'n"
  proof -
    have "v \<bullet> (transpose (matrix X) *v w) = v \<bullet> (w v* matrix X)"
      by simp
    also have "\<dots> = (w v* matrix X) \<bullet> v" by (rule inner_commute)
    also have "\<dots> = w \<bullet> (matrix X *v v)" by (rule dot_lmul_matrix)
    also have "\<dots> = w \<bullet> X v" unfolding fun_cong[OF matrix_vector_mul(2)[OF lin]] ..
    also have "\<dots> = v \<bullet> X w" by (rule sym[symmetric])
    also have "\<dots> = v \<bullet> (matrix X *v w)" unfolding fun_cong[OF matrix_vector_mul(2)[OF lin]] ..
    finally show ?thesis .
  qed
  have "((transpose (matrix X) *v w) - (matrix X *v w))
      \<bullet> ((transpose (matrix X) *v w) - (matrix X *v w)) = 0"
    using pt[of "(transpose (matrix X) *v w) - (matrix X *v w)"]
    by (simp add: inner_diff_right)
  thus "transpose (matrix X) *v w = matrix X *v w" by simp
qed

text \<open>The other half of the bridge: a symmetric matrix gives a quadratic
  test function.  Symmetry makes the two cross terms of the derivative
  equal, so the factor \<open>1/2\<close> leaves exactly \<open>h \<mapsto> h \<cdot> (H *v z)\<close>.\<close>

lemma has_derivative_quadratic_form:
  fixes H :: "real^'n::finite^'n"
  assumes symH: "transpose H = H"
  shows "((\<lambda>z. (z \<bullet> (H *v z))/2) has_derivative (\<lambda>h. h \<bullet> (H *v z0))) (at z0)"
proof -
  have blH: "bounded_linear ((*v) H)" by (rule matrix_vector_mul_bounded_linear)
  have dH: "(((*v) H) has_derivative ((*v) H)) (at z0)"
    using bounded_linear.has_derivative[OF blH has_derivative_ident] by simp
  have d1: "((\<lambda>z. z \<bullet> (H *v z)) has_derivative
      (\<lambda>h. z0 \<bullet> (H *v h) + h \<bullet> (H *v z0))) (at z0)"
    by (rule has_derivative_inner[OF has_derivative_ident dH])
  have eqd: "(\<lambda>h. z0 \<bullet> (H *v h) + h \<bullet> (H *v z0))
      = (\<lambda>h. 2 * (h \<bullet> (H *v z0)))"
    by (rule ext) (simp add: sym_inner_swap[OF symH])
  have d2: "((\<lambda>z. z \<bullet> (H *v z)) has_derivative (\<lambda>h. 2 * (h \<bullet> (H *v z0))))
      (at z0)"
    using d1 unfolding eqd .
  have "((\<lambda>z. (1/2) *\<^sub>R (z \<bullet> (H *v z))) has_derivative
      (\<lambda>h. (1/2) *\<^sub>R (2 * (h \<bullet> (H *v z0))))) (at z0)"
    by (rule has_derivative_scaleR_right[OF d2])
  thus ?thesis by simp
qed

text \<open>The quadratic test function attached to a jet \<open>(p, H)\<close> at \<open>x\<close>:
  \<open>\<phi> z = p \<cdot> (z - x) + ((z - x) \<cdot> (H *v (z - x)))/2\<close>, with gradient
  field \<open>g z = p + H *v (z - x)\<close>.  These, together with the symmetry of
  \<open>matrix_of_symmetric\<close>, are exactly what a viscosity test-function
  predicate requires of \<open>(\<phi>, g, H)\<close> at \<open>x\<close>.\<close>

lemma quadratic_test_derivative:
  fixes H :: "real^'n::finite^'n" and p x y :: "real^'n"
  assumes symH: "transpose H = H"
  shows "((\<lambda>z. p \<bullet> (z - x) + ((z - x) \<bullet> (H *v (z - x)))/2)
      has_derivative (\<lambda>h. (p + H *v (y - x)) \<bullet> h)) (at y)"
proof -
  have shift: "((\<lambda>z::real^'n. z - x) has_derivative (\<lambda>h. h)) (at y)"
    by (auto intro!: derivative_eq_intros)
  have dq0: "((\<lambda>w. (w \<bullet> (H *v w))/2) has_derivative
      (\<lambda>h. h \<bullet> (H *v (y - x)))) (at (y - x))"
    by (rule has_derivative_quadratic_form[OF symH])
  have dq: "((\<lambda>z. ((z - x) \<bullet> (H *v (z - x)))/2) has_derivative
      (\<lambda>h. h \<bullet> (H *v (y - x)))) (at y)"
    using diff_chain_at[OF shift dq0] by (simp add: comp_def)
  have dl: "((\<lambda>z::real^'n. p \<bullet> (z - x)) has_derivative (\<lambda>h. p \<bullet> h)) (at y)"
    by (auto intro!: derivative_eq_intros)
  have sum: "((\<lambda>z. p \<bullet> (z - x) + ((z - x) \<bullet> (H *v (z - x)))/2)
      has_derivative (\<lambda>h. p \<bullet> h + h \<bullet> (H *v (y - x)))) (at y)"
    by (rule has_derivative_add[OF dl dq])
  have eqf: "(\<lambda>h. p \<bullet> h + h \<bullet> (H *v (y - x)))
      = (\<lambda>h. (p + H *v (y - x)) \<bullet> h)"
    by (rule ext) (simp add: inner_add_right inner_commute)
  show ?thesis using sum unfolding eqf .
qed

lemma quadratic_test_grad_derivative:
  fixes H :: "real^'n::finite^'n" and p x y :: "real^'n"
  shows "((\<lambda>z. p + H *v (z - x)) has_derivative (\<lambda>h. H *v h)) (at y)"
  using bounded_linear.has_derivative[OF matrix_vector_mul_bounded_linear[of H]
      has_derivative_diff[OF has_derivative_ident has_derivative_const[of x]]]
  by (auto intro!: derivative_eq_intros)

subsection \<open>A difference of linear maps, read as a matrix\<close>

text \<open>\<open>sums_matrix_inequality\<close> gives \<open>v \<cdot> X v \<le> v \<cdot> Y v\<close> for bounded linear
  \<open>X\<close>, \<open>Y\<close>, while degenerate ellipticity of the operator in the application wants \<open>psd (N - M)\<close> for matrices.
  Since \<open>psd\<close> is symmetry plus \<open>0 \<le> x \<cdot> (a *v x)\<close>, the two are the same
  statement once represented by \<open>matrix\<close>.\<close>

lemma matrix_diff_vec:
  fixes X Y :: "(real^'n::finite) \<Rightarrow> (real^'n)"
  assumes lX: "linear X" and lY: "linear Y"
  shows "(matrix Y - matrix X) *v v = Y v - X v"
proof -
  have "(matrix Y - matrix X) *v v = matrix Y *v v - matrix X *v v"
    by (simp add: matrix_vector_mult_diff_rdistrib)
  thus ?thesis
    unfolding fun_cong[OF matrix_vector_mul(2)[OF lX]] fun_cong[OF matrix_vector_mul(2)[OF lY]] .
qed

(*<*)
end
(*>*)
