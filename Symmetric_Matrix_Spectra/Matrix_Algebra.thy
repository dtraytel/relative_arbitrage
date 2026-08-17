
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

lemma matrix_vector_neg_left:
  fixes B :: "real^'n::finite^'n"
  shows "(- B) *v x = - (B *v x)"
  by (simp add: matrix_vector_mult_def vec_eq_iff sum_negf)

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

lemma matrix_vector_mult_diff_gen:
  fixes Z :: "real^'n::finite^'n"
  shows "Z *v (u - v) = Z *v u - Z *v v"
  by (simp add: matrix_vector_mult_def vec_eq_iff sum_subtractf algebra_simps)

lemma matrix_vector_mult_scaleR_gen:
  fixes Z :: "real^'n::finite^'n"
  shows "Z *v (s *\<^sub>R u) = s *\<^sub>R (Z *v u)"
  by (simp add: matrix_vector_mult_def vec_eq_iff sum_distrib_left
      algebra_simps)

lemma inner_matrix_sym:
  fixes Z :: "real^'n::finite^'n"
  assumes s: "transpose Z = Z"
  shows "v \<bullet> (Z *v z) = z \<bullet> (Z *v v)"
proof -
  have zij: "Z $ i $ j = Z $ j $ i" for i j
  proof -
    have "Z $ i $ j = (transpose Z) $ i $ j" using s by simp
    also have "\<dots> = Z $ j $ i" by (simp add: transpose_def)
    finally show ?thesis .
  qed
  have "v \<bullet> (Z *v z) = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. v $ i * (Z $ i $ j * z $ j))"
    by (simp add: inner_vec_def matrix_vector_mult_def sum_distrib_left)
  also have "\<dots> = (\<Sum>j\<in>UNIV. \<Sum>i\<in>UNIV. v $ i * (Z $ i $ j * z $ j))"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>j\<in>UNIV. \<Sum>i\<in>UNIV. z $ j * (Z $ j $ i * v $ i))"
    by (simp add: zij mult.commute mult.left_commute)
  also have "\<dots> = z \<bullet> (Z *v v)"
    by (simp add: inner_vec_def matrix_vector_mult_def sum_distrib_left)
  finally show ?thesis .
qed

lemma norm_le_card_Basis_bound:
  fixes M :: "'a::euclidean_space"
  assumes b: "\<And>e. e \<in> Basis \<Longrightarrow> \<bar>M \<bullet> e\<bar> \<le> c"
  shows "norm M \<le> real (card (Basis :: 'a set)) * c"
proof -
  have "norm M \<le> (\<Sum>e\<in>(Basis :: 'a set). \<bar>M \<bullet> e\<bar>)"
    by (rule norm_le_l1)
  also have "\<dots> \<le> (\<Sum>e\<in>(Basis :: 'a set). c)"
    by (rule sum_mono) (rule b)
  also have "\<dots> = real (card (Basis :: 'a set)) * c"
    by simp
  finally show ?thesis .
qed

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

lemma sum_sq_le_sq_sum:
  fixes f :: "'b \<Rightarrow> real"
  assumes nn: "\<And>i. i \<in> F \<Longrightarrow> 0 \<le> f i"
  shows "(\<Sum>i\<in>F. (f i)\<^sup>2) \<le> (\<Sum>i\<in>F. f i)\<^sup>2"
proof (cases "finite F")
  case True
  then show ?thesis using nn
  proof (induction F)
    case empty
    show ?case by simp
  next
    case (insert a F)
    have fa: "0 \<le> f a" using insert.prems by simp
    have sn: "0 \<le> (\<Sum>i\<in>F. f i)"
      using insert.prems by (intro sum_nonneg) simp
    have "(\<Sum>i\<in>insert a F. (f i)\<^sup>2) = (f a)\<^sup>2 + (\<Sum>i\<in>F. (f i)\<^sup>2)"
      using insert.hyps by simp
    also have "\<dots> \<le> (f a)\<^sup>2 + (\<Sum>i\<in>F. f i)\<^sup>2"
      using insert by simp
    also have "\<dots> \<le> (f a)\<^sup>2 + 2 * f a * (\<Sum>i\<in>F. f i) + (\<Sum>i\<in>F. f i)\<^sup>2"
      using fa sn by simp
    also have "\<dots> = (f a + (\<Sum>i\<in>F. f i))\<^sup>2"
      by (simp add: power2_eq_square algebra_simps)
    finally show ?case using insert.hyps by simp
  qed
next
  case False
  then show ?thesis by simp
qed

subsection \<open>The calculus the doubling and comparison arguments consume\<close>

text \<open>Trace, transpose, matrix-vector and matrix-matrix identities, the
  bounded-linear and continuity facts that go with them, and the affine and
  quadratic-form bookkeeping around them.  All of it was written as steps of
  a viscosity-comparison proof and none of it is about one.\<close>

text \<open>
  For the ball \<open>K = cball 0 r\<close> the candidate value function is
  \<open>v x = max (r\<^sup>2 - \<bar>x\<bar>\<^sup>2) 0 / (n - k)\<close>, whose gradient at \<open>x\<close> is
  \<open>- (2/(n-k)) *\<^sub>R x\<close> and whose Hessian is the constant matrix
  \<open>- (2/(n-k)) *\<^sub>R mat 1\<close>.  Then \<open>F(\<nabla>v x, \<nabla>\<^sup>2 v x) = 1\<close> for all
  interior points \<open>x \<noteq> 0\<close>.
\<close>

lemma neg_half_trace_ball_op:
  fixes a :: "real^'n^'n"
  assumes c_pos: "0 < c"
  shows "- trace ((- (2 / c) *\<^sub>R mat 1) ** a) / 2 = trace a / c"
proof -
  have "((- (2 / c) *\<^sub>R mat 1) ** a) $ i $ i = - (2 / c) * a $ i $ i" for i
    by (simp add: matrix_matrix_mult_def mat_def if_distrib if_distribR
        cong: if_cong)
  then have "trace ((- (2 / c) *\<^sub>R mat 1) ** a) = - ((2 / c) * trace a)"
    by (simp add: trace_def sum_distrib_left sum_negf)
  then show ?thesis
    using c_pos by (simp add: field_simps)
qed

lemma local_min_gradient_zero:
  fixes \<psi> :: "real^'n \<Rightarrow> real"
  assumes deriv: "(\<psi> has_derivative (\<lambda>h. g \<bullet> h)) (at x)"
    and min: "eventually (\<lambda>y. \<psi> x \<le> \<psi> y) (at x)"
  shows "g = 0"
proof -
  have "(\<lambda>h. g \<bullet> h) = (\<lambda>h. 0)"
    by (rule has_derivative_local_min[OF deriv min])
  then have "g \<bullet> g = 0"
    using fun_cong[of "(\<lambda>h. g \<bullet> h)" "(\<lambda>h. 0)" g] by simp
  then show ?thesis
    by simp
qed

lemma local_min_hessian_psd:
  fixes \<psi> :: "real^'n \<Rightarrow> real" and g :: "real^'n \<Rightarrow> real^'n"
    and H :: "real^'n^'n"
  assumes e_pos: "0 < e"
    and deriv: "\<And>y. y \<in> ball x e \<Longrightarrow> (\<psi> has_derivative (\<lambda>h. g y \<bullet> h)) (at y)"
    and hess: "(g has_derivative (\<lambda>h. H *v h)) (at x)"
    and min: "\<And>y. y \<in> ball x e \<Longrightarrow> \<psi> x \<le> \<psi> y"
  shows "0 \<le> h \<bullet> (H *v h)"
proof (cases "h = 0")
  case True
  then show ?thesis
    by simp
next
  case False
  have x_mem: "x \<in> ball x e"
    using e_pos by simp
  have ev_min: "eventually (\<lambda>y. \<psi> x \<le> \<psi> y) (at x)"
    using min e_pos
    by (auto simp: eventually_at dist_commute intro!: exI[of _ e])
  have gx0: "g x = 0"
    by (rule local_min_gradient_zero[OF deriv[OF x_mem] ev_min])
  define A where "A = h \<bullet> (H *v h)"
  define nh where "nh = norm h"
  have nh_pos: "0 < nh"
    using False by (simp add: nh_def)
  define d where "d = e / nh"
  have d_pos: "0 < d"
    using e_pos nh_pos by (simp add: d_def)
  have mem: "x + t *\<^sub>R h \<in> ball x e" if "\<bar>t\<bar> < d" for t
  proof -
    have "dist x (x + t *\<^sub>R h) = \<bar>t\<bar> * nh"
      by (simp add: dist_norm nh_def)
    also have "\<dots> < d * nh"
      using that nh_pos by (simp add: mult_strict_right_mono)
    also have "\<dots> = e"
      using nh_pos by (simp add: d_def)
    finally show ?thesis
      by simp
  qed
  have f_deriv: "((\<lambda>s. \<psi> (x + s *\<^sub>R h)) has_real_derivative
      (g (x + t *\<^sub>R h) \<bullet> h)) (at t)"
    if t: "\<bar>t\<bar> < d" for t
  proof -
    have 1: "((\<lambda>s. x + s *\<^sub>R h) has_derivative (\<lambda>s. s *\<^sub>R h)) (at t)"
      by (auto intro!: derivative_eq_intros)
    have 2: "(\<psi> has_derivative (\<lambda>h'. g (x + t *\<^sub>R h) \<bullet> h')) (at (x + t *\<^sub>R h))"
      by (rule deriv[OF mem[OF t]])
    have "((\<lambda>s. \<psi> (x + s *\<^sub>R h)) has_derivative
        (\<lambda>s. g (x + t *\<^sub>R h) \<bullet> (s *\<^sub>R h))) (at t)"
      using diff_chain_at[OF 1 2] by (simp add: o_def)
    then have "((\<lambda>s. \<psi> (x + s *\<^sub>R h)) has_derivative
        (\<lambda>s. s * (g (x + t *\<^sub>R h) \<bullet> h))) (at t)"
      by (simp add: mult_ac)
    then show ?thesis
      unfolding has_field_derivative_def
      by (rule has_derivative_eq_rhs) (simp add: fun_eq_iff mult_ac)
  qed
  show ?thesis
  proof (rule ccontr)
    assume "\<not> 0 \<le> h \<bullet> (H *v h)"
    then have A_neg: "A < 0"
      by (simp add: A_def)
    have flim: "filterlim (\<lambda>t :: real. x + t *\<^sub>R h) (at x) (at 0)"
    proof -
      have "((\<lambda>t :: real. x + t *\<^sub>R h) \<longlongrightarrow> x) (at 0)"
        by (auto intro!: tendsto_eq_intros)
      moreover have "eventually (\<lambda>t :: real. x + t *\<^sub>R h \<noteq> x) (at 0)"
        using False by (auto simp: eventually_at_filter)
      ultimately show ?thesis
        by (simp add: filterlim_at)
    qed
    have hd: "((\<lambda>y. (1 / norm (y - x)) *\<^sub>R (g y - (g x + H *v (y - x)))) \<longlongrightarrow> 0) (at x)"
      using hess unfolding has_derivative_at2 by blast
    have comp: "((\<lambda>t. (1 / norm ((x + t *\<^sub>R h) - x)) *\<^sub>R
        (g (x + t *\<^sub>R h) - (g x + H *v ((x + t *\<^sub>R h) - x)))) \<longlongrightarrow> 0) (at 0)"
      by (rule filterlim_compose[OF hd flim])
    then have comp2: "((\<lambda>t. (1 / (\<bar>t\<bar> * nh)) *\<^sub>R
        (g (x + t *\<^sub>R h) - t *\<^sub>R (H *v h))) \<longlongrightarrow> 0) (at 0)"
      by (simp add: gx0 matrix_vector_mult_scaleR nh_def)
    have inner_lim: "((\<lambda>t. ((1 / (\<bar>t\<bar> * nh)) *\<^sub>R
        (g (x + t *\<^sub>R h) - t *\<^sub>R (H *v h))) \<bullet> h) \<longlongrightarrow> 0) (at 0)"
      using tendsto_inner[OF comp2 tendsto_const] by simp
    define E where
      "E = (\<lambda>t. ((1 / (\<bar>t\<bar> * nh)) *\<^sub>R (g (x + t *\<^sub>R h) - t *\<^sub>R (H *v h))) \<bullet> h)"
    have E_lim: "(E \<longlongrightarrow> 0) (at 0)"
      using inner_lim unfolding E_def .
    have E_val: "g (x + t *\<^sub>R h) \<bullet> h = t * A + (\<bar>t\<bar> * nh) * E t"
      if "t \<noteq> 0" for t
    proof -
      have nz: "\<bar>t\<bar> * nh \<noteq> 0"
        using that nh_pos by simp
      have "E t = (g (x + t *\<^sub>R h) \<bullet> h - t * A) / (\<bar>t\<bar> * nh)"
        by (simp add: E_def A_def inner_diff_left inner_diff_right
            inner_commute)
      with nz show ?thesis
        by (simp add: field_simps)
    qed
    define eps where "eps = - A / (2 * nh)"
    have eps_pos: "0 < eps"
      using A_neg nh_pos by (simp add: eps_def divide_neg_pos)
    have "eventually (\<lambda>t. \<bar>E t\<bar> < eps) (at 0)"
      using tendstoD[OF E_lim eps_pos] by (simp add: dist_real_def)
    then obtain dd where dd_pos: "0 < dd"
      and dd: "\<And>t. t \<noteq> 0 \<Longrightarrow> \<bar>t\<bar> < dd \<Longrightarrow> \<bar>E t\<bar> < eps"
      by (auto simp: eventually_at dist_real_def)
    define t0 where "t0 = min d dd / 2"
    have t0_pos: "0 < t0"
      using d_pos dd_pos by (simp add: t0_def)
    have t0d: "t0 < d" and t0dd: "t0 < dd"
      using d_pos dd_pos by (auto simp: t0_def)
    have fneg: "g (x + s *\<^sub>R h) \<bullet> h < 0" if s: "0 < s" "s \<le> t0" for s
    proof -
      have s_ne: "s \<noteq> 0" and s_dd: "\<bar>s\<bar> < dd"
        using s t0dd by auto
      have Es: "\<bar>E s\<bar> < eps"
        by (rule dd[OF s_ne s_dd])
      have gsh: "g (x + s *\<^sub>R h) \<bullet> h = s * A + (s * nh) * E s"
        using E_val[OF s_ne] s(1) by (simp add: abs_of_pos)
      have snh_pos: "0 < s * nh"
        using s(1) nh_pos by simp
      have "(s * nh) * E s < (s * nh) * eps"
        using Es snh_pos by (intro mult_strict_left_mono) auto
      moreover have "(s * nh) * eps = s * (- A / 2)"
        using nh_pos by (simp add: eps_def)
      ultimately have "g (x + s *\<^sub>R h) \<bullet> h < s * A + s * (- A / 2)"
        unfolding gsh by linarith
      also have "\<dots> = s * (A / 2)"
        by (simp add: algebra_simps)
      also have "\<dots> < 0"
        using s(1) A_neg by (intro mult_pos_neg) auto
      finally show ?thesis .
    qed
    have cont: "continuous_on {0..t0} (\<lambda>s. \<psi> (x + s *\<^sub>R h))"
    proof -
      have "isCont (\<lambda>s. \<psi> (x + s *\<^sub>R h)) s" if "s \<in> {0..t0}" for s
      proof -
        have "\<bar>s\<bar> < d"
          using that t0d by auto
        from f_deriv[OF this] show ?thesis
          by (rule DERIV_isCont)
      qed
      then show ?thesis
        by (auto intro: continuous_at_imp_continuous_on)
    qed
    obtain \<xi> where xi: "0 < \<xi>" "\<xi> < t0"
      and mvt_eq: "\<psi> (x + t0 *\<^sub>R h) - \<psi> (x + 0 *\<^sub>R h)
        = (g (x + \<xi> *\<^sub>R h) \<bullet> h) * (t0 - 0)"
    proof -
      have derf: "((\<lambda>s. \<psi> (x + s *\<^sub>R h)) has_derivative
          (\<lambda>y. y * (g (x + s *\<^sub>R h) \<bullet> h))) (at s)"
        if "0 < s" "s < t0" for s
      proof -
        have "\<bar>s\<bar> < d"
          using that t0d by auto
        from f_deriv[OF this, unfolded has_field_derivative_def]
        show ?thesis
          by (rule has_derivative_eq_rhs) (simp add: fun_eq_iff mult_ac)
      qed
      from mvt[OF t0_pos cont derf] obtain \<xi>
        where "0 < \<xi>" "\<xi> < t0"
          "\<psi> (x + t0 *\<^sub>R h) - \<psi> (x + 0 *\<^sub>R h)
            = (t0 - 0) * (g (x + \<xi> *\<^sub>R h) \<bullet> h)"
        by blast
      then show thesis
        by (intro that[of \<xi>]) (auto simp: algebra_simps)
    qed
    have "\<psi> (x + 0 *\<^sub>R h) \<le> \<psi> (x + t0 *\<^sub>R h)"
      using min[OF mem[of t0]] t0d t0_pos by simp
    with mvt_eq have "0 \<le> (g (x + \<xi> *\<^sub>R h) \<bullet> h) * t0"
      by simp
    with t0_pos have "0 \<le> g (x + \<xi> *\<^sub>R h) \<bullet> h"
      by (simp add: zero_le_mult_iff)
    with fneg[of \<xi>] xi show False
      by simp
  qed
qed

lemma quadratic_gradient:
  fixes y :: "real^'n"
  assumes c_pos: "0 < (c::real)"
  shows "((\<lambda>y :: real^'n. (r\<^sup>2 - y \<bullet> y) / c) has_derivative
      (\<lambda>h. (- (2 / c) *\<^sub>R y) \<bullet> h)) (at y)"
  using c_pos
  by (auto intro!: derivative_eq_intros simp: inner_commute divide_simps)

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

lemma norm_less_of_ball:
  fixes z :: "real^'n::finite"
  assumes z: "norm z < r" and y: "y \<in> ball z (r - norm z)"
  shows "norm y < r"
proof -
  have "norm y \<le> norm (y - z) + norm z"
    using norm_triangle_sub[of y z] by simp
  also have "\<dots> < (r - norm z) + norm z"
    using y by (simp add: dist_norm norm_minus_commute)
  finally show ?thesis by simp
qed

text \<open>Lemma 2.2 of \<^cite>\<open>LaiShkolnikovSoner\<close> of the paper assumes the set \<open>S\<close> of admissible covariances is
  bounded.  For the paper's \<open>S\<close> that is a purely linear-algebraic fact,
  provable without any probability: \<open>psd a\<close> bounds the diagonal below by
  \<open>0\<close> and \<open>eigen_ub a L\<close> bounds it above by \<open>L\<close>, testing the quadratic form
  at the coordinate vectors.\<close>

lemma inner_axis_one:
  fixes y :: "real^'n::finite"
  shows "axis i (1 :: real) \<bullet> y = y $ i"
  by (simp add: inner_axis')

lemma matrix_vector_axis_one:
  fixes a :: "real^'n::finite^'n"
  shows "(a *v axis i (1 :: real)) $ l = a $ l $ i"
proof -
  have "(a *v axis i (1 :: real)) $ l
      = (\<Sum>j\<in>UNIV. a $ l $ j * (if j = i then 1 else 0))"
    unfolding matrix_vector_mult_def axis_def by simp
  also have "\<dots> = (\<Sum>j\<in>UNIV. if j = i then a $ l $ j else 0)"
    by (intro sum.cong refl) simp
  also have "\<dots> = a $ l $ i"
    by simp
  finally show ?thesis .
qed

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
    unfolding mv by (simp add: inner_add_left inner_axis_one)
  also have "\<dots> = a $ i $ i + a $ i $ j + (a $ j $ i + a $ j $ j)"
    by (simp add: matrix_vector_axis_one)
  also have "\<dots> = a $ i $ i + a $ j $ j + 2 * a $ i $ j"
    unfolding aji by simp
  finally show ?thesis .
qed

lemma matrix_vector_mult_vec_diff:
  fixes a :: "real^'n::finite^'n"
  shows "a *v (x - y) = a *v x - a *v y"
  by (simp add: matrix_vector_mult_def vec_eq_iff right_diff_distrib sum_subtractf)

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
    by (rule matrix_vector_mult_vec_diff)
  have "(axis i (1::real) - axis j 1) \<bullet> (a *v (axis i (1::real) - axis j 1))
      = (a *v axis i (1::real)) $ i - (a *v axis j (1::real)) $ i
        - ((a *v axis i (1::real)) $ j - (a *v axis j (1::real)) $ j)"
    unfolding mv by (simp add: inner_diff_left inner_axis_one)
  also have "\<dots> = a $ i $ i - a $ i $ j - (a $ j $ i - a $ j $ j)"
    by (simp add: matrix_vector_axis_one)
  also have "\<dots> = a $ i $ i + a $ j $ j - 2 * a $ i $ j"
    unfolding aji by simp
  finally show ?thesis .
qed

text \<open>A local copy of \<open>trace_conjugate\<close> (\<open>Viscosity_Comparison_Interface\<close>), so
  that this theory need not import the \<open>Operator_Envelopes\<close> chain; see the header.\<close>

lemma trace_conj:
  fixes M Q a :: "real^'n::finite^'n"
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

text \<open>\<open>p\<close> itself is an eigenvector of \<open>M\<^sub>p\<close>, with eigenvalue
  \<open>min (\<lambda>\<^sub>(\<^sub>n\<^sub>)(M)) 0\<close>: the conjugation kills it and the correction term
  scales it.  This is the first half of the "sorts to the bottom of the
  spectrum" claim after Eq. (3.4) of \<^cite>\<open>LaiShkolnikovSoner\<close>; the second half is the Poincare bound
  \<open>\<lambda>\<^sub>(\<^sub>i\<^sub>)(M\<^sub>p) \<ge> \<lambda>\<^sub>(\<^sub>i\<^sub>+\<^sub>1\<^sub>)(M)\<close>, which is what still remains for Eq. (3.5).\<close>

lemma matrix_vector_mult_add:
  fixes A B :: "real^'n::finite^'n"
  shows "(A + B) *v x = A *v x + B *v x"
proof -
  have "((A + B) *v x) $ i = (A *v x) $ i + (B *v x) $ i" for i
  proof -
    have "((A + B) *v x) $ i = (\<Sum>j\<in>UNIV. (A $ i $ j + B $ i $ j) * x $ j)"
      by (simp add: matrix_vector_mult_def)
    also have "\<dots> = (\<Sum>j\<in>UNIV. A $ i $ j * x $ j + B $ i $ j * x $ j)"
      by (intro sum.cong refl) (simp add: distrib_right)
    also have "\<dots> = (\<Sum>j\<in>UNIV. A $ i $ j * x $ j) + (\<Sum>j\<in>UNIV. B $ i $ j * x $ j)"
      by (rule sum.distrib)
    also have "\<dots> = (A *v x) $ i + (B *v x) $ i"
      by (simp add: matrix_vector_mult_def)
    finally show ?thesis .
  qed
  then show ?thesis
    by (simp add: vec_eq_iff)
qed

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
proof -
  have "transpose (A + \<delta> *\<^sub>R mat 1) $ i $ j = (A + \<delta> *\<^sub>R mat 1) $ i $ j"
    for i j
  proof -
    have "transpose (A + \<delta> *\<^sub>R mat 1) $ i $ j
        = A $ j $ i + \<delta> * (if j = i then 1 else 0)"
      by (simp add: transpose_def mat_def)
    also have "A $ j $ i = transpose A $ i $ j"
      by (simp add: transpose_def)
    also have "transpose A $ i $ j = A $ i $ j"
      using s by simp
    finally show ?thesis
      by (simp add: mat_def)
  qed
  then show ?thesis
    by (simp add: vec_eq_iff)
qed

lemma transpose_shift_diff:
  fixes A :: "real^'n::finite^'n"
  assumes s: "transpose A = A"
  shows "transpose (A - \<delta> *\<^sub>R mat 1) = A - \<delta> *\<^sub>R mat 1"
proof -
  have "A - \<delta> *\<^sub>R mat 1 = A + (- \<delta>) *\<^sub>R mat 1"
    by simp
  then show ?thesis
    using transpose_shift_add[OF s, of "- \<delta>"] by simp
qed

lemma trace_matrix_commute:
  fixes A B :: "real^'n::finite^'n"
  shows "trace (A ** B) = trace (B ** A)"
proof -
  have "trace (A ** B) = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. A $ i $ j * B $ j $ i)"
    by (simp add: trace_def matrix_matrix_mult_def)
  also have "\<dots> = (\<Sum>j\<in>UNIV. \<Sum>i\<in>UNIV. A $ i $ j * B $ j $ i)"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>j\<in>UNIV. \<Sum>i\<in>UNIV. B $ j $ i * A $ i $ j)"
    by (simp add: mult.commute)
  also have "\<dots> = trace (B ** A)"
    by (simp add: trace_def matrix_matrix_mult_def)
  finally show ?thesis .
qed

lemma matvec_diff_right:
  fixes A :: "real^'n::finite^'n"
  shows "A *v (x - y) = A *v x - A *v y"
  by (simp add: matrix_vector_mult_def vec_eq_iff algebra_simps sum_subtractf)

lemma matvec_scaleR_right:
  fixes A :: "real^'n::finite^'n"
  shows "A *v (r *\<^sub>R x) = r *\<^sub>R (A *v x)"
  by (simp add: matrix_vector_mult_def vec_eq_iff sum_distrib_left mult.left_commute)

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
proof -
  have o1: "transpose R ** R = mat 1" using orth unfolding orthogonal_matrix_def by blast
  have "(R *v v) \<bullet> (R *v v) = (transpose R *v (R *v v)) \<bullet> v"
    by (rule inner_transpose_matrix)
  also have "transpose R *v (R *v v) = (transpose R ** R) *v v"
    by (metis matrix_vector_mul_assoc)
  also have "\<dots> = v" unfolding o1 by (rule matrix_vector_mul_lid)
  finally have "(R *v v) \<bullet> (R *v v) = v \<bullet> v" .
  then show ?thesis by (metis norm_eq_sqrt_inner)
qed

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
    by (rule trace_matrix_commute)
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

lemma open_orth_image:
  fixes R :: "real^'n::finite^'n"
  assumes orth: "orthogonal_matrix R" and op: "open S"
  shows "open ((\<lambda>z. R *v z) ` S)"
proof (rule openI)
  fix w assume "w \<in> (\<lambda>z. R *v z) ` S"
  then obtain z0 where z0: "z0 \<in> S" and wz: "w = R *v z0" by auto
  obtain e where e0: "0 < e" and eb: "ball z0 e \<subseteq> S"
    using op z0 unfolding open_contains_ball by blast
  have "ball w e \<subseteq> (\<lambda>z. R *v z) ` S"
  proof
    fix y assume yb: "y \<in> ball w e"
    define z where "z = transpose R *v y"
    have Rz: "R *v z = y" unfolding z_def by (rule matvec_orth_inv[OF orth])
    have rd: "R *v (z0 - z) = w - y"
    proof -
      have "R *v (z0 - z) = R *v z0 - R *v z" by (rule matvec_diff_right)
      then show ?thesis unfolding wz Rz .
    qed
    have "dist z0 z = norm (z0 - z)" by (simp add: dist_norm)
    also have "\<dots> = norm (R *v (z0 - z))"
      by (rule norm_orthogonal_matrix_vector[OF orth, symmetric])
    also have "\<dots> = norm (w - y)" unfolding rd by (rule refl)
    finally have "dist z0 z = dist w y" by (simp add: dist_norm)
    then have "z \<in> ball z0 e" using yb by simp
    then show "y \<in> (\<lambda>z. R *v z) ` S" using eb Rz by force
  qed
  then show "\<exists>e>0. ball w e \<subseteq> (\<lambda>z. R *v z) ` S" using e0 by blast
qed

lemma open_affine_image:
  fixes R :: "real^'n::finite^'n" and b :: "real^'n"
  assumes orth: "orthogonal_matrix R" and c0: "c \<noteq> 0" and op: "open S"
  shows "open ((\<lambda>z. c *\<^sub>R (R *v z) + b) ` S)"
proof -
  have eq: "(\<lambda>z. c *\<^sub>R (R *v z) + b) ` S
      = (\<lambda>y. b + y) ` ((\<lambda>y. c *\<^sub>R y) ` ((\<lambda>z. R *v z) ` S))"
    unfolding image_image by (rule image_cong[OF refl]) (simp add: add.commute)
  show ?thesis
    unfolding eq
    by (rule open_translation, rule open_scaling[OF c0 open_orth_image[OF orth op]])
qed

lemma affine_interior_sub:
  fixes R :: "real^'n::finite^'n" and b :: "real^'n"
  assumes orth: "orthogonal_matrix R" and c0: "c \<noteq> 0"
  shows "(\<lambda>z. c *\<^sub>R (R *v z) + b) ` interior S
       \<subseteq> interior ((\<lambda>z. c *\<^sub>R (R *v z) + b) ` S)"
  by (rule interior_maximal[OF image_mono[OF interior_subset]
        open_affine_image[OF orth c0 open_interior]])

text \<open>The inverse of \<open>z \<mapsto> c \<cdot> R z + b\<close> has the same shape, which upgrades the
  inclusion above to an equality.\<close>

lemma affine_inv_shape:
  fixes R :: "real^'n::finite^'n" and b :: "real^'n"
  assumes orth: "orthogonal_matrix R" and c0: "0 < c"
  shows "(\<lambda>y. (1/c) *\<^sub>R (transpose R *v (y - b)))
       = (\<lambda>y. (1/c) *\<^sub>R (transpose R *v y) + (- ((1/c) *\<^sub>R (transpose R *v b))))"
  by (rule ext) (simp add: matvec_diff_right scaleR_right_diff_distrib)

lemma affine_inv_left:
  fixes R :: "real^'n::finite^'n" and b :: "real^'n"
  assumes orth: "orthogonal_matrix R" and c0: "0 < c"
  shows "(1/c) *\<^sub>R (transpose R *v ((c *\<^sub>R (R *v z) + b) - b)) = z"
proof -
  have "(c *\<^sub>R (R *v z) + b) - b = c *\<^sub>R (R *v z)" by simp
  then have "transpose R *v ((c *\<^sub>R (R *v z) + b) - b)
      = c *\<^sub>R (transpose R *v (R *v z))" by (simp add: matvec_scaleR_right)
  also have "transpose R *v (R *v z) = z"
    using orth unfolding orthogonal_matrix_def
    by (metis matrix_vector_mul_assoc matrix_vector_mul_lid)
  finally show ?thesis using c0 by simp
qed

lemma affine_inv_right:
  fixes R :: "real^'n::finite^'n" and b :: "real^'n"
  assumes orth: "orthogonal_matrix R" and c0: "0 < c"
  shows "c *\<^sub>R (R *v ((1/c) *\<^sub>R (transpose R *v (y - b)))) + b = y"
proof -
  have "R *v ((1/c) *\<^sub>R (transpose R *v (y - b)))
      = (1/c) *\<^sub>R (R *v (transpose R *v (y - b)))"
    by (rule matvec_scaleR_right)
  also have "R *v (transpose R *v (y - b)) = y - b"
    by (rule matvec_orth_inv[OF orth])
  finally have "c *\<^sub>R (R *v ((1/c) *\<^sub>R (transpose R *v (y - b)))) = y - b"
    using c0 by simp
  then show ?thesis by simp
qed

lemma affine_interior_image:
  fixes R :: "real^'n::finite^'n" and b :: "real^'n"
  assumes orth: "orthogonal_matrix R" and c0: "0 < c"
  shows "interior ((\<lambda>z. c *\<^sub>R (R *v z) + b) ` S)
       = (\<lambda>z. c *\<^sub>R (R *v z) + b) ` interior S"
proof
  define T where "T = (\<lambda>z :: real^'n. c *\<^sub>R (R *v z) + b)"
  define S' where "S' = (\<lambda>y :: real^'n. (1/c) *\<^sub>R (transpose R *v (y - b)))"
  have cne: "c \<noteq> 0" using c0 by simp
  have orthT: "orthogonal_matrix (transpose R)"
    using orth unfolding orthogonal_matrix_def by auto
  have c1ne: "1 / c \<noteq> 0" using c0 by simp
  have ST: "S' (T z) = z" for z unfolding S'_def T_def by (rule affine_inv_left[OF orth c0])
  have TS: "T (S' y) = y" for y unfolding S'_def T_def by (rule affine_inv_right[OF orth c0])
  have Seq: "S' = (\<lambda>y. (1/c) *\<^sub>R (transpose R *v y)
      + (- ((1/c) *\<^sub>R (transpose R *v b))))"
    unfolding S'_def by (rule affine_inv_shape[OF orth c0])
  have opS': "open (S' ` A)" if "open A" for A
    unfolding Seq by (rule open_affine_image[OF orthT c1ne that])
  have STS: "S' ` (T ` S) = S" unfolding image_image ST by simp
  show "interior (T ` S) \<subseteq> T ` interior S"
  proof
    fix y assume yi: "y \<in> interior (T ` S)"
    have sub1: "S' ` interior (T ` S) \<subseteq> interior (S' ` (T ` S))"
      by (rule interior_maximal[OF image_mono[OF interior_subset]])
        (rule opS'[OF open_interior])
    have "S' y \<in> S' ` interior (T ` S)" using yi by (rule imageI)
    then have "S' y \<in> interior (S' ` (T ` S))" using sub1 by blast
    then have "S' y \<in> interior S" unfolding STS .
    then show "y \<in> T ` interior S" using TS[of y] by (metis imageI)
  qed
  show "T ` interior S \<subseteq> interior (T ` S)"
    unfolding T_def by (rule affine_interior_sub[OF orth cne])
qed

lemma trace_mat1: "trace (mat 1 :: real^'n::finite^'n) = real CARD('n)"
  by (simp add: trace_def mat_def)

lemma bm_compensator_const:
  assumes u: "0 \<le> u"
  shows "set_lebesgue_integral lborel {0..u}
      (\<lambda>_. trace (mat 1 :: real^'n::finite^'n))
    = real CARD('n) * u"
proof -
  have "set_lebesgue_integral lborel {0..u}
      (\<lambda>_. trace (mat 1 :: real^'n^'n)) = u * trace (mat 1 :: real^'n^'n)"
    using u by (subst set_integral_const) auto
  then show ?thesis
    by (simp add: trace_mat1 mult_ac)
qed

text \<open>the compensated squared norm compensates the squared norm by the trace,
  which is what the application's Ito functional and the quadratic Dynkin identity speak about. Lemma 2.2 of
  \<^cite>\<open>LaiShkolnikovSoner\<close> needs more: a fourth-moment bound on each coordinate
  separately, along the tightness chain
  \<open>Path_Tightness.tight_on_set_path_laws_vec \<leftarrow>
  Increment_Moments.fourth_moment_bound_bounded \<leftarrow>
  Stopped_Localization.stopped_covariation\<close>, so the compensated square of
  each coordinate must also be a martingale in its own right; a trace
  identity alone does not give this. The per-coordinate compensator is
  \<open>w\<close> rather than \<open>CARD('n) * w\<close>, since \<open>mat 1 $ i $ i = 1\<close>.\<close>

lemma bm_compensator_coord:
  assumes u: "0 \<le> u"
  shows "set_lebesgue_integral lborel {0..u}
      (\<lambda>_. (mat 1 :: real^'n::finite^'n) $ i $ i) = u"
proof -
  have "set_lebesgue_integral lborel {0..u}
      (\<lambda>_. (mat 1 :: real^'n^'n) $ i $ i)
      = u * ((mat 1 :: real^'n^'n) $ i $ i)"
    using u by (subst set_integral_const) auto
  then show ?thesis by (simp add: mat_def)
qed

text \<open>Two-sided pointwise bounds on the trace, from the eigenvalue
  conditions: positive semidefiniteness makes the diagonal, hence the trace,
  nonnegative, and the eigenvalue upper bound of Eq. (1.7) of \<^cite>\<open>LaiShkolnikovSoner\<close> caps every
  diagonal entry by \<open>L\<close>.\<close>

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
proof -
  have "0 \<le> a $ i $ i" for i
    unfolding diag_eq_inner_axis by (rule assms)
  then show ?thesis
    unfolding trace_def by (intro sum_nonneg) simp
qed

lemma diag_entry_quadform:
  fixes a :: "real^'m::finite^'m"
  shows "axis l 1 \<bullet> (a *v axis l 1) = a $ l $ l"
proof -
  have col: "(a *v axis l 1) $ l = a $ l $ l"
    by (simp add: matrix_vector_mult_def axis_def if_distrib
        cong: if_cong)
  have "axis l 1 \<bullet> (a *v axis l 1) = (a *v axis l 1) $ l"
    by (metis cart_eq_inner_axis inner_commute)
  with col show ?thesis by simp
qed

lemma inner_diff_self_expand:
  fixes a c :: "real^'m::finite"
  shows "(a - c) \<bullet> (a - c) = a \<bullet> a - 2 * (c \<bullet> a) + c \<bullet> c"
  by (simp add: inner_diff_left inner_diff_right inner_commute)

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

lemma continuous_on_trace_mult_right:
  fixes P :: "real^'n::finite^'n"
  shows "continuous_on UNIV (\<lambda>a :: real^'n^'n. trace (a ** P))"
proof -
  have eq: "(\<lambda>a :: real^'n^'n. trace (a ** P))
      = (\<lambda>a. \<Sum>i\<in>(UNIV :: 'n set). \<Sum>j\<in>(UNIV :: 'n set). a $ i $ j * P $ j $ i)"
    by (simp add: trace_def matrix_matrix_mult_def)
  show ?thesis
    unfolding eq
    by (intro continuous_on_sum continuous_on_mult continuous_on_const
        continuous_on_matrix_entry continuous_on_id)
qed

lemma closed_trace_proj_halfspace:
  fixes P :: "real^'n::finite^'n"
  shows "closed {a :: real^'n^'n. c \<le> trace (a ** P)}"
  by (intro closed_Collect_le continuous_on_const continuous_on_trace_mult_right)

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
proof -
  have "linear (\<lambda>v :: real^'n. (\<chi> i j. c $ i * v $ j) + (\<chi> i j. v $ i * c $ j))"
    by (rule linearI) (auto simp: vec_eq_iff algebra_simps)
  then show ?thesis by (simp add: linear_conv_bounded_linear)
qed

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

lemma trace_mult_diff:
  fixes M A B :: "real^'n::finite^'n"
  shows "trace (M ** (A - B)) = trace (M ** A) - trace (M ** B)"
  by (simp add: trace_mult_sum sum_subtractf right_diff_distrib)

lemma trace_mult_scaleR:
  fixes M A :: "real^'n::finite^'n"
  shows "trace (M ** (r *\<^sub>R A)) = r * trace (M ** A)"
  by (simp add: trace_mult_sum sum_distrib_left algebra_simps)

lemma bounded_linear_transpose:
  "bounded_linear (transpose :: real^'n::finite^'n \<Rightarrow> real^'n^'n)"
  unfolding linear_conv_bounded_linear[symmetric]
  by (intro linearI) (simp_all add: transpose_def vec_eq_iff)

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

lemma axis1_inner:
  fixes w :: "real^'n::finite"
  shows "axis i 1 \<bullet> w = w $ i"
proof -
  have "axis i 1 \<bullet> w = (\<Sum>l\<in>UNIV. axis i 1 $ l * w $ l)"
    by (simp add: inner_vec_def)
  also have "\<dots> = (\<Sum>l\<in>UNIV. if l = i then w $ l else 0)"
    by (rule sum.cong[OF refl]) (simp add: axis_def)
  also have "\<dots> = w $ i" by simp
  finally show ?thesis .
qed

lemma axis1_self:
  fixes i :: "'n::finite"
  shows "axis i 1 \<bullet> (axis i 1 :: real^'n) = (1::real)"
proof -
  have "axis i 1 \<bullet> (axis i 1 :: real^'n) = axis i 1 $ i"
    by (rule axis1_inner)
  also have "\<dots> = 1" by (simp add: axis_def)
  finally show ?thesis .
qed

lemma matvec_axis1:
  fixes a :: "real^'n::finite^'n"
  shows "(a *v axis i 1) $ l = a $ l $ i"
proof -
  have "(a *v axis i 1) $ l = (\<Sum>j\<in>UNIV. a $ l $ j * axis i 1 $ j)"
    by (simp add: matrix_vector_mult_def)
  also have "\<dots> = (\<Sum>j\<in>UNIV. if j = i then a $ l $ j else 0)"
    by (rule sum.cong[OF refl]) (simp add: axis_def)
  also have "\<dots> = a $ l $ i" by simp
  finally show ?thesis .
qed

lemma matvec_norm_le:
  fixes M :: "real^'n::finite^'n"
  shows "norm (M *v w) \<le> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>) * norm w"
proof -
  let ?C = "\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>"
  have comp: "\<bar>(M *v w) $ i\<bar> \<le> (\<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>) * norm w" for i
  proof -
    have "\<bar>(M *v w) $ i\<bar> = \<bar>\<Sum>j\<in>UNIV. M $ i $ j * w $ j\<bar>"
      by (simp add: matrix_vector_mult_def)
    also have "\<dots> \<le> (\<Sum>j\<in>UNIV. \<bar>M $ i $ j * w $ j\<bar>)"
      by (rule sum_abs)
    also have "\<dots> \<le> (\<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar> * norm w)"
      by (intro sum_mono)
        (simp add: abs_mult mult_left_mono component_le_norm_cart)
    also have "\<dots> = (\<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>) * norm w"
      by (simp add: sum_distrib_right)
    finally show ?thesis .
  qed
  have rownn: "0 \<le> (\<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>) * norm w" for i
    by (intro mult_nonneg_nonneg sum_nonneg) simp_all
  have "(norm (M *v w))\<^sup>2 = (M *v w) \<bullet> (M *v w)"
    by (simp add: power2_norm_eq_inner)
  also have "\<dots> = (\<Sum>i\<in>UNIV. ((M *v w) $ i)\<^sup>2)"
    by (simp add: inner_vec_def power2_eq_square)
  also have "\<dots> \<le> (\<Sum>i\<in>UNIV. ((\<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>) * norm w)\<^sup>2)"
  proof (rule sum_mono)
    fix i :: 'n
    have "((M *v w) $ i)\<^sup>2 = \<bar>(M *v w) $ i\<bar>\<^sup>2" by simp
    also have "\<dots> \<le> ((\<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>) * norm w)\<^sup>2"
      using comp[of i] rownn[of i] by (intro power_mono) simp_all
    finally show "((M *v w) $ i)\<^sup>2
        \<le> ((\<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>) * norm w)\<^sup>2" .
  qed
  also have "\<dots> \<le> (\<Sum>i\<in>UNIV. (\<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>) * norm w)\<^sup>2"
    by (rule sum_sq_le_sq_sum) (rule rownn)
  also have "\<dots> = (?C * norm w)\<^sup>2"
    by (simp add: sum_distrib_right)
  finally have h: "(norm (M *v w))\<^sup>2 \<le> (?C * norm w)\<^sup>2" .
  have Cnn: "0 \<le> ?C * norm w"
    by (intro mult_nonneg_nonneg sum_nonneg) simp_all
  show ?thesis
    using h Cnn by (simp add: power2_le_iff_abs_le)
qed

text \<open>The covariance field is \<open>\<Sum>\<^sub>u outerp (w u)\<close> for columns \<open>w u\<close>, and the
  Euler machinery reads it only through its trace against the Hessian.  That
  pairing is exact, whatever the columns: the trace of \<open>M\<close> against the sum is
  the sum of the quadratic forms \<open>w u \<bullet> (M *v w u)\<close>.\<close>

lemma trace_mult_zero_right: "trace (M ** (0 :: real^'n::finite^'n)) = 0"
  by (simp add: matrix_matrix_mult_def trace_def vec_eq_iff)

lemma matvec_blin: "bounded_linear ((*v) (S :: real^'n::finite^'m::finite))"
  using matrix_vector_mul_linear linear_conv_bounded_linear by blast

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

lemma matmul_scaleR_right:
  fixes A B :: "real^'n::finite^'n"
  shows "A ** (c *\<^sub>R B) = c *\<^sub>R (A ** B)"
  by (simp add: matrix_matrix_mult_def vec_eq_iff
      sum_distrib_left algebra_simps)

lemma sandwich_mat1:
  fixes S :: "real^'n::finite^'n"
  shows "S ** (c *\<^sub>R mat 1) ** transpose S = c *\<^sub>R (S ** transpose S)"
  by (simp add: matmul_scaleR_right scaleR_matrix_mult)

lemma exists_enum_of_card:
  fixes B :: "(real^'n::finite) set"
  assumes finB: "finite B" and cardB: "card B = CARD('n)"
  obtains f :: "'n \<Rightarrow> real^'n" where "bij_betw f (UNIV :: 'n set) B"
proof -
  have "\<exists>f. bij_betw f (UNIV :: 'n set) B"
    by (rule finite_same_card_bij) (use finB cardB in simp_all)
  then show ?thesis using that by blast
qed

text \<open>The Euler analysis needs exactly two facts per step: the compensated
  quadratic increment has mean zero (an instance of
  a mean-zero compensated-increment fact in the application, since the member's
  second component is deterministic), and its variance is \<open>O(h\<^sup>2)\<close>.  The
  variance bound needs no Wick calculus and no coordinate independence:
  the pointwise AM--GM bound \<open>a\<^sup>2b\<^sup>2 \<le> (a\<^sup>4 + b\<^sup>4)/2\<close> reduces everything
  to the fourth marginal moment \<open>3h\<^sup>2\<close> of one Brownian coordinate.\<close>

lemma trace_mult_blin:
  fixes M :: "real^'n::finite^'n"
  shows "bounded_linear (\<lambda>A :: real^'n^'n. trace (M ** A))"
  unfolding linear_conv_bounded_linear[symmetric]
  by (intro linearI)
    (simp_all add: trace_mult_add matmul_scaleR_right trace_scaleR)

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

lemma quad_diff_bound:
  fixes M :: "real^'n::finite^'n" and q x a b :: "real^'n" and rb :: real
  assumes sym: "transpose M = M"
    and a: "a \<in> cball x rb" and b: "b \<in> cball x rb"
  shows "\<bar>q \<bullet> (b - x) + (1/2) * ((b - x) \<bullet> (M *v (b - x)))
       - (q \<bullet> (a - x) + (1/2) * ((a - x) \<bullet> (M *v (a - x))))\<bar>
      \<le> (norm q + 2 * (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>) * rb)
          * norm (b - a)"
proof -
  let ?CM = "\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>"
  have CM0: "0 \<le> ?CM" by (auto intro!: sum_nonneg)
  have ax: "norm (a - x) \<le> rb"
    using a by (simp add: dist_norm norm_minus_commute)
  have bx: "norm (b - x) \<le> rb"
    using b by (simp add: dist_norm norm_minus_commute)
  have dble: "norm (b - a) \<le> 2 * rb"
  proof -
    have deq: "b - a = (b - x) + (x - a)" by simp
    have "norm (b - a) \<le> norm (b - x) + norm (x - a)"
      by (subst deq) (rule norm_triangle_ineq)
    moreover have "norm (x - a) \<le> rb"
      using ax by (simp add: norm_minus_commute)
    ultimately show ?thesis using bx by linarith
  qed
  have step: "q \<bullet> (b - x) + (1/2) * ((b - x) \<bullet> (M *v (b - x)))
      - (q \<bullet> (a - x) + (1/2) * ((a - x) \<bullet> (M *v (a - x))))
      = (q + M *v (a - x)) \<bullet> (b - a)
        + (1/2) * ((b - a) \<bullet> (M *v (b - a)))"
    by (rule quad_taylor_step[OF sym])
  have t1: "\<bar>(q + M *v (a - x)) \<bullet> (b - a)\<bar>
      \<le> (norm q + ?CM * rb) * norm (b - a)"
  proof -
    have cs: "\<bar>(q + M *v (a - x)) \<bullet> (b - a)\<bar>
        \<le> norm (q + M *v (a - x)) * norm (b - a)"
      by (rule Cauchy_Schwarz_ineq2)
    have "norm (q + M *v (a - x)) \<le> norm q + ?CM * rb"
    proof -
      have "norm (q + M *v (a - x)) \<le> norm q + norm (M *v (a - x))"
        by (rule norm_triangle_ineq)
      moreover have "norm (M *v (a - x)) \<le> ?CM * norm (a - x)"
        by (rule matvec_norm_le)
      moreover have "?CM * norm (a - x) \<le> ?CM * rb"
        by (rule mult_left_mono[OF ax CM0])
      ultimately show ?thesis by linarith
    qed
    then have "norm (q + M *v (a - x)) * norm (b - a)
        \<le> (norm q + ?CM * rb) * norm (b - a)"
      by (rule mult_right_mono) simp
    then show ?thesis using cs by linarith
  qed
  have t2: "\<bar>(1/2) * ((b - a) \<bullet> (M *v (b - a)))\<bar>
      \<le> ?CM * rb * norm (b - a)"
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
        \<le> ?CM * (2 * rb) * norm (b - a)"
      by (rule mult_right_mono[OF mult_left_mono[OF dble CM0] norm_ge_zero])
    have "\<bar>(1/2) * ((b - a) \<bullet> (M *v (b - a)))\<bar>
        = (1/2) * \<bar>(b - a) \<bullet> (M *v (b - a))\<bar>"
      by (simp add: abs_mult)
    also have "\<dots> \<le> (1/2) * (?CM * (2 * rb) * norm (b - a))"
      using h h2 by linarith
    also have "\<dots> = ?CM * rb * norm (b - a)" by simp
    finally show ?thesis .
  qed
  have tri: "\<bar>q \<bullet> (b - x) + (1/2) * ((b - x) \<bullet> (M *v (b - x)))
      - (q \<bullet> (a - x) + (1/2) * ((a - x) \<bullet> (M *v (a - x))))\<bar>
      \<le> \<bar>(q + M *v (a - x)) \<bullet> (b - a)\<bar>
        + \<bar>(1/2) * ((b - a) \<bullet> (M *v (b - a)))\<bar>"
    unfolding step by (rule abs_triangle_ineq)
  have fin: "(norm q + ?CM * rb) * norm (b - a)
      + ?CM * rb * norm (b - a)
      = (norm q + 2 * ?CM * rb) * norm (b - a)"
    by (simp add: algebra_simps)
  show ?thesis using tri t1 t2 fin by linarith
qed

text \<open>Small independent pieces the contradiction assembles: algebra for the
  softened Hessian, a generic small-radius chooser, the witness extraction
  from a failed operator inequality, the value bound \<open>v(x) < T\<close> forced by a
  nonzero touching gradient, and the exit-time identity on paths that never
  leave \<open>K\<close>.\<close>

lemma transpose_sub_smat:
  fixes H :: "real^'n::finite^'n" and s :: real
  assumes symH: "transpose H = H"
  shows "transpose (H - s *\<^sub>R mat 1) = H - s *\<^sub>R mat 1"
proof -
  have "transpose (H - s *\<^sub>R mat 1)
      = transpose H - transpose (s *\<^sub>R mat 1)"
    by (simp add: transpose_def vec_eq_iff)
  then show ?thesis by (simp add: transpose_scalar symH)
qed

lemma trace_msub_mat:
  fixes H a :: "real^'n::finite^'n" and s :: real
  shows "trace ((H - s *\<^sub>R mat 1) ** a) = trace (H ** a) - s * trace a"
proof -
  have e1: "(H - s *\<^sub>R mat 1) ** a = H ** a - (s *\<^sub>R mat 1) ** a"
    by (simp add: matrix_matrix_mult_def vec_eq_iff sum_subtractf
        left_diff_distrib)
  have e2: "(s *\<^sub>R mat 1) ** a = s *\<^sub>R a"
    by (simp add: scaleR_matrix_mult)
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
        scaleR_matrix_vector)
  have e2: "(H - (2 * \<gamma> + \<delta>) *\<^sub>R mat 1) *v v
      = H *v v - (2 * \<gamma> + \<delta>) *\<^sub>R v"
    by (simp add: matrix_vector_mult_diff_rdistrib
        scaleR_matrix_vector)
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

lemma invertible_matrix_vector_inj:
  fixes M :: "real^'n::finite^'n"
  assumes inv: "invertible M" and eq: "M *v a = M *v b"
  shows "a = b"
proof -
  obtain M' where M': "M' ** M = mat 1"
    using inv invertible_left_inverse by blast
  have "a = (M' ** M) *v a" unfolding M' by simp
  also have "\<dots> = M' *v (M *v a)" by (simp add: matrix_vector_mul_assoc)
  also have "\<dots> = M' *v (M *v b)" unfolding eq by (rule refl)
  also have "\<dots> = (M' ** M) *v b" by (simp add: matrix_vector_mul_assoc)
  also have "\<dots> = b" unfolding M' by simp
  finally show ?thesis .
qed

text \<open>\<open>matvec_scaleR_right\<close> lives in \<open>Operator_Envelopes\<close>.\<close>

lemma matvec_sum_right:
  fixes A :: "real^'n::finite^'n"
  shows "A *v (\<Sum>i\<in>S. v i) = (\<Sum>i\<in>S. A *v v i)"
proof (cases "finite S")
  case True
  then show ?thesis
    by (induct S rule: finite_induct)
      (simp_all add: matvec_add_right)
next
  case False
  then show ?thesis by simp
qed

text \<open>\<open>trace_sum_matrix\<close> is \<open>trace_matrix_sum\<close> from
  \<open>Matrix_Algebra\<close>.\<close>

lemma transpose_matrix_diff:
  fixes A B :: "real^'n::finite^'n"
  shows "transpose (A - B) = transpose A - transpose B"
  by (simp add: transpose_def vec_eq_iff)

text \<open>\<open>inner_matrix_transpose\<close> is the square case of \<open>inner_transpose_matrix\<close>
  from \<open>Symmetric_Spectral\<close>.\<close>

lemma unit_normalize:
  fixes v :: "real^'n::finite"
  assumes v0: "v \<noteq> 0"
  shows "(v /\<^sub>R norm v) \<bullet> (v /\<^sub>R norm v) = 1"
proof -
  have n0: "norm v \<noteq> 0" using v0 by simp
  have e1: "(v /\<^sub>R norm v) \<bullet> (v /\<^sub>R norm v) = (v \<bullet> v) / (norm v * norm v)"
    by (simp add: divide_inverse mult_ac)
  have e2: "v \<bullet> v = norm v * norm v"
    by (simp add: dot_square_norm power2_eq_square)
  show ?thesis unfolding e1 e2 using n0 by simp
qed

lemma orthonormal_inj:
  fixes b :: "nat \<Rightarrow> real^'n::finite"
  assumes orth: "\<And>i j. i < m \<Longrightarrow> j < m \<Longrightarrow> b i \<bullet> b j = (if i = j then 1 else 0)"
  shows "inj_on b {..<m}"
proof (rule inj_onI)
  fix i j assume i: "i \<in> {..<m}" and j: "j \<in> {..<m}" and eq: "b i = b j"
  have im: "i < m" and jm: "j < m" using i j by auto
  show "i = j"
  proof (rule ccontr)
    assume ne: "i \<noteq> j"
    have "b i \<bullet> b j = 0" using orth[OF im jm] ne by simp
    moreover have "b i \<bullet> b j = b i \<bullet> b i" using eq by simp
    moreover have "b i \<bullet> b i = 1" using orth[OF im im] by simp
    ultimately show False by simp
  qed
qed

lemma orthonormal_dim_span:
  fixes b :: "nat \<Rightarrow> real^'n::finite"
  assumes orth: "\<And>i j. i < m \<Longrightarrow> j < m \<Longrightarrow> b i \<bullet> b j = (if i = j then 1 else 0)"
  shows "dim (span (b ` {..<m})) = m"
proof (rule dim_unique[where B = "b ` {..<m}"])
  show "b ` {..<m} \<subseteq> span (b ` {..<m})" by (rule span_superset)
  show "span (b ` {..<m}) \<subseteq> span (b ` {..<m})" by (rule subset_refl)
next
  show "independent (b ` {..<m})"
  proof (rule pairwise_orthogonal_independent)
    show "pairwise orthogonal (b ` {..<m})"
    proof (rule pairwiseI)
      fix u v assume "u \<in> b ` {..<m}" and "v \<in> b ` {..<m}" and uv: "u \<noteq> v"
      then obtain i j where i: "i < m" and j: "j < m"
        and ui: "u = b i" and vj: "v = b j" by auto
      have "i \<noteq> j" using uv ui vj by blast
      then show "orthogonal u v"
        unfolding orthogonal_def ui vj using orth[OF i j] by simp
    qed
    show "(0 :: real^'n) \<notin> b ` {..<m}"
    proof (rule notI)
      assume "(0 :: real^'n) \<in> b ` {..<m}"
      then obtain i where i: "i < m" and z: "b i = 0" by auto
      have "b i \<bullet> b i = 1" using orth[OF i i] by simp
      then show False unfolding z by simp
    qed
  qed
next
  show "card (b ` {..<m}) = m"
    using card_image[OF orthonormal_inj[OF orth]] by simp
qed

text \<open>The kill condition, and it needs no confinement to the subspace: for any
  \<open>z\<close> with \<open>P *v z \<noteq> 0\<close>, \<open>(P *v z) \<bullet> z = \<bar>P *v z\<bar>\<^sup>2\<close> because \<open>P\<close> is a symmetric
  idempotent, so the clamped direction already sees the whole radial part.\<close>

lemma proj_inner_self:
  fixes P :: "real^'n::finite^'n" and z :: "real^'n"
  assumes Psym: "transpose P = P" and Pidem: "P ** P = P"
  shows "(P *v z) \<bullet> z = (P *v z) \<bullet> (P *v z)"
proof -
  have "(P *v z) \<bullet> (P *v z) = (transpose P *v (P *v z)) \<bullet> z"
    by (rule inner_transpose_matrix)
  also have "transpose P *v (P *v z) = P *v (P *v z)" unfolding Psym by (rule refl)
  also have "P *v (P *v z) = P *v z"
    using Pidem by (metis matrix_vector_mul_assoc)
  finally show ?thesis by (rule sym)
qed

lemma proj_inner_self':
  fixes P :: "real^'n::finite^'n" and y :: "real^'n"
  assumes Psym: "transpose P = P" and Pidem: "P ** P = P"
  shows "y \<bullet> (P *v y) = (P *v y) \<bullet> (P *v y)"
proof -
  have "(P *v y) \<bullet> y = (P *v y) \<bullet> (P *v y)"
    by (rule proj_inner_self[OF Psym Pidem])
  then show ?thesis by (simp add: inner_commute)
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

lemma proj_norm_le:
  fixes P :: "real^'n::finite^'n" and w :: "real^'n"
  assumes Psym: "transpose P = P" and Pidem: "P ** P = P"
  shows "norm (P *v w) \<le> norm w"
proof -
  have "(norm (P *v w))\<^sup>2 = (P *v w) \<bullet> (P *v w)" by (simp add: dot_square_norm)
  also have "\<dots> = (P *v w) \<bullet> w"
    by (rule proj_inner_self[OF Psym Pidem, symmetric])
  also have "\<dots> \<le> norm (P *v w) * norm w" by (rule norm_cauchy_schwarz)
  finally have key: "(norm (P *v w))\<^sup>2 \<le> norm (P *v w) * norm w" .
  show ?thesis
  proof (cases "norm (P *v w) = 0")
    case True
    then show ?thesis by simp
  next
    case False
    then have pos: "0 < norm (P *v w)" using norm_ge_zero[of "P *v w"] by linarith
    have "norm (P *v w) * norm (P *v w) \<le> norm (P *v w) * norm w"
      using key by (simp add: power2_eq_square)
    then show ?thesis using pos by simp
  qed
qed

lemma orthonormal_family_containing:
  fixes x0 :: "real^'n::finite"
  assumes u: "x0 \<bullet> x0 = 1" and m: "m \<le> CARD('n)" and m0: "0 < m"
  shows "\<exists>b :: nat \<Rightarrow> real^'n. b 0 = x0
      \<and> (\<forall>i < m. \<forall>j < m. b i \<bullet> b j = (if i = j then 1 else 0))"
  using m m0
proof (induct m)
  case 0
  then show ?case by simp
next
  case (Suc m)
  show ?case
  proof (cases "m = 0")
    case True
    show ?thesis
      by (rule exI[of _ "\<lambda>_. x0"]) (use True u in auto)
  next
    case False
    then have m0': "0 < m" by simp
    have mle: "m \<le> CARD('n)" using Suc.prems by simp
    obtain b :: "nat \<Rightarrow> real^'n" where b0: "b 0 = x0"
      and bo: "\<And>i j. i < m \<Longrightarrow> j < m \<Longrightarrow> b i \<bullet> b j = (if i = j then 1 else 0)"
      using Suc.hyps[OF mle m0'] by blast
    have dimlt: "dim (b ` {..<m}) < DIM(real^'n)"
    proof -
      have "dim (b ` {..<m}) = dim (span (b ` {..<m}))" by simp
      also have "\<dots> = m" by (rule orthonormal_dim_span[OF bo])
      also have "\<dots> < CARD('n)" using Suc.prems by simp
      finally show ?thesis by simp
    qed
    have ex: "\<exists>v :: real^'n. v \<noteq> 0
        \<and> (\<forall>y \<in> span (b ` {..<m}). orthogonal v y)"
    proof (rule orthogonal_to_subspace_exists[OF dimlt])
      fix v :: "real^'n"
      assume v0: "v \<noteq> 0"
        and vo: "\<And>y. y \<in> span (b ` {..<m}) \<Longrightarrow> orthogonal v y"
      show ?thesis using v0 vo by blast
    qed
    obtain v :: "real^'n" where v0: "v \<noteq> 0"
      and vo: "\<And>y. y \<in> span (b ` {..<m}) \<Longrightarrow> orthogonal v y" using ex by blast
    define w :: "real^'n" where "w = v /\<^sub>R norm v"
    have ww: "w \<bullet> w = 1" unfolding w_def by (rule unit_normalize[OF v0])
    have wo: "w \<bullet> b i = 0" if i: "i < m" for i
    proof -
      have "b i \<in> span (b ` {..<m})" using i by (intro span_base) auto
      then have "orthogonal v (b i)" by (rule vo)
      then show ?thesis unfolding w_def orthogonal_def by simp
    qed
    define b' :: "nat \<Rightarrow> real^'n" where "b' = (\<lambda>i. if i = m then w else b i)"
    have b'0: "b' 0 = x0" unfolding b'_def using False b0 by simp
    have b'o: "b' i \<bullet> b' j = (if i = j then 1 else 0)"
      if i: "i < Suc m" and j: "j < Suc m" for i j
    proof -
      consider (both) "i = m" "j = m" | (im) "i = m" "j < m"
        | (jm) "i < m" "j = m" | (nn) "i < m" "j < m"
        using i j by fastforce
      then show ?thesis
      proof cases
        case both then show ?thesis unfolding b'_def using ww by simp
      next
        case im then show ?thesis unfolding b'_def using wo[of j] by simp
      next
        case jm then show ?thesis
          unfolding b'_def using wo[of i] by (simp add: inner_commute)
      next
        case nn then show ?thesis unfolding b'_def using bo by simp
      qed
    qed
    show ?thesis by (rule exI[of _ b']) (use b'0 b'o in blast)
  qed
qed

text \<open>The two envelope-form hypotheses in the shape the doubling produces:
  on an open \<open>\<Omega>\<close> inside \<open>K\<close>, a subsolution and supersolution in the
  envelope-free sense are also envelope sub/supersolutions, letting the
  doubling argument run where the \<open>\<delta> \<rightarrow> 0\<close> passage is legitimate.\<close>

lemma ball_prod_shift_snd:
  fixes p :: "real^'n::finite" and M N :: "real^'n^'n"
  assumes "w \<in> ball (p, M) e"
  shows "w + (0, N - M) \<in> ball (p, N) e"
proof -
  have eq: "(w + (0, N - M)) - (p, N) = w - (p, M)"
    by (simp add: prod_eq_iff)
  have "dist (w + (0, N - M)) (p, N) = dist w (p, M)"
    unfolding dist_norm eq ..
  moreover have "dist w (p, M) < e"
    using assms by (simp add: dist_commute)
  ultimately show ?thesis
    by (simp add: dist_commute)
qed

text \<open>The supersolution mirror: the sup-convolution is taken of \<open>-w\<close>, the
  summand the doubled functional carries, and the transferred bound
  becomes a local minimum statement for \<open>w\<close> after negation. The
  correction runs the other way, \<open>Ym - \<delta> I\<close>, as with
  \<open>jet_imp_local_min_test\<close>.\<close>

lemma neg_shift_matrix_apply:
  fixes B :: "real^'n::finite^'n"
  shows "((- B) + \<delta> *\<^sub>R mat 1) *v h = - ((B - \<delta> *\<^sub>R mat 1) *v h)"
proof -
  have e: "(- B) + \<delta> *\<^sub>R mat 1 = - (B - \<delta> *\<^sub>R mat 1)"
    by simp
  show ?thesis
    unfolding e by (rule matrix_vector_neg_left)
qed

text \<open>Symmetry and positive semidefiniteness are closed conditions and so
  survive the passage to a limit point, proved entrywise via
  \<open>tendsto_vec_nth\<close>: convergence in \<open>real^'n^'n\<close> is convergence of every
  entry.\<close>

lemma tendsto_entry:
  fixes A :: "nat \<Rightarrow> real^'n::finite^'n"
  assumes conv: "A \<longlonglongrightarrow> A0"
  shows "(\<lambda>i. A i $ j $ k) \<longlonglongrightarrow> A0 $ j $ k"
  by (rule tendsto_vec_nth[OF tendsto_vec_nth[OF conv]])

lemma transpose_limit:
  fixes A :: "nat \<Rightarrow> real^'n::finite^'n"
  assumes conv: "A \<longlonglongrightarrow> A0" and sym: "\<And>i. transpose (A i) = A i"
  shows "transpose A0 = A0"
proof -
  have eq: "A0 $ j $ k = A0 $ k $ j" for j k
  proof -
    have f: "(\<lambda>i. A i $ j $ k) = (\<lambda>i. A i $ k $ j)"
    proof (rule ext)
      fix i
      have "A i $ j $ k = (transpose (A i)) $ k $ j"
        by (simp add: transpose_def)
      also have "\<dots> = A i $ k $ j"
        using sym by simp
      finally show "A i $ j $ k = A i $ k $ j" .
    qed
    have "(\<lambda>i. A i $ j $ k) \<longlonglongrightarrow> A0 $ k $ j"
      unfolding f by (rule tendsto_entry[OF conv])
    from tendsto_entry[OF conv] this show ?thesis
      by (rule LIMSEQ_unique)
  qed
  show ?thesis
    by (simp add: vec_eq_iff transpose_def eq)
qed

lemma tendsto_quadratic_form:
  fixes A :: "nat \<Rightarrow> real^'n::finite^'n"
  assumes conv: "A \<longlonglongrightarrow> A0"
  shows "(\<lambda>i. x \<bullet> (A i *v x)) \<longlonglongrightarrow> x \<bullet> (A0 *v x)"
proof -
  have e: "y \<bullet> (B *v y) = (\<Sum>j\<in>UNIV. y $ j * (\<Sum>k\<in>UNIV. B $ j $ k * y $ k))"
    for B :: "real^'n^'n" and y :: "real^'n"
    by (simp add: inner_vec_def matrix_vector_mult_def)
  show ?thesis
    unfolding e
    by (intro tendsto_sum tendsto_mult tendsto_const tendsto_entry[OF conv])
qed

text \<open>\<open>transpose_scaleR\<close> and \<open>transpose_add\<close> live in
  \<open>Matrix_Algebra\<close>.\<close>

lemma transpose_shifted_block:
  fixes M :: "real^'n::finite^'n"
  assumes s: "transpose M = M"
  shows "transpose (M + c *\<^sub>R mat 1) = M + c *\<^sub>R mat 1"
proof -
  have "transpose (M + c *\<^sub>R mat 1)
      = transpose M + transpose (c *\<^sub>R (mat 1 :: real^'n^'n))"
    by (rule transpose_add)
  also have "transpose (c *\<^sub>R (mat 1 :: real^'n^'n))
      = c *\<^sub>R transpose (mat 1 :: real^'n^'n)"
    by (rule transpose_scaleR)
  also have "transpose (mat 1 :: real^'n^'n) = mat 1"
    by (rule transpose_mat)
  finally show ?thesis using s by simp
qed

text \<open>The bridge between the jets' operator-form Hessian
  \<open>\<lambda>v. f v + c *\<^sub>R v\<close> and the matrix form the family theorem wants:
  taking the matrix of the shifted operator adds \<open>cI\<close>.  Every shifted
  fact then reduces to its unshifted counterpart plus
  \<open>transpose_shifted_block\<close>, the shifted positivity fact and \<open>norm_shifted_block\<close>.\<close>

lemma matrix_shift_apply:
  fixes M :: "real^'n::finite^'n"
  shows "(M + c *\<^sub>R mat 1) *v h = M *v h + c *\<^sub>R h"
proof -
  have "((M + c *\<^sub>R mat 1) *v h) $ i = (M *v h + c *\<^sub>R h) $ i" for i
  proof -
    have "((M + c *\<^sub>R mat 1) *v h) $ i
        = (\<Sum>j\<in>UNIV. (M $ i $ j + c * (if i = j then 1 else 0)) * h $ j)"
      by (simp add: matrix_vector_mult_def mat_def)
    also have "\<dots> = (\<Sum>j\<in>UNIV. M $ i $ j * h $ j)
        + (\<Sum>j\<in>UNIV. c * (if i = j then 1 else 0) * h $ j)"
      by (simp add: algebra_simps sum.distrib)
    also have "(\<Sum>j\<in>UNIV. c * (if i = j then 1 else 0) * h $ j)
        = (\<Sum>j\<in>UNIV. if j = i then c * h $ j else 0)"
      by (rule sum.cong) auto
    also have "(\<Sum>j\<in>UNIV. if j = i then c * h $ j else 0) = c * h $ i"
      by simp    finally show ?thesis
      by (simp add: matrix_vector_mult_def)
  qed
  then show ?thesis by (simp add: vec_eq_iff)
qed

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

text \<open>\<open>matvec_scaleR_right'\<close> is \<open>matvec_scaleR_right\<close> from
  \<open>Operator_Envelopes\<close>.\<close>

lemma affine_linear:
  fixes R :: "real^'n::finite^'n"
  shows "bounded_linear (\<lambda>z :: real^'n. c *\<^sub>R (R *v z))"
proof -
  have "linear (\<lambda>z :: real^'n. c *\<^sub>R (R *v z))"
    by (simp add: linear_iff matvec_add_right matvec_scaleR_right
        scaleR_right_distrib)
  then show ?thesis by (simp add: linear_conv_bounded_linear)
qed

lemma affine_has_derivative:
  fixes R :: "real^'n::finite^'n" and b :: "real^'n"
  shows "((\<lambda>z. c *\<^sub>R (R *v z) + b) has_derivative (\<lambda>h. c *\<^sub>R (R *v h))) (at y)"
proof -
  have lin: "((\<lambda>z :: real^'n. c *\<^sub>R (R *v z)) has_derivative
      (\<lambda>h. c *\<^sub>R (R *v h))) (at y)"
    by (rule bounded_linear.has_derivative[OF affine_linear has_derivative_ident])
  have "((\<lambda>z. c *\<^sub>R (R *v z) + b) has_derivative
      (\<lambda>h. c *\<^sub>R (R *v h) + 0)) (at y)"
    by (rule has_derivative_add[OF lin has_derivative_const])
  then show ?thesis by simp
qed

lemma conj_mat_continuous:
  fixes R :: "real^'n::finite^'n"
  assumes "continuous_on UNIV M"
  shows "continuous_on UNIV (\<lambda>y. transpose R ** M y ** R)"
proof -
  have lin: "linear (\<lambda>N :: real^'n^'n. transpose R ** N ** R)"
    unfolding linear_iff
    by (auto simp: matrix_matrix_mult_def vec_eq_iff sum.distrib
        sum_distrib_left sum_distrib_right algebra_simps)
  have bl: "bounded_linear (\<lambda>N :: real^'n^'n. transpose R ** N ** R)"
    using lin by (simp add: linear_conv_bounded_linear)
  show ?thesis by (rule bounded_linear.continuous_on[OF bl assms])
qed

text \<open>Two small facts about the inverse of the dilation, used to transfer
  lower semicontinuity and the bound to the transformed supersolution.\<close>

lemma affine_inv_dist:
  fixes R :: "real^'n::finite^'n" and b :: "real^'n"
  assumes orth: "orthogonal_matrix R" and c0: "0 < c"
  shows "dist ((1/c) *\<^sub>R (transpose R *v (X - b)))
             ((1/c) *\<^sub>R (transpose R *v (Y - b))) = (1/c) * dist X Y"
proof -
  have orthT: "orthogonal_matrix (transpose R)"
    using orth unfolding orthogonal_matrix_def by auto
  have e1: "transpose R *v (X - b) - transpose R *v (Y - b)
      = transpose R *v (X - Y)"
  proof -
    have "transpose R *v (X - b) - transpose R *v (Y - b)
        = transpose R *v ((X - b) - (Y - b))"
      by (rule matvec_diff_right[symmetric])
    also have "(X - b) - (Y - b) = X - Y" by simp
    finally show ?thesis .
  qed
  have d: "(1/c) *\<^sub>R (transpose R *v (X - b)) - (1/c) *\<^sub>R (transpose R *v (Y - b))
      = (1/c) *\<^sub>R (transpose R *v (X - Y))"
  proof -
    have "(1/c) *\<^sub>R (transpose R *v (X - b)) - (1/c) *\<^sub>R (transpose R *v (Y - b))
        = (1/c) *\<^sub>R (transpose R *v (X - b) - transpose R *v (Y - b))"
      by (rule scaleR_right_diff_distrib[symmetric])
    also have "\<dots> = (1/c) *\<^sub>R (transpose R *v (X - Y))" unfolding e1 by (rule refl)
    finally show ?thesis .
  qed
  have nn: "norm (transpose R *v (X - Y)) = norm (X - Y)"
    by (rule norm_orthogonal_matrix_vector[OF orthT])
  have "dist ((1/c) *\<^sub>R (transpose R *v (X - b)))
      ((1/c) *\<^sub>R (transpose R *v (Y - b)))
      = norm ((1/c) *\<^sub>R (transpose R *v (X - Y)))"
    unfolding dist_norm d by (rule refl)
  also have "\<dots> = \<bar>1/c\<bar> * norm (transpose R *v (X - Y))" by (rule norm_scaleR)
  also have "\<dots> = (1/c) * norm (X - Y)" unfolding nn using c0 by simp
  finally show ?thesis unfolding dist_norm .
qed

text \<open>On \<open>real^'n\<close> compactness is closedness together with a ball bound, so
  one hypothesis supplies both of the ones the transfer needs.  The radius is
  named only where it appears in a conclusion, which is clause (0).\<close>

lemma compact_cball_bound:
  fixes K :: "(real^'n::finite) set"
  assumes cK: "compact K"
  shows "\<exists>rK. 0 \<le> rK \<and> K \<subseteq> cball 0 rK"
proof -
  obtain a where a: "\<forall>x\<in>K. norm x \<le> a"
    using compact_imp_bounded[OF cK] unfolding bounded_iff by blast
  have "K \<subseteq> cball 0 (max a 0)" using a by (auto simp: dist_norm)
  moreover have "0 \<le> max a 0" by simp
  ultimately show ?thesis by blast
qed

(*<*)
end
(*>*)
