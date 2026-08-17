section \<open>The subspace-tangential field for Example 3.1, general \<open>k\<close>\<close>

(*<*)
theory Value_Function_Tangential_Field
  imports Value_Function_Supersolution_Case_2
    "Symmetric_Matrix_Spectra.Matrix_Algebra"
begin

(*>*)

section \<open>The subspace-tangential field for Example 3.1, general \<open>k\<close>\<close>

text \<open>The \<open>tanp\<close> block above, generalised: the ambient identity is replaced
  by the orthogonal projector onto an \<open>(n-k+1)\<close>-dimensional subspace
  containing the start.\<close>

subsection \<open>Small matrix, trace and inner-product facts\<close>

text \<open>\<open>matvec_add_right\<close> lives in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>

text \<open>\<open>matvec_sum_right\<close>, \<open>transpose_matrix_diff\<close> live in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


text \<open>\<open>trace_matrix_diff\<close> is \<open>trace_diff_matrix\<close> from
  @{theory Relative_Arbitrage.Operator_Formula}.\<close>

text \<open>\<open>unit_normalize\<close> lives in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


subsection \<open>The projector onto an orthonormal family\<close>

definition projmat :: "(nat \<Rightarrow> real^'n::finite) \<Rightarrow> nat \<Rightarrow> real^'n^'n" where
  "projmat b m = (\<Sum>i < m. outer_prod (b i) (b i))"

lemma projmat_sym: "transpose (projmat b m) = projmat b m"
  unfolding projmat_def by (simp add: transpose_matrix_sum)

lemma projmat_mv: "projmat b m *v z = (\<Sum>i < m. (b i \<bullet> z) *\<^sub>R b i)"
  unfolding projmat_def by (simp add: matrix_vector_mult_sum)

lemma projmat_trace:
  fixes b :: "nat \<Rightarrow> real^'n::finite"
  assumes orth: "\<And>i j. i < m \<Longrightarrow> j < m \<Longrightarrow> b i \<bullet> b j = (if i = j then 1 else 0)"
  shows "trace (projmat b m) = real m"
proof -
  have "trace (projmat b m) = (\<Sum>i < m. trace (outer_prod (b i) (b i)))"
    unfolding projmat_def by (rule trace_matrix_sum)
  also have "\<dots> = (\<Sum>i < m. b i \<bullet> b i)" by simp
  also have "\<dots> = (\<Sum>i < m. 1 :: real)" using orth by simp
  also have "\<dots> = real m" by simp
  finally show ?thesis .
qed

lemma projmat_fix:
  fixes b :: "nat \<Rightarrow> real^'n::finite"
  assumes orth: "\<And>i j. i < m \<Longrightarrow> j < m \<Longrightarrow> b i \<bullet> b j = (if i = j then 1 else 0)"
    and i: "i < m"
  shows "projmat b m *v b i = b i"
proof -
  have "projmat b m *v b i = (\<Sum>l < m. (b l \<bullet> b i) *\<^sub>R b l)" by (rule projmat_mv)
  also have "\<dots> = (\<Sum>l < m. if l = i then b i else 0)"
    by (rule sum.cong[OF refl]) (use orth i in auto)
  also have "\<dots> = b i" using i by simp
  finally show ?thesis .
qed

lemma projmat_idem:
  fixes b :: "nat \<Rightarrow> real^'n::finite"
  assumes orth: "\<And>i j. i < m \<Longrightarrow> j < m \<Longrightarrow> b i \<bullet> b j = (if i = j then 1 else 0)"
  shows "projmat b m ** projmat b m = projmat b m"
proof -
  have key: "projmat b m *v (projmat b m *v z) = projmat b m *v z" for z
  proof -
    have "projmat b m *v (projmat b m *v z)
        = projmat b m *v (\<Sum>l < m. (b l \<bullet> z) *\<^sub>R b l)"
      by (simp only: projmat_mv)
    also have "\<dots> = (\<Sum>l < m. projmat b m *v ((b l \<bullet> z) *\<^sub>R b l))"
      by (rule matvec_sum_right)
    also have "\<dots> = (\<Sum>l < m. (b l \<bullet> z) *\<^sub>R (projmat b m *v b l))"
      by (rule sum.cong[OF refl]) (simp add: matvec_scaleR_right)
    also have "\<dots> = (\<Sum>l < m. (b l \<bullet> z) *\<^sub>R b l)"
      by (rule sum.cong[OF refl]) (simp add: projmat_fix[OF orth])
    also have "\<dots> = projmat b m *v z" by (rule projmat_mv[symmetric])
    finally show ?thesis .
  qed
  show ?thesis
    unfolding matrix_eq using key by (metis matrix_vector_mul_assoc)
qed

lemma projmat_span_fix:
  fixes b :: "nat \<Rightarrow> real^'n::finite"
  assumes orth: "\<And>i j. i < m \<Longrightarrow> j < m \<Longrightarrow> b i \<bullet> b j = (if i = j then 1 else 0)"
    and x: "x \<in> span (b ` {..<m})"
  shows "projmat b m *v x = x"
proof -
  have sub: "subspace {y :: real^'n. projmat b m *v y = y}"
    unfolding subspace_def
    by (auto simp: matvec_add_right matvec_scaleR_right)
  have "b ` {..<m} \<subseteq> {y :: real^'n. projmat b m *v y = y}"
    using projmat_fix[OF orth] by auto
  then have "span (b ` {..<m}) \<subseteq> {y :: real^'n. projmat b m *v y = y}"
    using sub by (simp add: span_minimal)
  then show ?thesis using x by blast
qed

text \<open>\<open>orthonormal_inj\<close>, \<open>orthonormal_dim_span\<close> live in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


subsection \<open>The subspace-tangential field\<close>

definition tanpV :: "real^'n::finite^'n \<Rightarrow> real^'n \<Rightarrow> real^'n^'n" where
  "tanpV P z =
     P - outer_prod ((P *v z) /\<^sub>R norm (P *v z)) ((P *v z) /\<^sub>R norm (P *v z))"

text \<open>The lower eigenvalue bound.  The witnessing subspace is the span of the
  family cut by the hyperplane orthogonal to the singled-out direction: the
  dimension drops by at most one, which is exactly what \<open>n - k\<close> needs.\<close>

text \<open>The field is a projector, which is what makes the Euler chain's
  covariance equal to it and the radial drift vanish --- the two facts
  the construction below relies on.\<close>

text \<open>The radial direction is killed at the point itself: this is why the
  squared radius has no drift beyond the trace term, so the growth is exact
  rather than merely bounded.\<close>

subsection \<open>The subspace-tangential field with a clamped direction\<close>

text \<open>To feed the Euler chain the field must be defined and feasible
  everywhere, not just where \<open>P *v z \<noteq> 0\<close>.  Mirror the \<open>tanp\<close>/\<open>uvec\<close> pair:
  take the direction as a parameter and clamp its normalisation.\<close>

definition tanpU :: "real^'n::finite^'n \<Rightarrow> real^'n \<Rightarrow> real^'n^'n" where
  "tanpU P u = P - outer_prod u u"

definition uvecV :: "real^'n::finite^'n \<Rightarrow> real \<Rightarrow> real^'n \<Rightarrow> real^'n" where
  "uvecV P \<rho> z = (1 / max \<rho> (norm (P *v z))) *\<^sub>R (P *v z)"

lemma tanpU_sym:
  fixes P :: "real^'n::finite^'n" and u :: "real^'n"
  assumes P: "transpose P = P"
  shows "transpose (tanpU P u) = tanpU P u"
  unfolding tanpU_def by (simp add: transpose_matrix_diff P)

lemma tanpU_mv:
  fixes P :: "real^'n::finite^'n" and u y :: "real^'n"
  shows "tanpU P u *v y = P *v y - (u \<bullet> y) *\<^sub>R u"
  unfolding tanpU_def by (simp add: matrix_vector_mult_diff_rdistrib)

lemma tanpU_trace:
  fixes P :: "real^'n::finite^'n" and u :: "real^'n"
  shows "trace (tanpU P u) = trace P - u \<bullet> u"
  unfolding tanpU_def by (simp add: trace_diff_matrix)

lemma uvecV_norm_le:
  fixes P :: "real^'n::finite^'n" and z :: "real^'n"
  assumes rho0: "0 < \<rho>"
  shows "norm (uvecV P \<rho> z) \<le> 1"
proof -
  have mx0: "0 < max \<rho> (norm (P *v z))" using rho0 by simp
  have "norm (uvecV P \<rho> z) = norm (P *v z) / max \<rho> (norm (P *v z))"
    unfolding uvecV_def using mx0 by simp
  also have "\<dots> \<le> 1" using mx0 by (simp add: divide_le_eq)
  finally show ?thesis .
qed

lemma uvecV_fix:
  fixes P :: "real^'n::finite^'n" and z :: "real^'n"
  assumes Pidem: "P ** P = P"
  shows "P *v (uvecV P \<rho> z) = uvecV P \<rho> z"
proof -
  have PP: "P *v (P *v z) = P *v z"
    using Pidem by (metis matrix_vector_mul_assoc)
  show ?thesis unfolding uvecV_def
    by (simp add: matvec_scaleR_right PP)
qed

lemma uvecV_unit:
  fixes P :: "real^'n::finite^'n" and z :: "real^'n"
  assumes rho0: "0 < \<rho>" and far: "\<rho> \<le> norm (P *v z)"
  shows "norm (uvecV P \<rho> z) = 1"
proof -
  have mx: "max \<rho> (norm (P *v z)) = norm (P *v z)" using far by (simp add: max_def)
  have n0: "norm (P *v z) \<noteq> 0" using rho0 far by linarith
  show ?thesis unfolding uvecV_def mx using n0 by simp
qed

lemma uvecV_par:
  fixes P :: "real^'n::finite^'n" and z :: "real^'n"
  assumes rho0: "0 < \<rho>" and far: "\<rho> \<le> norm (P *v z)"
  shows "P *v z = norm (P *v z) *\<^sub>R uvecV P \<rho> z"
proof -
  have mx: "max \<rho> (norm (P *v z)) = norm (P *v z)" using far by (simp add: max_def)
  have n0: "norm (P *v z) \<noteq> 0" using rho0 far by linarith
  show ?thesis unfolding uvecV_def mx using n0 by simp
qed

text \<open>\<open>proj_inner_self\<close>, \<open>proj_inner_self'\<close> live in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


lemma tanpU_kill:
  fixes P :: "real^'n::finite^'n" and z :: "real^'n"
  assumes Psym: "transpose P = P" and Pidem: "P ** P = P"
    and rho0: "0 < \<rho>" and far: "\<rho> \<le> norm (P *v z)"
  shows "tanpU P (uvecV P \<rho> z) *v z = 0"
proof -
  define u where "u = uvecV P \<rho> z"
  have u1: "norm u = 1" unfolding u_def by (rule uvecV_unit[OF rho0 far])
  have par: "P *v z = norm (P *v z) *\<^sub>R u"
    unfolding u_def by (rule uvecV_par[OF rho0 far])
  have ufix: "P *v u = u" unfolding u_def by (rule uvecV_fix[OF Pidem])
  have uu1: "u \<bullet> u = 1" using u1 by (metis norm_eq_1)
  have uz: "u \<bullet> z = norm (P *v z)"
  proof -
    have "u \<bullet> z = (P *v u) \<bullet> z" unfolding ufix by (rule refl)
    also have "\<dots> = z \<bullet> (P *v u)" by (rule inner_commute)
    also have "\<dots> = (transpose P *v z) \<bullet> u" by (rule inner_transpose_matrix)
    also have "\<dots> = (P *v z) \<bullet> u" unfolding Psym by (rule refl)
    also have "\<dots> = (norm (P *v z) *\<^sub>R u) \<bullet> u"
      using par by (rule arg_cong[where f = "\<lambda>v. v \<bullet> u"])
    also have "\<dots> = norm (P *v z) * (u \<bullet> u)" by simp
    also have "\<dots> = norm (P *v z)" unfolding uu1 by simp
    finally show ?thesis .
  qed
  have "tanpU P u *v z = P *v z - (u \<bullet> z) *\<^sub>R u" by (rule tanpU_mv)
  also have "(u \<bullet> z) *\<^sub>R u = P *v z" unfolding uz by (rule par[symmetric])
  finally show ?thesis unfolding u_def by simp
qed

subsection \<open>Feasibility of the clamped field\<close>

lemma tanpU_psd:
  fixes P :: "real^'n::finite^'n" and u :: "real^'n"
  assumes Psym: "transpose P = P" and Pidem: "P ** P = P"
    and u1: "norm u \<le> 1" and ufix: "P *v u = u"
  shows "psd (tanpU P u)"
  unfolding psd_def
proof (intro conjI allI)
  show "transpose (tanpU P u) = tanpU P u" by (rule tanpU_sym[OF Psym])
next
  fix y :: "real^'n"
  have uy: "u \<bullet> y = (P *v y) \<bullet> u"
  proof -
    have "u \<bullet> y = (P *v u) \<bullet> y" unfolding ufix by (rule refl)
    also have "\<dots> = y \<bullet> (P *v u)" by (rule inner_commute)
    also have "\<dots> = (transpose P *v y) \<bullet> u" by (rule inner_transpose_matrix)
    also have "\<dots> = (P *v y) \<bullet> u" unfolding Psym by (rule refl)
    finally show ?thesis .
  qed
  have uu: "u \<bullet> u \<le> 1" using u1 by (simp add: power_le_one_iff
      dot_square_norm)
  have "(u \<bullet> y)\<^sup>2 = ((P *v y) \<bullet> u)\<^sup>2" unfolding uy by (rule refl)
  also have "\<dots> \<le> ((P *v y) \<bullet> (P *v y)) * (u \<bullet> u)"
    by (rule Cauchy_Schwarz_ineq)
  also have "\<dots> \<le> (P *v y) \<bullet> (P *v y)"
    using uu inner_ge_zero[of "P *v y"] by (simp add: mult_left_le)
  also have "\<dots> = y \<bullet> (P *v y)"
    by (rule proj_inner_self'[OF Psym Pidem, symmetric])
  finally have le: "(u \<bullet> y)\<^sup>2 \<le> y \<bullet> (P *v y)" .
  have "y \<bullet> (tanpU P u *v y) = y \<bullet> (P *v y) - (u \<bullet> y) * (y \<bullet> u)"
    unfolding tanpU_mv by (simp add: inner_diff_right)
  then have "y \<bullet> (tanpU P u *v y) = y \<bullet> (P *v y) - (u \<bullet> y)\<^sup>2"
    by (simp add: power2_eq_square inner_commute)
  then show "0 \<le> y \<bullet> (tanpU P u *v y)" using le by linarith
qed

lemma tanpU_eigen_ub:
  fixes P :: "real^'n::finite^'n" and u :: "real^'n"
  assumes Psym: "transpose P = P" and Pidem: "P ** P = P" and L1: "1 \<le> L"
  shows "eigen_ub (tanpU P u) L"
  unfolding eigen_ub_def
proof
  fix y :: "real^'n"
  have pq: "y \<bullet> (P *v y) = (P *v y) \<bullet> (P *v y)"
    by (rule proj_inner_self'[OF Psym Pidem])
  have shrink: "y \<bullet> (P *v y) \<le> y \<bullet> y"
  proof -
    have "(y - P *v y) \<bullet> (y - P *v y)
        = y \<bullet> y - y \<bullet> (P *v y) - (P *v y) \<bullet> y + (P *v y) \<bullet> (P *v y)"
      by (simp add: inner_diff_left inner_diff_right)
    also have "(P *v y) \<bullet> y = y \<bullet> (P *v y)" by (rule inner_commute)
    finally have "(y - P *v y) \<bullet> (y - P *v y) = y \<bullet> y - y \<bullet> (P *v y)"
      using pq by simp
    then show ?thesis using inner_ge_zero[of "y - P *v y"] by linarith
  qed
  have q: "y \<bullet> (tanpU P u *v y) = y \<bullet> (P *v y) - (u \<bullet> y) * (y \<bullet> u)"
    unfolding tanpU_mv by (simp add: inner_diff_right)
  have sq: "(u \<bullet> y) * (y \<bullet> u) = (u \<bullet> y)\<^sup>2"
    by (simp add: power2_eq_square inner_commute)
  have "y \<bullet> (tanpU P u *v y) \<le> y \<bullet> y"
    unfolding q sq using shrink zero_le_power2[of "u \<bullet> y"] by linarith
  also have "y \<bullet> y = 1 * (y \<bullet> y)" by simp
  also have "\<dots> \<le> L * (y \<bullet> y)" by (rule mult_right_mono[OF L1 inner_ge_zero])
  finally show "y \<bullet> (tanpU P u *v y) \<le> L * (y \<bullet> y)" .
qed

lemma tanpU_eigen_lb:
  fixes b :: "nat \<Rightarrow> real^'n::finite" and u :: "real^'n"
  assumes orth: "\<And>i j. i < m \<Longrightarrow> j < m \<Longrightarrow> b i \<bullet> b j = (if i = j then 1 else 0)"
  shows "eigen_lb (tanpU (projmat b m) u) (m - 1)"
proof -
  define P where "P = projmat b m"
  define W :: "(real^'n) set" where "W = span (b ` {..<m})"
  define S where "S = W \<inter> {x. u \<bullet> x = 0}"
  have subW: "subspace W" unfolding W_def by (rule subspace_span)
  have subH: "subspace {x :: real^'n. u \<bullet> x = 0}" by (rule subspace_hyperplane)
  have subS: "subspace S" unfolding S_def by (rule subspace_inter[OF subW subH])
  have dimW: "dim W = m" unfolding W_def by (rule orthonormal_dim_span[OF orth])
  have dimS: "m - 1 \<le> dim S"
  proof (cases "u = 0")
    case True
    have "S = W" unfolding S_def True by simp
    then show ?thesis unfolding dimW[symmetric] by simp
  next
    case False
    have dimH: "dim {x :: real^'n. u \<bullet> x = 0} = CARD('n) - 1"
      using False by (simp add: dim_hyperplane)
    have sums: "dim {x + y |x y. x \<in> W \<and> y \<in> {x :: real^'n. u \<bullet> x = 0}}
        + dim S = dim W + dim {x :: real^'n. u \<bullet> x = 0}"
      unfolding S_def by (rule dim_sums_Int[OF subW subH])
    have le: "dim {x + y |x y. x \<in> W \<and> y \<in> {x :: real^'n. u \<bullet> x = 0}}
        \<le> CARD('n)"
      using dim_subset_UNIV[of
        "{x + y |x y. x \<in> W \<and> y \<in> {x :: real^'n. u \<bullet> x = 0}}"] by simp
    have n1: "1 \<le> CARD('n)" by simp
    show ?thesis using sums le dimW dimH n1 by linarith
  qed
  show ?thesis
    unfolding eigen_lb_def P_def[symmetric]
  proof (intro exI[of _ S] conjI ballI)
    show "subspace S" by (rule subS)
    show "m - 1 \<le> dim S" by (rule dimS)
  next
    fix x assume xS: "x \<in> S"
    then have xW: "x \<in> span (b ` {..<m})" and xu: "u \<bullet> x = 0"
      unfolding S_def W_def by auto
    have Px: "P *v x = x" unfolding P_def by (rule projmat_span_fix[OF orth xW])
    have "x \<bullet> (tanpU P u *v x) = x \<bullet> (P *v x) - (u \<bullet> x) * (x \<bullet> u)"
      unfolding tanpU_mv by (simp add: inner_diff_right)
    also have "\<dots> = x \<bullet> x" unfolding Px xu by simp
    finally show "x \<bullet> x \<le> x \<bullet> (tanpU P u *v x)" by simp
  qed
qed

theorem tanpU_feasible:
  fixes b :: "nat \<Rightarrow> real^'n::finite" and u :: "real^'n"
  assumes orth: "\<And>i j. i < m \<Longrightarrow> j < m \<Longrightarrow> b i \<bullet> b j = (if i = j then 1 else 0)"
    and u1: "norm u \<le> 1" and ufix: "projmat b m *v u = u"
    and mk: "CARD('n) - k \<le> m - 1" and L1: "1 \<le> L"
  shows "tanpU (projmat b m) u \<in> feasible k L 0"
  unfolding feasible_def
proof (intro CollectI conjI)
  have Psym: "transpose (projmat b m) = projmat b m" by (rule projmat_sym)
  have Pidem: "projmat b m ** projmat b m = projmat b m"
    by (rule projmat_idem[OF orth])
  show "psd (tanpU (projmat b m) u)"
    by (rule tanpU_psd[OF Psym Pidem u1 ufix])
  show "tanpU (projmat b m) u *v 0 = 0" by simp
  show "eigen_ub (tanpU (projmat b m) u) L"
    by (rule tanpU_eigen_ub[OF Psym Pidem L1])
  show "eigen_lb (tanpU (projmat b m) u) (CARD('n) - k)"
    using tanpU_eigen_lb[where b = b and m = m and u = u, OF orth] mk
    unfolding eigen_lb_def by (meson le_trans)
qed

subsection \<open>Continuity and the covariance of the clamped field\<close>

lemma uvecV_cont:
  fixes P :: "real^'n::finite^'n"
  assumes rho0: "0 < \<rho>"
  shows "continuous_on UNIV (uvecV P \<rho>)"
proof -
  have pc: "continuous_on UNIV (\<lambda>z :: real^'n. P *v z)"
    by (simp add: linear_continuous_on
        linear_linear)
  have nz: "\<And>w :: real^'n. max \<rho> (norm (P *v w)) \<noteq> 0" using rho0 by simp
  show ?thesis
    unfolding uvecV_def
    by (intro continuous_intros pc) (use nz in simp_all)
qed

lemma tanpUV_cont:
  fixes P :: "real^'n::finite^'n"
  assumes rho0: "0 < \<rho>"
  shows "continuous_on UNIV (\<lambda>z. tanpU P (uvecV P \<rho> z))"
proof -
  have uc: "continuous_on UNIV (uvecV P \<rho>)" by (rule uvecV_cont[OF rho0])
  have ci: "continuous_on UNIV (\<lambda>z. uvecV P \<rho> z $ i)" for i
    by (rule continuous_on_compose2[OF
        linear_continuous_on[OF bounded_linear_vec_nth] uc]) auto
  have eq: "(\<lambda>z. tanpU P (uvecV P \<rho> z)) = (\<lambda>z. \<chi> i j.
      P $ i $ j - uvecV P \<rho> z $ i * uvecV P \<rho> z $ j)"
    by (rule ext) (simp add: tanpU_def outer_prod_def vec_eq_iff)
  show ?thesis unfolding eq
    by (intro continuous_on_vec_lambda continuous_intros ci)
qed

text \<open>\<open>tanpU_sq_norm_le\<close> lives in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


lemma tanpU_sq:
  fixes P :: "real^'n::finite^'n" and u :: "real^'n"
  assumes Psym: "transpose P = P" and Pidem: "P ** P = P"
    and ufix: "P *v u = u" and u1: "norm u \<le> 1"
  shows "tanpU P u ** tanpU P u = tanpU P (sqrt (2 - u \<bullet> u) *\<^sub>R u)"
proof -
  define a where "a = u \<bullet> u"
  have a0: "0 \<le> a" unfolding a_def by simp
  have anorm: "a = (norm u)\<^sup>2" unfolding a_def by (simp add: dot_square_norm)
  have a1: "a \<le> 1" unfolding anorm using u1 by (simp add: power_le_one)
  have a2: "0 \<le> 2 - a" using a1 by linarith
  have sq2: "sqrt (2 - a) * sqrt (2 - a) = 2 - a" using a2 by simp
  have uP: "u \<bullet> (P *v y) = u \<bullet> y" for y
  proof -
    have "u \<bullet> (P *v y) = (transpose P *v u) \<bullet> y" by (rule inner_transpose_matrix)
    also have "\<dots> = (P *v u) \<bullet> y" unfolding Psym by (rule refl)
    finally show ?thesis unfolding ufix .
  qed
  have PP: "P *v (P *v y) = P *v y" for y
    using Pidem by (metis matrix_vector_mul_assoc)
  have onP: "tanpU P u *v (P *v y) = P *v y - (u \<bullet> y) *\<^sub>R u" for y
    using tanpU_mv[of P u "P *v y"] unfolding PP uP by simp
  have onu: "tanpU P u *v u = (1 - a) *\<^sub>R u"
    using tanpU_mv[of P u u] unfolding ufix a_def[symmetric]
    by (simp add: algebra_simps)
  have coef: "(u \<bullet> y) + (u \<bullet> y) * (1 - a) = (2 - a) * (u \<bullet> y)" for y
    by (simp add: algebra_simps)
  have vec: "(u \<bullet> y) *\<^sub>R u + ((u \<bullet> y) * (1 - a)) *\<^sub>R u
      = ((2 - a) * (u \<bullet> y)) *\<^sub>R u" for y
    unfolding scaleR_left_distrib[symmetric] coef by (rule refl)
  have rhs: "(sqrt (2 - a) *\<^sub>R u \<bullet> y) *\<^sub>R (sqrt (2 - a) *\<^sub>R u)
      = ((2 - a) * (u \<bullet> y)) *\<^sub>R u" for y
  proof -
    have c: "(sqrt (2 - a) * (u \<bullet> y)) * sqrt (2 - a) = (2 - a) * (u \<bullet> y)"
    proof -
      have "(sqrt (2 - a) * (u \<bullet> y)) * sqrt (2 - a)
          = (sqrt (2 - a) * sqrt (2 - a)) * (u \<bullet> y)"
        by (simp add: algebra_simps)
      then show ?thesis unfolding sq2 .
    qed
    have "(sqrt (2 - a) *\<^sub>R u \<bullet> y) *\<^sub>R (sqrt (2 - a) *\<^sub>R u)
        = ((sqrt (2 - a) * (u \<bullet> y)) * sqrt (2 - a)) *\<^sub>R u"
      by (simp only: inner_scaleR_left scaleR_scaleR)
    then show ?thesis unfolding c .
  qed
  have key: "tanpU P u *v (tanpU P u *v y)
      = tanpU P (sqrt (2 - a) *\<^sub>R u) *v y" for y
  proof -
    have "tanpU P u *v (tanpU P u *v y)
        = tanpU P u *v (P *v y - (u \<bullet> y) *\<^sub>R u)"
      by (simp only: tanpU_mv)
    also have "\<dots> = tanpU P u *v (P *v y) - (u \<bullet> y) *\<^sub>R (tanpU P u *v u)"
      by (simp add: matvec_diff_right matvec_scaleR_right)
    also have "\<dots> = (P *v y - (u \<bullet> y) *\<^sub>R u)
        - ((u \<bullet> y) * (1 - a)) *\<^sub>R u"
      unfolding onP onu scaleR_scaleR by (rule refl)
    also have "\<dots> = P *v y - ((u \<bullet> y) *\<^sub>R u + ((u \<bullet> y) * (1 - a)) *\<^sub>R u)"
      by (simp only: diff_diff_add)
    also have "\<dots> = P *v y - ((2 - a) * (u \<bullet> y)) *\<^sub>R u"
      unfolding vec by (rule refl)
    also have "\<dots> = tanpU P (sqrt (2 - a) *\<^sub>R u) *v y"
      unfolding tanpU_mv rhs by (rule refl)
    finally show ?thesis .
  qed  show ?thesis
    unfolding a_def[symmetric] matrix_eq using key
    by (metis matrix_vector_mul_assoc)
qed

theorem tanpU_sq_sconstraint:
  fixes b :: "nat \<Rightarrow> real^'n::finite" and u :: "real^'n"
  assumes orth: "\<And>i j. i < m \<Longrightarrow> j < m \<Longrightarrow> b i \<bullet> b j = (if i = j then 1 else 0)"
    and u1: "norm u \<le> 1" and ufix: "projmat b m *v u = u"
    and mk: "CARD('n) - k \<le> m - 1" and L1: "1 \<le> L"
  shows "tanpU (projmat b m) u ** transpose (tanpU (projmat b m) u)
      \<in> sconstraint k L"
proof -
  have Psym: "transpose (projmat b m) = projmat b m" by (rule projmat_sym)
  have Pidem: "projmat b m ** projmat b m = projmat b m"
    by (rule projmat_idem[OF orth])
  have tsym: "transpose (tanpU (projmat b m) u) = tanpU (projmat b m) u"
    by (rule tanpU_sym[OF Psym])
  have sq: "tanpU (projmat b m) u ** transpose (tanpU (projmat b m) u)
      = tanpU (projmat b m) (sqrt (2 - u \<bullet> u) *\<^sub>R u)"
    unfolding tsym by (rule tanpU_sq[OF Psym Pidem ufix u1])
  have n1: "norm (sqrt (2 - u \<bullet> u) *\<^sub>R u) \<le> 1" by (rule tanpU_sq_norm_le[OF u1])
  have f1: "projmat b m *v (sqrt (2 - u \<bullet> u) *\<^sub>R u) = sqrt (2 - u \<bullet> u) *\<^sub>R u"
    by (simp add: matvec_scaleR_right ufix)
  have "tanpU (projmat b m) (sqrt (2 - u \<bullet> u) *\<^sub>R u) \<in> feasible k L 0"
    by (rule tanpU_feasible[OF orth n1 f1 mk L1])
  then show ?thesis unfolding sq using feasible_subset_sconstraint by blast
qed

text \<open>\<open>proj_norm_le\<close> lives in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


lemma tanpU_absorb:
  fixes P :: "real^'n::finite^'n" and u :: "real^'n"
  assumes Pidem: "P ** P = P" and ufix: "P *v u = u"
  shows "P ** tanpU P u = tanpU P u"
proof -
  have PP: "P *v (P *v y) = P *v y" for y
    using Pidem by (metis matrix_vector_mul_assoc)
  have key: "P *v (tanpU P u *v y) = tanpU P u *v y" for y
  proof -
    have "P *v (tanpU P u *v y) = P *v (P *v y - (u \<bullet> y) *\<^sub>R u)"
      by (simp only: tanpU_mv)
    also have "\<dots> = P *v (P *v y) - (u \<bullet> y) *\<^sub>R (P *v u)"
      by (simp add: matvec_diff_right matvec_scaleR_right)
    also have "\<dots> = P *v y - (u \<bullet> y) *\<^sub>R u" unfolding PP ufix by (rule refl)
    also have "\<dots> = tanpU P u *v y" by (simp only: tanpU_mv)
    finally show ?thesis .
  qed
  show ?thesis unfolding matrix_eq using key by (metis matrix_vector_mul_assoc)
qed

lemma tanpU_kill_proj:
  fixes P :: "real^'n::finite^'n" and z :: "real^'n"
  assumes rho0: "0 < \<rho>" and far: "\<rho> \<le> norm (P *v z)" and Pidem: "P ** P = P"
  shows "tanpU P (uvecV P \<rho> z) *v (P *v z) = 0"
proof -
  define u where "u = uvecV P \<rho> z"
  have un: "norm u = 1" unfolding u_def by (rule uvecV_unit[OF rho0 far])
  have par: "P *v z = norm (P *v z) *\<^sub>R u"
    unfolding u_def by (rule uvecV_par[OF rho0 far])
  have PP: "P *v (P *v z) = P *v z" using Pidem by (metis matrix_vector_mul_assoc)
  have ip: "u \<bullet> (P *v z) = norm (P *v z)"
  proof -
    have "u \<bullet> (P *v z) = u \<bullet> (norm (P *v z) *\<^sub>R u)"
      by (rule arg_cong[where f = "\<lambda>w. u \<bullet> w", OF par])
    also have "\<dots> = norm (P *v z) * (u \<bullet> u)" by simp
    also have "\<dots> = norm (P *v z)" using un by (simp add: dot_square_norm)
    finally show ?thesis .
  qed
  have "tanpU P u *v (P *v z) = P *v (P *v z) - (u \<bullet> (P *v z)) *\<^sub>R u"
    by (rule tanpU_mv)
  also have "\<dots> = P *v z - norm (P *v z) *\<^sub>R u" unfolding PP ip by (rule refl)
  also have "\<dots> = 0" unfolding par[symmetric] by simp
  finally show ?thesis unfolding u_def .
qed

text \<open>The exact growth identity for the subspace-tangential field, for
  general \<open>k\<close>: inside the region where the projection onto
  \<open>V = span (b ` {..<m})\<close> is longer than the clamp \<open>\<rho>\<close>, the squared distance
  from the origin grows at the exact rate \<open>m - 1\<close>.  Taking \<open>m = CARD('n)\<close>
  recovers @{thm [source] tangential_exact_growth} at \<open>y\<^sub>0 = 0\<close>; taking
  \<open>m = CARD('n) - k + 1\<close> gives the rate \<open>real (CARD('n) - k)\<close> that
  Example 3.1 asks for.

  The conclusion pins both the full norm and the projected norm, and they
  coincide: the two Euler slots carry the quadratics \<open>|P z|\<^sup>2\<close> (lower) and
  \<open>|z|\<^sup>2\<close> (upper), and \<open>|P w| \<le> |w|\<close> squeezes them together.  That is what
  makes the region's inner barrier --- stated in the projected norm, as
  \<open>tanpU_kill_proj\<close> demands --- a barrier for a quantity that only grows.\<close>

theorem subspace_tangential_exact_growth:
  fixes b :: "nat \<Rightarrow> real^'n::finite" and x :: "real^'n" and \<rho> rB T :: real
  assumes T0: "0 < T" and L1: "1 \<le> L" and rho0: "0 < \<rho>"
    and orth: "\<And>i j. i < m \<Longrightarrow> j < m \<Longrightarrow> b i \<bullet> b j = (if i = j then 1 else 0)"
    and mk: "CARD('n) - k \<le> m - 1"
    and xfix: "projmat b m *v x = x"
  shows "\<exists>P \<in> exit_class k L T x. AE \<omega> in P. \<forall>t.
      0 < t \<longrightarrow> t \<le> T \<longrightarrow>
      (\<forall>s\<in>{0..t}. fst (\<omega> s)
          \<in> {w. \<rho> < norm (projmat b m *v w)} \<inter> ball 0 rB) \<longrightarrow>
      (norm (projmat b m *v fst (\<omega> t)))\<^sup>2 = (norm x)\<^sup>2 + t * (real m - 1)
        \<and> (norm (fst (\<omega> t)))\<^sup>2 = (norm x)\<^sup>2 + t * (real m - 1)"
proof -
  have Psym: "transpose (projmat b m) = projmat b m" by (rule projmat_sym)
  have Pidem: "projmat b m ** projmat b m = projmat b m"
    by (rule projmat_idem[OF orth])
  define RO where
    "RO = {w :: real^'n. \<rho> < norm (projmat b m *v w)} \<inter> ball 0 rB"
  define SF where "SF = (\<lambda>z. tanpU (projmat b m) (uvecV (projmat b m) \<rho> z))"
  define Rn where "Rn = rB + norm x"
  have SFc: "continuous_on UNIV SF"
    unfolding SF_def by (rule tanpUV_cont[OF rho0])
  have SFs: "\<And>z. SF z ** transpose (SF z) \<in> sconstraint k L"
    unfolding SF_def
    by (rule tanpU_sq_sconstraint[OF orth uvecV_norm_le[OF rho0]
          uvecV_fix[OF Pidem] mk L1])
  have ROo: "open RO"
  proof -
    have mvc: "continuous_on UNIV (\<lambda>w :: real^'n. projmat b m *v w)"
      by (simp add: linear_continuous_on
          linear_linear)
    have pc: "continuous_on UNIV (\<lambda>w :: real^'n. norm (projmat b m *v w))"
      using mvc by (rule continuous_on_norm)
    have "open {w :: real^'n. \<rho> < norm (projmat b m *v w)}"
      by (rule open_Collect_less[OF continuous_on_const pc])
    then show ?thesis unfolding RO_def by (intro open_Int open_ball)
  qed
  have ROb: "\<And>z. z \<in> RO \<Longrightarrow> norm (z - x) \<le> Rn"
  proof -
    fix z :: "real^'n" assume "z \<in> RO"
    then have "norm z < rB"
      unfolding RO_def by (simp add: dist_norm)
    moreover have "norm (z - x) \<le> norm z + norm x"
      by (metis
          norm_triangle_ineq4)
    ultimately show "norm (z - x) \<le> Rn" unfolding Rn_def by linarith
  qed
  have farRO: "\<rho> \<le> norm (projmat b m *v z)" if z: "z \<in> RO" for z
    using z unfolding RO_def by auto
  have unitRO: "norm (uvecV (projmat b m) \<rho> z) = 1" if z: "z \<in> RO" for z
    by (rule uvecV_unit[OF rho0 farRO[OF z]])
  have uuRO: "uvecV (projmat b m) \<rho> z \<bullet> uvecV (projmat b m) \<rho> z = 1"
    if z: "z \<in> RO" for z
    using unitRO[OF z] by (simp add: dot_square_norm)
  have tsym: "transpose (SF z) = SF z" for z
    unfolding SF_def by (rule tanpU_sym[OF Psym])
  \<comment> \<open>slot 1: the quadratic \<open>|P z|\<^sup>2\<close>, whose kill is \<open>tanpU_kill_proj\<close>\<close>
  have kill1: "transpose (SF z) *v (2 *\<^sub>R x
      + ((2::real) *\<^sub>R projmat b m) *v (z - x)) = 0" if z: "z \<in> RO" for z
  proof -
    have arg: "2 *\<^sub>R x + ((2::real) *\<^sub>R projmat b m) *v (z - x)
        = 2 *\<^sub>R (projmat b m *v z)"
      by (simp add: scaleR_matrix_vector matvec_diff_right
          scaleR_right_diff_distrib xfix)    have k0: "SF z *v (projmat b m *v z) = 0"
      unfolding SF_def by (rule tanpU_kill_proj[OF rho0 farRO[OF z] Pidem])
    have "transpose (SF z) *v (2 *\<^sub>R (projmat b m *v z))
        = 2 *\<^sub>R (transpose (SF z) *v (projmat b m *v z))"
      by (rule matvec_scaleR_right)
    also have "\<dots> = 0" unfolding tsym k0 by simp
    finally show ?thesis unfolding arg .
  qed
  \<comment> \<open>slot 2: the quadratic \<open>-|z|\<^sup>2\<close>, whose kill is \<open>tanpU_kill\<close>\<close>
  have kill2: "transpose (SF z) *v ((-2) *\<^sub>R x
      + ((-2::real) *\<^sub>R mat 1) *v (z - x)) = 0" if z: "z \<in> RO" for z
  proof -
    have argc: "c' *\<^sub>R x + (c' *\<^sub>R mat 1) *v (z - x) = c' *\<^sub>R z" for c'
      by (simp add: scaleR_matrix_vector
          scaleR_right_diff_distrib scaleR_add_right)
    have arg: "(-2) *\<^sub>R x + ((-2::real) *\<^sub>R mat 1) *v (z - x)
        = (-2) *\<^sub>R z"
      by (rule argc)    have k0: "SF z *v z = 0"
      unfolding SF_def by (rule tanpU_kill[OF Psym Pidem rho0 farRO[OF z]])
    have "transpose (SF z) *v ((-2) *\<^sub>R z) = (-2) *\<^sub>R (transpose (SF z) *v z)"
      by (rule matvec_scaleR_right)
    also have "\<dots> = 0" unfolding tsym k0 by simp
    finally show ?thesis unfolding arg .
  qed
  have sqRO: "SF z ** transpose (SF z)
      = tanpU (projmat b m) (uvecV (projmat b m) \<rho> z)"
    if z: "z \<in> RO" for z
  proof -
    define u where "u = uvecV (projmat b m) \<rho> z"
    have uu: "u \<bullet> u = 1" unfolding u_def by (rule uuRO[OF z])
    have ufix: "projmat b m *v u = u"
      unfolding u_def by (rule uvecV_fix[OF Pidem])
    have u1: "norm u \<le> 1" unfolding u_def by (rule uvecV_norm_le[OF rho0])
    have "SF z ** transpose (SF z)
        = tanpU (projmat b m) u ** tanpU (projmat b m) u"
      unfolding SF_def u_def tanpU_sym[OF Psym] by (rule refl)
    also have "\<dots> = tanpU (projmat b m) (sqrt (2 - u \<bullet> u) *\<^sub>R u)"
      by (rule tanpU_sq[OF Psym Pidem ufix u1])
    also have "\<dots> = tanpU (projmat b m) u" unfolding uu by simp
    finally show ?thesis unfolding u_def .
  qed
  have trtan: "trace (tanpU (projmat b m) (uvecV (projmat b m) \<rho> z))
      = real m - 1" if z: "z \<in> RO" for z
  proof -
    have "trace (tanpU (projmat b m) (uvecV (projmat b m) \<rho> z))
        = trace (projmat b m)
          - uvecV (projmat b m) \<rho> z \<bullet> uvecV (projmat b m) \<rho> z"
      by (rule tanpU_trace)
    also have "\<dots> = real m - 1"
      by (simp only: projmat_trace[OF orth] uuRO[OF z])
    finally show ?thesis .
  qed
  have trRO: "trace ((c' *\<^sub>R mat 1) ** (SF z ** transpose (SF z)))
      = c' * (real m - 1)"
    if z: "z \<in> RO" for z c'
  proof -
    have "(c' *\<^sub>R mat 1) ** (SF z ** transpose (SF z))
        = c' *\<^sub>R (SF z ** transpose (SF z))"
      by (simp add: scaleR_matrix_mult)
    then have step: "trace ((c' *\<^sub>R mat 1) ** (SF z ** transpose (SF z)))
        = c' * trace (SF z ** transpose (SF z))"
      by (simp add: trace_scaleR)
    have "trace (SF z ** transpose (SF z)) = real m - 1"
      unfolding sqRO[OF z] by (rule trtan[OF z])
    then show ?thesis unfolding step by simp
  qed
  have trP: "trace (((2::real) *\<^sub>R projmat b m) ** (SF z ** transpose (SF z)))
      = 2 * (real m - 1)" if z: "z \<in> RO" for z
  proof -
    have ab: "projmat b m ** (SF z ** transpose (SF z))
        = SF z ** transpose (SF z)"
      unfolding sqRO[OF z]
      by (rule tanpU_absorb[OF Pidem uvecV_fix[OF Pidem]])
    have "((2::real) *\<^sub>R projmat b m) ** (SF z ** transpose (SF z))
        = (2::real) *\<^sub>R (projmat b m ** (SF z ** transpose (SF z)))"
      by (simp add: scaleR_matrix_mult)
    then have e: "((2::real) *\<^sub>R projmat b m) ** (SF z ** transpose (SF z))
        = (2::real) *\<^sub>R (SF z ** transpose (SF z))"
      unfolding ab .
    have "trace (SF z ** transpose (SF z)) = real m - 1"
      unfolding sqRO[OF z] by (rule trtan[OF z])
    then show ?thesis unfolding e trace_scaleR by simp
  qed
  have sym1: "transpose ((2::real) *\<^sub>R projmat b m)
      = (2::real) *\<^sub>R projmat b m"
  proof -
    have "transpose ((2::real) *\<^sub>R projmat b m)
        = (2::real) *\<^sub>R transpose (projmat b m)"
      by (simp add: transpose_def vec_eq_iff)
    then show ?thesis unfolding Psym .
  qed
  have sym2: "transpose ((-2::real) *\<^sub>R mat 1 :: real^'n^'n)
      = (-2::real) *\<^sub>R mat 1"
    by (simp add: transpose_def vec_eq_iff mat_def)
  obtain P where P: "P \<in> exit_class k L T x"
    and AE2: "AE \<omega> in P. \<forall>t.
      0 < t \<longrightarrow> t \<le> T \<longrightarrow> (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> RO) \<longrightarrow>
      (t * (2 * (real m - 1)) / 2
        \<le> (2 *\<^sub>R x) \<bullet> (fst (\<omega> t) - x)
          + (1/2) * ((fst (\<omega> t) - x)
              \<bullet> (((2::real) *\<^sub>R projmat b m) *v (fst (\<omega> t) - x))))
      \<and> (t * (- 2 * (real m - 1)) / 2
        \<le> ((-2) *\<^sub>R x) \<bullet> (fst (\<omega> t) - x)
          + (1/2) * ((fst (\<omega> t) - x)
              \<bullet> (((-2::real) *\<^sub>R mat 1) *v (fst (\<omega> t) - x))))"
  proof -
    have marg1: "\<And>z. z \<in> RO \<Longrightarrow> 2 * (real m - 1)
        \<le> trace (((2::real) *\<^sub>R projmat b m) ** (SF z ** transpose (SF z)))"
      using trP by simp
    have marg2: "\<And>z. z \<in> RO \<Longrightarrow> - 2 * (real m - 1)
        \<le> trace (((-2::real) *\<^sub>R mat 1) ** (SF z ** transpose (SF z)))"
    proof -
      fix z :: "real^'n" assume zRO: "z \<in> RO"
      show "- 2 * (real m - 1)
          \<le> trace (((-2::real) *\<^sub>R mat 1) ** (SF z ** transpose (SF z)))"
        using trRO[OF zRO, of "-2"] by simp
    qed
    show ?thesis
      using eulerp_limit_good2_region[OF T0 L1 SFc SFs sym1 sym2
          ROo ROb kill1 marg1 kill2 marg2] that by blast
  qed
  show ?thesis
  proof (intro bexI[OF _ P])
    show "AE \<omega> in P. \<forall>t.
        0 < t \<longrightarrow> t \<le> T \<longrightarrow>
        (\<forall>s\<in>{0..t}. fst (\<omega> s)
            \<in> {w. \<rho> < norm (projmat b m *v w)} \<inter> ball 0 rB)
        \<longrightarrow> (norm (projmat b m *v fst (\<omega> t)))\<^sup>2
              = (norm x)\<^sup>2 + t * (real m - 1)
          \<and> (norm (fst (\<omega> t)))\<^sup>2 = (norm x)\<^sup>2 + t * (real m - 1)"
      using AE2
    proof (eventually_elim)
      case (elim \<omega>)
      show ?case
      proof (intro allI impI)
        fix t assume t0: "0 < t" and tT: "t \<le> T"
          and inb: "\<forall>s\<in>{0..t}. fst (\<omega> s)
            \<in> {w. \<rho> < norm (projmat b m *v w)} \<inter> ball 0 rB"
        have inb': "\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> RO"
          using inb unfolding RO_def by blast
        have g1: "t * (2 * (real m - 1)) / 2
            \<le> (2 *\<^sub>R x) \<bullet> (fst (\<omega> t) - x)
              + (1/2) * ((fst (\<omega> t) - x)
                  \<bullet> (((2::real) *\<^sub>R projmat b m) *v (fst (\<omega> t) - x)))"
          and g2: "t * (- 2 * (real m - 1)) / 2
            \<le> ((-2) *\<^sub>R x) \<bullet> (fst (\<omega> t) - x)
              + (1/2) * ((fst (\<omega> t) - x)
                  \<bullet> (((-2::real) *\<^sub>R mat 1) *v (fst (\<omega> t) - x)))"
          using elim t0 tT inb' by blast+
        define d where "d = fst (\<omega> t) - x"
        have e1: "(2 *\<^sub>R x) \<bullet> d = 2 * (x \<bullet> d)"
          by simp
        have e2: "((-2) *\<^sub>R x) \<bullet> d = - 2 * (x \<bullet> d)"
          by simp
        have e3: "d \<bullet> (((2::real) *\<^sub>R projmat b m) *v d)
            = 2 * (d \<bullet> (projmat b m *v d))"
          by (simp add: scaleR_matrix_vector)
        have negmv: "\<And>A :: real^'n^'n. (- A) *v d = - (A *v d)"
          by (simp add: matrix_vector_mult_def vec_eq_iff sum_negf)
        have e4: "d \<bullet> (((-2::real) *\<^sub>R mat 1) *v d) = - 2 * (d \<bullet> d)"
          by (simp add: negmv scaleR_matrix_vector)

        have id1: "t * (2 * (real m - 1)) / 2 = t * (real m - 1)" by simp
        have id2: "t * (- 2 * (real m - 1)) / 2 = - (t * (real m - 1))"
          by (simp add: field_simps)
        have xPd: "x \<bullet> (projmat b m *v d) = x \<bullet> d"
        proof -
          have "x \<bullet> (projmat b m *v d)
              = (transpose (projmat b m) *v x) \<bullet> d"
            by (rule inner_transpose_matrix)
          also have "\<dots> = (projmat b m *v x) \<bullet> d"
            unfolding Psym by (rule refl)
          finally show ?thesis unfolding xfix .
        qed
        have dPd: "(projmat b m *v d) \<bullet> (projmat b m *v d)
            = d \<bullet> (projmat b m *v d)"
          by (rule proj_inner_self'[OF Psym Pidem, symmetric])
        have projsplit: "(norm (projmat b m *v fst (\<omega> t)))\<^sup>2
            = (norm x)\<^sup>2 + (2 * (x \<bullet> d) + d \<bullet> (projmat b m *v d))"
        proof -
          have dd: "projmat b m *v fst (\<omega> t) = x + projmat b m *v d"
          proof -
            have "fst (\<omega> t) = x + d" unfolding d_def by simp
            then have "projmat b m *v fst (\<omega> t)
                = projmat b m *v x + projmat b m *v d"
              by (simp add: matvec_add_right)
            then show ?thesis unfolding xfix .
          qed
          have "(norm (projmat b m *v fst (\<omega> t)))\<^sup>2
              = (projmat b m *v fst (\<omega> t)) \<bullet> (projmat b m *v fst (\<omega> t))"
            by (simp add: dot_square_norm)
          also have "\<dots> = x \<bullet> x + 2 * (x \<bullet> (projmat b m *v d))
              + (projmat b m *v d) \<bullet> (projmat b m *v d)"
            unfolding dd
            by (simp add: inner_add_left inner_add_right inner_commute)
          also have "x \<bullet> x = (norm x)\<^sup>2" by (simp add: dot_square_norm)
          finally show ?thesis using xPd dPd by simp
        qed
        have split: "(norm (fst (\<omega> t)))\<^sup>2
            = (norm x)\<^sup>2 + (2 * (x \<bullet> d) + d \<bullet> d)"
        proof -
          have dd: "fst (\<omega> t) = x + d" unfolding d_def by simp
          have "(norm (fst (\<omega> t)))\<^sup>2 = (fst (\<omega> t)) \<bullet> (fst (\<omega> t))"
            by (simp add: dot_square_norm)
          also have "\<dots> = x \<bullet> x + 2 * (x \<bullet> d) + d \<bullet> d"
            unfolding dd
            by (simp add: inner_add_left inner_add_right inner_commute)
          also have "x \<bullet> x = (norm x)\<^sup>2" by (simp add: dot_square_norm)
          finally show ?thesis by simp
        qed
        have pge: "(norm x)\<^sup>2 + t * (real m - 1)
            \<le> (norm (projmat b m *v fst (\<omega> t)))\<^sup>2"
          using g1[unfolded id1]
          unfolding d_def[symmetric] e1 e3 projsplit
          by linarith
        have nle: "(norm (fst (\<omega> t)))\<^sup>2 \<le> (norm x)\<^sup>2 + t * (real m - 1)"
          using g2[unfolded id2]
          unfolding d_def[symmetric] e2 e4 split
          by linarith
        have ple: "(norm (projmat b m *v fst (\<omega> t)))\<^sup>2
            \<le> (norm (fst (\<omega> t)))\<^sup>2"
        proof -
          have "norm (projmat b m *v fst (\<omega> t)) \<le> norm (fst (\<omega> t))"
            by (rule proj_norm_le[OF Psym Pidem])
          then show ?thesis by (intro power_mono) simp_all
        qed
        show "(norm (projmat b m *v fst (\<omega> t)))\<^sup>2
              = (norm x)\<^sup>2 + t * (real m - 1)
            \<and> (norm (fst (\<omega> t)))\<^sup>2 = (norm x)\<^sup>2 + t * (real m - 1)"
          using pge ple nle by linarith
      qed
    qed
  qed
qed
text \<open>@{thm [source] tangential_exact_growth} gives the unclamped tangential
  field exact growth at rate \<open>real CARD('n) - 1\<close>, which for \<open>k = 1\<close> equals
  \<open>real (CARD('n) - k)\<close>.\<close>

text \<open>The trace of the field is exactly the growth rate \<open>n - k\<close> needed above.\<close>

subsection \<open>An orthonormal family through a prescribed unit vector\<close>

text \<open>\<open>orthonormal_family_containing\<close> lives in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>



(*<*)
end
(*>*)
