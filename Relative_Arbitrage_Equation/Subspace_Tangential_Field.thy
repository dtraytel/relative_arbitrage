(*<*)
theory Subspace_Tangential_Field
  imports
    Elliptic_Operator
    "Symmetric_Matrix_Spectra.Orthogonal_Projections"
begin

(*>*)

section \<open>The subspace-tangential field\<close>

text \<open>The tangential projector field: the orthogonal projector onto a
  subspace with one unit direction of that subspace removed, together with its
  clamped direction field.  For \<open>m - 1 \<ge> n - k\<close> the field is feasible for the
  eigenvalue constraint of the operator, it kills its own direction, and it
  is continuous in the clamped variables.  These are deterministic matrix
  facts, without the controlled processes that use them.\<close>

subsection \<open>The subspace-tangential field with a clamped direction\<close>

text \<open>To feed the Euler chain the field must be defined and feasible
  everywhere, not just where \<open>P *v z \<noteq> 0\<close>: take the direction as a
  parameter and clamp its normalisation.\<close>

definition tanpU :: "real^'n::finite^'n \<Rightarrow> real^'n \<Rightarrow> real^'n^'n" where
  "tanpU P u = P - outer_prod u u"

definition uvecV :: "real^'n::finite^'n \<Rightarrow> real \<Rightarrow> real^'n \<Rightarrow> real^'n" where
  "uvecV P \<rho> z = (1 / max \<rho> (norm (P *v z))) *\<^sub>R (P *v z)"

lemma tanpU_sym:
  fixes P :: "real^'n::finite^'n" and u :: "real^'n"
  assumes P: "transpose P = P"
  shows "transpose (tanpU P u) = tanpU P u"
  unfolding tanpU_def by (simp add: transpose_diff_matrix P)

lemma tanpU_mv:
  fixes P :: "real^'n::finite^'n" and u y :: "real^'n"
  shows "tanpU P u *v y = P *v y - (u \<bullet> y) *\<^sub>R u"
  unfolding tanpU_def by (simp add: matrix_vector_mult_diff_rdistrib)

lemma tanpU_trace:
  fixes P :: "real^'n::finite^'n" and u :: "real^'n"
  shows "trace (tanpU P u) = trace P - u \<bullet> u"
  unfolding tanpU_def by (simp add: trace_sub)

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
    by (simp add: matrix_vector_mult_scaleR PP)
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

text \<open>Once the clamp is inactive, \<open>\<rho> \<le> |P z|\<close>, the field kills the point
  itself: this is why the squared radius has no drift beyond the trace term,
  so the growth is exact rather than merely bounded.\<close>

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
    by (rule proj_quadform_self[unfolded is_proj_def, OF conjI[OF Psym Pidem], symmetric])
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
    by (rule proj_quadform_self[unfolded is_proj_def, OF conjI[OF Psym Pidem]])
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

text \<open>The lower eigenvalue bound.  The witnessing subspace is the span of the
  family cut by the hyperplane orthogonal to the singled-out direction: the
  dimension drops by at most one, which is exactly what \<open>n - k\<close> needs.\<close>

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

text \<open>The square of the field is the field at the rescaled direction
  \<open>sqrt (2 - u \<bullet> u) u\<close>, so for a unit direction the field is a
  projector; this is what makes the covariance of a process driven by it
  equal to the field.\<close>


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
      by (simp add: matrix_vector_mult_diff_distrib matrix_vector_mult_scaleR)
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
      by (simp add: matrix_vector_mult_diff_distrib matrix_vector_mult_scaleR)
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

(*<*)
end
(*>*)
