
(*<*)
theory Householder_Rotation
  imports Outer_Products
begin

(*>*)

text \<open>
  One Householder reflection \<open>hrefl\<close> and the rotation \<open>rotm\<close> built from a
  pair of them: the product of two reflections, one fixed at \<open>q\<close> and one at
  the bisector of \<open>q\<close> and \<open>w\<close>, carries \<open>q\<close> onto the ray through \<open>w\<close> and is
  the identity at \<open>w = q\<close>. Both are stated without normalising their axis,
  since real division by zero is zero, so the algebraic facts below are
  unconditional in the reflection's axis.
\<close>

section \<open>The Householder reflection\<close>

text \<open>\<open>continuous_on_matrix_entry\<close>, \<open>continuous_on_matrix_mult\<close> and
  \<open>continuous_on_matrix_transpose\<close> live in
  @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>

definition hrefl :: "real^'n::finite \<Rightarrow> real^'n^'n" where
  "hrefl v = mat 1 - (2 / (v \<bullet> v)) *\<^sub>R outer_prod v v"

lemma hrefl_apply: "hrefl v *v z = z - (2 * (v \<bullet> z) / (v \<bullet> v)) *\<^sub>R v"
proof -
  have "hrefl v *v z = mat 1 *v z - ((2 / (v \<bullet> v)) *\<^sub>R outer_prod v v) *v z"
    unfolding hrefl_def by (rule matrix_vector_mult_diff_rdistrib)
  also have "mat 1 *v z = z" by (rule matrix_vector_mul_lid)
  also have "((2 / (v \<bullet> v)) *\<^sub>R outer_prod v v) *v z
      = (2 / (v \<bullet> v)) *\<^sub>R (outer_prod v v *v z)"
    by (simp add: scaleR_matrix_vector_assoc[symmetric])
  also have "outer_prod v v *v z = (v \<bullet> z) *\<^sub>R v" by simp
  finally show ?thesis by simp
qed

lemma hrefl_key:
  fixes v :: "real^'n::finite"
  shows "(2 / (v \<bullet> v)) * (2 / (v \<bullet> v)) * (v \<bullet> v) = 2 * (2 / (v \<bullet> v))"
  by (cases "v \<bullet> v = 0") auto

lemma hrefl_involution: "hrefl v *v (hrefl v *v z) = z"
proof -
  define c where "c = 2 / (v \<bullet> v)"
  have step: "hrefl v *v y = y - (c * (v \<bullet> y)) *\<^sub>R v" for y
    unfolding c_def hrefl_apply by simp
  have vsplit: "(z - a *\<^sub>R v) - b *\<^sub>R v = z - (a + b) *\<^sub>R v" for a b :: real
    by (simp add: scaleR_left_distrib)
  have coef: "(c * (v \<bullet> z)) + (c * ((v \<bullet> z) - (c * (v \<bullet> z)) * (v \<bullet> v)))
      = (2 * c - c * c * (v \<bullet> v)) * (v \<bullet> z)"
    by (simp add: algebra_simps)
  have "hrefl v *v (hrefl v *v z)
      = (z - (c * (v \<bullet> z)) *\<^sub>R v)
        - (c * (v \<bullet> (z - (c * (v \<bullet> z)) *\<^sub>R v))) *\<^sub>R v"
    unfolding step[of z] step[of "z - (c * (v \<bullet> z)) *\<^sub>R v"] by (rule refl)
  also have "v \<bullet> (z - (c * (v \<bullet> z)) *\<^sub>R v)
      = (v \<bullet> z) - (c * (v \<bullet> z)) * (v \<bullet> v)"
    by (simp add: inner_diff_right)
  also have "(z - (c * (v \<bullet> z)) *\<^sub>R v)
        - (c * ((v \<bullet> z) - (c * (v \<bullet> z)) * (v \<bullet> v))) *\<^sub>R v
      = z - ((2 * c - c * c * (v \<bullet> v)) * (v \<bullet> z)) *\<^sub>R v"
    unfolding vsplit coef by (rule refl)
  also have "2 * c - c * c * (v \<bullet> v) = 0"
    unfolding c_def using hrefl_key[of v] by simp
  finally show ?thesis by simp
qed

lemma hrefl_inner: "(hrefl v *v y) \<bullet> (hrefl v *v z) = y \<bullet> z"
proof -
  define c where "c = 2 / (v \<bullet> v)"
  have step: "hrefl v *v w = w - (c * (v \<bullet> w)) *\<^sub>R v" for w
    unfolding c_def hrefl_apply by simp
  have "(hrefl v *v y) \<bullet> (hrefl v *v z)
      = (y - (c * (v \<bullet> y)) *\<^sub>R v) \<bullet> (z - (c * (v \<bullet> z)) *\<^sub>R v)"
    unfolding step[of y] step[of z] by (rule refl)
  also have "\<dots> = y \<bullet> z
      + ((c * c * (v \<bullet> v) - 2 * c) * ((v \<bullet> y) * (v \<bullet> z)))"
    by (simp add: algebra_simps inner_commute)
  also have "c * c * (v \<bullet> v) - 2 * c = 0"
    unfolding c_def using hrefl_key[of v] by simp
  finally show ?thesis by simp
qed

lemma orthogonal_matrixI:
  fixes Q :: "real^'n::finite^'n"
  assumes inn: "\<And>y z. (Q *v y) \<bullet> (Q *v z) = y \<bullet> z"
  shows "orthogonal_matrix Q"
  using inn orthogonal_transformation_matrix[of "(*v) Q"]
  by (simp add: orthogonal_transformation_def)

lemma hrefl_orthogonal: "orthogonal_matrix (hrefl v)"
  by (rule orthogonal_matrixI) (rule hrefl_inner)

lemma hrefl_zero: "hrefl 0 *v z = z"
  by (simp add: hrefl_apply)

lemma hrefl_scale:
  assumes c0: "c \<noteq> 0"
  shows "hrefl (c *\<^sub>R v) *v z = hrefl v *v z"
proof -
  have inn1: "(c *\<^sub>R v) \<bullet> z = c * (v \<bullet> z)" by simp
  have inn2: "(c *\<^sub>R v) \<bullet> (c *\<^sub>R v) = c * c * (v \<bullet> v)" by simp
  have coef: "2 * (c * (v \<bullet> z)) / (c * c * (v \<bullet> v)) * c
      = 2 * (v \<bullet> z) / (v \<bullet> v)"
  proof (cases "v \<bullet> v = 0")
    case True
    then show ?thesis by simp
  next
    case False
    then show ?thesis using c0 by (simp add: field_simps)
  qed
  have "hrefl (c *\<^sub>R v) *v z
      = z - (2 * (c * (v \<bullet> z)) / (c * c * (v \<bullet> v))) *\<^sub>R (c *\<^sub>R v)"
    unfolding hrefl_apply inn1 inn2 by (rule refl)
  also have "(2 * (c * (v \<bullet> z)) / (c * c * (v \<bullet> v))) *\<^sub>R (c *\<^sub>R v)
      = (2 * (v \<bullet> z) / (v \<bullet> v)) *\<^sub>R v"
    unfolding scaleR_scaleR coef by (rule refl)
  also have "z - (2 * (v \<bullet> z) / (v \<bullet> v)) *\<^sub>R v = hrefl v *v z"
    unfolding hrefl_apply by (rule refl)
  finally show ?thesis .
qed

lemma scaleR_self_diff:
  fixes q :: "'a::real_vector"
  shows "q - (c::real) *\<^sub>R q = (1 - c) *\<^sub>R q"
proof -
  have "(1 - c) *\<^sub>R q = 1 *\<^sub>R q - c *\<^sub>R q" by (rule scaleR_diff_left)
  then show ?thesis by simp
qed

lemma hrefl_fix:
  fixes q :: "real^'n::finite"
  assumes q0: "q \<noteq> 0"
  shows "hrefl q *v q = - q"
proof -
  have qq: "q \<bullet> q \<noteq> 0" using q0 by simp
  have "hrefl q *v q = q - (2 * (q \<bullet> q) / (q \<bullet> q)) *\<^sub>R q"
    by (rule hrefl_apply)
  also have "\<dots> = (1 - 2 * (q \<bullet> q) / (q \<bullet> q)) *\<^sub>R q"
    by (rule scaleR_self_diff)
  also have "1 - 2 * (q \<bullet> q) / (q \<bullet> q) = - 1" using qq by simp
  also have "(- 1 :: real) *\<^sub>R q = - q" by simp
  finally show ?thesis .
qed

lemma hrefl_bisect:
  fixes u v :: "real^'n::finite"
  assumes u1: "norm u = 1" and v1: "norm v = 1" and ne: "u + v \<noteq> 0"
  shows "hrefl (u + v) *v u = - v"
proof -
  have uu: "u \<bullet> u = 1" using u1 by (metis norm_eq_1)
  have vv: "v \<bullet> v = 1" using v1 by (metis norm_eq_1)
  have s1: "(u + v) \<bullet> u = 1 + u \<bullet> v"
  proof -
    have a: "(u + v) \<bullet> u = u \<bullet> u + v \<bullet> u" by (rule inner_add_left)
    have b: "v \<bullet> u = u \<bullet> v" by (rule inner_commute)
    show ?thesis unfolding a b uu by (rule refl)
  qed
  have s2: "(u + v) \<bullet> (u + v) = 2 * (1 + u \<bullet> v)"
  proof -
    have a: "(u + v) \<bullet> (u + v) = u \<bullet> (u + v) + v \<bullet> (u + v)"
      by (rule inner_add_left)
    have b: "u \<bullet> (u + v) = u \<bullet> u + u \<bullet> v" by (rule inner_add_right)
    have d: "v \<bullet> (u + v) = v \<bullet> u + v \<bullet> v" by (rule inner_add_right)
    have e: "v \<bullet> u = u \<bullet> v" by (rule inner_commute)
    show ?thesis unfolding a b d e uu vv by simp
  qed
  have nz: "(u + v) \<bullet> (u + v) \<noteq> 0" using ne by simp
  have c1: "1 + u \<bullet> v \<noteq> 0" using nz unfolding s2 by simp
  have "hrefl (u + v) *v u
      = u - (2 * ((u + v) \<bullet> u) / ((u + v) \<bullet> (u + v))) *\<^sub>R (u + v)"
    by (rule hrefl_apply)
  also have "2 * ((u + v) \<bullet> u) / ((u + v) \<bullet> (u + v)) = 1"
    unfolding s1 s2 using c1 by simp
  finally show ?thesis by simp
qed

section \<open>The two-reflection rotation\<close>

text \<open>\<open>rotv u v\<close>, the product of the reflection at \<open>u\<close> and the reflection at
  the bisector \<open>u+v\<close>, does what conjugating by \<open>hrefl (u+v) \<circ> hrefl u\<close>
  should: it sends \<open>u \<mapsto> -u \<mapsto> v\<close> and is the identity at \<open>v = u\<close>.\<close>

definition rotv :: "real^'n::finite \<Rightarrow> real^'n \<Rightarrow> real^'n^'n"
  where "rotv u v = hrefl (u + v) ** hrefl u"

text \<open>The normalised rotation, \<open>rotm q w = hrefl (\<parallel>w\<parallel> q + \<parallel>q\<parallel> w) ** hrefl q\<close>:
  it carries \<open>q\<close> onto the ray through \<open>w\<close> as soon as the two are not
  opposed, and \<open>rotm q w = rotv q (\<parallel>q\<parallel>/\<parallel>w\<parallel> \<cdot>\<^sub>R w)\<close> up to the normalisation
  that keeps its second argument off the unit sphere.\<close>

definition rotm :: "real^'n::finite \<Rightarrow> real^'n \<Rightarrow> real^'n^'n" where
  "rotm q w = hrefl (norm w *\<^sub>R q + norm q *\<^sub>R w) ** hrefl q"

lemma rotm_vec:
  "rotm q w *v z = hrefl (norm w *\<^sub>R q + norm q *\<^sub>R w) *v (hrefl q *v z)"
  unfolding rotm_def by (metis matrix_vector_mul_assoc)

lemma rotm_orthogonal:
  fixes q w :: "real^'n::finite"
  shows "orthogonal_matrix (rotm q w)"
  unfolding rotm_def by (intro orthogonal_matrix_mul hrefl_orthogonal)

lemma rotm_self: "rotm q q *v z = z"
proof (cases "q = 0")
  case True
  then show ?thesis unfolding rotm_vec by (simp add: hrefl_zero)
next
  case False
  then have ne: "norm q + norm q \<noteq> 0" by simp
  have sum2: "norm q *\<^sub>R q + norm q *\<^sub>R q = (norm q + norm q) *\<^sub>R q"
    by (rule scaleR_left_distrib[symmetric])
  have "rotm q q *v z = hrefl ((norm q + norm q) *\<^sub>R q) *v (hrefl q *v z)"
    unfolding rotm_vec sum2 by (rule refl)
  also have "\<dots> = hrefl q *v (hrefl q *v z)" by (rule hrefl_scale[OF ne])
  also have "\<dots> = z" by (rule hrefl_involution)
  finally show ?thesis .
qed

lemma rotm_apply:
  fixes q w :: "real^'n::finite"
  assumes q0: "q \<noteq> 0" and w0: "w \<noteq> 0"
    and pos: "0 < norm q * norm w + q \<bullet> w"
  shows "rotm q w *v q = (norm q / norm w) *\<^sub>R w"
proof -
  define nq where "nq = norm q"
  define nw where "nw = norm w"
  define pp where "pp = q \<bullet> w"
  have nq0: "0 < nq" unfolding nq_def using q0 by simp
  have nw0: "0 < nw" unfolding nw_def using w0 by simp
  have pos': "0 < nq * nw + pp" unfolding nq_def nw_def pp_def using pos .
  have qq: "q \<bullet> q = nq * nq"
    unfolding nq_def by (simp add: dot_square_norm power2_eq_square)
  have ww: "w \<bullet> w = nw * nw"
    unfolding nw_def by (simp add: dot_square_norm power2_eq_square)
  have qw: "q \<bullet> w = pp" unfolding pp_def by (rule refl)
  have wq: "w \<bullet> q = pp" unfolding pp_def by (rule inner_commute)
  define v where "v = nw *\<^sub>R q + nq *\<^sub>R w"
  have h1: "hrefl q *v q = - q" by (rule hrefl_fix[OF q0])
  have vq: "v \<bullet> q = nq * (nq * nw + pp)"
    unfolding v_def by (simp add: qq wq algebra_simps)
  have vv: "v \<bullet> v = (2 * (nq * nw)) * (nq * nw + pp)"
    unfolding v_def
    by (simp add: qq ww qw wq algebra_simps)
  have ratio: "2 * (v \<bullet> (- q)) / (v \<bullet> v) = - (1 / nw)"
  proof -
    have "2 * (v \<bullet> (- q)) / (v \<bullet> v)
        = - (2 * (nq * (nq * nw + pp)) / ((2 * (nq * nw)) * (nq * nw + pp)))"
      unfolding vv using vq by simp
    also have "2 * (nq * (nq * nw + pp)) / ((2 * (nq * nw)) * (nq * nw + pp))
        = 1 / nw"
    proof -
      have A: "nq * nw + pp \<noteq> 0" using pos' by simp
      have B: "nq \<noteq> 0" using nq0 by simp
      have C: "nw \<noteq> 0" using nw0 by simp
      have D: "(2 * (nq * nw)) * (nq * nw + pp) \<noteq> 0" using A B C by simp
      show ?thesis
        unfolding frac_eq_eq[OF D C] by (simp add: algebra_simps)
    qed
    finally show ?thesis .
  qed
  have r1: "rotm q w *v q = hrefl v *v (- q)"
    unfolding v_def nq_def nw_def rotm_vec h1 by (rule refl)
  have "rotm q w *v q = - q - (2 * (v \<bullet> (- q)) / (v \<bullet> v)) *\<^sub>R v"
    unfolding r1 by (rule hrefl_apply)
  also have "\<dots> = - q + (1 / nw) *\<^sub>R v"
    unfolding ratio by simp
  also have "(1 / nw) *\<^sub>R v = q + (nq / nw) *\<^sub>R w"
    unfolding v_def using nw0
    by (simp add: scaleR_right_distrib field_simps)
  finally show ?thesis unfolding nq_def nw_def by simp
qed

lemma rotm_refl_vec_norm:
  fixes q w :: "real^'n::finite"
  shows "(norm w *\<^sub>R q + norm q *\<^sub>R w) \<bullet> (norm w *\<^sub>R q + norm q *\<^sub>R w)
       = 2 * (norm q * norm w) * (norm q * norm w + q \<bullet> w)"
proof -
  have qq: "q \<bullet> q = norm q * norm q"
    by (simp add: dot_square_norm power2_eq_square)
  have ww: "w \<bullet> w = norm w * norm w"
    by (simp add: dot_square_norm power2_eq_square)
  have wq: "w \<bullet> q = q \<bullet> w" by (rule inner_commute)
  show ?thesis
    by (simp add: qq ww wq algebra_simps)
qed

lemma rotm_refl_vec_nonzero:
  fixes q w :: "real^'n::finite"
  assumes q0: "q \<noteq> 0" and pos: "0 < norm q * norm w + q \<bullet> w"
  shows "(norm w *\<^sub>R q + norm q *\<^sub>R w) \<bullet> (norm w *\<^sub>R q + norm q *\<^sub>R w) \<noteq> 0"
proof -
  have w0: "w \<noteq> 0"
  proof
    assume "w = 0"
    then show False using pos by simp
  qed
  have pos2: "0 < (norm w *\<^sub>R q + norm q *\<^sub>R w) \<bullet> (norm w *\<^sub>R q + norm q *\<^sub>R w)"
    unfolding rotm_refl_vec_norm using q0 w0 pos by simp
  show ?thesis by (rule not_sym[OF less_imp_neq[OF pos2]])
qed

section \<open>Continuity of the transport\<close>

text \<open>The half space, and what it rules out.\<close>

lemma rotm_vec_cont:
  fixes q c :: "real^'n::finite" and A :: "(real^'n) set"
  assumes q0: "q \<noteq> 0"
    and ok: "\<And>w. w \<in> A \<Longrightarrow> 0 < norm q * norm w + q \<bullet> w"
  shows "continuous_on A (\<lambda>w. rotm q w *v c)"
proof -
  define y0 where "y0 = hrefl q *v c"
  define V where "V = (\<lambda>w::real^'n. norm w *\<^sub>R q + norm q *\<^sub>R w)"
  have Vc: "continuous_on A V"
    unfolding V_def by (intro continuous_intros)
  have Vne: "V w \<bullet> V w \<noteq> 0" if w: "w \<in> A" for w
    unfolding V_def by (rule rotm_refl_vec_nonzero[OF q0 ok[OF w]])
  have eq: "rotm q w *v c = y0 - (2 * (V w \<bullet> y0) / (V w \<bullet> V w)) *\<^sub>R V w" for w
    unfolding y0_def V_def rotm_vec hrefl_apply by (rule refl)
  show ?thesis
    unfolding eq by (intro continuous_intros Vc) (use Vne in auto)
qed

text \<open>The same along an affine family of targets \<open>q + M (y - x)\<close>.\<close>

lemma rot_col_cont:
  fixes q x c :: "real^'n::finite" and M :: "real^'n^'n" and A :: "(real^'n) set"
  assumes q0: "q \<noteq> 0"
    and ok: "\<And>y. y \<in> A \<Longrightarrow>
      0 < norm q * norm (q + M *v (y - x)) + q \<bullet> (q + M *v (y - x))"
  shows "continuous_on A (\<lambda>y. rotm q (q + M *v (y - x)) *v c)"
proof -
  have gradc: "continuous_on A (\<lambda>y::real^'n. q + M *v (y - x))"
  proof -
    have d: "continuous_on A (\<lambda>y :: real^'n. y - x)"
      by (intro continuous_intros)
    have mv: "continuous_on A (\<lambda>y :: real^'n. M *v (y - x))"
      by (rule continuous_on_compose2[OF
          linear_continuous_on[OF matrix_vector_mul_bounded_linear] d]) auto
    show ?thesis by (intro continuous_intros mv)
  qed
  show ?thesis
  proof (rule continuous_on_compose2[OF _ gradc])
    show "continuous_on {w :: real^'n. 0 < norm q * norm w + q \<bullet> w}
        (\<lambda>w. rotm q w *v c)"
      by (rule rotm_vec_cont[OF q0]) simp
    show "(\<lambda>y::real^'n. q + M *v (y - x)) ` A
        \<subseteq> {w :: real^'n. 0 < norm q * norm w + q \<bullet> w}"
      using ok by blast
  qed
qed

text \<open>The real-valued functional the assembly actually needs: the Hessian
  paired with the conjugated witness.\<close>

(*<*)
end
(*>*)
