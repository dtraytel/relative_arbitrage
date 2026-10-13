
(*<*)
theory Orthogonal_Projections
  imports Outer_Products
begin

(*>*)

text \<open>
  Orthogonal projections as matrices: the rank-one projection
  \<open>p p\<^sup>T / |p|\<^sup>2\<close> onto a line, with its complement, and the projection
  onto the span of an orthonormal family, as a sum of outer squares.
\<close>

section \<open>The rank-one projection onto \<open>span p\<close>\<close>

text \<open>For \<open>p \<noteq> 0\<close>, \<open>rank1proj p = p p\<^sup>T / (p \<bullet> p)\<close> is the orthogonal
  projection onto \<open>span p\<close>, and \<open>I - rank1proj p\<close> the one onto its
  orthogonal complement.  (At \<open>p = 0\<close> it is \<open>0\<close>.)\<close>

definition rank1proj :: "real^'n::finite \<Rightarrow> real^'n^'n" where
  "rank1proj p = outer_prod p p /\<^sub>R (p \<bullet> p)"

lemma transpose_rank1proj: "transpose (rank1proj p) = rank1proj p"
  by (simp add: rank1proj_def transpose_scalar)

lemma rank1proj_annihilates_perp:
  fixes p :: "real^'n::finite"
  assumes y: "p \<bullet> y = 0"
  shows "rank1proj p *v y = 0"
  by (simp add: rank1proj_def scaleR_matrix_vector_assoc[symmetric] y)

text \<open>A symmetric \<open>a\<close> annihilating \<open>p\<close> also kills the range of the
  projection, in both orders.\<close>

lemma rank1proj_annihilates:
  fixes a :: "real^'n::finite^'n"
  assumes sym: "transpose a = a" and ap: "a *v p = 0"
  shows "rank1proj p *v (a *v x) = 0"
  by (rule rank1proj_annihilates_perp) (simp add: sym_inner_swap[OF sym, of p x] ap)

lemma proj_perp_left:
  fixes a :: "real^'n::finite^'n"
  assumes sym: "transpose a = a" and ap: "a *v p = 0"
  shows "(mat 1 - rank1proj p) ** a = a"
proof -
  have "((mat 1 - rank1proj p) ** a) *v x = a *v x" for x
  proof -
    have "((mat 1 - rank1proj p) ** a) *v x
        = (mat 1 - rank1proj p) *v (a *v x)"
      by (simp add: matrix_vector_mul_assoc)
    also have "\<dots> = a *v x - rank1proj p *v (a *v x)"
      by (simp add: matrix_vector_mult_diff_rdistrib)
    also have "\<dots> = a *v x"
      by (simp add: rank1proj_annihilates[OF sym ap])
    finally show ?thesis .
  qed
  then show ?thesis
    unfolding matrix_eq by blast
qed

lemma symmetric_perp_proj:
  "transpose (mat 1 - rank1proj p :: real^'n::finite^'n) = mat 1 - rank1proj p"
  by (simp add: transpose_diff_matrix transpose_rank1proj)

lemma proj_perp_right:
  fixes a :: "real^'n::finite^'n"
  assumes sym: "transpose a = a" and ap: "a *v p = 0"
  shows "a ** (mat 1 - rank1proj p) = a"
proof -
  have "transpose (a ** (mat 1 - rank1proj p))
      = transpose (mat 1 - rank1proj p) ** transpose a"
    by (rule matrix_transpose_mul)
  also have "\<dots> = (mat 1 - rank1proj p) ** a"
    by (simp add: symmetric_perp_proj sym)
  also have "\<dots> = a"
    by (rule proj_perp_left[OF sym ap])
  finally have "transpose (a ** (mat 1 - rank1proj p)) = a" .
  then have "transpose (transpose (a ** (mat 1 - rank1proj p))) = transpose a"
    by simp
  then show ?thesis
    using sym by simp
qed

lemma trace_rank1proj_mult:
  fixes a :: "real^'n::finite^'n"
  assumes ap: "a *v p = 0"
  shows "trace (rank1proj p ** a) = 0"
proof -
  have "trace (outer_prod p p ** a) = trace (a ** outer_prod p p)"
    by (rule trace_mul_sym)
  also have "\<dots> = trace (outer_prod (a *v p) p)"
    by (simp add: mult_outer_prod)
  also have "\<dots> = 0"
    by (simp add: ap)
  finally have z: "trace (outer_prod p p ** a) = 0" .
  show ?thesis
    by (simp add: rank1proj_def scalar_matrix_assoc[symmetric] trace_scaleR z)
qed

lemma rank1proj_apply_self:
  fixes p :: "real^'n::finite"
  assumes p: "p \<noteq> 0"
  shows "rank1proj p *v p = p"
proof -
  have nz: "p \<bullet> p \<noteq> 0"
    using p by simp
  have mv: "outer_prod p p *v p = (p \<bullet> p) *\<^sub>R p"
    by (rule outer_prod_mv)
  have "rank1proj p *v p = inverse (p \<bullet> p) *\<^sub>R (outer_prod p p *v p)"
    unfolding rank1proj_def by (rule scaleR_matrix_vector_assoc[symmetric])
  also have "\<dots> = inverse (p \<bullet> p) *\<^sub>R ((p \<bullet> p) *\<^sub>R p)"
    unfolding mv by (rule refl)
  also have "\<dots> = (inverse (p \<bullet> p) * (p \<bullet> p)) *\<^sub>R p"
    by (rule scaleR_scaleR)
  also have "\<dots> = p"
    using nz by simp
  finally show ?thesis .
qed

lemma perp_proj_fixes_perp:
  fixes p :: "real^'n::finite"
  assumes y: "p \<bullet> y = 0"
  shows "(mat 1 - rank1proj p) *v y = y"
  by (simp add: matrix_vector_mult_diff_rdistrib rank1proj_annihilates_perp[OF y])

text \<open>\<open>rank1proj\<close> depends only on the line through \<open>p\<close>.\<close>

lemma rank1proj_scaleR:
  fixes p :: "real^'n::finite"
  assumes c: "c \<noteq> 0" and p: "p \<noteq> 0"
  shows "rank1proj (c *\<^sub>R p) = rank1proj p"
proof -
  have pp: "p \<bullet> p \<noteq> 0"
    using p by simp
  have c2: "c * c \<noteq> 0"
    using c by simp
  have num: "outer_prod (c *\<^sub>R p) (c *\<^sub>R p) = (c * c) *\<^sub>R outer_prod p p"
    by (simp add: outer_prod_scaleR_left outer_prod_scaleR_right)
  have den: "(c *\<^sub>R p) \<bullet> (c *\<^sub>R p) = (c * c) * (p \<bullet> p)"
    by simp
  have "rank1proj (c *\<^sub>R p)
      = inverse ((c * c) * (p \<bullet> p)) *\<^sub>R ((c * c) *\<^sub>R outer_prod p p)"
    unfolding rank1proj_def num den by (rule refl)
  also have "\<dots> = (inverse ((c * c) * (p \<bullet> p)) * (c * c)) *\<^sub>R outer_prod p p"
    by (rule scaleR_scaleR)
  also have "\<dots> = inverse (p \<bullet> p) *\<^sub>R outer_prod p p"
    using c2 pp by (simp add: field_simps)
  finally show ?thesis
    unfolding rank1proj_def .
qed

text \<open>As the outer square of the unit vector \<open>p/|p|\<close>, \<open>rank1proj\<close> is
  Lipschitz away from the origin, with constant \<open>4/|p|\<close> (normalisation is
  Lipschitz there with constant \<open>2/|p|\<close>), and has Frobenius norm \<open>1\<close>; its
  complement \<open>I - rank1proj p\<close> has norm at most \<open>\<surd>n + 1\<close>.\<close>

lemma rank1proj_eq_outer_unit:
  fixes p :: "real^'n::finite"
  assumes p: "p \<noteq> 0"
  shows "rank1proj p = outer_prod (p /\<^sub>R norm p) (p /\<^sub>R norm p)"
proof -
  have np: "norm p \<noteq> 0"
    using p by simp
  have pp: "p \<bullet> p = norm p * norm p"
    by (simp add: dot_square_norm power2_eq_square)
  have "outer_prod (inverse (norm p) *\<^sub>R p) (inverse (norm p) *\<^sub>R p)
      = (inverse (norm p) * inverse (norm p)) *\<^sub>R outer_prod p p"
    by (simp add: outer_prod_scaleR_left outer_prod_scaleR_right)
  also have "\<dots> = inverse (p \<bullet> p) *\<^sub>R outer_prod p p"
    unfolding pp using np by (simp add: field_simps)
  finally show ?thesis
    unfolding rank1proj_def by simp
qed

theorem norm_rank1proj_diff_le:
  fixes p p' :: "real^'n::finite"
  assumes p: "p \<noteq> 0" and p': "p' \<noteq> 0"
  shows "norm (rank1proj p' - rank1proj p) \<le> 4 * norm (p' - p) / norm p"
proof -
  define q where "q = p /\<^sub>R norm p"
  define q' where "q' = p' /\<^sub>R norm p'"
  have nq: "norm q = 1"
    unfolding q_def using p by simp
  have nq': "norm q' = 1"
    unfolding q'_def using p' by simp
  have r: "rank1proj p = outer_prod q q"
    unfolding q_def by (rule rank1proj_eq_outer_unit[OF p])
  have r': "rank1proj p' = outer_prod q' q'"
    unfolding q'_def by (rule rank1proj_eq_outer_unit[OF p'])
  have bil: "outer_prod q' q' - outer_prod q q
      = outer_prod (q' - q) q' + outer_prod q (q' - q)"
    by (simp add: outer_prod_diff_left outer_prod_diff_right)
  have "norm (rank1proj p' - rank1proj p)
      \<le> norm (outer_prod (q' - q) q') + norm (outer_prod q (q' - q))"
    unfolding r r' bil by (rule norm_triangle_ineq)
  also have "\<dots> = 2 * norm (q' - q)"
    by (simp add: norm_outer_prod nq nq')
  also have "\<dots> \<le> 2 * (2 * norm (p' - p) / norm p)"
    using norm_unit_diff_le[OF p p'] unfolding q_def q'_def by simp
  also have "\<dots> = 4 * norm (p' - p) / norm p"
    by simp
  finally show ?thesis .
qed

lemma norm_rank1proj:
  fixes p :: "real^'n::finite"
  assumes p: "p \<noteq> 0"
  shows "norm (rank1proj p) = 1"
proof -
  have "norm (rank1proj p) = norm (p /\<^sub>R norm p) * norm (p /\<^sub>R norm p)"
    unfolding rank1proj_eq_outer_unit[OF p] by (rule norm_outer_prod)
  also have "\<dots> = 1"
    using p by simp
  finally show ?thesis .
qed

corollary norm_perp_proj_le:
  fixes p :: "real^'n::finite"
  assumes p: "p \<noteq> 0"
  shows "norm (mat 1 - rank1proj p :: real^'n^'n) \<le> sqrt (real CARD('n)) + 1"
proof -
  have "norm (mat 1 - rank1proj p :: real^'n^'n)
      \<le> norm (mat 1 :: real^'n^'n) + norm (rank1proj p)"
    by (rule norm_triangle_ineq4)
  also have "\<dots> = sqrt (real CARD('n)) + 1"
    by (simp add: norm_mat_1 norm_rank1proj[OF p])
  finally show ?thesis .
qed

section \<open>The projection onto an orthonormal family\<close>

text \<open>The sum of the outer squares of the first \<open>m\<close> members of an orthonormal
  family is the orthogonal projection onto their span: symmetric, of trace
  \<open>m\<close>, idempotent, and the identity on the span; for a full family, the
  identity.\<close>

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
      by (rule matrix_vector_mult_vsum)
    also have "\<dots> = (\<Sum>l < m. (b l \<bullet> z) *\<^sub>R (projmat b m *v b l))"
      by (rule sum.cong[OF refl]) (simp add: matrix_vector_mult_scaleR)
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
    by (auto simp: matrix_vector_right_distrib matrix_vector_mult_scaleR)
  have "b ` {..<m} \<subseteq> {y :: real^'n. projmat b m *v y = y}"
    using projmat_fix[OF orth] by auto
  then have "span (b ` {..<m}) \<subseteq> {y :: real^'n. projmat b m *v y = y}"
    using sub by (simp add: span_minimal)
  then show ?thesis using x by blast
qed

lemma projmat_full_id:
  fixes b :: "nat \<Rightarrow> real^'n::finite"
  assumes orth: "\<And>i j. i < CARD('n) \<Longrightarrow> j < CARD('n) \<Longrightarrow>
      b i \<bullet> b j = (if i = j then 1 else 0)"
  shows "projmat b CARD('n) *v w = w"
proof (rule projmat_span_fix[OF orth])
  have "span (b ` {..<CARD('n)}) = UNIV"
    using orthonormal_dim_span[OF orth] dim_eq_full[of "b ` {..<CARD('n)}"] by simp
  then show "w \<in> span (b ` {..<CARD('n)})" by simp
qed

(*<*)
end
(*>*)
