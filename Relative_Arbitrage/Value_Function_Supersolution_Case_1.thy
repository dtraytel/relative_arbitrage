section \<open>The supersolution, case 1: a nonzero gradient\<close>

(*<*)
theory Value_Function_Supersolution_Case_1
  imports Value_Function_Euler_Construction
begin

(*>*)

subsection \<open>Bricks for the Case-1 contradiction\<close>

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

lemma ell_op_lt_witness:
  fixes p :: "real^'n::finite" and H :: "real^'n^'n"
  assumes k1: "1 \<le> k" and kn: "k < CARD('n)" and L1: "1 \<le> L"
    and lt: "ell_op k L p H < 1"
  obtains a where "a \<in> feasible k L p" and "- trace (H ** a) / 2 < 1"
proof -
  have L0: "0 \<le> L" using L1 by linarith
  have ne: "(\<lambda>a. - trace (H ** a) / 2) ` feasible k L p \<noteq> {}"
    using feasible_nonempty[OF k1 kn L1] by blast
  have bdd: "bdd_below ((\<lambda>a. - trace (H ** a) / 2) ` feasible k L p)"
    by (rule bdd_below_mono[OF ell_op_s_bdd_below[OF L0]
        image_mono[OF feasible_subset_sconstraint]])
  have "\<exists>v \<in> (\<lambda>a. - trace (H ** a) / 2) ` feasible k L p. v < 1"
    using lt unfolding ell_op_def using cInf_less_iff[OF ne bdd] by blast
  then obtain a where a: "a \<in> feasible k L p"
    and tr: "- trace (H ** a) / 2 < 1" by blast
  show ?thesis by (rule that[OF a tr])
qed

lemma pexit_eq_of_stays:
  fixes f :: "real \<Rightarrow> 'b::polish_space"
  assumes T0: "0 \<le> T'" and stays: "\<And>s. 0 \<le> s \<Longrightarrow> s \<le> T' \<Longrightarrow> f s \<in> K"
  shows "pexit T' K f = T'"
proof (rule order.antisym)
  show "pexit T' K f \<le> T'" by (rule pexit_le_T[OF T0])
  show "T' \<le> pexit T' K f"
  proof (rule ccontr)
    assume "\<not> T' \<le> pexit T' K f"
    then have "pexit T' K f < T'" by simp
    then have "(\<exists>r. 0 \<le> r \<and> r \<le> T' \<and> f r \<in> - K \<and> r < T') \<or> T' < T'"
      using pexit_less_iff[OF T0] by blast
    then show False using stays by auto
  qed
qed

text \<open>A nonzero touching gradient forces \<open>v(x) < T\<close>: the test function
  strictly increases along its gradient, the global minimum of \<open>v - \<phi>\<close>
  transfers the increase to \<open>v\<close>, and \<open>v \<le> T\<close> caps the other end.  This
  is what neutralises the horizon cap in the Case-1 functional.\<close>

lemma touching_grad_lt_horizon:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and \<phi> :: "real^'n \<Rightarrow> real" and g :: "real^'n \<Rightarrow> real^'n"
    and H :: "real^'n^'n"
  assumes T0: "0 < T" and L1: "1 \<le> L" and Kc: "closed K"
    and xi: "x \<in> interior K"
    and tf: "test_fun_at \<phi> g H x"
    and tmin: "\<And>y. y \<in> K \<Longrightarrow>
      enn2real (exit_val k L T K x) - \<phi> x
        \<le> enn2real (exit_val k L T K y) - \<phi> y"
    and gx0: "g x \<noteq> 0"
  shows "enn2real (exit_val k L T K x) < T"
proof -
  obtain eK where eK0: "0 < eK" and eKK: "ball x eK \<subseteq> K"
    using xi mem_interior by blast
  obtain e where e0: "0 < e"
    and dphi: "\<And>y. y \<in> ball x e \<Longrightarrow> (\<phi> has_derivative (\<lambda>h. g y \<bullet> h)) (at y)"
    using tf unfolding test_fun_at_def by blast
  define h where "h = (\<lambda>s. \<phi> (x + s *\<^sub>R g x))"
  have hd: "(h has_field_derivative (g x \<bullet> g x)) (at 0)"
  proof -
    have i1: "((\<lambda>s :: real. x + s *\<^sub>R g x)
        has_derivative (\<lambda>u. u *\<^sub>R g x)) (at 0)"
      by (auto intro!: derivative_eq_intros)
    have mem0: "x + (0::real) *\<^sub>R g x \<in> ball x e" using e0 by simp
    have i2: "(\<phi> has_derivative (\<lambda>u. g (x + (0::real) *\<^sub>R g x) \<bullet> u))
        (at (x + (0::real) *\<^sub>R g x))"
      by (rule dphi[OF mem0])
    have "((\<lambda>s. \<phi> (x + s *\<^sub>R g x)) has_derivative
        (\<lambda>u. g (x + (0::real) *\<^sub>R g x) \<bullet> (u *\<^sub>R g x))) (at 0)"
      using diff_chain_at[OF i1 i2] by (simp add: o_def)
    then show ?thesis unfolding h_def
      by (rule has_derivative_imp_has_field_derivative)
        (simp add: ac_simps)
  qed
  have gg0: "0 < g x \<bullet> g x"
    using gx0 by simp
  have "((\<lambda>s. (h s - h 0) / (s - 0)) \<longlongrightarrow> g x \<bullet> g x) (at 0)"
    using hd by (simp add: has_field_derivative_iff)
  then have "\<forall>\<^sub>F s in at (0::real). 0 < (h s - h 0) / (s - 0)"
    by (rule order_tendstoD(1)[OF _ gg0])
  then obtain d where d0: "0 < d"
    and hpos: "\<And>s :: real. s \<noteq> 0 \<Longrightarrow> \<bar>s\<bar> < d \<Longrightarrow> 0 < (h s - h 0) / s"
    unfolding eventually_at by (auto simp: dist_real_def)
  define ng where "ng = norm (g x) + 1"
  have ng0: "0 < ng" unfolding ng_def
    using norm_ge_zero[of "g x"] by linarith
  define s where "s = min (min d (e / ng)) (eK / ng) / 2"
  have s0: "0 < s"
    unfolding s_def using d0 e0 eK0 ng0 by simp
  have sd: "s < d" unfolding s_def using d0 e0 eK0 ng0 by auto
  have se: "s * ng < e"
  proof -
    have "s \<le> (e / ng) / 2" unfolding s_def by simp
    then have "s * ng \<le> e / 2"
      using ng0 by (simp add: field_simps)
    then show ?thesis using e0 by linarith
  qed
  have sK: "s * ng < eK"
  proof -
    have "s \<le> (eK / ng) / 2" unfolding s_def by simp
    then have "s * ng \<le> eK / 2"
      using ng0 by (simp add: field_simps)
    then show ?thesis using eK0 by linarith
  qed
  have sg_lt: "s * norm (g x) < min e eK"
  proof -
    have "s * norm (g x) \<le> s * ng"
      unfolding ng_def using s0 by (intro mult_left_mono) auto
    then show ?thesis using se sK by simp
  qed
  define z where "z = x + s *\<^sub>R g x"
  have dz: "dist x z = s * norm (g x)"
    unfolding z_def dist_norm using s0 by simp
  have zK: "z \<in> K"
  proof -
    have "z \<in> ball x eK" using dz sg_lt by simp
    then show ?thesis using eKK by blast
  qed
  have hgt: "\<phi> x < \<phi> z"
  proof -
    have "0 < (h s - h 0) / s"
      using hpos[of s] s0 sd by simp
    then have "0 < h s - h 0"
      using s0 by (simp add: zero_less_divide_iff)
    then show ?thesis unfolding h_def z_def by simp
  qed
  have zT: "enn2real (exit_val k L T K z) \<le> T"
  proof -
    have "enn2real (exit_val k L T K z)
        = min (enn2real (exit_val k L T K z)) T"
      by (rule enn2real_paper_v_horizon_cap[OF less_imp_le[OF T0]
          order_refl L1 Kc])
    then show ?thesis by (metis min.cobounded2)
  qed
  have "enn2real (exit_val k L T K x)
      \<le> enn2real (exit_val k L T K z) - (\<phi> z - \<phi> x)"
    using tmin[OF zK] by simp
  also have "\<dots> < enn2real (exit_val k L T K z)" using hgt by simp
  also have "\<dots> \<le> T" by (rule zT)
  finally show ?thesis .
qed

subsection \<open>Exact rotations: a covariance field with no eigenvalue margin\<close>

text \<open>The skew field above moves the witness off its own eigenframe, and the
  margins that absorb that motion are what force \<open>1 < L\<close>: at \<open>L = 1\<close> the
  feasible set of Eq. (1.9) is rigid, its top \<open>n - k\<close> eigenvalues pinned to
  \<open>1\<close> from both sides, so no witness has slack to perturb.  A field of exact
  rotations needs none.  Conjugating the witness by an orthogonal matrix
  leaves its spectrum, and hence its membership of the feasible set,
  untouched; and the rotation carrying the frozen gradient \<open>q\<close> to the current
  gradient makes the conjugate annihilate the current gradient, which is all
  the Euler construction asks of the field.  The package \<open>rotSF_exists\<close> below
  therefore carries no hypothesis on \<open>L\<close> at all, and in particular is
  available at \<open>L = 1\<close>, the Ambrosio-Soner flow case of Remark 1.1(c).

  The rotation \<open>rotm q w\<close> is a product of two Householder reflections; it
  carries \<open>q\<close> onto the ray through \<open>w\<close> as soon as the two are not opposed,
  and is the identity at \<open>w = q\<close>, which is where the trace margin is read
  off: by continuity at the touching point, in place of the three explicit
  smallness estimates the skew field needs. \<open>hrefl\<close>, \<open>rotm\<close> and their
  properties, including the continuity of \<open>w \<mapsto> rotm q w\<close>
  (\<open>rotm_vec_cont\<close>), live in
  @{theory Symmetric_Matrix_Spectra.Householder_Rotation}.\<close>

lemma colmat_matvec:
  fixes R :: "real^'n::finite^'n" and c :: "'n \<Rightarrow> real^'n"
  shows "(\<chi> i j. (R *v c j) $ i) = R ** (\<chi> i j. c j $ i)"
  by (simp add: vec_eq_iff matrix_matrix_mult_def matrix_vector_mult_def)

lemma outerp_scale_self:
  fixes u :: "real^'n::finite"
  shows "outerp (c *\<^sub>R u) = (c * c) *\<^sub>R outer_prod u u"
  by (simp add: vec_eq_iff outerp_def outer_prod_def)

definition rotSF ::
  "(real^'n::finite \<Rightarrow> real) \<Rightarrow> ('n \<Rightarrow> real^'n) \<Rightarrow> real^'n
     \<Rightarrow> real^'n^'n \<Rightarrow> real^'n \<Rightarrow> real \<Rightarrow> real^'n \<Rightarrow> real^'n^'n"
  where "rotSF lam f q M x r z
    = (\<chi> i j. (rotm q (q + M *v (closest_point (cball x r) z - x))
        *v (sqrt (lam (f j)) *\<^sub>R f j)) $ i)"

lemma rotSF_cont:
  fixes q x :: "real^'n::finite" and M :: "real^'n^'n" and r :: real
  assumes r0: "0 \<le> r" and q0: "q \<noteq> 0"
    and ok: "\<And>y. dist y x \<le> r \<Longrightarrow>
      0 < norm q * norm (q + M *v (y - x)) + q \<bullet> (q + M *v (y - x))"
  shows "continuous_on UNIV (rotSF lam f q M x r)"
proof -
  define cp where "cp = closest_point (cball x r)"
  have cpc: "continuous_on UNIV cp"
    unfolding cp_def by (rule continuous_on_closest_point) (use r0 in auto)
  have cpin: "cp z \<in> cball x r" for z
    unfolding cp_def by (rule closest_point_in_set) (use r0 in auto)
  have gradc: "continuous_on UNIV (\<lambda>z::real^'n. q + M *v (cp z - x))"
  proof -
    have d: "continuous_on UNIV (\<lambda>z :: real^'n. cp z - x)"
      by (intro continuous_intros cpc)
    have mv: "continuous_on UNIV (\<lambda>z :: real^'n. M *v (cp z - x))"
      by (rule continuous_on_compose2[OF
          linear_continuous_on[OF matvec_blin] d]) auto
    show ?thesis by (intro continuous_intros mv)
  qed
  have Gin: "q + M *v (cp z - x) \<in> {w :: real^'n. 0 < norm q * norm w + q \<bullet> w}"
    for z
  proof -
    have "dist (cp z) x \<le> r" using cpin[of z] by (simp add: dist_commute)
    then show ?thesis by (simp add: ok)
  qed
  have colc: "continuous_on UNIV
      (\<lambda>z. rotm q (q + M *v (cp z - x)) *v (sqrt (lam (f j)) *\<^sub>R f j))" for j
  proof (rule continuous_on_compose2[OF _ gradc])
    show "continuous_on {w :: real^'n. 0 < norm q * norm w + q \<bullet> w}
        (\<lambda>w. rotm q w *v (sqrt (lam (f j)) *\<^sub>R f j))"
      by (rule rotm_vec_cont[OF q0]) simp
    show "(\<lambda>z::real^'n. q + M *v (cp z - x)) ` UNIV
        \<subseteq> {w :: real^'n. 0 < norm q * norm w + q \<bullet> w}"
      using Gin by blast
  qed
  have entry: "continuous_on UNIV
      (\<lambda>z. (rotm q (q + M *v (cp z - x)) *v (sqrt (lam (f j)) *\<^sub>R f j)) $ i)"
    for i j
    by (rule continuous_on_compose2[OF
        linear_continuous_on[OF bounded_linear_vec_nth] colc]) auto
  show ?thesis
    unfolding rotSF_def cp_def[symmetric]
    by (intro continuous_on_vec_lambda entry)
qed

text \<open>\<open>feasible_scale\<close> lives in @{theory Relative_Arbitrage.Operator_Envelopes},
  as the set equality; this theory re-proved the membership direction under
  the same name, shadowing it.\<close>

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
          linear_continuous_on[OF matvec_blin] d]) auto
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

definition colm :: "(real^'n::finite \<Rightarrow> real) \<Rightarrow> ('n \<Rightarrow> real^'n) \<Rightarrow> real^'n^'n"
  where "colm lam f = (\<chi> i j. (sqrt (lam (f j)) *\<^sub>R f j) $ i)"

lemma colm_square:
  fixes a :: "real^'n::finite^'n" and B :: "(real^'n) set" and f :: "'n \<Rightarrow> real^'n"
  assumes bij: "bij_betw f (UNIV :: 'n set) B"
    and Bon: "onormal B" and sp: "span B = UNIV"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
    and nn: "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> lam u"
    and lamB: "\<And>u. u \<in> B \<Longrightarrow> lam u = u \<bullet> (a *v u)"
  shows "colm lam f ** transpose (colm lam f) = a"
proof -
  have "colm lam f ** transpose (colm lam f)
      = (\<Sum>j\<in>UNIV. outerp (sqrt (lam (f j)) *\<^sub>R f j))"
    unfolding colm_def by (rule cols_mult_transpose)
  also have "\<dots> = (\<Sum>u\<in>B. outerp (sqrt (lam u) *\<^sub>R u))"
    by (rule sum.reindex_bij_betw[OF bij])
  also have "\<dots> = (\<Sum>u\<in>B. (u \<bullet> (a *v u)) *\<^sub>R outer_prod u u)"
  proof (rule sum.cong[OF refl])
    fix u assume u: "u \<in> B"
    have sq: "sqrt (lam u) * sqrt (lam u) = lam u"
    proof -
      have "sqrt (lam u) * sqrt (lam u) = (sqrt (lam u))\<^sup>2"
        by (rule power2_eq_square[symmetric])
      also have "\<dots> = lam u" by (rule real_sqrt_pow2[OF nn[OF u]])
      finally show ?thesis .
    qed
    have "outerp (sqrt (lam u) *\<^sub>R u)
        = (sqrt (lam u) * sqrt (lam u)) *\<^sub>R outer_prod u u"
      by (rule outerp_scale_self)
    also have "\<dots> = lam u *\<^sub>R outer_prod u u" unfolding sq by (rule refl)
    also have "\<dots> = (u \<bullet> (a *v u)) *\<^sub>R outer_prod u u"
      unfolding lamB[OF u] by (rule refl)
    finally show "outerp (sqrt (lam u) *\<^sub>R u)
        = (u \<bullet> (a *v u)) *\<^sub>R outer_prod u u" .
  qed
  also have "\<dots> = a" by (rule spectral_decomposition[OF Bon sp eig, symmetric])
  finally show ?thesis .
qed

lemma rotSF_matrix:
  "rotSF lam f q M x r z
     = rotm q (q + M *v (closest_point (cball x r) z - x)) ** colm lam f"
  unfolding rotSF_def colm_def by (rule colmat_matvec)

lemma rotSF_conj:
  fixes a :: "real^'n::finite^'n"
  assumes sq: "colm lam f ** transpose (colm lam f) = a"
  shows "rotSF lam f q M x r z ** transpose (rotSF lam f q M x r z)
       = rotm q (q + M *v (closest_point (cball x r) z - x)) ** a
         ** transpose (rotm q (q + M *v (closest_point (cball x r) z - x)))"
proof -
  define R where
    "R = rotm q (q + M *v (closest_point (cball x r) z - x))"
  have "rotSF lam f q M x r z ** transpose (rotSF lam f q M x r z)
      = (R ** colm lam f) ** transpose (R ** colm lam f)"
    unfolding R_def rotSF_matrix by (rule refl)
  also have "transpose (R ** colm lam f)
      = transpose (colm lam f) ** transpose R"
    by (rule matrix_transpose_mul)
  also have "(R ** colm lam f) ** (transpose (colm lam f) ** transpose R)
      = R ** (colm lam f ** transpose (colm lam f)) ** transpose R"
    by (simp add: matrix_mul_assoc)
  also have "\<dots> = R ** a ** transpose R" unfolding sq by (rule refl)
  finally show ?thesis unfolding R_def .
qed

theorem rotSF_exists:
  fixes a M :: "real^'n::finite^'n" and q x :: "real^'n"
    and \<epsilon> r0 :: real
  assumes aF: "a \<in> feasible k L q" and q0: "q \<noteq> 0"
    and eps: "0 < \<epsilon>" and r00: "0 < r0"
  obtains SF :: "real^'n \<Rightarrow> real^'n^'n" and r :: real where
    "0 < r" and "r \<le> r0"
    and "continuous_on UNIV SF"
    and "\<And>z. SF z ** transpose (SF z) \<in> sconstraint k L"
    and "\<And>z. transpose (SF z)
          *v (q + M *v (closest_point (cball x r) z - x)) = 0"
    and "\<And>z. \<bar>trace (M ** (SF z ** transpose (SF z))) - trace (M ** a)\<bar> \<le> \<epsilon>"
proof -
  have psda: "psd a" using aF unfolding feasible_def by blast
  have syma: "transpose a = a" using psda unfolding psd_def by blast
  obtain B where Bon: "onormal B" and sp: "span B = UNIV"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
    using symmetric_eigenbasis[OF syma] by blast
  have finB: "finite B" by (rule onormal_finite[OF Bon])
  have cardB: "card B = CARD('n)" by (rule onormal_span_card[OF Bon sp])
  obtain f :: "'n \<Rightarrow> real^'n" where bij: "bij_betw f (UNIV :: 'n set) B"
    by (rule exists_enum_of_card[OF finB cardB])
  define lam where "lam = (\<lambda>u :: real^'n. u \<bullet> (a *v u))"
  have lam_nn: "0 \<le> lam u" for u
    using psda unfolding lam_def psd_def by blast
  have sq: "colm lam f ** transpose (colm lam f) = a"
  proof (rule colm_square[OF bij Bon sp eig])
    show "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> lam u" using lam_nn by blast
    show "\<And>u. u \<in> B \<Longrightarrow> lam u = u \<bullet> (a *v u)" unfolding lam_def by (rule refl)
  qed
  define cc where "cc = (\<lambda>j. sqrt (lam (f j)) *\<^sub>R f j)"
  \<comment> \<open>a radius on which the rotation is defined and continuous\<close>
  obtain KM where KM0: "0 < KM" and KMb: "\<And>y. norm (M *v y) \<le> norm y * KM"
    using bounded_linear.pos_bounded[OF matvec_blin] by blast
  define d0 where "d0 = norm q / KM"
  have d00: "0 < d0" unfolding d0_def using q0 KM0 by simp
  have cone: "0 < norm q * norm (q + M *v (y - x)) + q \<bullet> (q + M *v (y - x))"
    if yd: "dist y x < d0" for y
  proof (rule rot_cone_ok[OF q0])
    have "norm (M *v (y - x)) \<le> norm (y - x) * KM" by (rule KMb)
    also have "\<dots> < d0 * KM"
      using yd KM0 by (simp add: dist_norm mult_strict_right_mono)
    also have "d0 * KM = norm q" unfolding d0_def using KM0 by simp
    finally show "norm (M *v (y - x)) < norm q" .
  qed
  \<comment> \<open>the trace along the rotated frame, and its value at the centre\<close>
  define TT where "TT = (\<lambda>y. \<Sum>j\<in>UNIV. (rotm q (q + M *v (y - x)) *v cc j)
      \<bullet> (M *v (rotm q (q + M *v (y - x)) *v cc j)))"
  have TTx: "TT x = trace (M ** a)"
  proof -
    have "TT x = (\<Sum>j\<in>UNIV. cc j \<bullet> (M *v cc j))"
      unfolding TT_def by (simp add: rotm_self)
    also have "\<dots> = trace (M ** (\<Sum>j\<in>UNIV. outerp (cc j)))"
      by (simp add: trace_mult_outerp_sum)
    also have "(\<Sum>j\<in>UNIV. outerp (cc j)) = colm lam f ** transpose (colm lam f)"
      unfolding colm_def cc_def by (rule cols_mult_transpose[symmetric])
    also have "\<dots> = a" by (rule sq)
    finally show ?thesis .
  qed
  have TTc: "continuous_on (ball x d0) TT"
    unfolding TT_def
  proof (rule continuous_on_sum)
    fix j :: 'n
    have c1: "continuous_on (ball x d0)
        (\<lambda>y. rotm q (q + M *v (y - x)) *v cc j)"
      by (rule rot_col_cont[OF q0]) (use cone in \<open>auto simp: dist_commute\<close>)
    have c2: "continuous_on (ball x d0)
        (\<lambda>y. M *v (rotm q (q + M *v (y - x)) *v cc j))"
      by (rule continuous_on_compose2[OF
          linear_continuous_on[OF matvec_blin] c1]) auto
    show "continuous_on (ball x d0)
        (\<lambda>y. (rotm q (q + M *v (y - x)) *v cc j)
           \<bullet> (M *v (rotm q (q + M *v (y - x)) *v cc j)))"
      by (intro continuous_intros c1 c2)
  qed
  have isc: "isCont TT x"
  proof -
    have "continuous_on (ball x d0) TT = (\<forall>y\<in>ball x d0. isCont TT y)"
      by (rule continuous_on_eq_continuous_at[OF open_ball])
    then have "\<forall>y\<in>ball x d0. isCont TT y" using TTc by blast
    then show ?thesis using d00 by simp
  qed
  obtain d1 where d10: "0 < d1"
    and d1b: "\<And>y. dist y x < d1 \<Longrightarrow> \<bar>TT y - TT x\<bar> < \<epsilon>"
    using isc eps unfolding continuous_at_eps_delta dist_real_def by blast
  define r where "r = min r0 (min (d0 / 2) (d1 / 2))"
  have rpos: "0 < r" unfolding r_def using r00 d00 d10 by simp
  have rr0: "r \<le> r0" unfolding r_def by simp
  have rd0: "r < d0" unfolding r_def using d00 d10 r00 by simp
  have rd1: "r < d1" unfolding r_def using d00 d10 r00 by simp
  have okr: "0 < norm q * norm (q + M *v (y - x)) + q \<bullet> (q + M *v (y - x))"
    if yd: "dist y x \<le> r" for y
    using cone[of y] yd rd0 by simp
  \<comment> \<open>the clamped point stays in the ball\<close>
  have cpin: "dist (closest_point (cball x r) z) x \<le> r" for z
  proof -
    have "closest_point (cball x r) z \<in> cball x r"
      by (rule closest_point_in_set) (use rpos in auto)
    then show ?thesis by (simp add: dist_commute)
  qed
  define SF where "SF = rotSF lam f q M x r"
  define GG where "GG = (\<lambda>z. q + M *v (closest_point (cball x r) z - x))"
  have okG: "0 < norm q * norm (GG z) + q \<bullet> (GG z)" for z
    unfolding GG_def by (rule okr[OF cpin])
  have Gnz: "GG z \<noteq> 0" for z
  proof
    assume "GG z = 0"
    then show False using okG[of z] by simp
  qed
  have cov: "SF z ** transpose (SF z)
      = rotm q (GG z) ** a ** transpose (rotm q (GG z))" for z
    unfolding SF_def GG_def by (rule rotSF_conj[OF sq])
  have feas: "SF z ** transpose (SF z) \<in> feasible k L (GG z)" for z
  proof -
    have o1: "transpose (rotm q (GG z)) ** rotm q (GG z) = mat 1"
      and o2: "rotm q (GG z) ** transpose (rotm q (GG z)) = mat 1"
      using rotm_orthogonal unfolding orthogonal_matrix_def by blast+
    have inF: "rotm q (GG z) ** a ** transpose (rotm q (GG z))
        \<in> feasible k L (rotm q (GG z) *v q)"
      by (rule feasible_conj[OF o1 o2 aF])
    have rq: "rotm q (GG z) *v q = (norm q / norm (GG z)) *\<^sub>R GG z"
      by (rule rotm_apply[OF q0 Gnz okG])
    have cne: "norm q / norm (GG z) \<noteq> 0" using q0 Gnz by simp
    show ?thesis
      unfolding cov using inF[unfolded rq feasible_scale[OF cne]] .
  qed
  show ?thesis
  proof (rule that[of r SF])
    show "0 < r" by (rule rpos)
    show "r \<le> r0" by (rule rr0)
    show "continuous_on UNIV SF"
      unfolding SF_def by (rule rotSF_cont[OF less_imp_le[OF rpos] q0 okr])
    show "SF z ** transpose (SF z) \<in> sconstraint k L" for z
      using feas[of z] feasible_subset_sconstraint by blast
    show "transpose (SF z) *v (q + M *v (closest_point (cball x r) z - x)) = 0"
      for z
    proof -
      have a0: "(SF z ** transpose (SF z)) *v GG z = 0"
        using feas[of z] unfolding feasible_def by blast
      have e1: "(transpose (SF z) *v GG z) \<bullet> (transpose (SF z) *v GG z)
          = (transpose (transpose (SF z)) *v (transpose (SF z) *v GG z)) \<bullet> GG z"
        by (rule inner_transpose_matrix)
      have e2: "transpose (transpose (SF z)) *v (transpose (SF z) *v GG z)
          = SF z *v (transpose (SF z) *v GG z)"
        by (simp only: transpose_transpose)
      have e3: "SF z *v (transpose (SF z) *v GG z)
          = (SF z ** transpose (SF z)) *v GG z"
        by (metis matrix_vector_mul_assoc)
      have e4: "((SF z ** transpose (SF z)) *v GG z) \<bullet> GG z = 0"
        using a0 by simp
      have "(transpose (SF z) *v GG z) \<bullet> (transpose (SF z) *v GG z) = 0"
        by (metis e1 e2 e3 e4)
      then have "transpose (SF z) *v GG z = 0" by simp
      then show ?thesis unfolding GG_def .
    qed
    show "\<bar>trace (M ** (SF z ** transpose (SF z))) - trace (M ** a)\<bar> \<le> \<epsilon>"
      for z
    proof -
      have "SF z ** transpose (SF z)
          = (\<Sum>j\<in>UNIV. outerp (rotm q (GG z) *v cc j))"
        unfolding SF_def GG_def rotSF_def cc_def by (rule cols_mult_transpose)
      then have teq: "trace (M ** (SF z ** transpose (SF z)))
          = TT (closest_point (cball x r) z)"
        unfolding TT_def GG_def by (simp add: trace_mult_outerp_sum)
      have "dist (closest_point (cball x r) z) x < d1"
        using cpin[of z] rd1 by simp
      then have "\<bar>TT (closest_point (cball x r) z) - TT x\<bar> < \<epsilon>"
        by (rule d1b)
      then show ?thesis unfolding teq TTx[symmetric] by simp
    qed
  qed
qed

subsection \<open>Case 1: a nonzero gradient contradicts a failed supersolution
  inequality\<close>

text \<open>If the supersolution inequality fails at a touching point with
  nonzero gradient, the failure yields a feasible witness with slack
  \<open>2\<eta>\<^sub>0\<close>.  Softening the Hessian by \<open>(2\<gamma>+\<delta>)\<cdot>1\<close> keeps slack \<open>2\<eta>\<close> and buys
  both the Taylor minorant (via \<open>\<delta>\<close>) and a strict sphere margin (via
  \<open>\<gamma>\<close>); the witness is rotated into a covariance field by
  @{thm [source] rotSF_exists}, the Euler limit
  produces a class member whose paths grow along the quadratic, and at the
  stopping time \<open>min cc (pball_exit T x rr)\<close> the DPP functional is at
  least \<open>v(x) + mg\<close> almost surely -- the exit branch is paid by
  \<open>\<gamma> rr\<^sup>2\<close>, the no-exit branch by \<open>cc \<eta> / 2\<close>, and the horizon cap by
  \<open>T - v(x) > 0\<close>, which a nonzero gradient forces.  That contradicts
  @{thm [source] exit_val_dpp_sup_ge_time}.\<close>

theorem exit_val_supersol_contradiction_case1:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and \<phi> :: "real^'n \<Rightarrow> real" and g :: "real^'n \<Rightarrow> real^'n"
    and H :: "real^'n^'n"
  assumes T0: "0 < T" and L1: "1 \<le> L" and k1: "1 \<le> k"
    and kn: "k < CARD('n)" and Kc: "closed K"
    and xi: "x \<in> interior K"
    and tf: "test_fun_at \<phi> g H x"
    and tmin: "\<And>y. y \<in> K \<Longrightarrow>
      enn2real (exit_val k L T K x) - \<phi> x
        \<le> enn2real (exit_val k L T K y) - \<phi> y"
    and gx0: "g x \<noteq> 0"
    and fail: "ell_op k L (g x) H < 1"
  shows False
proof -
  have L1': "1 \<le> L" using L1 by linarith
  have L0: "0 \<le> L" using L1 by linarith
  have T0': "0 \<le> T" using T0 by linarith
  define tv where "tv = (\<lambda>y. enn2real (exit_val k L T K y))"
  have vxT: "tv x < T"
    unfolding tv_def
    by (rule touching_grad_lt_horizon[OF T0 L1' Kc xi tf tmin gx0])
  obtain a where aF: "a \<in> feasible k L (g x)"
    and aTr: "- trace (H ** a) / 2 < 1"
    by (rule ell_op_lt_witness[OF k1 kn L1' fail])
  define \<eta>\<^sub>0 where "\<eta>\<^sub>0 = (1 - (- trace (H ** a) / 2)) / 2"
  have h00: "0 < \<eta>\<^sub>0" unfolding \<eta>\<^sub>0_def using aTr by simp
  have trH: "2 * \<eta>\<^sub>0 \<le> 1 + trace (H ** a) / 2"
    unfolding \<eta>\<^sub>0_def by simp
  have aS: "a \<in> sconstraint k L"
    using aF feasible_subset_sconstraint by blast
  define TB where "TB = real CARD('n) * (real CARD('n) * L)"
  have trab: "trace a \<le> TB"
    unfolding TB_def by (rule sconstraint_trace_le[OF L0 aS])
  have tra0: "0 \<le> trace a"
    using sconstraint_trace_ge[OF kn aS] by linarith
  have TB1: "0 < TB + 1"
  proof -
    have "0 \<le> TB" using trab tra0 by linarith
    then show ?thesis by linarith
  qed
  define sft where "sft = min (\<eta>\<^sub>0 / (TB + 1)) 1"
  have sft0: "0 < sft"
    unfolding sft_def using h00 TB1 by simp
  define \<gamma> where "\<gamma> = sft / 4"
  define \<delta> where "\<delta> = sft / 2"
  have g0: "0 < \<gamma>" unfolding \<gamma>_def using sft0 by simp
  have d0: "0 < \<delta>" unfolding \<delta>_def using sft0 by simp
  have gd_le: "2 * \<gamma> + \<delta> \<le> sft" unfolding \<gamma>_def \<delta>_def by simp
  have gd0: "0 \<le> 2 * \<gamma> + \<delta>" using g0 d0 by linarith
  define M where "M = H - (2 * \<gamma> + \<delta>) *\<^sub>R mat 1"
  have symH: "transpose H = H" using tf unfolding test_fun_at_def by blast
  have symM: "transpose M = M"
    unfolding M_def by (rule transpose_sub_smat[OF symH])
  define \<eta> where "\<eta> = \<eta>\<^sub>0 / 2"
  have e0: "0 < \<eta>" unfolding \<eta>_def using h00 by simp
  have trM: "2 * \<eta> \<le> 1 + trace (M ** a) / 2"
  proof -
    have tr_eq: "trace (M ** a) = trace (H ** a) - (2 * \<gamma> + \<delta>) * trace a"
      unfolding M_def by (rule trace_msub_mat)
    have "(2 * \<gamma> + \<delta>) * trace a \<le> sft * trace a"
      by (rule mult_right_mono[OF gd_le tra0])
    also have "\<dots> \<le> (\<eta>\<^sub>0 / (TB + 1)) * (TB + 1)"
    proof (rule mult_mono)
      show "sft \<le> \<eta>\<^sub>0 / (TB + 1)" unfolding sft_def by simp
      show "trace a \<le> TB + 1" using trab by linarith
      show "0 \<le> \<eta>\<^sub>0 / (TB + 1)" using h00 TB1 by simp
      show "0 \<le> trace a" by (rule tra0)
    qed
    also have "\<dots> = \<eta>\<^sub>0" using TB1 by simp
    finally have "(2 * \<gamma> + \<delta>) * trace a \<le> \<eta>\<^sub>0" .
    then show ?thesis unfolding \<eta>_def using trH tr_eq h00 by linarith
  qed
  have e3: "0 < 3 * \<eta>" using e0 by simp
  have trMa: "4 * \<eta> - 2 \<le> trace (M ** a)"
  proof -
    have d2: "2 * (1 + trace (M ** a) / 2) = 2 + trace (M ** a)"
      by (simp add: field_simps)
    have "2 * (2 * \<eta>) \<le> 2 * (1 + trace (M ** a) / 2)"
      by (rule mult_left_mono[OF trM]) simp
    then have "4 * \<eta> \<le> 2 + trace (M ** a)" unfolding d2 by simp
    then show ?thesis by linarith
  qed
  obtain rphi where rphi0: "0 < rphi"
    and mino: "\<And>z. z \<in> ball x rphi \<Longrightarrow>
      \<phi> x + g x \<bullet> (z - x)
        + ((z - x) \<bullet> ((H - \<delta> *\<^sub>R mat 1) *v (z - x))) / 2 \<le> \<phi> z"
    using test_fun_quadratic_minorates[OF tf d0] by metis
  obtain eK where eK0: "0 < eK" and eKK: "ball x eK \<subseteq> K"
    using xi mem_interior by blast
  have rmx0: "0 < min (rphi / 2) (eK / 2)" using rphi0 eK0 by simp
  show False
  proof (rule rotSF_exists[where M = M and x = x, OF aF gx0 e3 rmx0])
    fix SF :: "real^'n \<Rightarrow> real^'n^'n" and rr :: real
    assume rr0: "0 < rr" and rrx: "rr \<le> min (rphi / 2) (eK / 2)"
      and SFc: "continuous_on UNIV SF"
      and SFs: "\<And>z. SF z ** transpose (SF z) \<in> sconstraint k L"
      and kill: "\<And>z. transpose (SF z)
          *v (g x + M *v (closest_point (cball x rr) z - x)) = 0"
      and trcl: "\<And>z. \<bar>trace (M ** (SF z ** transpose (SF z)))
          - trace (M ** a)\<bar> \<le> 3 * \<eta>"
    show False
    proof -
  have rr_phi: "rr < rphi" and rr_K: "rr < eK"
    using rrx rphi0 eK0 by auto
  have cb_phi: "cball x rr \<subseteq> ball x rphi"
    using rr_phi by auto
  have cb_K: "cball x rr \<subseteq> K"
  proof -
    have "cball x rr \<subseteq> ball x eK"
      using rr_K by auto
    then show ?thesis using eKK by blast
  qed
  have marg: "\<eta> - 2 \<le> trace (M ** (SF z ** transpose (SF z)))" for z
  proof -
    have "- (trace (M ** (SF z ** transpose (SF z))) - trace (M ** a))
        \<le> 3 * \<eta>"
      by (rule abs_le_D2[OF trcl])
    then show ?thesis using trMa by linarith
  qed
  obtain P where Pc: "P \<in> exit_class k L T x"
    and AEpack: "AE \<omega> in P.
      0 < pball_exit T x rr \<omega>
      \<and> (\<forall>s\<in>{0..pball_exit T x rr \<omega>}. fst (\<omega> s) \<in> cball x rr)
      \<and> (pball_exit T x rr \<omega> < T \<longrightarrow>
          dist (fst (\<omega> (pball_exit T x rr \<omega>))) x = rr)
      \<and> pball_exit T x rr \<omega> * (\<eta> - 2) / 2
          \<le> g x \<bullet> (fst (\<omega> (pball_exit T x rr \<omega>)) - x)
            + (1/2) * ((fst (\<omega> (pball_exit T x rr \<omega>)) - x)
                \<bullet> (M *v (fst (\<omega> (pball_exit T x rr \<omega>)) - x)))
      \<and> (\<forall>s. 0 \<le> s \<longrightarrow> s < pball_exit T x rr \<omega> \<longrightarrow>
          fst (\<omega> s) \<in> ball x rr)
      \<and> (\<forall>t. 0 < t \<longrightarrow> t \<le> T \<longrightarrow>
          (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> ball x rr) \<longrightarrow>
          t * (\<eta> - 2) / 2 \<le> g x \<bullet> (fst (\<omega> t) - x)
            + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x))))"
    using eulerp_limit_exit[OF T0 L1' SFc SFs symM rr0 kill marg] by blast
  define cc where "cc = T / 2"
  have cc0: "0 < cc" unfolding cc_def using T0 by simp
  have ccT: "cc < T" unfolding cc_def using T0 by simp
  have ccT': "cc \<le> T" using ccT by linarith
  define \<theta> where "\<theta> = (\<lambda>\<omega> :: 'n pairpath. min cc (pball_exit T x rr \<omega>))"
  have st: "path_stopping_time T \<theta>"
    unfolding \<theta>_def
    by (rule path_stopping_time_min[OF pball_exit_path_stopping_time[OF T0']
        less_imp_le[OF cc0] ccT'])
  have thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    unfolding \<theta>_def
    by (intro borel_measurable_min pball_exit_measurable[OF T0']
        borel_measurable_const)
  define FN where "FN = (\<lambda>\<omega> :: 'n pairpath.
      pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
      + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega>
            \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
         then enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>))))
         else 0))"
  have dpp: "(SUP P' \<in> exit_class k L T x. ess_inf_time P' FN)
      \<le> exit_val k L T K x"
    unfolding FN_def
    by (rule exit_val_dpp_sup_ge_time[OF T0 L1' Kc st thM])
  define mg where "mg = min (min (\<gamma> * rr\<^sup>2) (cc * \<eta> / 2)) (T - tv x)"
  have mg0: "0 < mg"
  proof -
    have "0 < \<gamma> * rr\<^sup>2" using g0 rr0 by simp
    moreover have "0 < cc * \<eta> / 2" using cc0 e0 by simp
    moreover have "0 < T - tv x" using vxT by simp
    ultimately show ?thesis unfolding mg_def by simp
  qed
  have AEfun: "AE \<omega> in P. ennreal (tv x + mg) \<le> ennreal (FN \<omega>)"
    using AEpack
  proof (eventually_elim)
    case (elim \<omega>)
    define \<tau> where "\<tau> = pball_exit T x rr \<omega>"
    note elim' = elim[folded \<tau>_def]
    have tau0: "0 < \<tau>" using elim' by blast
    have stays: "\<And>s. s \<in> {0..\<tau>} \<Longrightarrow> fst (\<omega> s) \<in> cball x rr"
      using elim' by blast
    have bdry: "\<tau> < T \<Longrightarrow> dist (fst (\<omega> \<tau>)) x = rr"
      using elim' by blast
    have growtau: "\<tau> * (\<eta> - 2) / 2
        \<le> g x \<bullet> (fst (\<omega> \<tau>) - x)
          + (1/2) * ((fst (\<omega> \<tau>) - x) \<bullet> (M *v (fst (\<omega> \<tau>) - x)))"
      using elim' by blast
    have inside: "\<And>s. 0 \<le> s \<Longrightarrow> s < \<tau> \<Longrightarrow> fst (\<omega> s) \<in> ball x rr"
      using elim' by blast
    have growall: "\<And>t. 0 < t \<Longrightarrow> t \<le> T \<Longrightarrow>
        (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> ball x rr) \<Longrightarrow>
        t * (\<eta> - 2) / 2 \<le> g x \<bullet> (fst (\<omega> t) - x)
          + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x)))"
      using elim' by blast
    have tauT: "\<tau> \<le> T" unfolding \<tau>_def by (rule pball_exit_le[OF T0'])
    have thw: "\<theta> \<omega> = min cc \<tau>" unfolding \<theta>_def \<tau>_def by (rule refl)
    have th0: "0 < \<theta> \<omega>" unfolding thw using cc0 tau0 by simp
    have thcc: "\<theta> \<omega> \<le> cc" unfolding thw by simp
    have thtau: "\<theta> \<omega> \<le> \<tau>" unfolding thw by simp
    have thT: "\<theta> \<omega> < T" using thcc ccT by linarith
    have inK: "\<And>s. 0 \<le> s \<Longrightarrow> s \<le> \<theta> \<omega> \<Longrightarrow> fst (\<omega> s) \<in> K"
    proof -
      fix s assume s0: "0 \<le> s" and sth: "s \<le> \<theta> \<omega>"
      have "s \<in> {0..\<tau>}" using s0 sth thtau by simp
      then have "fst (\<omega> s) \<in> cball x rr" by (rule stays)
      then show "fst (\<omega> s) \<in> K" using cb_K by blast
    qed
    have pex: "pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega>"
      by (rule pexit_eq_of_stays[OF less_imp_le[OF th0]]) (use inK in simp)
    have XinK: "fst (\<omega> (\<theta> \<omega>)) \<in> K"
      using inK[of "\<theta> \<omega>"] th0 by simp
    have cap: "enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>))))
        = min (tv (fst (\<omega> (\<theta> \<omega>)))) (T - \<theta> \<omega>)"
      unfolding tv_def
      by (rule enn2real_paper_v_horizon_cap[OF _ _ L1' Kc])
        (use thT th0 in auto)
    have feq: "FN \<omega> = \<theta> \<omega> + min (tv (fst (\<omega> (\<theta> \<omega>)))) (T - \<theta> \<omega>)"
      unfolding FN_def using pex XinK cap by simp
    have Xcb: "fst (\<omega> (\<theta> \<omega>)) \<in> cball x rr"
      using stays[of "\<theta> \<omega>"] th0 thtau by simp
    have Xphi: "fst (\<omega> (\<theta> \<omega>)) \<in> ball x rphi"
      using Xcb cb_phi by blast
    have touch: "tv x + (\<phi> (fst (\<omega> (\<theta> \<omega>))) - \<phi> x)
        \<le> tv (fst (\<omega> (\<theta> \<omega>)))"
      using tmin[OF XinK] unfolding tv_def by linarith
    have minor: "\<phi> x + g x \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x)
        + ((fst (\<omega> (\<theta> \<omega>)) - x)
            \<bullet> ((H - \<delta> *\<^sub>R mat 1) *v (fst (\<omega> (\<theta> \<omega>)) - x))) / 2
        \<le> \<phi> (fst (\<omega> (\<theta> \<omega>)))"
      by (rule mino[OF Xphi])
    have soften: "(fst (\<omega> (\<theta> \<omega>)) - x)
        \<bullet> ((H - \<delta> *\<^sub>R mat 1) *v (fst (\<omega> (\<theta> \<omega>)) - x))
        = (fst (\<omega> (\<theta> \<omega>)) - x) \<bullet> (M *v (fst (\<omega> (\<theta> \<omega>)) - x))
          + 2 * \<gamma> * ((fst (\<omega> (\<theta> \<omega>)) - x) \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x))"
      unfolding M_def by (rule quad_soften_split)
    have tvX: "tv x + (g x \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x)
        + (1/2) * ((fst (\<omega> (\<theta> \<omega>)) - x)
            \<bullet> (M *v (fst (\<omega> (\<theta> \<omega>)) - x)))
        + \<gamma> * ((fst (\<omega> (\<theta> \<omega>)) - x) \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x)))
        \<le> tv (fst (\<omega> (\<theta> \<omega>)))"
      using touch minor soften by linarith
    have QQ: "\<theta> \<omega> * (\<eta> - 2) / 2
        + (if \<tau> \<le> cc then \<gamma> * rr\<^sup>2 else 0)
        \<le> g x \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x)
          + (1/2) * ((fst (\<omega> (\<theta> \<omega>)) - x)
              \<bullet> (M *v (fst (\<omega> (\<theta> \<omega>)) - x)))
          + \<gamma> * ((fst (\<omega> (\<theta> \<omega>)) - x) \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x))"
    proof (cases "\<tau> \<le> cc")
      case True
      have theq: "\<theta> \<omega> = \<tau>" unfolding thw using True by simp
      have tauTs: "\<tau> < T" using True ccT by linarith
      have sphere: "dist (fst (\<omega> \<tau>)) x = rr" by (rule bdry[OF tauTs])
      have nrm: "norm (fst (\<omega> \<tau>) - x) = rr"
        using sphere by (simp add: dist_norm norm_minus_commute)
      have dsq: "(fst (\<omega> \<tau>) - x) \<bullet> (fst (\<omega> \<tau>) - x) = rr\<^sup>2"
        using nrm by (simp add: dot_square_norm)
      show ?thesis
        unfolding theq using growtau dsq True by simp
    next
      case False
      have theq: "\<theta> \<omega> = cc" unfolding thw using False by simp
      have inb: "\<forall>s\<in>{0..cc}. fst (\<omega> s) \<in> ball x rr"
      proof
        fix s assume "s \<in> {0..cc}"
        then have "0 \<le> s" and "s < \<tau>" using False by auto
        then show "fst (\<omega> s) \<in> ball x rr" by (rule inside)
      qed
      have gq: "cc * (\<eta> - 2) / 2 \<le> g x \<bullet> (fst (\<omega> cc) - x)
          + (1/2) * ((fst (\<omega> cc) - x) \<bullet> (M *v (fst (\<omega> cc) - x)))"
        by (rule growall[OF cc0 ccT' inb])
      have nn: "0 \<le> \<gamma> * ((fst (\<omega> cc) - x) \<bullet> (fst (\<omega> cc) - x))"
        using g0 inner_ge_zero by simp
      show ?thesis unfolding theq using gq nn False by simp
    qed
    have fun_ge: "tv x + mg \<le> FN \<omega>"
    proof (cases "tv (fst (\<omega> (\<theta> \<omega>))) \<le> T - \<theta> \<omega>")
      case True
      have mfe: "FN \<omega> = \<theta> \<omega> + tv (fst (\<omega> (\<theta> \<omega>)))"
        unfolding feq using True by simp
      have id1: "\<theta> \<omega> * (\<eta> - 2) / 2 + \<theta> \<omega> = \<theta> \<omega> * \<eta> / 2"
        by (simp add: field_simps)
      show ?thesis
      proof (cases "\<tau> \<le> cc")
        case True
        have QQc: "\<theta> \<omega> * (\<eta> - 2) / 2 + \<gamma> * rr\<^sup>2
            \<le> g x \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x)
              + (1/2) * ((fst (\<omega> (\<theta> \<omega>)) - x)
                  \<bullet> (M *v (fst (\<omega> (\<theta> \<omega>)) - x)))
              + \<gamma> * ((fst (\<omega> (\<theta> \<omega>)) - x) \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x))"
          using QQ True by simp
        have the0: "0 \<le> \<theta> \<omega> * \<eta> / 2"
          using th0 e0 by simp
        have mg1: "mg \<le> \<gamma> * rr\<^sup>2" unfolding mg_def by linarith
        show ?thesis
          unfolding mfe using tvX QQc id1 the0 mg1 by linarith
      next
        case False
        have QQc: "\<theta> \<omega> * (\<eta> - 2) / 2
            \<le> g x \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x)
              + (1/2) * ((fst (\<omega> (\<theta> \<omega>)) - x)
                  \<bullet> (M *v (fst (\<omega> (\<theta> \<omega>)) - x)))
              + \<gamma> * ((fst (\<omega> (\<theta> \<omega>)) - x) \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x))"
          using QQ False by simp
        have theq: "\<theta> \<omega> = cc" unfolding thw using False by simp
        have mg2: "mg \<le> cc * \<eta> / 2" unfolding mg_def by linarith
        show ?thesis
          unfolding mfe theq
          using tvX[unfolded theq] QQc[unfolded theq] id1[unfolded theq] mg2
          by linarith
      qed
    next
      case False
      have mfe: "FN \<omega> = \<theta> \<omega> + (T - \<theta> \<omega>)"
        unfolding feq using False by simp
      have "FN \<omega> = T" unfolding mfe by simp
      moreover have "mg \<le> T - tv x" unfolding mg_def by simp
      ultimately show ?thesis by linarith
    qed
    show ?case by (rule ennreal_leI[OF fun_ge])
  qed
  have essge: "ennreal (tv x + mg) \<le> ess_inf_time P FN"
    unfolding ess_inf_time_def
    by (rule Sup_upper) (use AEfun in blast)
  have esle: "ess_inf_time P FN \<le> exit_val k L T K x"
  proof -
    have "ess_inf_time P FN
        \<le> (SUP P' \<in> exit_class k L T x. ess_inf_time P' FN)"
      by (rule SUP_upper[OF Pc])
    then show ?thesis using dpp by (rule order_trans)
  qed
  have vfin: "ennreal (tv x) = exit_val k L T K x"
    unfolding tv_def
    using exit_val_neq_top[OF T0', of k L K x]
    by (simp add: less_top)
  have chain: "ennreal (tv x + mg) \<le> exit_val k L T K x"
    by (rule order_trans[OF essge esle])
  have "ennreal (tv x + mg) \<le> ennreal (tv x)"
    using chain by (simp add: vfin)
  moreover have "0 \<le> tv x" unfolding tv_def by simp
  ultimately have "tv x + mg \<le> tv x" by simp
  then show False using mg0 by linarith
    qed
  qed
qed

subsection \<open>Case 1, packaged for the envelope form\<close>

text \<open>The contradiction, read back as the positive statement the envelope
  supersolution definition wants: at any interior touching point with a
  nonzero gradient the usc envelope of the operator is at least one, since
  \<open>F \<le> F\<^sup>*\<close> (@{thm [source] ell_op_le_ell_op_usc}) turns a failed envelope
  inequality into a failed plain one.\<close>

subsection \<open>Bricks for Case 2: the envelope limit and the tangential field\<close>

text \<open>The sphere-tangential projector field.  The companion input, that the
  usc envelope passes \<open>\<ge> 1\<close> through limits in \<open>(p, M)\<close> and so turns the
  Case-1 conclusions at perturbed touching points into
  \<open>1 \<le> F\<^sup>*(0, H)\<close>, is @{thm [source] ell_op_usc_ge_one_limit}.  Clamped
  to a ball separated from its centre \<open>y\<^sub>0\<close>, the field is an admissible
  volatility that kills the radial direction exactly, so the squared
  distance to \<open>y\<^sub>0\<close> moves at the deterministic rate \<open>CARD('n) - 1\<close>; this
  feeds the same Euler machinery as Case 1 and is the positivity input for
  the second horn of the dichotomy, and for Example 3.1's lower bound.\<close>

text \<open>Matrix difference distributes over the product, entrywise:
  \<open>matrix_msub_rdistrib\<close> is \<open>matrix_mul_diff_left\<close> and \<open>matrix_msub_ldistrib\<close>
  is \<open>matrix_mul_diff_right\<close>, both from
  @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>

subsubsection \<open>The tangential projector\<close>

definition tanp :: "real^'n::finite \<Rightarrow> real^'n^'n"
  where "tanp u = mat 1 - outerp u"

lemma tanp_mv: "tanp u *v w = w - (u \<bullet> w) *\<^sub>R u"
  unfolding tanp_def outerp_eq_outer_prod
  by (simp add: matrix_vector_mult_diff_rdistrib)

lemma tanp_sym: "transpose (tanp u) = tanp u"
proof -
  have "transpose (tanp u) = transpose (mat 1) - transpose (outerp u)"
    unfolding tanp_def by (simp add: transpose_def vec_eq_iff)
  also have "transpose (outerp u) = outerp u"
    by (simp add: transpose_def outerp_def vec_eq_iff mult_ac)
  finally show ?thesis by (simp add: tanp_def)
qed

lemma tanp_quadform: "x \<bullet> (tanp u *v x) = x \<bullet> x - (u \<bullet> x)\<^sup>2"
  unfolding tanp_mv
  by (simp add: inner_diff_right
      power2_eq_square inner_commute)

lemma tanp_psd:
  fixes u :: "real^'n::finite"
  assumes u1: "norm u \<le> 1"
  shows "psd (tanp u)"
  unfolding psd_def
proof (intro conjI allI)
  show "transpose (tanp u) = tanp u" by (rule tanp_sym)
next
  fix x :: "real^'n"
  have "\<bar>u \<bullet> x\<bar> \<le> norm u * norm x" by (rule Cauchy_Schwarz_ineq2)
  also have "\<dots> \<le> 1 * norm x"
    by (rule mult_right_mono[OF u1 norm_ge_zero])
  finally have cs: "\<bar>u \<bullet> x\<bar> \<le> norm x" by simp
  have sq: "(u \<bullet> x)\<^sup>2 \<le> (norm x)\<^sup>2"
    using cs by (metis abs_ge_zero power2_abs power_mono)
  have xx: "x \<bullet> x = (norm x)\<^sup>2" by (simp add: dot_square_norm)
  show "0 \<le> x \<bullet> (tanp u *v x)"
    unfolding tanp_quadform using sq xx by linarith
qed

lemma tanp_eigen_ub:
  fixes u :: "real^'n::finite"
  assumes L1: "1 \<le> L"
  shows "eigen_ub (tanp u) L"
  unfolding eigen_ub_def
proof
  fix x :: "real^'n"
  have "x \<bullet> (tanp u *v x) \<le> x \<bullet> x"
    unfolding tanp_quadform by simp
  also have "\<dots> = 1 * (x \<bullet> x)" by simp
  also have "\<dots> \<le> L * (x \<bullet> x)"
    by (rule mult_right_mono[OF L1 inner_ge_zero])
  finally show "x \<bullet> (tanp u *v x) \<le> L * (x \<bullet> x)" .
qed

lemma tanp_eigen_lb:
  fixes u :: "real^'n::finite"
  assumes k1: "1 \<le> k"
  shows "eigen_lb (tanp u) (CARD('n) - k)"
  unfolding eigen_lb_def
proof (intro exI[of _ "{x :: real^'n. u \<bullet> x = 0}"] conjI ballI)
  show "subspace {x :: real^'n. u \<bullet> x = 0}"
    by (rule subspace_hyperplane)
  show "CARD('n) - k \<le> dim {x :: real^'n. u \<bullet> x = 0}"
  proof (cases "u = 0")
    case True
    then have "{x :: real^'n. u \<bullet> x = 0} = UNIV" by simp
    then show ?thesis by simp
  next
    case False
    then have "dim {x :: real^'n. u \<bullet> x = 0} = CARD('n) - 1"
      by (simp add: dim_hyperplane)
    then show ?thesis using k1 by simp
  qed
next
  fix x :: "real^'n" assume "x \<in> {x. u \<bullet> x = 0}"
  then have "u \<bullet> x = 0" by simp
  then show "x \<bullet> x \<le> x \<bullet> (tanp u *v x)"
    unfolding tanp_quadform by simp
qed

lemma tanp_feasible:
  fixes u :: "real^'n::finite"
  assumes u1: "norm u \<le> 1" and k1: "1 \<le> k" and L1: "1 \<le> L"
  shows "tanp u \<in> feasible k L 0"
  unfolding feasible_def
  using tanp_psd[OF u1] tanp_eigen_ub[OF L1, of u]
    tanp_eigen_lb[OF k1, of u]
  by simp

lemma tanp_sconstraint:
  fixes u :: "real^'n::finite"
  assumes u1: "norm u \<le> 1" and k1: "1 \<le> k" and L1: "1 \<le> L"
  shows "tanp u \<in> sconstraint k L"
  using tanp_feasible[OF u1 k1 L1] feasible_subset_sconstraint by blast

lemma outerp_sq: "outerp u ** outerp u = (u \<bullet> u) *\<^sub>R outerp u"
proof -
  have "(outerp u ** outerp u) $ i $ j = ((u \<bullet> u) *\<^sub>R outerp u) $ i $ j"
    for i j
  proof -
    have "(outerp u ** outerp u) $ i $ j
        = (\<Sum>l\<in>UNIV. (u $ i * u $ l) * (u $ l * u $ j))"
      by (simp add: outerp_def matrix_matrix_mult_def)
    also have "\<dots> = u $ i * u $ j * (\<Sum>l\<in>UNIV. u $ l * u $ l)"
      by (simp add: sum_distrib_left mult_ac)
    also have "\<dots> = ((u \<bullet> u) *\<^sub>R outerp u) $ i $ j"
      by (simp add: outerp_def inner_vec_def mult_ac)
    finally show ?thesis .
  qed
  then show ?thesis by (simp add: vec_eq_iff)
qed

lemma tanp_sq:
  fixes u :: "real^'n::finite"
  assumes u1: "norm u = 1"
  shows "tanp u ** tanp u = tanp u"
proof -
  have uu: "u \<bullet> u = 1"
    using u1 by (metis norm_eq_1)
  have "tanp u ** tanp u
      = mat 1 ** tanp u - outerp u ** tanp u"
    unfolding tanp_def by (rule matrix_mul_diff_left)
  also have "mat 1 ** tanp u = tanp u" by (rule matrix_mul_lid)
  also have "outerp u ** tanp u
      = outerp u ** mat 1 - outerp u ** outerp u"
    unfolding tanp_def by (rule matrix_mul_diff_right)
  also have "\<dots> = outerp u - outerp u"
    by (simp add: outerp_sq uu)
  finally show ?thesis by (simp add: tanp_def)
qed

lemma tanp_trace:
  fixes u :: "real^'n::finite"
  assumes u1: "norm u = 1"
  shows "trace (tanp u) = real CARD('n) - 1"
proof -
  have uu: "u \<bullet> u = 1" using u1 by (metis norm_eq_1)
  have tm: "trace (mat 1 :: real^'n^'n) = real CARD('n)"
    by (simp add: trace_def mat_def)
  have td: "trace (tanp u :: real^'n^'n)
      = trace (mat 1 :: real^'n^'n) - trace (outerp u)"
    unfolding tanp_def by (simp add: trace_def sum_subtractf)
  show ?thesis unfolding td tm trace_outerp uu by simp
qed

lemma tanp_kill:
  fixes u :: "real^'n::finite"
  assumes u1: "norm u = 1" and par: "w = (norm w) *\<^sub>R u"
  shows "tanp u *v w = 0"
proof -
  have uu: "u \<bullet> u = 1" using u1 by (metis norm_eq_1)
  have "u \<bullet> w = u \<bullet> ((norm w) *\<^sub>R u)"
    by (rule arg_cong[where f = "\<lambda>v. u \<bullet> v", OF par])
  also have "\<dots> = norm w * (u \<bullet> u)"
    by simp
  also have "\<dots> = norm w" using uu by simp
  finally have uw: "u \<bullet> w = norm w" .
  have "tanp u *v w = w - (u \<bullet> w) *\<^sub>R u" by (rule tanp_mv)
  also have "\<dots> = w - (norm w) *\<^sub>R u" using uw by simp
  also have "\<dots> = 0" using par by simp
  finally show ?thesis .
qed

subsubsection \<open>The guarded unit radial and the clamped field\<close>

definition uvec :: "real^'n::finite \<Rightarrow> real \<Rightarrow> real^'n \<Rightarrow> real^'n"
  where "uvec y\<^sub>0 \<rho> w = (1 / max \<rho> (norm (w - y\<^sub>0))) *\<^sub>R (w - y\<^sub>0)"

lemma uvec_unit:
  assumes rho0: "0 < \<rho>" and far: "\<rho> \<le> norm (w - y\<^sub>0)"
  shows "norm (uvec y\<^sub>0 \<rho> w) = 1"
proof -
  have mx: "max \<rho> (norm (w - y\<^sub>0)) = norm (w - y\<^sub>0)"
    using far by (simp add: max_def)
  have n0: "norm (w - y\<^sub>0) \<noteq> 0" using rho0 far by linarith
  show ?thesis unfolding uvec_def mx using n0 by simp
qed

lemma uvec_norm_le:
  assumes rho0: "0 < \<rho>"
  shows "norm (uvec y\<^sub>0 \<rho> w) \<le> 1"
proof -
  have mx0: "0 < max \<rho> (norm (w - y\<^sub>0))" using rho0 by simp
  have le: "norm (w - y\<^sub>0) \<le> max \<rho> (norm (w - y\<^sub>0))" by simp
  have "norm (uvec y\<^sub>0 \<rho> w)
      = norm (w - y\<^sub>0) / max \<rho> (norm (w - y\<^sub>0))"
    unfolding uvec_def using mx0 by simp
  also have "\<dots> \<le> 1" using mx0 le by (simp add: divide_le_eq_1)
  finally show ?thesis .
qed

lemma uvec_par:
  assumes rho0: "0 < \<rho>" and far: "\<rho> \<le> norm (w - y\<^sub>0)"
  shows "w - y\<^sub>0 = norm (w - y\<^sub>0) *\<^sub>R uvec y\<^sub>0 \<rho> w"
proof -
  have mx: "max \<rho> (norm (w - y\<^sub>0)) = norm (w - y\<^sub>0)"
    using far by (simp add: max_def)
  have n0: "norm (w - y\<^sub>0) \<noteq> 0" using rho0 far by linarith
  show ?thesis unfolding uvec_def mx using n0 by simp
qed

lemma uvec_cont:
  fixes y\<^sub>0 :: "real^'n::finite"
  assumes rho0: "0 < \<rho>"
  shows "continuous_on UNIV (uvec y\<^sub>0 \<rho>)"
proof -
  have nz: "\<And>w :: real^'n. max \<rho> (norm (w - y\<^sub>0)) \<noteq> 0"
    using rho0 by simp
  show ?thesis
    unfolding uvec_def
    by (intro continuous_intros) (use nz in simp_all)
qed

definition tanSF ::
  "real^'n::finite \<Rightarrow> real \<Rightarrow> real^'n \<Rightarrow> real \<Rightarrow> real^'n \<Rightarrow> real^'n^'n"
  where "tanSF y\<^sub>0 \<rho> x rb z
    = tanp (uvec y\<^sub>0 \<rho> (closest_point (cball x rb) z))"

theorem tanSF_package:
  fixes y\<^sub>0 x :: "real^'n::finite" and \<rho> rb :: real
  assumes rho0: "0 < \<rho>" and rb0: "0 \<le> rb"
    and sep: "\<rho> + rb \<le> dist x y\<^sub>0"
    and k1: "1 \<le> k" and kn: "k < CARD('n)" and L1: "1 \<le> L"
  shows tanSF_cont: "continuous_on UNIV (tanSF y\<^sub>0 \<rho> x rb)"
    and tanSF_sconstraint: "\<And>z. tanSF y\<^sub>0 \<rho> x rb z
        ** transpose (tanSF y\<^sub>0 \<rho> x rb z) \<in> sconstraint k L"
    and tanSF_kill: "\<And>z c. transpose (tanSF y\<^sub>0 \<rho> x rb z)
        *v (c *\<^sub>R (x - y\<^sub>0) + (c *\<^sub>R mat 1)
            *v (closest_point (cball x rb) z - x)) = 0"
    and tanSF_trace: "\<And>z. trace (tanSF y\<^sub>0 \<rho> x rb z
        ** transpose (tanSF y\<^sub>0 \<rho> x rb z)) = real CARD('n) - 1"
proof -
  have cin: "closest_point (cball x rb) z \<in> cball x rb" for z
    by (rule closest_point_in_set) (use rb0 in \<open>auto\<close>)
  have far: "\<rho> \<le> norm (closest_point (cball x rb) z - y\<^sub>0)" for z
  proof -
    have "dist (closest_point (cball x rb) z) x \<le> rb"
      using cin[of z] by (simp add: dist_commute)
    moreover have "dist x y\<^sub>0
        \<le> dist x (closest_point (cball x rb) z)
          + dist (closest_point (cball x rb) z) y\<^sub>0"
      by (rule dist_triangle)
    ultimately have "\<rho> \<le> dist (closest_point (cball x rb) z) y\<^sub>0"
      using sep by (simp add: dist_commute)
    then show ?thesis by (simp add: dist_norm)
  qed
  have unit: "norm (uvec y\<^sub>0 \<rho> (closest_point (cball x rb) z)) = 1" for z
    by (rule uvec_unit[OF rho0 far])
  show "continuous_on UNIV (tanSF y\<^sub>0 \<rho> x rb)"
  proof -
    have cpc: "continuous_on UNIV (closest_point (cball x rb))"
      by (rule continuous_on_closest_point)
        (use rb0 in \<open>auto\<close>)
    have uc: "continuous_on UNIV
        (\<lambda>z. uvec y\<^sub>0 \<rho> (closest_point (cball x rb) z))"
      by (rule continuous_on_compose2[OF uvec_cont[OF rho0] cpc]) auto
    have ci: "continuous_on UNIV
        (\<lambda>z. uvec y\<^sub>0 \<rho> (closest_point (cball x rb) z) $ i)" for i
      by (rule continuous_on_compose2[OF
          linear_continuous_on[OF bounded_linear_vec_nth] uc]) auto
    have eq: "tanSF y\<^sub>0 \<rho> x rb = (\<lambda>z. \<chi> i j.
        (if i = j then 1 else 0)
        - uvec y\<^sub>0 \<rho> (closest_point (cball x rb) z) $ i
          * uvec y\<^sub>0 \<rho> (closest_point (cball x rb) z) $ j)"
      by (rule ext)
        (simp add: tanSF_def tanp_def outerp_def mat_def vec_eq_iff)
    show ?thesis unfolding eq
      by (intro continuous_on_vec_lambda continuous_intros ci)
  qed
  have sq: "tanSF y\<^sub>0 \<rho> x rb z ** transpose (tanSF y\<^sub>0 \<rho> x rb z)
      = tanSF y\<^sub>0 \<rho> x rb z" for z
    unfolding tanSF_def
    by (simp add: tanp_sym tanp_sq[OF unit])
  show "tanSF y\<^sub>0 \<rho> x rb z ** transpose (tanSF y\<^sub>0 \<rho> x rb z)
      \<in> sconstraint k L" for z
    unfolding sq unfolding tanSF_def
    by (rule tanp_sconstraint[OF uvec_norm_le[OF rho0] k1 L1])
  show "transpose (tanSF y\<^sub>0 \<rho> x rb z)
      *v (c *\<^sub>R (x - y\<^sub>0) + (c *\<^sub>R mat 1)
          *v (closest_point (cball x rb) z - x)) = 0" for z c
  proof -
    have arg: "c *\<^sub>R (x - y\<^sub>0) + (c *\<^sub>R mat 1)
        *v (closest_point (cball x rb) z - x)
        = c *\<^sub>R (closest_point (cball x rb) z - y\<^sub>0)"
      by (simp add: scaleR_matrix_vector
          scaleR_right_diff_distrib scaleR_add_right)
    have k0: "tanp (uvec y\<^sub>0 \<rho> (closest_point (cball x rb) z))
        *v (closest_point (cball x rb) z - y\<^sub>0) = 0"
      by (rule tanp_kill[OF unit uvec_par[OF rho0 far]])
    have "transpose (tanSF y\<^sub>0 \<rho> x rb z)
        *v (c *\<^sub>R (closest_point (cball x rb) z - y\<^sub>0))
        = c *\<^sub>R (tanSF y\<^sub>0 \<rho> x rb z
            *v (closest_point (cball x rb) z - y\<^sub>0))"
      unfolding tanSF_def tanp_sym
      by (simp add: matrix_vector_mult_scaleR)
    also have "\<dots> = 0" unfolding tanSF_def using k0 by simp
    finally show ?thesis unfolding arg .
  qed
  show "trace (tanSF y\<^sub>0 \<rho> x rb z
      ** transpose (tanSF y\<^sub>0 \<rho> x rb z)) = real CARD('n) - 1" for z
    unfolding sq unfolding tanSF_def by (rule tanp_trace[OF unit])
qed

subsection \<open>Conditional orthogonality: the kill checked at the point\<close>

text \<open>The Euler increments annihilate a continuous field wherever the field
  is killed by the volatility: the kill condition moves from a global
  hypothesis into the conclusion, checked at each grid point.  This lets a
  field be tangential only away from its singular centre, since the growth
  telescope only ever uses orthogonality at grid points inside the good
  region, where the kill holds.  The proof is the committed induction of
  @{thm [source] eulerp_orth_increments} with the implication carried
  through the glue.\<close>

lemma euOrth_mset_cond:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n"
    and G :: "real^'n \<Rightarrow> real^'n" and h :: real
  assumes SFc: "continuous_on UNIV SF" and Gc: "continuous_on UNIV G"
  shows "{\<omega> \<in> space (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric))).
      \<forall>j<m. transpose (SF (fst (\<omega> (real j * h))))
          *v G (fst (\<omega> (real j * h))) = 0 \<longrightarrow>
        G (fst (\<omega> (real j * h))) \<bullet>
          (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0}
    \<in> sets (borel_of (mtopology_of (path_metric T :: ('n pairpath) metric)))"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have evm: "(\<lambda>\<omega> :: 'n pairpath. \<omega> u) \<in> ?B \<rightarrow>\<^sub>M borel" for u
    by (rule pair_law_eval_measurable[OF refl])
  have mfst: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
      \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI[OF
        continuous_on_fst[OF continuous_on_id]])
  have evf: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> u)) \<in> ?B \<rightarrow>\<^sub>M borel" for u
    by (rule measurable_compose[OF evm mfst])
  have condm: "(\<lambda>\<omega> :: 'n pairpath.
      transpose (SF (fst (\<omega> (real j * h))))
        *v G (fst (\<omega> (real j * h)))) \<in> ?B \<rightarrow>\<^sub>M borel" for j
  proof -
    have c: "continuous_on UNIV (\<lambda>w :: real^'n. transpose (SF w) *v G w)"
    proof -
      have ct: "continuous_on UNIV (\<lambda>w :: real^'n. transpose (SF w))"
      proof -
        have e: "(\<lambda>w :: real^'n. transpose (SF w))
            = (\<lambda>w. \<chi> i j. SF w $ j $ i)"
          by (rule ext) (simp add: transpose_def)
        have entry: "continuous_on UNIV (\<lambda>w :: real^'n. SF w $ j $ i)"
          for i j
        proof -
          have bl: "bounded_linear (\<lambda>A :: real^'n^'n. A $ j $ i)"
            using bounded_linear_vec_nth bounded_linear_compose by blast
          show ?thesis
            by (rule continuous_on_compose2[OF
                linear_continuous_on[OF bl] SFc]) auto
        qed
        show ?thesis unfolding e
          by (intro continuous_on_vec_lambda entry)
      qed
      have prodc: "continuous_on UNIV (\<lambda>w :: real^'n.
          transpose (SF w) *v G w)"
      proof -
        have e: "(\<lambda>w :: real^'n. transpose (SF w) *v G w)
            = (\<lambda>w. \<chi> i. (\<Sum>l\<in>UNIV. transpose (SF w) $ i $ l * G w $ l))"
          by (rule ext) (simp add: matrix_vector_mult_def)
        have entry: "continuous_on UNIV (\<lambda>w :: real^'n.
            \<Sum>l\<in>UNIV. transpose (SF w) $ i $ l * G w $ l)" for i
        proof -
          have tc: "continuous_on UNIV
              (\<lambda>w :: real^'n. transpose (SF w) $ i $ l)" for l
          proof -
            have bl: "bounded_linear (\<lambda>A :: real^'n^'n. A $ i $ l)"
              using bounded_linear_vec_nth bounded_linear_compose by blast
            show ?thesis
              by (rule continuous_on_compose2[OF
                  linear_continuous_on[OF bl] ct]) auto
          qed
          have gc: "continuous_on UNIV (\<lambda>w :: real^'n. G w $ l)" for l
            by (rule continuous_on_compose2[OF
                linear_continuous_on[OF bounded_linear_vec_nth] Gc]) auto
          show ?thesis
            by (intro continuous_on_sum continuous_on_mult tc gc)
        qed
        show ?thesis unfolding e
          by (intro continuous_on_vec_lambda entry)
      qed
      show ?thesis by (rule prodc)
    qed
    show ?thesis
      by (rule measurable_compose[OF evf
          borel_measurable_continuous_onI[OF c]])
  qed
  have orthm: "(\<lambda>\<omega> :: 'n pairpath.
      G (fst (\<omega> (real j * h))) \<bullet>
        (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))))
      \<in> ?B \<rightarrow>\<^sub>M borel" for j
  proof -
    have gc: "(\<lambda>\<omega> :: 'n pairpath. G (fst (\<omega> (real j * h))))
        \<in> ?B \<rightarrow>\<^sub>M borel"
      by (rule measurable_compose[OF evf
          borel_measurable_continuous_onI[OF Gc]])
    have dc: "(\<lambda>\<omega> :: 'n pairpath.
        fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h)))
        \<in> ?B \<rightarrow>\<^sub>M borel"
      by (intro borel_measurable_diff evf)
    show ?thesis by (intro borel_measurable_inner gc dc)
  qed
  have per: "{\<omega> \<in> space ?B.
      transpose (SF (fst (\<omega> (real j * h))))
        *v G (fst (\<omega> (real j * h))) = 0 \<longrightarrow>
      G (fst (\<omega> (real j * h))) \<bullet>
        (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0}
      \<in> sets ?B" for j
  proof -
    have cset: "{\<omega> \<in> space ?B.
        transpose (SF (fst (\<omega> (real j * h))))
          *v G (fst (\<omega> (real j * h))) = 0} \<in> sets ?B"
    proof -
      have "{\<omega> \<in> space ?B.
          transpose (SF (fst (\<omega> (real j * h))))
            *v G (fst (\<omega> (real j * h))) = 0}
          = (\<lambda>\<omega> :: 'n pairpath.
            transpose (SF (fst (\<omega> (real j * h))))
              *v G (fst (\<omega> (real j * h)))) -` {0} \<inter> space ?B"
        by auto
      then show ?thesis
        using measurable_sets[OF condm[of j], of "{0}"]
        by (simp add: borel_closed)
    qed
    have oset: "{\<omega> \<in> space ?B.
        G (fst (\<omega> (real j * h))) \<bullet>
          (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0}
        \<in> sets ?B"
    proof -
      have "{\<omega> \<in> space ?B.
          G (fst (\<omega> (real j * h))) \<bullet>
            (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0}
          = (\<lambda>\<omega> :: 'n pairpath.
            G (fst (\<omega> (real j * h))) \<bullet>
              (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))))
            -` {0} \<inter> space ?B"
        by auto
      then show ?thesis
        using measurable_sets[OF orthm[of j], of "{0}"]
        by (simp add: borel_closed)
    qed
    have eq: "{\<omega> \<in> space ?B.
        transpose (SF (fst (\<omega> (real j * h))))
          *v G (fst (\<omega> (real j * h))) = 0 \<longrightarrow>
        G (fst (\<omega> (real j * h))) \<bullet>
          (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0}
        = (space ?B - {\<omega> \<in> space ?B.
            transpose (SF (fst (\<omega> (real j * h))))
              *v G (fst (\<omega> (real j * h))) = 0})
          \<union> {\<omega> \<in> space ?B.
            G (fst (\<omega> (real j * h))) \<bullet>
              (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0}"
      by auto
    show ?thesis unfolding eq
      by (intro sets.Un sets.Diff sets.top cset oset)
  qed
  show ?thesis
  proof (induction m)
    case 0
    show ?case by simp
  next
    case (Suc m)
    have eq: "{\<omega> \<in> space ?B. \<forall>j<Suc m.
        transpose (SF (fst (\<omega> (real j * h))))
          *v G (fst (\<omega> (real j * h))) = 0 \<longrightarrow>
        G (fst (\<omega> (real j * h))) \<bullet>
          (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0}
        = {\<omega> \<in> space ?B. \<forall>j<m.
            transpose (SF (fst (\<omega> (real j * h))))
              *v G (fst (\<omega> (real j * h))) = 0 \<longrightarrow>
            G (fst (\<omega> (real j * h))) \<bullet>
              (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0}
          \<inter> {\<omega> \<in> space ?B.
            transpose (SF (fst (\<omega> (real m * h))))
              *v G (fst (\<omega> (real m * h))) = 0 \<longrightarrow>
            G (fst (\<omega> (real m * h))) \<bullet>
              (fst (\<omega> (real (Suc m) * h)) - fst (\<omega> (real m * h))) = 0}"
      by (auto simp: less_Suc_eq)
    show ?case unfolding eq by (intro sets.Int Suc.IH per)
  qed
qed

theorem eulerp_orth_increments_cond:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n" and G :: "real^'n \<Rightarrow> real^'n"
    and x :: "real^'n" and h :: real
  assumes h0: "0 < h" and L1: "1 \<le> L"
    and SFc: "continuous_on UNIV SF"
    and SFs: "\<And>z. SF z ** transpose (SF z) \<in> sconstraint k L"
    and Gc: "continuous_on UNIV G"
  shows "AE \<omega> in eulerp SF x h N. \<forall>j<Suc N.
      transpose (SF (fst (\<omega> (real j * h))))
        *v G (fst (\<omega> (real j * h))) = 0 \<longrightarrow>
      G (fst (\<omega> (real j * h))) \<bullet>
        (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0"
proof (induction N)
  case 0
  have h0': "(0::real) \<le> h" using h0 by simp
  let ?\<mu>0 = "pair_law_of h (sbmpair (SF x) h)
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)"
  have E0: "eulerp SF x h 0 = pshift_law h x ?\<mu>0" by simp
  have sets\<mu>: "sets ?\<mu>0 = sets (borel_of (mtopology_of
      (path_metric h :: ('n pairpath) metric)))" by simp
  have st: "AE \<omega> in ?\<mu>0. fst (\<omega> 0) = (0 :: real^'n)"
    using sbmpair_law_start[OF h0', of "SF x"]
    by (rule eventually_mono) simp
  have orth0: "AE \<omega> in ?\<mu>0. transpose (SF x) *v G x = 0 \<longrightarrow>
      G x \<bullet> (fst (\<omega> h) - fst (\<omega> 0)) = 0"
  proof (cases "transpose (SF x) *v G x = 0")
    case True
    have "AE \<omega> in ?\<mu>0. G x \<bullet> (fst (\<omega> h) - fst (\<omega> 0)) = 0"
      by (rule sbm_orth_increment[OF h0' True])
    then show ?thesis by (rule eventually_mono) simp
  next
    case False
    then show ?thesis by simp
  qed
  have ae: "AE \<omega> in ?\<mu>0. \<forall>j<Suc 0.
      transpose (SF (fst (pshift h x \<omega> (real j * h))))
        *v G (fst (pshift h x \<omega> (real j * h))) = 0 \<longrightarrow>
      G (fst (pshift h x \<omega> (real j * h))) \<bullet>
        (fst (pshift h x \<omega> (real (Suc j) * h))
          - fst (pshift h x \<omega> (real j * h))) = 0"
    using st orth0
  proof eventually_elim
    case (elim \<omega>)
    have m1: "h \<in> {0..h}" and m2: "(0::real) \<in> {0..h}"
      using h0' by simp_all
    show ?case using elim
      by (simp add: pshift_fst[OF m1] pshift_fst[OF m2])
  qed
  show ?case unfolding E0 by (rule AE_pshift_law[OF h0' sets\<mu> ae])
next
  case (Suc N)
  have h0': "(0::real) \<le> h" using h0 by simp
  define r where "r = real (Suc N) * h"
  define T' where "T' = real (Suc (Suc N)) * h"
  let ?Q = "eulerp SF x h N"
  let ?Br = "borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))"
  let ?MR = "borel_of (mtopology_of
      (path_metric (T' - r) :: ('n pairpath) metric))"
  let ?K = "\<lambda>\<omega> :: 'n pairpath.
      pair_law_of h (sbmpair (SF (fst (\<omega> r))) h) bm_paths"
  have hT: "T' - r = h" unfolding r_def T'_def by (simp add: algebra_simps)
  have r0: "0 \<le> r" unfolding r_def using h0' by simp
  have rleT: "r \<le> T'" unfolding r_def T'_def
    using h0' by (intro mult_right_mono) simp_all
  have Qc: "?Q \<in> exit_class k L r x"
    unfolding r_def by (rule eulerp_in_class[OF h0 L1 SFc SFs])
  have PQ: "prob_space ?Q" by (rule exit_class_prob[OF Qc])
  have setsQ: "sets ?Q = sets ?Br" by (rule exit_class_sets[OF Qc])
  note pack = sbm_kernel_package[OF h0 L1 SFc SFs]
  have mfst: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
      \<in> borel_measurable borel"
    using measurable_fst[of "borel :: (real^'n) measure"
        "borel :: (real^'n^'n) measure"] by (simp add: borel_prod)
  have eQ: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> r)) \<in> borel_measurable ?Q"
    by (rule measurable_compose[OF pair_law_eval_measurable[OF setsQ] mfst])
  have Kp: "?K \<in> ?Q \<rightarrow>\<^sub>M prob_algebra ?MR"
    unfolding hT by (rule measurable_compose[OF eQ pack(1)])
  have Ee: "eulerp SF x h (Suc N) = kglue_law' r T' ?K ?Q"
    by (simp add: r_def T'_def)
  have msetP: "{\<omega> \<in> mspace (path_metric T' :: ('n pairpath) metric).
      \<forall>j<Suc (Suc N).
        transpose (SF (fst (\<omega> (real j * h))))
          *v G (fst (\<omega> (real j * h))) = 0 \<longrightarrow>
        G (fst (\<omega> (real j * h))) \<bullet>
          (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0}
      \<in> sets (borel_of (mtopology_of
        (path_metric T' :: ('n pairpath) metric)))"
  proof -
    have spB: "space (borel_of (mtopology_of
        (path_metric T' :: ('n pairpath) metric)))
        = mspace (path_metric T' :: ('n pairpath) metric)"
      by (rule space_of_path_sets[OF refl])
    show ?thesis
      using euOrth_mset_cond[OF SFc Gc,
          where h = h and T = T' and m = "Suc (Suc N)"]
      unfolding spB .
  qed
  show ?case
    unfolding Ee
  proof (rule AE_kglue_law'[OF r0 rleT PQ setsQ Kp msetP])
    show "AE \<omega> in ?Q. \<forall>j<Suc N.
        transpose (SF (fst (\<omega> (real j * h))))
          *v G (fst (\<omega> (real j * h))) = 0 \<longrightarrow>
        G (fst (\<omega> (real j * h))) \<bullet>
          (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0"
      by (rule Suc.IH)
    show "AE \<omega>' in ?K \<omega>.
        transpose (SF (fst (\<omega> r))) *v G (fst (\<omega> r)) = 0 \<longrightarrow>
        G (fst (\<omega> r)) \<bullet> (fst (\<omega>' h) - fst (\<omega>' 0)) = 0"
      if "\<omega> \<in> space ?Q" for \<omega> :: "'n pairpath"
    proof (cases "transpose (SF (fst (\<omega> r))) *v G (fst (\<omega> r)) = 0")
      case True
      have "AE \<omega>' in ?K \<omega>. G (fst (\<omega> r)) \<bullet> (fst (\<omega>' h) - fst (\<omega>' 0)) = 0"
        by (rule sbm_orth_increment[OF h0' True])
      then show ?thesis by (rule eventually_mono) simp
    next
      case False
      then show ?thesis by simp
    qed
    fix \<omega> \<omega>' :: "'n pairpath"
    assume "\<omega> \<in> mspace (path_metric r :: ('n pairpath) metric)"
      and "\<omega>' \<in> mspace (path_metric (T' - r) :: ('n pairpath) metric)"
      and A: "\<forall>j<Suc N.
        transpose (SF (fst (\<omega> (real j * h))))
          *v G (fst (\<omega> (real j * h))) = 0 \<longrightarrow>
        G (fst (\<omega> (real j * h))) \<bullet>
          (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0"
      and B: "transpose (SF (fst (\<omega> r))) *v G (fst (\<omega> r)) = 0 \<longrightarrow>
        G (fst (\<omega> r)) \<bullet> (fst (\<omega>' h) - fst (\<omega>' 0)) = 0"
    have mem: "real j * h \<in> {0..T'}" if le: "j \<le> Suc (Suc N)" for j
    proof -
      have a: "0 \<le> real j * h"
        by (intro mult_nonneg_nonneg h0') simp_all
      have b: "real j * h \<le> T'" unfolding T'_def
        using le h0' by (intro mult_right_mono) simp_all
      show ?thesis using a b by simp
    qed
    have prefl: "pglue r T' \<omega> \<omega>' (real j * h) = \<omega> (real j * h)"
      if j: "j \<le> Suc N" for j
    proof (rule pglue_le)
      show "real j * h \<in> {0..T'}" using j by (intro mem) simp
      show "real j * h \<le> r" unfolding r_def
        using j h0' by (intro mult_right_mono) simp_all
    qed
    have Tmem: "T' \<in> {0..T'}"
      using mem[of "Suc (Suc N)"] unfolding T'_def by simp
    have gT: "pglue r T' \<omega> \<omega>' T' = \<omega> r + (\<omega>' (T' - r) - \<omega>' 0)"
      by (rule pglue_ge[OF Tmem rleT])
    have gr: "pglue r T' \<omega> \<omega>' r = \<omega> r"
      using prefl[of "Suc N"] unfolding r_def by simp
    show "\<forall>j<Suc (Suc N).
        transpose (SF (fst (pglue r T' \<omega> \<omega>' (real j * h))))
          *v G (fst (pglue r T' \<omega> \<omega>' (real j * h))) = 0 \<longrightarrow>
        G (fst (pglue r T' \<omega> \<omega>' (real j * h))) \<bullet>
          (fst (pglue r T' \<omega> \<omega>' (real (Suc j) * h))
            - fst (pglue r T' \<omega> \<omega>' (real j * h))) = 0"
    proof (intro allI impI)
      fix j assume jle: "j < Suc (Suc N)"
        and cnd: "transpose (SF (fst (pglue r T' \<omega> \<omega>' (real j * h))))
          *v G (fst (pglue r T' \<omega> \<omega>' (real j * h))) = 0"
      show "G (fst (pglue r T' \<omega> \<omega>' (real j * h))) \<bullet>
          (fst (pglue r T' \<omega> \<omega>' (real (Suc j) * h))
            - fst (pglue r T' \<omega> \<omega>' (real j * h))) = 0"
      proof (cases "j < Suc N")
        case True
        then have j1: "Suc j \<le> Suc N" and j2: "j \<le> Suc N" by simp_all
        show ?thesis
          using A True cnd by (simp only: prefl[OF j1] prefl[OF j2])
      next
        case False
        with jle have jeq: "j = Suc N" by simp
        have e1: "real (Suc j) * h = T'" unfolding jeq T'_def by (rule refl)
        have e2: "real j * h = r" unfolding jeq r_def by (rule refl)
        show ?thesis
          using B cnd unfolding e1 e2 gT gr hT by simp
      qed
    qed
  qed
qed

subsection \<open>The growth telescope on an arbitrary region\<close>

text \<open>The quadratic lower bound of @{thm [source] eulerp_quad_lower},
  decoupled from the start-centred clamp: the kill and the trace margin
  are assumed only on the confinement region, and the conclusion holds
  on the event that the grid stays there.  The conditional orthogonality
  @{thm [source] eulerp_orth_increments_cond} checks the kill at each
  grid point, so no clamp or global hypothesis is needed.  This form
  admits a vector field that is tangential only on an annulus around its
  own centre.\<close>

theorem eulerp_quad_lower_region:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n" and M :: "real^'n^'n"
    and q x :: "real^'n" and h cm :: real and R :: "(real^'n) set"
  assumes h0: "0 < h" and L1: "1 \<le> L"
    and SFc: "continuous_on UNIV SF"
    and SFs: "\<And>z. SF z ** transpose (SF z) \<in> sconstraint k L"
    and sym: "transpose M = M"
    and kill: "\<And>z. z \<in> R \<Longrightarrow>
        transpose (SF z) *v (q + M *v (z - x)) = 0"
    and marg: "\<And>z. z \<in> R \<Longrightarrow>
        cm \<le> trace (M ** (SF z ** transpose (SF z)))"
  shows "AE \<omega> in eulerp SF x h N. \<forall>m\<le>Suc N.
      (\<forall>j<m. fst (\<omega> (real j * h)) \<in> R) \<longrightarrow>
      (1/2) * euXi SF M h m \<omega> + real m * h * cm / 2
        \<le> q \<bullet> (fst (\<omega> (real m * h)) - x)
          + (1/2) * ((fst (\<omega> (real m * h)) - x)
              \<bullet> (M *v (fst (\<omega> (real m * h)) - x)))"
proof -
  have Gc: "continuous_on UNIV (\<lambda>z :: real^'n. q + M *v (z - x))"
  proof -
    have d: "continuous_on UNIV (\<lambda>z :: real^'n. z - x)"
      by (intro continuous_intros)
    have mv: "continuous_on UNIV (\<lambda>z :: real^'n. M *v (z - x))"
      by (rule continuous_on_compose2[OF
          linear_continuous_on[OF matvec_blin] d]) auto
    show ?thesis by (intro continuous_intros mv)
  qed
  note orth = eulerp_orth_increments_cond[OF h0 L1 SFc SFs Gc]
  have Qc: "eulerp SF x h N \<in> exit_class k L (real (Suc N) * h) x"
    by (rule eulerp_in_class[OF h0 L1 SFc SFs])
  have st: "AE \<omega> in eulerp SF x h N. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    using Qc unfolding exit_class_def by blast
  show ?thesis
    using orth st
  proof eventually_elim
    case (elim \<omega>)
    show ?case
    proof (intro allI impI)
      fix m assume mle: "m \<le> Suc N"
        and inb: "\<forall>j<m. fst (\<omega> (real j * h)) \<in> R"
      define X where "X j = fst (\<omega> (real j * h))" for j
      define \<psi> where "\<psi> z = q \<bullet> (z - x)
          + (1/2) * ((z - x) \<bullet> (M *v (z - x)))" for z
      have x0: "X 0 = x" unfolding X_def using elim by simp
      have XR: "X j \<in> R" if j: "j < m" for j
        using inb j unfolding X_def by blast
      have step: "\<psi> (X (Suc j)) - \<psi> (X j)
          = (1/2) * ((X (Suc j) - X j) \<bullet> (M *v (X (Suc j) - X j)))"
        if j: "j < m" for j
      proof -
        have jN: "j < Suc N" using j mle by simp
        have cnd: "transpose (SF (X j)) *v (q + M *v (X j - x)) = 0"
          by (rule kill[OF XR[OF j]])
        have k0: "(q + M *v (X j - x)) \<bullet> (X (Suc j) - X j) = 0"
          using elim(1) jN cnd unfolding X_def by metis
        have "\<psi> (X (Suc j)) - \<psi> (X j)
            = (q + M *v (X j - x)) \<bullet> (X (Suc j) - X j)
              + (1/2) * ((X (Suc j) - X j) \<bullet> (M *v (X (Suc j) - X j)))"
          unfolding \<psi>_def by (rule quad_taylor_step[OF sym])
        then show ?thesis using k0 by simp
      qed
      have tele: "\<psi> (X m) - \<psi> (X 0)
          = (\<Sum>j<m. \<psi> (X (Suc j)) - \<psi> (X j))"
        by (rule sum_lessThan_telescope[symmetric])
      have quadsum: "\<psi> (X m) - \<psi> (X 0)
          = (\<Sum>j<m. (1/2) * ((X (Suc j) - X j)
              \<bullet> (M *v (X (Suc j) - X j))))"
        unfolding tele
        by (rule sum.cong[OF refl]) (use step in simp)
      have perj: "(1/2) * ((X (Suc j) - X j) \<bullet> (M *v (X (Suc j) - X j)))
          = (1/2) * (trace (M ** (outerp (X (Suc j) - X j)
              - h *\<^sub>R (SF (X j) ** transpose (SF (X j)))))
            + h * trace (M ** (SF (X j) ** transpose (SF (X j)))))" for j
      proof -
        have "trace (M ** (outerp (X (Suc j) - X j)
            - h *\<^sub>R (SF (X j) ** transpose (SF (X j)))))
            = trace (M ** outerp (X (Suc j) - X j))
              - h * trace (M ** (SF (X j) ** transpose (SF (X j))))"
          by (simp add: trace_mult_diff matmul_scaleR_right trace_scaleR)
        then show ?thesis by (simp add: trace_mult_outerp)
      qed
      have persum: "(\<Sum>j<m. (1/2) * ((X (Suc j) - X j)
            \<bullet> (M *v (X (Suc j) - X j))))
          = (1/2) * euXi SF M h m \<omega>
            + (h/2) * (\<Sum>j<m. trace (M ** (SF (X j)
                ** transpose (SF (X j)))))"
      proof -
        have "(\<Sum>j<m. (1/2) * ((X (Suc j) - X j)
              \<bullet> (M *v (X (Suc j) - X j))))
            = (\<Sum>j<m. (1/2) * (trace (M ** (outerp (X (Suc j) - X j)
                - h *\<^sub>R (SF (X j) ** transpose (SF (X j)))))
              + h * trace (M ** (SF (X j) ** transpose (SF (X j))))))"
          by (rule sum.cong[OF refl]) (rule perj)
        also have "\<dots> = (\<Sum>j<m. (1/2) * trace (M **
              (outerp (X (Suc j) - X j)
                - h *\<^sub>R (SF (X j) ** transpose (SF (X j)))))
            + (h/2) * trace (M ** (SF (X j) ** transpose (SF (X j)))))"
          by (rule sum.cong[OF refl]) (simp add: field_simps)
        also have "\<dots> = (\<Sum>j<m. (1/2) * trace (M **
              (outerp (X (Suc j) - X j)
                - h *\<^sub>R (SF (X j) ** transpose (SF (X j))))))
            + (\<Sum>j<m. (h/2) * trace (M ** (SF (X j)
                ** transpose (SF (X j)))))"
          by (rule sum.distrib)
        also have "(\<Sum>j<m. (1/2) * trace (M **
              (outerp (X (Suc j) - X j)
                - h *\<^sub>R (SF (X j) ** transpose (SF (X j))))))
            = (1/2) * (\<Sum>j<m. trace (M **
              (outerp (X (Suc j) - X j)
                - h *\<^sub>R (SF (X j) ** transpose (SF (X j))))))"
          by (rule sum_distrib_left[symmetric])
        also have "(\<Sum>j<m. (h/2) * trace (M ** (SF (X j)
              ** transpose (SF (X j)))))
            = (h/2) * (\<Sum>j<m. trace (M ** (SF (X j)
                ** transpose (SF (X j)))))"
          by (rule sum_distrib_left[symmetric])
        also have "(\<Sum>j<m. trace (M ** (outerp (X (Suc j) - X j)
              - h *\<^sub>R (SF (X j) ** transpose (SF (X j))))))
            = euXi SF M h m \<omega>"
          unfolding euXi_def X_def by (rule refl)
        finally show ?thesis .
      qed
      have margsum: "real m * cm
          \<le> (\<Sum>j<m. trace (M ** (SF (X j) ** transpose (SF (X j)))))"
      proof -
        have "real m * cm = (\<Sum>j\<in>{..<m}. cm)" by simp
        also have "\<dots> \<le> (\<Sum>j<m. trace (M ** (SF (X j)
            ** transpose (SF (X j)))))"
        proof (rule sum_mono)
          fix j assume "j \<in> {..<m}"
          then have "X j \<in> R" by (intro XR) simp
          then show "cm \<le> trace (M ** (SF (X j) ** transpose (SF (X j))))"
            by (rule marg)
        qed
        finally show ?thesis .
      qed
      have psi0: "\<psi> (X 0) = 0" unfolding \<psi>_def x0 by simp
      have hm: "(h/2) * (real m * cm)
          \<le> (h/2) * (\<Sum>j<m. trace (M ** (SF (X j)
              ** transpose (SF (X j)))))"
        using h0 margsum by (intro mult_left_mono) simp_all
      have ee: "real m * h * cm / 2 = (h/2) * (real m * cm)" by simp
      have main: "(1/2) * euXi SF M h m \<omega> + real m * h * cm / 2
          \<le> \<psi> (X m)"
        using quadsum persum psi0 hm ee by linarith
      show "(1/2) * euXi SF M h m \<omega> + real m * h * cm / 2
          \<le> q \<bullet> (fst (\<omega> (real m * h)) - x)
            + (1/2) * ((fst (\<omega> (real m * h)) - x)
                \<bullet> (M *v (fst (\<omega> (real m * h)) - x)))"
        using main unfolding \<psi>_def X_def .
    qed
  qed
qed

subsection \<open>Region variants of the Lipschitz bound and the open event\<close>

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

lemma open_quad_bad_event_region:
  fixes x q :: "real^'n::finite" and M :: "real^'n^'n"
    and t T thr :: real and RO :: "(real^'n) set"
  assumes t0: "0 \<le> t" and tT: "t \<le> T" and RO: "open RO"
  shows "openin (mtopology_of (path_metric T :: ('n pairpath) metric))
      {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
        (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> RO)
        \<and> q \<bullet> (fst (\<omega> t) - x)
          + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x))) < thr}"
proof -
  have T0: "0 \<le> T" using t0 tT by linarith
  let ?pm = "path_metric T :: ('n pairpath) metric"
  have o1: "openin (mtopology_of ?pm)
      {\<omega> \<in> mspace ?pm. \<forall>s\<in>{0..t}. \<omega> s \<in> fst -` RO}"
    by (rule open_stay_inside[OF T0 open_vimage_fst[OF RO] t0 tT])
  have c0: "continuous_on UNIV
      (\<lambda>p :: (real^'n) \<times> (real^'n^'n). fst p - x)"
    by (intro continuous_intros)
  have c1: "continuous_on UNIV
      (\<lambda>p :: (real^'n) \<times> (real^'n^'n). M *v (fst p - x))"
    by (rule continuous_on_compose2[OF
        linear_continuous_on[OF matvec_blin] c0]) auto
  have cq: "continuous_on UNIV
      (\<lambda>p :: (real^'n) \<times> (real^'n^'n). q \<bullet> (fst p - x))"
    by (rule continuous_on_compose2[OF
        linear_continuous_on[OF bounded_linear_inner_right] c0]) auto
  have cin: "continuous_on UNIV
      (\<lambda>p :: (real^'n) \<times> (real^'n^'n).
        (fst p - x) \<bullet> (M *v (fst p - x)))"
    by (rule bounded_bilinear.continuous_on[OF bounded_bilinear_inner c0 c1])
  have contf: "continuous_on UNIV
      (\<lambda>p :: (real^'n) \<times> (real^'n^'n).
        q \<bullet> (fst p - x) + (1/2) * ((fst p - x) \<bullet> (M *v (fst p - x))))"
    by (intro continuous_on_add continuous_on_mult
        continuous_on_const cq cin)
  have oU: "open {p :: (real^'n) \<times> (real^'n^'n).
      q \<bullet> (fst p - x) + (1/2) * ((fst p - x) \<bullet> (M *v (fst p - x))) < thr}"
    by (rule open_Collect_less[OF contf continuous_on_const])
  have o2: "openin (mtopology_of ?pm)
      {\<omega> \<in> mspace ?pm. \<omega> t \<in> {p. q \<bullet> (fst p - x)
        + (1/2) * ((fst p - x) \<bullet> (M *v (fst p - x))) < thr}}"
    by (rule open_eval_preimage[OF _ oU]) (use t0 tT in simp)
  have eq: "{\<omega> \<in> mspace ?pm.
      (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> RO)
      \<and> q \<bullet> (fst (\<omega> t) - x)
        + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x))) < thr}
      = {\<omega> \<in> mspace ?pm. \<forall>s\<in>{0..t}. \<omega> s \<in> fst -` RO}
        \<inter> {\<omega> \<in> mspace ?pm. \<omega> t \<in> {p. q \<bullet> (fst p - x)
          + (1/2) * ((fst p - x) \<bullet> (M *v (fst p - x))) < thr}}"
    by auto
  show ?thesis unfolding eq by (rule openin_Int[OF o1 o2])
qed

subsection \<open>The bad event vanishes on a region\<close>

text \<open>The vanishing-probability theorem @{thm [source]
  eulerp_bad_event_null}, over an arbitrary bounded open stay-region:
  the kill and the trace margin hold on the region, which is contained
  in a ball of radius \<open>Rn\<close> around the quadratic's centre, and the same
  Chebyshev-plus-gap dissection gives the \<open>A h + B h\<^sup>2\<close> bound once the
  mesh is fine.\<close>

theorem eulerp_bad_event_null_region:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n" and M :: "real^'n^'n"
    and q x :: "real^'n" and c cm t \<beta> Rn :: real
    and RO :: "(real^'n) set"
  assumes c0: "0 < c" and L1: "1 \<le> L"
    and SFc: "continuous_on UNIV SF"
    and SFs: "\<And>z. SF z ** transpose (SF z) \<in> sconstraint k L"
    and sym: "transpose M = M"
    and ROb: "\<And>z. z \<in> RO \<Longrightarrow> norm (z - x) \<le> Rn"
    and kill: "\<And>z. z \<in> RO \<Longrightarrow>
        transpose (SF z) *v (q + M *v (z - x)) = 0"
    and marg: "\<And>z. z \<in> RO \<Longrightarrow>
        cm \<le> trace (M ** (SF z ** transpose (SF z)))"
    and t0: "0 < t" and tc: "t \<le> c" and b0: "0 < \<beta>"
  shows "(\<lambda>i. measure (eulerp SF x (c / real (Suc i)) i)
      {\<omega> \<in> mspace (path_metric c :: ('n pairpath) metric).
        (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> RO)
        \<and> q \<bullet> (fst (\<omega> t) - x)
          + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x)))
          < t * cm / 2 - \<beta>}) \<longlonglongrightarrow> 0"
proof -
  let ?U = "{\<omega> \<in> mspace (path_metric c :: ('n pairpath) metric).
      (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> RO)
      \<and> q \<bullet> (fst (\<omega> t) - x)
        + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x)))
        < t * cm / 2 - \<beta>}"
  let ?h = "\<lambda>i. c / real (Suc i)"
  let ?CM = "\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>"
  define C\<psi> where "C\<psi> = norm q + 2 * ?CM * Rn + 1"
  define \<delta> where "\<delta> = \<beta> / (4 * C\<psi>)"
  define h\<^sub>0 where "h\<^sub>0 = \<beta> / (2 * (\<bar>cm\<bar> + 1))"
  define A where "A = 4 * c * xiC M L / \<beta>\<^sup>2"
  define B where "B = real (CARD('n)) ^ 5 * 8 * L\<^sup>2 / \<delta>^4"
  have CM0: "0 \<le> ?CM" by (auto intro!: sum_nonneg)
  have Rn0: "0 \<le> Rn \<or> RO = {}"
  proof (cases "RO = {}")
    case False
    then obtain z where "z \<in> RO" by blast
    then have "0 \<le> Rn" using ROb norm_ge_zero order_trans by metis
    then show ?thesis by simp
  qed simp
  have C\<psi>1: "1 \<le> C\<psi> \<or> RO = {}"
  proof (cases "RO = {}")
    case False
    then have "0 \<le> Rn" using Rn0 by simp
    then have "0 \<le> 2 * ?CM * Rn"
      using CM0 by (auto intro!: mult_nonneg_nonneg)
    then have "1 \<le> C\<psi>"
      unfolding C\<psi>_def using norm_ge_zero[of q] by linarith
    then show ?thesis by simp
  qed simp
  show ?thesis
  proof (cases "RO = {}")
    case True
    have Ue: "?U = {}" unfolding True using t0 by auto
    show ?thesis unfolding Ue by simp
  next
    case ne: False
    have C\<psi>1': "1 \<le> C\<psi>" using C\<psi>1 ne by simp
    have C\<psi>0: "0 < C\<psi>" using C\<psi>1' by linarith
    have \<delta>0: "0 < \<delta>" unfolding \<delta>_def using b0 C\<psi>0 by simp
    have h\<^sub>00: "0 < h\<^sub>0" unfolding h\<^sub>0_def using b0 by simp
    have L0: "0 \<le> L" using L1 by linarith
    have bound: "measure (eulerp SF x (?h i) i) ?U
        \<le> A * ?h i + B * (?h i)\<^sup>2"
      if hs: "?h i \<le> h\<^sub>0" for i
    proof -
      define h where "h = ?h i"
      have hs': "h \<le> h\<^sub>0" using hs unfolding h_def .
      have h0: "0 < h" unfolding h_def using c0 by simp
      have hc: "real (Suc i) * h = c" unfolding h_def by simp
      let ?Q = "eulerp SF x h i"
      have Qc: "?Q \<in> exit_class k L c x"
        unfolding h_def by (rule eulerp_seq_in_class[OF c0 L1 SFc SFs])
      have setsQ: "sets ?Q = sets (borel_of (mtopology_of
          (path_metric c :: ('n pairpath) metric)))"
        by (rule exit_class_sets[OF Qc])
      have spQ: "space ?Q = mspace (path_metric c :: ('n pairpath) metric)"
        by (rule space_of_path_sets[OF setsQ])
      interpret PQ: prob_space ?Q by (rule exit_class_prob[OF Qc])
      define m where "m = nat \<lfloor>t / h\<rfloor>"
      have tdh0: "0 \<le> t / h" using t0 h0 by simp
      have fl0: "0 \<le> \<lfloor>t / h\<rfloor>" using tdh0 by simp
      have mreal: "real m = real_of_int \<lfloor>t / h\<rfloor>"
        unfolding m_def using fl0 by simp
      have mh_le: "real m * h \<le> t"
      proof -
        have "real_of_int \<lfloor>t / h\<rfloor> \<le> t / h" by (rule of_int_floor_le)
        then have "real m \<le> t / h" using mreal by simp
        then show ?thesis
          using h0 by (simp add: pos_le_divide_eq mult_ac)
      qed
      have mh0: "0 \<le> real m * h" using h0 by simp
      have t_mh: "t - real m * h \<le> h"
      proof -
        have "t / h < real_of_int \<lfloor>t / h\<rfloor> + 1"
          using floor_correct[of "t / h"] by linarith
        then have "t / h < real m + 1" using mreal by simp
        then have "t < (real m + 1) * h"
          using h0 by (simp add: pos_divide_less_eq)
        then show ?thesis by (simp add: algebra_simps)
      qed
      have mSuc: "m \<le> Suc i"
      proof -
        have "t / h \<le> real (Suc i)"
          using tc hc h0 by (simp add: pos_divide_le_eq mult_ac)
        then have "\<lfloor>t / h\<rfloor> \<le> int (Suc i)"
          by (simp add: floor_le_iff)
        then show ?thesis unfolding m_def by simp
      qed
      define E1 where "E1 = {\<omega> \<in> space ?Q. \<beta> / 2 \<le> \<bar>euXi SF M h m \<omega>\<bar>}"
      define E2 where "E2 = {\<omega> \<in> space ?Q.
          \<delta> \<le> norm (fst (\<omega> t) - fst (\<omega> (real m * h)))}"
      have b20: "0 < \<beta> / 2" using b0 by simp
      have mE1: "measure ?Q E1 \<le> real m * xiC M L * h\<^sup>2 / (\<beta> / 2)\<^sup>2"
        unfolding E1_def
        by (rule eulerp_Xi_chebyshev[OF h0 L1 SFc SFs mSuc b20])
      have mE2: "measure ?Q E2
          \<le> real (CARD('n)) ^ 5 * (8 * L\<^sup>2 * (t - real m * h)\<^sup>2) / \<delta>^4"
        unfolding E2_def
        by (rule exit_class_increment_tail_norm[OF c0 L0 Qc
            mh0 mh_le tc \<delta>0])
      have sE1: "E1 \<in> sets ?Q"
      proof -
        have xm: "euXi SF M h m \<in> borel_measurable ?Q"
          using euXi_measurable[OF SFc]
            measurable_cong_sets[OF setsQ refl] by blast
        have am: "(\<lambda>\<omega>. \<bar>euXi SF M h m \<omega>\<bar>) \<in> borel_measurable ?Q"
          by (intro borel_measurable_abs xm)
        have "E1 = (\<lambda>\<omega>. \<bar>euXi SF M h m \<omega>\<bar>) -` {\<beta>/2..} \<inter> space ?Q"
          unfolding E1_def by auto
        then show ?thesis
          using measurable_sets[OF am borel_closed[OF closed_atLeast]]
          by simp
      qed
      have sE2: "E2 \<in> sets ?Q"
      proof -
        have e1: "(\<lambda>\<omega> :: 'n pairpath. \<omega> t) \<in> borel_measurable ?Q"
          using pair_law_eval_measurable[OF setsQ] by blast
        have e2: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (real m * h))
            \<in> borel_measurable ?Q"
          using pair_law_eval_measurable[OF setsQ] by blast
        have fm: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
            \<in> borel_measurable borel"
          by (rule borel_measurable_continuous_onI[OF
              continuous_on_fst[OF continuous_on_id]])
        have dd: "(\<lambda>\<omega>. fst (\<omega> t) - fst (\<omega> (real m * h)))
            \<in> borel_measurable ?Q"
          by (intro borel_measurable_diff
              measurable_compose[OF e1 fm] measurable_compose[OF e2 fm])
        have nm: "(\<lambda>\<omega>. norm (fst (\<omega> t) - fst (\<omega> (real m * h))))
            \<in> borel_measurable ?Q"
          by (rule measurable_compose[OF dd borel_measurable_norm])
        have "E2 = (\<lambda>\<omega>. norm (fst (\<omega> t) - fst (\<omega> (real m * h)))) -` {\<delta>..}
            \<inter> space ?Q"
          unfolding E2_def by auto
        then show ?thesis
          using measurable_sets[OF nm borel_closed[OF closed_atLeast]]
          by simp
      qed
      have QL: "AE \<omega> in ?Q. \<forall>m'\<le>Suc i.
          (\<forall>j<m'. fst (\<omega> (real j * h)) \<in> RO) \<longrightarrow>
          (1/2) * euXi SF M h m' \<omega> + real m' * h * cm / 2
            \<le> q \<bullet> (fst (\<omega> (real m' * h)) - x)
              + (1/2) * ((fst (\<omega> (real m' * h)) - x)
                  \<bullet> (M *v (fst (\<omega> (real m' * h)) - x)))"
        by (rule eulerp_quad_lower_region[OF h0 L1 SFc SFs sym kill marg])
      have incl: "AE \<omega> in ?Q. \<omega> \<in> ?U \<longrightarrow> \<omega> \<in> E1 \<union> E2"
        using QL
      proof (eventually_elim)
        case (elim \<omega>)
        show ?case
        proof (intro impI)
          assume U: "\<omega> \<in> ?U"
          show "\<omega> \<in> E1 \<union> E2"
          proof (cases "\<omega> \<in> E1")
            case True then show ?thesis by simp
          next
            case False
            have wsp: "\<omega> \<in> space ?Q" using U spQ by auto
            have inb: "\<And>s. s \<in> {0..t} \<Longrightarrow> fst (\<omega> s) \<in> RO"
              using U by auto
            have bad: "q \<bullet> (fst (\<omega> t) - x)
                + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x)))
                < t * cm / 2 - \<beta>"
              using U by auto
            have small: "\<bar>euXi SF M h m \<omega>\<bar> < \<beta> / 2"
              using False wsp unfolding E1_def by (auto simp: not_le)
            have grid: "\<And>j. j < m \<Longrightarrow> fst (\<omega> (real j * h)) \<in> RO"
            proof -
              fix j assume jm: "j < m"
              have "real j * h < real m * h"
                using jm h0 by (intro mult_strict_right_mono) simp_all
              then have jh2: "real j * h \<le> t" using mh_le by linarith
              have jh1: "0 \<le> real j * h" using h0 by simp
              have "real j * h \<in> {0..t}" using jh1 jh2 by simp
              then show "fst (\<omega> (real j * h)) \<in> RO" by (rule inb)
            qed
            have QLm: "(1/2) * euXi SF M h m \<omega> + real m * h * cm / 2
                \<le> q \<bullet> (fst (\<omega> (real m * h)) - x)
                  + (1/2) * ((fst (\<omega> (real m * h)) - x)
                      \<bullet> (M *v (fst (\<omega> (real m * h)) - x)))"
              using elim mSuc grid by blast
            have tin: "t \<in> {0..t}" using t0 by simp
            have min': "real m * h \<in> {0..t}" using mh0 mh_le by simp
            have nT: "norm (fst (\<omega> t) - x) \<le> Rn"
              by (rule ROb[OF inb[OF tin]])
            have nM: "norm (fst (\<omega> (real m * h)) - x) \<le> Rn"
              by (rule ROb[OF inb[OF min']])
            define p1 where "p1 = q \<bullet> (fst (\<omega> (real m * h)) - x)
                + (1/2) * ((fst (\<omega> (real m * h)) - x)
                    \<bullet> (M *v (fst (\<omega> (real m * h)) - x)))"
            define p2 where "p2 = q \<bullet> (fst (\<omega> t) - x)
                + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x)))"
            define nd where "nd = norm (fst (\<omega> t) - fst (\<omega> (real m * h)))"
            have nd0: "0 \<le> nd" unfolding nd_def by simp
            have habs: "\<bar>real m * h - t\<bar> \<le> h"
            proof -
              have "real m * h - t \<le> h" using mh_le h0 by linarith
              moreover have "- h \<le> real m * h - t" using t_mh by linarith
              ultimately show ?thesis by (simp add: abs_le_iff)
            qed
            have g1: "\<bar>(real m * h - t) * cm\<bar> \<le> h * \<bar>cm\<bar>"
            proof -
              have "\<bar>(real m * h - t) * cm\<bar> = \<bar>real m * h - t\<bar> * \<bar>cm\<bar>"
                by (rule abs_mult)
              also have "\<dots> \<le> h * \<bar>cm\<bar>"
                by (rule mult_right_mono[OF habs abs_ge_zero])
              finally show ?thesis .
            qed
            have g2: "h * \<bar>cm\<bar> \<le> \<beta> / 2"
            proof -
              have "h * (2 * (\<bar>cm\<bar> + 1)) \<le> \<beta>"
                using hs' unfolding h\<^sub>0_def
                by (simp add: pos_le_divide_eq)
              moreover have "h * (2 * (\<bar>cm\<bar> + 1))
                  = 2 * (h * (\<bar>cm\<bar> + 1))" by simp
              ultimately have hcm1: "h * (\<bar>cm\<bar> + 1) \<le> \<beta> / 2" by linarith
              have "h * \<bar>cm\<bar> \<le> h * (\<bar>cm\<bar> + 1)"
                using h0 by (intro mult_left_mono) simp_all
              then show ?thesis using hcm1 by linarith
            qed
            have cmb: "- (\<beta> / 4) \<le> (real m * h - t) * cm / 2"
            proof -
              have "- (h * \<bar>cm\<bar>) \<le> (real m * h - t) * cm"
                using g1 by linarith
              then show ?thesis using g2 by linarith
            qed
            have p1low: "- (\<beta> / 4) + real m * h * cm / 2 \<le> p1"
              using QLm small unfolding p1_def by linarith
            have badp: "p2 < t * cm / 2 - \<beta>"
              unfolding p2_def by (rule bad)
            have distrib: "(real m * h - t) * cm
                = real m * h * cm - t * cm"
              by (simp add: algebra_simps)
            have gap: "\<beta> / 2 < p1 - p2"
              using p1low badp cmb distrib by linarith
            have db: "\<bar>p1 - p2\<bar> \<le> (norm q + 2 * ?CM * Rn) * nd"
              unfolding p1_def p2_def nd_def
              using quad_diff_bound_gen[OF sym nT nM]
              by (simp add: norm_minus_commute)
            have Cle: "norm q + 2 * ?CM * Rn \<le> C\<psi>"
              unfolding C\<psi>_def by simp
            have bCn: "\<beta> / 2 < C\<psi> * nd"
            proof -
              have "\<beta> / 2 < (norm q + 2 * ?CM * Rn) * nd"
                using gap db by linarith
              also have "\<dots> \<le> C\<psi> * nd"
                by (rule mult_right_mono[OF Cle nd0])
              finally show ?thesis .
            qed
            have b2Cn: "\<beta> < nd * (2 * C\<psi>)"
            proof -
              have "\<beta> < 2 * (C\<psi> * nd)" using bCn by linarith
              then show ?thesis by (simp add: mult_ac)
            qed
            have lt: "\<beta> / (2 * C\<psi>) < nd"
              using b2Cn C\<psi>0 by (simp add: pos_divide_less_eq)
            have dle: "\<delta> \<le> \<beta> / (2 * C\<psi>)"
              unfolding \<delta>_def
            proof (rule divide_left_mono)
              show "2 * C\<psi> \<le> 4 * C\<psi>" using C\<psi>0 by linarith
              show "0 \<le> \<beta>" using b0 by linarith
              show "0 < 4 * C\<psi> * (2 * C\<psi>)"
                using C\<psi>0 by (simp add: zero_less_mult_iff)
            qed
            have ndl: "\<delta> \<le> nd" using lt dle by linarith
            show ?thesis
              using wsp ndl unfolding E2_def nd_def by auto
          qed
        qed
      qed
      have s1: "measure ?Q ?U \<le> measure ?Q (E1 \<union> E2)"
        by (rule PQ.finite_measure_mono_AE[OF incl sets.Un[OF sE1 sE2]])
      have s2: "measure ?Q (E1 \<union> E2) \<le> measure ?Q E1 + measure ?Q E2"
        by (rule measure_Un_le[OF sE1 sE2])
      have n1: "real m * xiC M L * h\<^sup>2 / (\<beta> / 2)\<^sup>2 \<le> A * h"
      proof -
        have mhc: "real m * h \<le> c"
        proof -
          have "real m \<le> real (Suc i)" using mSuc by simp
          then have "real m * h \<le> real (Suc i) * h"
            using h0 by (intro mult_right_mono) simp_all
          then show ?thesis using hc by simp
        qed
        have e1: "real m * xiC M L * h\<^sup>2 = real m * h * xiC M L * h"
          by (simp add: power2_eq_square algebra_simps)
        have e2: "real m * h * xiC M L * h \<le> c * xiC M L * h"
          by (intro mult_right_mono mult_right_mono[OF mhc xiC_nonneg])
            (use h0 in simp_all)
        have num: "real m * xiC M L * h\<^sup>2 \<le> c * xiC M L * h"
          unfolding e1 by (rule e2)
        have "real m * xiC M L * h\<^sup>2 / (\<beta> / 2)\<^sup>2
            \<le> c * xiC M L * h / (\<beta> / 2)\<^sup>2"
          by (rule divide_right_mono[OF num]) simp
        also have "\<dots> = A * h"
          unfolding A_def using b0 by (simp add: field_simps)
        finally show ?thesis .
      qed
      have n2: "real (CARD('n)) ^ 5 * (8 * L\<^sup>2 * (t - real m * h)\<^sup>2) / \<delta>^4
          \<le> B * h\<^sup>2"
      proof -
        have sq: "(t - real m * h)\<^sup>2 \<le> h\<^sup>2"
          using t_mh mh_le by (intro power_mono) simp_all
        have inner8: "8 * L\<^sup>2 * (t - real m * h)\<^sup>2 \<le> 8 * L\<^sup>2 * h\<^sup>2"
          by (intro mult_left_mono[OF sq]) simp
        have "real (CARD('n)) ^ 5 * (8 * L\<^sup>2 * (t - real m * h)\<^sup>2)
            \<le> real (CARD('n)) ^ 5 * (8 * L\<^sup>2 * h\<^sup>2)"
          by (intro mult_left_mono[OF inner8]) simp
        then have "real (CARD('n)) ^ 5
            * (8 * L\<^sup>2 * (t - real m * h)\<^sup>2) / \<delta>^4
            \<le> real (CARD('n)) ^ 5 * (8 * L\<^sup>2 * h\<^sup>2) / \<delta>^4"
          by (intro divide_right_mono) simp_all
        also have "\<dots> = B * h\<^sup>2"
          unfolding B_def using \<delta>0 by (simp add: field_simps)
        finally show ?thesis .
      qed
      have "measure ?Q ?U \<le> A * h + B * h\<^sup>2"
        using s1 s2 mE1 mE2 n1 n2 by linarith
      then show ?thesis unfolding h_def .
    qed
    have hlim: "(\<lambda>i. ?h i) \<longlonglongrightarrow> 0"
      using tendsto_mult[OF tendsto_const LIMSEQ_inverse_real_of_nat, of c]
      by (simp add: divide_inverse)
    have ev: "\<forall>\<^sub>F i in sequentially.
        measure (eulerp SF x (?h i) i) ?U \<le> A * ?h i + B * (?h i)\<^sup>2"
    proof -
      have "\<forall>\<^sub>F i in sequentially. ?h i < h\<^sub>0"
        by (rule order_tendstoD(2)[OF hlim h\<^sub>00])
      then show ?thesis
      proof (eventually_elim)
        case (elim i)
        show ?case by (rule bound[OF less_imp_le[OF elim]])
      qed
    qed
    have ev0: "\<forall>\<^sub>F i in sequentially.
        (0 :: real) \<le> measure (eulerp SF x (?h i) i) ?U"
      by (intro always_eventually allI measure_nonneg)
    have glim: "(\<lambda>i. A * ?h i + B * (?h i)\<^sup>2) \<longlonglongrightarrow> 0"
    proof -
      have "(\<lambda>i. A * ?h i + B * (?h i)\<^sup>2) \<longlonglongrightarrow> A * 0 + B * 0\<^sup>2"
        by (intro tendsto_add tendsto_mult tendsto_const
            tendsto_power hlim)
      then show ?thesis by simp
    qed
    show ?thesis
      by (rule tendsto_sandwich[OF ev0 ev tendsto_const glim])
  qed
qed

subsection \<open>One limit member, two quadratics, one region\<close>

text \<open>The region version of the almost-sure growth statement, carrying
  two quadratic packages against one field and one limit member: the
  weak-limit transfer serves every vanishing open event of a single
  member simultaneously, so both growth directions hold together.  For
  the tangential field with \<open>\<plusminus>(2(x-y\<^sub>0), 2\<cdot>1)\<close> this pins
  \<open>|X\<^sub>t - y\<^sub>0|\<^sup>2\<close> to the deterministic line \<open>|x - y\<^sub>0|\<^sup>2 + (n-1) t\<close>
  while the path stays in the region.\<close>

lemma quad_good_rat_to_real_region:
  fixes \<omega> :: "'n::finite pairpath" and q x :: "real^'n"
    and M :: "real^'n^'n" and c cm t :: real and RO :: "(real^'n) set"
  assumes wm: "\<omega> \<in> mspace (path_metric c :: ('n pairpath) metric)"
    and rat: "\<And>r. r \<in> \<rat> \<Longrightarrow> 0 < r \<Longrightarrow> r \<le> c \<Longrightarrow>
      (\<forall>s\<in>{0..r}. fst (\<omega> s) \<in> RO) \<Longrightarrow>
      r * cm / 2 \<le> q \<bullet> (fst (\<omega> r) - x)
        + (1/2) * ((fst (\<omega> r) - x) \<bullet> (M *v (fst (\<omega> r) - x)))"
    and t0: "0 < t" and tc: "t \<le> c"
    and inb: "\<And>s. s \<in> {0..t} \<Longrightarrow> fst (\<omega> s) \<in> RO"
  shows "t * cm / 2 \<le> q \<bullet> (fst (\<omega> t) - x)
      + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x)))"
proof -
  define g where "g = (\<lambda>s. q \<bullet> (fst (\<omega> s) - x)
      + (1/2) * ((fst (\<omega> s) - x) \<bullet> (M *v (fst (\<omega> s) - x))))"
  have gc: "continuous_on {0..c} g"
    unfolding g_def by (rule quad_eval_cont[OF wm])
  have exr: "\<exists>r. r \<in> \<rat>
      \<and> max 0 (t - inverse (real (Suc j))) < r \<and> r < t" for j
  proof -
    have "max 0 (t - inverse (real (Suc j))) < t"
      using t0 by simp
    then show ?thesis
      using Rats_dense_in_real[of
          "max 0 (t - inverse (real (Suc j)))" t] by blast
  qed
  have exr': "\<forall>j. \<exists>r. r \<in> \<rat>
      \<and> max 0 (t - inverse (real (Suc j))) < r \<and> r < t"
    using exr by blast
  obtain rj where rjprop: "\<forall>j. rj j \<in> \<rat>
      \<and> max 0 (t - inverse (real (Suc j))) < rj j \<and> rj j < t"
    using choice[OF exr'] by blast
  have rjQ: "rj j \<in> \<rat>" for j using rjprop by blast
  have rjl: "max 0 (t - inverse (real (Suc j))) < rj j" for j
    using rjprop by blast
  have rju: "rj j < t" for j using rjprop by blast
  have rj0: "0 < rj j" for j
  proof -
    have "(0::real) \<le> max 0 (t - inverse (real (Suc j)))" by simp
    then show ?thesis using rjl[of j] by linarith
  qed
  have rjc: "rj j \<le> c" for j using rju[of j] tc by linarith
  have glow: "rj j * cm / 2 \<le> g (rj j)" for j
    unfolding g_def
  proof (rule rat)
    show "rj j \<in> \<rat>" by (rule rjQ)
    show "0 < rj j" by (rule rj0)
    show "rj j \<le> c" by (rule rjc)
    show "\<forall>s\<in>{0..rj j}. fst (\<omega> s) \<in> RO"
    proof
      fix s assume "s \<in> {0..rj j}"
      then have "s \<in> {0..t}" using rju[of j] by auto
      then show "fst (\<omega> s) \<in> RO" by (rule inb)
    qed
  qed
  have rjlim: "rj \<longlonglongrightarrow> t"
  proof (rule tendsto_sandwich[of
      "\<lambda>j. t - inverse (real (Suc j))" rj sequentially "\<lambda>_. t"])
    show "\<forall>\<^sub>F j in sequentially. t - inverse (real (Suc j)) \<le> rj j"
    proof (intro always_eventually allI)
      fix j
      have "t - inverse (real (Suc j))
          \<le> max 0 (t - inverse (real (Suc j)))"
        by (rule max.cobounded2)
      then show "t - inverse (real (Suc j)) \<le> rj j"
        using rjl[of j] by linarith
    qed
    show "\<forall>\<^sub>F j in sequentially. rj j \<le> t"
      by (intro always_eventually allI less_imp_le rju)
    show "(\<lambda>j. t - inverse (real (Suc j))) \<longlonglongrightarrow> t"
      using tendsto_diff[OF tendsto_const
          LIMSEQ_inverse_real_of_nat, of t] by simp
    show "(\<lambda>_. t) \<longlonglongrightarrow> t" by (rule tendsto_const)
  qed
  have gcomp: "(\<lambda>j. g (rj j)) \<longlonglongrightarrow> g t"
  proof -
    have inS: "\<forall>n. rj n \<in> {0..c}"
      using rj0 rjc by (auto intro: less_imp_le)
    have tS: "t \<in> {0..c}" using t0 tc by auto
    have "(g \<circ> rj) \<longlonglongrightarrow> g t"
      using continuous_on_sequentially[THEN iffD1, OF gc] inS tS rjlim
      by blast
    then show ?thesis by (simp add: o_def)
  qed
  have lim1: "(\<lambda>j. rj j * cm / 2) \<longlonglongrightarrow> t * cm / 2"
    by (rule tendsto_divide[OF
        tendsto_mult[OF rjlim tendsto_const] tendsto_const]) simp
  have "t * cm / 2 \<le> g t"
    by (rule LIMSEQ_le[OF lim1 gcomp]) (use glow in blast)
  then show ?thesis unfolding g_def .
qed

theorem eulerp_limit_good2_region:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n" and M1 M2 :: "real^'n^'n"
    and q1 q2 x :: "real^'n" and c cm1 cm2 Rn :: real
    and RO :: "(real^'n) set"
  assumes c0: "0 < c" and L1: "1 \<le> L"
    and SFc: "continuous_on UNIV SF"
    and SFs: "\<And>z. SF z ** transpose (SF z) \<in> sconstraint k L"
    and sym1: "transpose M1 = M1" and sym2: "transpose M2 = M2"
    and ROo: "open RO"
    and ROb: "\<And>z. z \<in> RO \<Longrightarrow> norm (z - x) \<le> Rn"
    and kill1: "\<And>z. z \<in> RO \<Longrightarrow>
        transpose (SF z) *v (q1 + M1 *v (z - x)) = 0"
    and marg1: "\<And>z. z \<in> RO \<Longrightarrow>
        cm1 \<le> trace (M1 ** (SF z ** transpose (SF z)))"
    and kill2: "\<And>z. z \<in> RO \<Longrightarrow>
        transpose (SF z) *v (q2 + M2 *v (z - x)) = 0"
    and marg2: "\<And>z. z \<in> RO \<Longrightarrow>
        cm2 \<le> trace (M2 ** (SF z ** transpose (SF z)))"
  shows "\<exists>P \<in> exit_class k L c x. AE \<omega> in P. \<forall>t.
      0 < t \<longrightarrow> t \<le> c \<longrightarrow> (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> RO) \<longrightarrow>
      (t * cm1 / 2 \<le> q1 \<bullet> (fst (\<omega> t) - x)
        + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M1 *v (fst (\<omega> t) - x))))
      \<and> (t * cm2 / 2 \<le> q2 \<bullet> (fst (\<omega> t) - x)
        + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M2 *v (fst (\<omega> t) - x))))"
proof -
  let ?pm = "path_metric c :: ('n pairpath) metric"
  define U1 where "U1 = (\<lambda>r \<beta> :: real. {\<omega> \<in> mspace ?pm.
      (\<forall>s\<in>{0..r}. fst (\<omega> s) \<in> RO)
      \<and> q1 \<bullet> (fst (\<omega> r) - x)
        + (1/2) * ((fst (\<omega> r) - x) \<bullet> (M1 *v (fst (\<omega> r) - x)))
        < r * cm1 / 2 - \<beta>})"
  define U2 where "U2 = (\<lambda>r \<beta> :: real. {\<omega> \<in> mspace ?pm.
      (\<forall>s\<in>{0..r}. fst (\<omega> s) \<in> RO)
      \<and> q2 \<bullet> (fst (\<omega> r) - x)
        + (1/2) * ((fst (\<omega> r) - x) \<bullet> (M2 *v (fst (\<omega> r) - x)))
        < r * cm2 / 2 - \<beta>})"
  obtain P where P: "P \<in> exit_class k L c x"
    and Praw: "\<forall>U b'. openin (mtopology_of ?pm) U \<longrightarrow>
      (\<lambda>i. measure (eulerp SF x (c / real (Suc i)) i) U) \<longlonglongrightarrow> b' \<longrightarrow>
      measure P U \<le> b'"
    using eulerp_weak_limit[OF c0 L1 SFc SFs] by blast
  interpret FP: prob_space P by (rule exit_class_prob[OF P])
  have setsP: "sets P = sets (borel_of (mtopology_of ?pm))"
    by (rule exit_class_sets[OF P])
  have spaceP: "space P = mspace ?pm"
    by (rule space_of_path_sets[OF setsP])
  have AErn1: "AE \<omega> in P. \<omega> \<notin> U1 r (inverse (real (Suc n)))"
    if r0: "0 < r" and rc: "r \<le> c" for r and n :: nat
  proof -
    have inv0: "(0::real) < inverse (real (Suc n))" by simp
    have opn: "openin (mtopology_of ?pm) (U1 r (inverse (real (Suc n))))"
      unfolding U1_def
      by (rule open_quad_bad_event_region[OF less_imp_le[OF r0] rc ROo])
    have tnd: "(\<lambda>i. measure (eulerp SF x (c / real (Suc i)) i)
        (U1 r (inverse (real (Suc n))))) \<longlonglongrightarrow> 0"
      unfolding U1_def
      by (rule eulerp_bad_event_null_region[OF c0 L1 SFc SFs sym1
          ROb kill1 marg1 r0 rc inv0])
    have le0: "measure P (U1 r (inverse (real (Suc n)))) \<le> 0"
      using Praw opn tnd by blast
    have m0: "measure P (U1 r (inverse (real (Suc n)))) = 0"
      using le0 measure_nonneg[of P "U1 r (inverse (real (Suc n)))"]
      by linarith
    have Uset: "U1 r (inverse (real (Suc n))) \<in> sets P"
      using borel_of_open[OF opn] by (simp add: setsP)
    have "U1 r (inverse (real (Suc n))) \<in> null_sets P"
    proof (rule null_setsI)
      show "emeasure P (U1 r (inverse (real (Suc n)))) = 0"
        using m0 by (simp add: FP.emeasure_eq_measure)
      show "U1 r (inverse (real (Suc n))) \<in> sets P" by (rule Uset)
    qed
    then show ?thesis by (rule AE_not_in)
  qed
  have AErn2: "AE \<omega> in P. \<omega> \<notin> U2 r (inverse (real (Suc n)))"
    if r0: "0 < r" and rc: "r \<le> c" for r and n :: nat
  proof -
    have inv0: "(0::real) < inverse (real (Suc n))" by simp
    have opn: "openin (mtopology_of ?pm) (U2 r (inverse (real (Suc n))))"
      unfolding U2_def
      by (rule open_quad_bad_event_region[OF less_imp_le[OF r0] rc ROo])
    have tnd: "(\<lambda>i. measure (eulerp SF x (c / real (Suc i)) i)
        (U2 r (inverse (real (Suc n))))) \<longlonglongrightarrow> 0"
      unfolding U2_def
      by (rule eulerp_bad_event_null_region[OF c0 L1 SFc SFs sym2
          ROb kill2 marg2 r0 rc inv0])
    have le0: "measure P (U2 r (inverse (real (Suc n)))) \<le> 0"
      using Praw opn tnd by blast
    have m0: "measure P (U2 r (inverse (real (Suc n)))) = 0"
      using le0 measure_nonneg[of P "U2 r (inverse (real (Suc n)))"]
      by linarith
    have Uset: "U2 r (inverse (real (Suc n))) \<in> sets P"
      using borel_of_open[OF opn] by (simp add: setsP)
    have "U2 r (inverse (real (Suc n))) \<in> null_sets P"
    proof (rule null_setsI)
      show "emeasure P (U2 r (inverse (real (Suc n)))) = 0"
        using m0 by (simp add: FP.emeasure_eq_measure)
      show "U2 r (inverse (real (Suc n))) \<in> sets P" by (rule Uset)
    qed
    then show ?thesis by (rule AE_not_in)
  qed
  define I where "I = {r. r \<in> \<rat> \<and> 0 < r \<and> r \<le> c}"
  have cI: "countable I"
    unfolding I_def by (rule countable_subset[OF _ countable_rat]) auto
  have AEall1: "AE \<omega> in P. \<forall>r\<in>I. \<forall>n::nat.
      \<omega> \<notin> U1 r (inverse (real (Suc n)))"
    unfolding AE_ball_countable[OF cI]
  proof
    fix r assume "r \<in> I"
    then have r0: "0 < r" and rc: "r \<le> c" unfolding I_def by auto
    show "AE \<omega> in P. \<forall>n::nat. \<omega> \<notin> U1 r (inverse (real (Suc n)))"
      unfolding AE_all_countable by (intro allI AErn1[OF r0 rc])
  qed
  have AEall2: "AE \<omega> in P. \<forall>r\<in>I. \<forall>n::nat.
      \<omega> \<notin> U2 r (inverse (real (Suc n)))"
    unfolding AE_ball_countable[OF cI]
  proof
    fix r assume "r \<in> I"
    then have r0: "0 < r" and rc: "r \<le> c" unfolding I_def by auto
    show "AE \<omega> in P. \<forall>n::nat. \<omega> \<notin> U2 r (inverse (real (Suc n)))"
      unfolding AE_all_countable by (intro allI AErn2[OF r0 rc])
  qed
  have sp: "AE \<omega> in P. \<omega> \<in> space P" by (rule AE_space)
  show ?thesis
  proof (intro bexI[OF _ P])
    show "AE \<omega> in P. \<forall>t.
        0 < t \<longrightarrow> t \<le> c \<longrightarrow> (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> RO) \<longrightarrow>
        (t * cm1 / 2 \<le> q1 \<bullet> (fst (\<omega> t) - x)
          + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M1 *v (fst (\<omega> t) - x))))
        \<and> (t * cm2 / 2 \<le> q2 \<bullet> (fst (\<omega> t) - x)
          + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M2 *v (fst (\<omega> t) - x))))"
      using AEall1 AEall2 sp
    proof (eventually_elim)
      case (elim \<omega>)
      have wm: "\<omega> \<in> mspace ?pm" using elim(3) by (simp add: spaceP)
      have notin1: "\<And>r n. r \<in> I \<Longrightarrow>
          \<omega> \<notin> U1 r (inverse (real (Suc n)))"
        using elim(1) by blast
      have notin2: "\<And>r n. r \<in> I \<Longrightarrow>
          \<omega> \<notin> U2 r (inverse (real (Suc n)))"
        using elim(2) by blast
      show ?case
      proof (intro allI impI conjI)
        fix t assume t0: "0 < t" and tc: "t \<le> c"
          and inb: "\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> RO"
        have rat1: "r * cm1 / 2 \<le> q1 \<bullet> (fst (\<omega> r) - x)
            + (1/2) * ((fst (\<omega> r) - x) \<bullet> (M1 *v (fst (\<omega> r) - x)))"
          if rQ: "r \<in> \<rat>" and r0: "0 < r" and rc: "r \<le> c"
            and rball: "\<forall>s\<in>{0..r}. fst (\<omega> s) \<in> RO" for r
        proof (rule ccontr)
          assume nle: "\<not> r * cm1 / 2 \<le> q1 \<bullet> (fst (\<omega> r) - x)
              + (1/2) * ((fst (\<omega> r) - x) \<bullet> (M1 *v (fst (\<omega> r) - x)))"
          have pos: "0 < r * cm1 / 2 - (q1 \<bullet> (fst (\<omega> r) - x)
              + (1/2) * ((fst (\<omega> r) - x) \<bullet> (M1 *v (fst (\<omega> r) - x))))"
            using nle by simp
          obtain n where nsm: "inverse (real (Suc n))
              < r * cm1 / 2 - (q1 \<bullet> (fst (\<omega> r) - x)
                + (1/2) * ((fst (\<omega> r) - x) \<bullet> (M1 *v (fst (\<omega> r) - x))))"
            using reals_Archimedean[OF pos] by auto
          have drop: "q1 \<bullet> (fst (\<omega> r) - x)
              + (1/2) * ((fst (\<omega> r) - x) \<bullet> (M1 *v (fst (\<omega> r) - x)))
              < r * cm1 / 2 - inverse (real (Suc n))"
            using nsm by linarith
          have "\<omega> \<in> U1 r (inverse (real (Suc n)))"
            unfolding U1_def using wm rball drop by auto
          moreover have "r \<in> I" unfolding I_def using rQ r0 rc by simp
          ultimately show False using notin1 by blast
        qed
        have rat2: "r * cm2 / 2 \<le> q2 \<bullet> (fst (\<omega> r) - x)
            + (1/2) * ((fst (\<omega> r) - x) \<bullet> (M2 *v (fst (\<omega> r) - x)))"
          if rQ: "r \<in> \<rat>" and r0: "0 < r" and rc: "r \<le> c"
            and rball: "\<forall>s\<in>{0..r}. fst (\<omega> s) \<in> RO" for r
        proof (rule ccontr)
          assume nle: "\<not> r * cm2 / 2 \<le> q2 \<bullet> (fst (\<omega> r) - x)
              + (1/2) * ((fst (\<omega> r) - x) \<bullet> (M2 *v (fst (\<omega> r) - x)))"
          have pos: "0 < r * cm2 / 2 - (q2 \<bullet> (fst (\<omega> r) - x)
              + (1/2) * ((fst (\<omega> r) - x) \<bullet> (M2 *v (fst (\<omega> r) - x))))"
            using nle by simp
          obtain n where nsm: "inverse (real (Suc n))
              < r * cm2 / 2 - (q2 \<bullet> (fst (\<omega> r) - x)
                + (1/2) * ((fst (\<omega> r) - x) \<bullet> (M2 *v (fst (\<omega> r) - x))))"
            using reals_Archimedean[OF pos] by auto
          have drop: "q2 \<bullet> (fst (\<omega> r) - x)
              + (1/2) * ((fst (\<omega> r) - x) \<bullet> (M2 *v (fst (\<omega> r) - x)))
              < r * cm2 / 2 - inverse (real (Suc n))"
            using nsm by linarith
          have "\<omega> \<in> U2 r (inverse (real (Suc n)))"
            unfolding U2_def using wm rball drop by auto
          moreover have "r \<in> I" unfolding I_def using rQ r0 rc by simp
          ultimately show False using notin2 by blast
        qed
        show "t * cm1 / 2 \<le> q1 \<bullet> (fst (\<omega> t) - x)
            + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M1 *v (fst (\<omega> t) - x)))"
        proof (rule quad_good_rat_to_real_region[OF wm rat1 t0 tc])
          fix s assume "s \<in> {0..t}"
          then show "fst (\<omega> s) \<in> RO" using inb by blast
        qed
        show "t * cm2 / 2 \<le> q2 \<bullet> (fst (\<omega> t) - x)
            + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M2 *v (fst (\<omega> t) - x)))"
        proof (rule quad_good_rat_to_real_region[OF wm rat2 t0 tc])
          fix s assume "s \<in> {0..t}"
          then show "fst (\<omega> s) \<in> RO" using inb by blast
        qed
      qed
    qed
  qed
qed

subsection \<open>The tangential member: exact radial growth\<close>

text \<open>The unclamped tangential field is admissible everywhere: even
  where the guarded radial is short, its square keeps a full
  \<open>(n-1)\<close>-dimensional unit eigenspace, and on the region where the guard
  is inactive it kills the radial exactly.  Feeding the two-quadratic
  limit theorem with \<open>\<plusminus>(2(x-y\<^sub>0), 2\<cdot>1)\<close> pins the squared distance to
  \<open>y\<^sub>0\<close> to the deterministic line \<open>|x-y\<^sub>0|\<^sup>2 + (CARD('n)-1) t\<close> while the
  path stays in the region, so exit times of concentric balls are
  deterministic, as used in Example 3.1's lower bound.\<close>

lemma tanp_sq_sconstraint:
  fixes u :: "real^'n::finite"
  assumes u1: "norm u \<le> 1" and k1: "1 \<le> k" and L1: "1 \<le> L"
  shows "tanp u ** transpose (tanp u) \<in> sconstraint k L"
proof -
  have tr: "transpose (tanp u) = tanp u" by (rule tanp_sym)
  define A where "A = tanp u ** tanp u"
  have symA: "transpose A = A"
    unfolding A_def by (simp add: matrix_transpose_mul tanp_sym)
  have qf: "v \<bullet> (A *v v) = (tanp u *v v) \<bullet> (tanp u *v v)" for v
  proof -
    have assoc: "A *v v = tanp u *v (tanp u *v v)"
      unfolding A_def by (metis matrix_vector_mul_assoc)
    have "v \<bullet> (tanp u *v (tanp u *v v))
        = (transpose (tanp u) *v v) \<bullet> (tanp u *v v)"
      by (rule inner_transpose_matrix)
    then show ?thesis unfolding assoc tr .
  qed
  have contract: "(tanp u *v v) \<bullet> (tanp u *v v) \<le> v \<bullet> v" for v
  proof -
    have e: "(tanp u *v v) \<bullet> (tanp u *v v)
        = v \<bullet> v - (2 - u \<bullet> u) * (u \<bullet> v)\<^sup>2"
      unfolding tanp_mv
      by (simp add: inner_commute
          power2_eq_square
          algebra_simps)
    have uu1: "u \<bullet> u \<le> 1"
    proof -
      have "u \<bullet> u = (norm u)\<^sup>2" by (simp add: dot_square_norm)
      also have "\<dots> \<le> 1"
        using u1 norm_ge_zero[of u] by (simp add: power_le_one)
      finally show ?thesis .
    qed
    have "0 \<le> (2 - u \<bullet> u) * (u \<bullet> v)\<^sup>2"
      using uu1 by (intro mult_nonneg_nonneg) simp_all
    then show ?thesis unfolding e by linarith
  qed
  have psdA: "psd A"
    unfolding psd_def
  proof (intro conjI allI)
    show "transpose A = A" by (rule symA)
    show "0 \<le> v \<bullet> (A *v v)" for v
      unfolding qf by (rule inner_ge_zero)
  qed
  have ubA: "eigen_ub A L"
    unfolding eigen_ub_def
  proof
    fix v :: "real^'n"
    have "v \<bullet> (A *v v) \<le> v \<bullet> v" unfolding qf by (rule contract)
    also have "\<dots> = 1 * (v \<bullet> v)" by simp
    also have "\<dots> \<le> L * (v \<bullet> v)"
      by (rule mult_right_mono[OF L1 inner_ge_zero])
    finally show "v \<bullet> (A *v v) \<le> L * (v \<bullet> v)" .
  qed
  have lbA: "eigen_lb A (CARD('n) - k)"
    unfolding eigen_lb_def
  proof (intro exI[of _ "{v :: real^'n. u \<bullet> v = 0}"] conjI ballI)
    show "subspace {v :: real^'n. u \<bullet> v = 0}"
      by (rule subspace_hyperplane)
    show "CARD('n) - k \<le> dim {v :: real^'n. u \<bullet> v = 0}"
    proof (cases "u = 0")
      case True
      then have "{v :: real^'n. u \<bullet> v = 0} = UNIV" by simp
      then show ?thesis by simp
    next
      case False
      then have "dim {v :: real^'n. u \<bullet> v = 0} = CARD('n) - 1"
        by (simp add: dim_hyperplane)
      then show ?thesis using k1 by simp
    qed
  next
    fix v :: "real^'n" assume "v \<in> {v. u \<bullet> v = 0}"
    then have uv: "u \<bullet> v = 0" by simp
    have "tanp u *v v = v" unfolding tanp_mv uv by simp
    then show "v \<bullet> v \<le> v \<bullet> (A *v v)" unfolding qf by simp
  qed
  have "A \<in> feasible k L 0"
    unfolding feasible_def
    using psdA ubA lbA by simp
  then have "A \<in> sconstraint k L"
    using feasible_subset_sconstraint by blast
  then show ?thesis unfolding A_def tr .
qed

lemma tanRF_cont:
  fixes y\<^sub>0 :: "real^'n::finite"
  assumes rho0: "0 < \<rho>"
  shows "continuous_on UNIV (\<lambda>z. tanp (uvec y\<^sub>0 \<rho> z))"
proof -
  have uc: "continuous_on UNIV (uvec y\<^sub>0 \<rho>)"
    by (rule uvec_cont[OF rho0])
  have ci: "continuous_on UNIV (\<lambda>z. uvec y\<^sub>0 \<rho> z $ i)" for i
    by (rule continuous_on_compose2[OF
        linear_continuous_on[OF bounded_linear_vec_nth] uc]) auto
  have eq: "(\<lambda>z. tanp (uvec y\<^sub>0 \<rho> z)) = (\<lambda>z. \<chi> i j.
      (if i = j then 1 else 0)
      - uvec y\<^sub>0 \<rho> z $ i * uvec y\<^sub>0 \<rho> z $ j)"
    by (rule ext) (simp add: tanp_def outerp_def mat_def vec_eq_iff)
  show ?thesis unfolding eq
    by (intro continuous_on_vec_lambda continuous_intros ci)
qed

theorem tangential_exact_growth:
  fixes y\<^sub>0 x :: "real^'n::finite" and \<rho> rB T :: real
  assumes T0: "0 < T" and L1: "1 \<le> L" and k1: "1 \<le> k"
    and kn: "k < CARD('n)"
    and rho0: "0 < \<rho>"
  shows "\<exists>P \<in> exit_class k L T x. AE \<omega> in P. \<forall>t.
      0 < t \<longrightarrow> t \<le> T \<longrightarrow>
      (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> {w. \<rho> < norm (w - y\<^sub>0)} \<inter> ball y\<^sub>0 rB) \<longrightarrow>
      (norm (fst (\<omega> t) - y\<^sub>0))\<^sup>2
        = (norm (x - y\<^sub>0))\<^sup>2 + t * (real CARD('n) - 1)"
proof -
  define RO where "RO = {w :: real^'n. \<rho> < norm (w - y\<^sub>0)} \<inter> ball y\<^sub>0 rB"
  define SF where "SF = (\<lambda>z. tanp (uvec y\<^sub>0 \<rho> z))"
  define Rn where "Rn = rB + norm (y\<^sub>0 - x)"
  have SFc: "continuous_on UNIV SF"
    unfolding SF_def by (rule tanRF_cont[OF rho0])
  have SFs: "\<And>z. SF z ** transpose (SF z) \<in> sconstraint k L"
    unfolding SF_def
    by (rule tanp_sq_sconstraint[OF uvec_norm_le[OF rho0] k1 L1])
  have ROo: "open RO"
  proof -
    have "open {w :: real^'n. \<rho> < norm (w - y\<^sub>0)}"
      by (intro open_Collect_less continuous_intros
          continuous_on_const)
    then show ?thesis unfolding RO_def
      by (intro open_Int open_ball)
  qed
  have ROb: "\<And>z. z \<in> RO \<Longrightarrow> norm (z - x) \<le> Rn"
  proof -
    fix z assume "z \<in> RO"
    then have "norm (z - y\<^sub>0) < rB"
      unfolding RO_def by (simp add: dist_norm norm_minus_commute)
    moreover have "norm (z - x) \<le> norm (z - y\<^sub>0) + norm (y\<^sub>0 - x)"
    proof -
      have "z - x = (z - y\<^sub>0) + (y\<^sub>0 - x)" by simp
      then show ?thesis
        by (metis norm_triangle_ineq)
    qed
    ultimately show "norm (z - x) \<le> Rn" unfolding Rn_def by linarith
  qed
  have unitRO: "norm (uvec y\<^sub>0 \<rho> z) = 1" if z: "z \<in> RO" for z
  proof -
    have "\<rho> \<le> norm (z - y\<^sub>0)" using z unfolding RO_def by auto
    then show ?thesis by (rule uvec_unit[OF rho0])
  qed
  have killRO: "transpose (SF z) *v (c' *\<^sub>R (x - y\<^sub>0)
      + (c' *\<^sub>R mat 1) *v (z - x)) = 0"
    if z: "z \<in> RO" for z c'
  proof -
    have far: "\<rho> \<le> norm (z - y\<^sub>0)" using z unfolding RO_def by auto
    have arg: "c' *\<^sub>R (x - y\<^sub>0) + (c' *\<^sub>R mat 1) *v (z - x)
        = c' *\<^sub>R (z - y\<^sub>0)"
      by (simp add: scaleR_matrix_vector
          scaleR_right_diff_distrib scaleR_add_right)
    have k0: "tanp (uvec y\<^sub>0 \<rho> z) *v (z - y\<^sub>0) = 0"
      by (rule tanp_kill[OF unitRO[OF z] uvec_par[OF rho0 far]])
    have "transpose (SF z) *v (c' *\<^sub>R (z - y\<^sub>0))
        = c' *\<^sub>R (SF z *v (z - y\<^sub>0))"
      unfolding SF_def tanp_sym
      by (simp add: matrix_vector_mult_scaleR)
    also have "\<dots> = 0" unfolding SF_def using k0 by simp
    finally show ?thesis unfolding arg .
  qed
  have sqRO: "SF z ** transpose (SF z) = tanp (uvec y\<^sub>0 \<rho> z)"
    if z: "z \<in> RO" for z
    unfolding SF_def
    by (simp add: tanp_sym tanp_sq[OF unitRO[OF z]])
  have trRO: "trace ((c' *\<^sub>R mat 1) ** (SF z ** transpose (SF z)))
      = c' * (real CARD('n) - 1)"
    if z: "z \<in> RO" for z c'
  proof -
    have "(c' *\<^sub>R mat 1) ** (SF z ** transpose (SF z))
        = c' *\<^sub>R (SF z ** transpose (SF z))"
      by (simp add: scaleR_matrix_mult)
    then have "trace ((c' *\<^sub>R mat 1) ** (SF z ** transpose (SF z)))
        = c' * trace (SF z ** transpose (SF z))"
      by (simp add: trace_scaleR)
    also have "trace (SF z ** transpose (SF z))
        = real CARD('n) - 1"
      unfolding sqRO[OF z] by (rule tanp_trace[OF unitRO[OF z]])
    finally show ?thesis .
  qed
  have sym1: "transpose ((2::real) *\<^sub>R mat 1 :: real^'n^'n)
      = (2::real) *\<^sub>R mat 1"
    by (simp add: transpose_scalar)
  have sym2: "transpose ((-2::real) *\<^sub>R mat 1 :: real^'n^'n)
      = (-2::real) *\<^sub>R mat 1"
    by (simp add: transpose_def vec_eq_iff mat_def)
  obtain P where P: "P \<in> exit_class k L T x"
    and AE2: "AE \<omega> in P. \<forall>t.
      0 < t \<longrightarrow> t \<le> T \<longrightarrow> (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> RO) \<longrightarrow>
      (t * (2 * (real CARD('n) - 1)) / 2
        \<le> (2 *\<^sub>R (x - y\<^sub>0)) \<bullet> (fst (\<omega> t) - x)
          + (1/2) * ((fst (\<omega> t) - x)
              \<bullet> (((2::real) *\<^sub>R mat 1) *v (fst (\<omega> t) - x))))
      \<and> (t * (- 2 * (real CARD('n) - 1)) / 2
        \<le> ((-2) *\<^sub>R (x - y\<^sub>0)) \<bullet> (fst (\<omega> t) - x)
          + (1/2) * ((fst (\<omega> t) - x)
              \<bullet> (((-2::real) *\<^sub>R mat 1) *v (fst (\<omega> t) - x))))"
  proof -
    have kill1: "\<And>z. z \<in> RO \<Longrightarrow> transpose (SF z)
        *v (2 *\<^sub>R (x - y\<^sub>0) + ((2::real) *\<^sub>R mat 1) *v (z - x)) = 0"
      using killRO by blast
    have kill2: "\<And>z. z \<in> RO \<Longrightarrow> transpose (SF z)
        *v ((-2) *\<^sub>R (x - y\<^sub>0) + ((-2::real) *\<^sub>R mat 1) *v (z - x)) = 0"
      using killRO by blast
    have marg1: "\<And>z. z \<in> RO \<Longrightarrow> 2 * (real CARD('n) - 1)
        \<le> trace (((2::real) *\<^sub>R mat 1) ** (SF z ** transpose (SF z)))"
      using trRO by simp
    have marg2: "\<And>z. z \<in> RO \<Longrightarrow> - 2 * (real CARD('n) - 1)
        \<le> trace (((-2::real) *\<^sub>R mat 1) ** (SF z ** transpose (SF z)))"
    proof -
      fix z assume zRO: "z \<in> RO"
      show "- 2 * (real CARD('n) - 1)
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
        (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> {w. \<rho> < norm (w - y\<^sub>0)} \<inter> ball y\<^sub>0 rB)
        \<longrightarrow> (norm (fst (\<omega> t) - y\<^sub>0))\<^sup>2
          = (norm (x - y\<^sub>0))\<^sup>2 + t * (real CARD('n) - 1)"
      using AE2
    proof (eventually_elim)
      case (elim \<omega>)
      show ?case
      proof (intro allI impI)
        fix t assume t0: "0 < t" and tT: "t \<le> T"
          and inb: "\<forall>s\<in>{0..t}. fst (\<omega> s)
            \<in> {w. \<rho> < norm (w - y\<^sub>0)} \<inter> ball y\<^sub>0 rB"
        have inb': "\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> RO"
          using inb unfolding RO_def by blast
        have g1: "t * (2 * (real CARD('n) - 1)) / 2
            \<le> (2 *\<^sub>R (x - y\<^sub>0)) \<bullet> (fst (\<omega> t) - x)
              + (1/2) * ((fst (\<omega> t) - x)
                  \<bullet> (((2::real) *\<^sub>R mat 1) *v (fst (\<omega> t) - x)))"
          and g2: "t * (- 2 * (real CARD('n) - 1)) / 2
            \<le> ((-2) *\<^sub>R (x - y\<^sub>0)) \<bullet> (fst (\<omega> t) - x)
              + (1/2) * ((fst (\<omega> t) - x)
                  \<bullet> (((-2::real) *\<^sub>R mat 1) *v (fst (\<omega> t) - x)))"
          using elim t0 tT inb' by blast+
        define d where "d = fst (\<omega> t) - x"
        have e1: "(2 *\<^sub>R (x - y\<^sub>0)) \<bullet> d = 2 * ((x - y\<^sub>0) \<bullet> d)"
          by simp
        have e2: "((-2) *\<^sub>R (x - y\<^sub>0)) \<bullet> d = - 2 * ((x - y\<^sub>0) \<bullet> d)"
          by simp
        have e3: "d \<bullet> (((2::real) *\<^sub>R mat 1) *v d) = 2 * (d \<bullet> d)"
          by (simp add: scaleR_matrix_vector)

        have negmv: "\<And>A :: real^'n^'n. (- A) *v d = - (A *v d)"
          by (simp add: matrix_vector_mult_def vec_eq_iff sum_negf)
        have e4: "d \<bullet> (((-2::real) *\<^sub>R mat 1) *v d) = - 2 * (d \<bullet> d)"
          by (simp add: negmv scaleR_matrix_vector)

        have id1: "t * (2 * (real CARD('n) - 1)) / 2
            = t * (real CARD('n) - 1)" by simp
        have id2: "t * (- 2 * (real CARD('n) - 1)) / 2
            = - (t * (real CARD('n) - 1))" by (simp add: field_simps)
        have both: "2 * ((x - y\<^sub>0) \<bullet> d) + d \<bullet> d
            = t * (real CARD('n) - 1)"
          using g1[unfolded id1] g2[unfolded id2]
          unfolding d_def[symmetric] e1 e2 e3 e4
          by linarith
        have split: "(norm (fst (\<omega> t) - y\<^sub>0))\<^sup>2
            = (norm (x - y\<^sub>0))\<^sup>2 + (2 * ((x - y\<^sub>0) \<bullet> d) + d \<bullet> d)"
        proof -
          have dd: "fst (\<omega> t) - y\<^sub>0 = (x - y\<^sub>0) + d"
            unfolding d_def by simp
          have "(norm (fst (\<omega> t) - y\<^sub>0))\<^sup>2
              = (fst (\<omega> t) - y\<^sub>0) \<bullet> (fst (\<omega> t) - y\<^sub>0)"
            by (simp add: dot_square_norm)
          also have "\<dots> = (x - y\<^sub>0) \<bullet> (x - y\<^sub>0)
              + 2 * ((x - y\<^sub>0) \<bullet> d) + d \<bullet> d"
            unfolding dd
            by (simp add: inner_add_left inner_add_right
                inner_commute)
          also have "(x - y\<^sub>0) \<bullet> (x - y\<^sub>0) = (norm (x - y\<^sub>0))\<^sup>2"
            by (simp add: dot_square_norm)
          finally show ?thesis by simp
        qed
        show "(norm (fst (\<omega> t) - y\<^sub>0))\<^sup>2
            = (norm (x - y\<^sub>0))\<^sup>2 + t * (real CARD('n) - 1)"
          unfolding split both by (rule refl)
      qed
    qed
  qed
qed

subsection \<open>Deterministic confinement and the ball lower bound\<close>

text \<open>Paths of the tangential member cannot leave the annulus before the
  deterministic time \<open>(rB\<^sup>2 - |x-y\<^sub>0|\<^sup>2)/(n-1)\<close>: the inner boundary is
  unreachable because the squared distance only grows, and reaching the
  outer sphere pins the time exactly.  Feeding the constant-time DPP
  @{thm [source] exit_val_dpp_sup_ge} turns confinement into the lower
  bound \<open>v(x) \<ge> min(T/2, \<delta>/2)\<close> whenever the ball sits inside \<open>K\<close>, a
  (non-sharp) form of Example 3.1's lower bound.\<close>

lemma radial_sq_upto:
  fixes \<omega> :: "'n::finite pairpath" and y\<^sub>0 x :: "real^'n"
    and TT e cn :: real and RO :: "(real^'n) set"
  assumes wm: "\<omega> \<in> mspace (path_metric TT :: ('n pairpath) metric)"
    and grow: "\<And>t. 0 < t \<Longrightarrow> t \<le> TT \<Longrightarrow>
      (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> RO) \<Longrightarrow>
      (norm (fst (\<omega> t) - y\<^sub>0))\<^sup>2 = (norm (x - y\<^sub>0))\<^sup>2 + t * cn"
    and e0: "0 < e" and eT: "e \<le> TT"
    and inside: "\<And>s. 0 \<le> s \<Longrightarrow> s < e \<Longrightarrow> fst (\<omega> s) \<in> RO"
  shows "(norm (fst (\<omega> e) - y\<^sub>0))\<^sup>2 = (norm (x - y\<^sub>0))\<^sup>2 + e * cn"
proof -
  define g where "g = (\<lambda>s. (norm (fst (\<omega> s) - y\<^sub>0))\<^sup>2)"
  have gc: "continuous_on {0..TT} g"
  proof -
    have wc: "continuous_on {0..TT} \<omega>"
      by (rule mspace_path_metricD[OF wm])
    have fc: "continuous_on {0..TT} (\<lambda>s. fst (\<omega> s))"
      by (rule continuous_on_fst[OF wc])
    show ?thesis
      unfolding g_def by (intro continuous_intros fc)
  qed
  define tj where "tj = (\<lambda>j. e - e / (2 * real (Suc j)))"
  have tjl: "0 < tj j" for j
  proof -
    have "e / (2 * real (Suc j)) \<le> e / 2"
    proof (rule divide_left_mono)
      show "2 \<le> 2 * real (Suc j)" by simp
      show "0 \<le> e" using e0 by linarith
      show "0 < 2 * real (Suc j) * 2" by simp
    qed
    then show ?thesis unfolding tj_def using e0 by linarith
  qed
  have tju: "tj j < e" for j
  proof -
    have "0 < e / (2 * real (Suc j))" using e0 by simp
    then show ?thesis unfolding tj_def by linarith
  qed
  have tjT: "tj j \<le> TT" for j using tju[of j] eT by linarith
  have glow: "g (tj j) = (norm (x - y\<^sub>0))\<^sup>2 + tj j * cn" for j
    unfolding g_def
  proof (rule grow)
    show "0 < tj j" by (rule tjl)
    show "tj j \<le> TT" by (rule tjT)
    show "\<forall>s\<in>{0..tj j}. fst (\<omega> s) \<in> RO"
    proof
      fix s assume s: "s \<in> {0..tj j}"
      then have "0 \<le> s" and "s < e" using tju[of j] by auto
      then show "fst (\<omega> s) \<in> RO" by (rule inside)
    qed
  qed
  have tjlim: "tj \<longlonglongrightarrow> e"
  proof -
    have eq: "(\<lambda>j. (e / 2) * inverse (real (Suc j)))
        = (\<lambda>j. e / (2 * real (Suc j)))"
      by (rule ext) (simp add: field_simps)
    have "(\<lambda>j. (e / 2) * inverse (real (Suc j))) \<longlonglongrightarrow> (e / 2) * 0"
      by (intro tendsto_mult tendsto_const LIMSEQ_inverse_real_of_nat)
    then have "(\<lambda>j. e / (2 * real (Suc j))) \<longlonglongrightarrow> 0"
      unfolding eq by simp
    then have "(\<lambda>j. e - e / (2 * real (Suc j))) \<longlonglongrightarrow> e - 0"
      by (intro tendsto_diff tendsto_const)
    then show ?thesis unfolding tj_def by simp
  qed
  have gcomp: "(\<lambda>j. g (tj j)) \<longlonglongrightarrow> g e"
  proof -
    have inS: "\<forall>n. tj n \<in> {0..TT}"
      using tjl tjT by (auto intro: less_imp_le)
    have eS: "e \<in> {0..TT}" using e0 eT by auto
    have "(g \<circ> tj) \<longlonglongrightarrow> g e"
      using continuous_on_sequentially[THEN iffD1, OF gc] inS eS tjlim
      by blast
    then show ?thesis by (simp add: o_def)
  qed
  have vlim: "(\<lambda>j. (norm (x - y\<^sub>0))\<^sup>2 + tj j * cn)
      \<longlonglongrightarrow> (norm (x - y\<^sub>0))\<^sup>2 + e * cn"
    by (intro tendsto_add tendsto_const tendsto_mult tjlim)
  have "(\<lambda>j. g (tj j)) \<longlonglongrightarrow> (norm (x - y\<^sub>0))\<^sup>2 + e * cn"
    using vlim unfolding glow by simp
  then have "g e = (norm (x - y\<^sub>0))\<^sup>2 + e * cn"
    using gcomp LIMSEQ_unique by blast
  then show ?thesis unfolding g_def .
qed

theorem exit_val_ball_lower_plus:
  fixes K :: "(real^'n::finite) set" and y\<^sub>0 x :: "real^'n"
    and rB T \<beta> :: real
  assumes T0: "0 < T" and L1: "1 \<le> L" and k1: "1 \<le> k"
    and kn: "k < CARD('n)"
    and Kc: "closed K" and sub: "cball y\<^sub>0 rB \<subseteq> K"
    and xy: "x \<noteq> y\<^sub>0" and xin: "norm (x - y\<^sub>0) < rB"
    and b0: "0 \<le> \<beta>"
    and vlow: "\<And>w. w \<in> ball y\<^sub>0 rB \<Longrightarrow>
      \<beta> \<le> enn2real (exit_val k L T K w)"
  shows "ennreal (min (T / 2)
      ((rB\<^sup>2 - (norm (x - y\<^sub>0))\<^sup>2) / (2 * (real CARD('n) - 1)))
      + min \<beta> (T / 2))
      \<le> exit_val k L T K x"
proof -
  define \<rho>\<^sub>0 where "\<rho>\<^sub>0 = norm (x - y\<^sub>0)"
  define \<rho> where "\<rho> = \<rho>\<^sub>0 / 2"
  define cn where "cn = real CARD('n) - 1"
  define \<delta>f where "\<delta>f = (rB\<^sup>2 - \<rho>\<^sub>0\<^sup>2) / cn"
  define cc where "cc = min (T / 2) (\<delta>f / 2)"
  let ?RO = "{w :: real^'n. \<rho> < norm (w - y\<^sub>0)} \<inter> ball y\<^sub>0 rB"
  have r00: "0 < \<rho>\<^sub>0" unfolding \<rho>\<^sub>0_def using xy by simp
  have rho0: "0 < \<rho>" unfolding \<rho>_def using r00 by simp
  have n2: "2 \<le> CARD('n)" using k1 kn by linarith
  have cn1: "1 \<le> cn"
  proof -
    have "(2::real) \<le> real CARD('n)"
      using n2 by (simp add: of_nat_le_iff [where m = 2, symmetric])
    then show ?thesis unfolding cn_def by linarith
  qed
  have cn0: "0 < cn" using cn1 by linarith
  have rr: "\<rho>\<^sub>0 < rB" using xin unfolding \<rho>\<^sub>0_def .
  have rB0: "0 < rB" using r00 rr by linarith
  have sq_lt: "\<rho>\<^sub>0\<^sup>2 < rB\<^sup>2"
    using r00 rr by (intro power_strict_mono) simp_all
  have df0: "0 < \<delta>f" unfolding \<delta>f_def using sq_lt cn0 by simp
  have cc0: "0 < cc" unfolding cc_def using T0 df0 by simp
  have ccT: "cc < T" unfolding cc_def using T0 by simp
  have ccT2: "cc \<le> T / 2" unfolding cc_def by simp
  have ccdf: "cc < \<delta>f" unfolding cc_def using df0 by simp
  obtain P where P: "P \<in> exit_class k L T x"
    and AEg: "AE \<omega> in P. \<forall>t.
      0 < t \<longrightarrow> t \<le> T \<longrightarrow>
      (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> ?RO) \<longrightarrow>
      (norm (fst (\<omega> t) - y\<^sub>0))\<^sup>2
        = (norm (x - y\<^sub>0))\<^sup>2 + t * (real CARD('n) - 1)"
    using tangential_exact_growth[OF T0 L1 k1 kn rho0,
        where y\<^sub>0 = y\<^sub>0 and rB = rB and x = x]
    by blast
  have setsP: "sets P = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    by (rule exit_class_sets[OF P])
  have spaceP: "space P = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsP])
  have start: "AE \<omega> in P. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    by (rule exit_class_start[OF P])
  have sp: "AE \<omega> in P. \<omega> \<in> space P" by (rule AE_space)
  have AEfun: "AE \<omega> in P. ennreal (cc + min \<beta> (T / 2))
      \<le> ennreal (pexit cc K (\<lambda>t. fst (\<omega> t))
        + (if pexit cc K (\<lambda>t. fst (\<omega> t)) = cc \<and> fst (\<omega> cc) \<in> K
           then enn2real (exit_val k L (T - cc) K (fst (\<omega> cc))) else 0))"
    using AEg start sp
  proof (eventually_elim)
    case (elim \<omega>)
    have wm: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using elim(3) by (simp add: spaceP)
    have x0: "fst (\<omega> 0) = x" using elim(2) by blast
    have cont: "continuous_on {0..T} (\<lambda>t. fst (\<omega> t))"
      by (rule path_sets_fst_continuous[OF setsP])
        (use elim(3) in simp)
    have grow: "\<And>t. 0 < t \<Longrightarrow> t \<le> T \<Longrightarrow>
        (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> ?RO) \<Longrightarrow>
        (norm (fst (\<omega> t) - y\<^sub>0))\<^sup>2 = (norm (x - y\<^sub>0))\<^sup>2 + t * cn"
      unfolding cn_def using elim(1) by blast
    have xRO: "x \<in> ?RO"
      using rho0 rr r00 unfolding \<rho>_def \<rho>\<^sub>0_def
      by (auto simp: dist_norm norm_minus_commute)
    have ROopen: "open ?RO"
    proof -
      have "open {w :: real^'n. \<rho> < norm (w - y\<^sub>0)}"
        by (intro open_Collect_less continuous_intros
            continuous_on_const)
      then show ?thesis by (intro open_Int open_ball)
    qed
    have cc0': "0 \<le> cc" using cc0 by linarith
    have contc: "continuous_on {0..cc} (\<lambda>t. fst (\<omega> t))"
      by (rule continuous_on_subset[OF cont]) (use ccT in auto)
    \<comment> \<open>the path stays in the annulus strictly before \<open>cc\<close>\<close>
    have IN: "fst (\<omega> s) \<in> ?RO" if s0: "0 \<le> s" and sc: "s < cc" for s
    proof -
      define e where "e = pexit cc ?RO (\<lambda>t. fst (\<omega> t))"
      have eup: "e \<le> cc" unfolding e_def by (rule pexit_le_T[OF cc0'])
      have before: "fst (\<omega> u) \<in> ?RO"
        if u0: "0 \<le> u" and ue: "u < e" for u
      proof (rule ccontr)
        assume nb: "fst (\<omega> u) \<notin> ?RO"
        have uc: "u \<le> cc" using ue eup by linarith
        have "pexit cc ?RO (\<lambda>t. fst (\<omega> t)) \<le> u"
          by (rule pexit_le_of_mem[OF cc0' u0 uc]) (use nb in simp)
        then show False using ue unfolding e_def by linarith
      qed
      have ecc: "e = cc"
      proof (rule ccontr)
        assume "e \<noteq> cc"
        then have elt: "e < cc" using eup by linarith
        have Xe: "fst (\<omega> e) \<notin> ?RO"
          using pexit_mem_of_less_T[OF cc0' ROopen contc]
          using elt unfolding e_def by simp
        have e0': "0 < e"
        proof (rule ccontr)
          assume "\<not> 0 < e"
          moreover have "0 \<le> e"
            unfolding e_def by (rule pexit_nonneg[OF cc0'])
          ultimately have "e = 0" by linarith
          then show False using Xe x0 xRO by simp
        qed
        have esq: "(norm (fst (\<omega> e) - y\<^sub>0))\<^sup>2
            = (norm (x - y\<^sub>0))\<^sup>2 + e * cn"
        proof (rule radial_sq_upto[OF wm grow e0'])
          show "e \<le> T" using elt ccT by linarith
          show "\<And>s. 0 \<le> s \<Longrightarrow> s < e \<Longrightarrow> fst (\<omega> s) \<in> ?RO"
            by (rule before)
        qed
        have dichot: "norm (fst (\<omega> e) - y\<^sub>0) \<le> \<rho>
            \<or> rB \<le> norm (fst (\<omega> e) - y\<^sub>0)"
          using Xe
          by (auto simp: dist_norm norm_minus_commute)
        show False
        proof (cases rule: disjE[OF dichot])
          case 1
          have "(norm (fst (\<omega> e) - y\<^sub>0))\<^sup>2 \<le> \<rho>\<^sup>2"
            using 1 rho0 by (intro power_mono) simp_all
          moreover have "\<rho>\<^sup>2 < \<rho>\<^sub>0\<^sup>2"
            unfolding \<rho>_def using r00 by (simp add: power_divide)
          moreover have "\<rho>\<^sub>0\<^sup>2 \<le> (norm (fst (\<omega> e) - y\<^sub>0))\<^sup>2"
            unfolding esq \<rho>\<^sub>0_def using e0' cn0
            by simp
          ultimately show False by linarith
        next
          case 2
          have "rB\<^sup>2 \<le> (norm (fst (\<omega> e) - y\<^sub>0))\<^sup>2"
            using 2 rB0 by (intro power_mono) simp_all
          then have "rB\<^sup>2 - \<rho>\<^sub>0\<^sup>2 \<le> e * cn"
            unfolding esq \<rho>\<^sub>0_def by linarith
          then have "\<delta>f \<le> e"
            unfolding \<delta>f_def using cn0 by (simp add: pos_divide_le_eq)
          then show False using elt ccdf by linarith
        qed
      qed
      show ?thesis using before[OF s0] sc unfolding ecc by simp
    qed
    \<comment> \<open>hence in \<open>K\<close> through \<open>cc\<close>, including the endpoint\<close>
    have inB: "fst (\<omega> s) \<in> ball y\<^sub>0 rB"
      if s0: "0 \<le> s" and sc: "s \<le> cc" for s
    proof (cases "s < cc")
      case True
      show ?thesis using IN[OF s0 True] by blast
    next
      case False
      then have seq: "s = cc" using sc by linarith
      have csq: "(norm (fst (\<omega> cc) - y\<^sub>0))\<^sup>2
          = (norm (x - y\<^sub>0))\<^sup>2 + cc * cn"
      proof (rule radial_sq_upto[OF wm grow cc0])
        show "cc \<le> T" using ccT by linarith
        show "\<And>s. 0 \<le> s \<Longrightarrow> s < cc \<Longrightarrow> fst (\<omega> s)
            \<in> {w. \<rho> < norm (w - y\<^sub>0)} \<inter> ball y\<^sub>0 rB"
          by (rule IN)
      qed
      have "(norm (fst (\<omega> cc) - y\<^sub>0))\<^sup>2 < rB\<^sup>2"
      proof -
        have "cc * cn < \<delta>f * cn"
          using ccdf cn0 by (intro mult_strict_right_mono)
        also have "\<delta>f * cn = rB\<^sup>2 - \<rho>\<^sub>0\<^sup>2"
          unfolding \<delta>f_def using cn0 by simp
        finally show ?thesis
          unfolding csq \<rho>\<^sub>0_def[symmetric] by linarith
      qed
      then have "norm (fst (\<omega> cc) - y\<^sub>0) < rB"
        using rB0 by (metis power2_le_imp_le
            linorder_not_less nless_le)
      then have "fst (\<omega> cc) \<in> ball y\<^sub>0 rB"
        by (simp add: dist_norm norm_minus_commute)
      then show ?thesis unfolding seq .
    qed
    have inK: "fst (\<omega> s) \<in> K" if s0: "0 \<le> s" and sc: "s \<le> cc" for s
      using inB[OF s0 sc] sub ball_subset_cball by blast
    have pex: "pexit cc K (\<lambda>t. fst (\<omega> t)) = cc"
      by (rule pexit_eq_of_stays[OF cc0']) (use inK in simp)
    have XccK: "fst (\<omega> cc) \<in> K" using inK[of cc] cc0 by simp
    have fn: "pexit cc K (\<lambda>t. fst (\<omega> t))
        + (if pexit cc K (\<lambda>t. fst (\<omega> t)) = cc \<and> fst (\<omega> cc) \<in> K
           then enn2real (exit_val k L (T - cc) K (fst (\<omega> cc))) else 0)
        = cc + enn2real (exit_val k L (T - cc) K (fst (\<omega> cc)))"
      using pex XccK by simp
    have XccB: "fst (\<omega> cc) \<in> ball y\<^sub>0 rB"
      using inB[of cc] cc0 by simp
    have s1: "0 \<le> T - cc" using ccT by linarith
    have s2: "T - cc \<le> T" using cc0 by linarith
    have cap: "enn2real (exit_val k L (T - cc) K (fst (\<omega> cc)))
        = min (enn2real (exit_val k L T K (fst (\<omega> cc)))) (T - cc)"
      by (rule enn2real_paper_v_horizon_cap[OF s1 s2 L1 Kc])
    have vge: "min \<beta> (T / 2)
        \<le> enn2real (exit_val k L (T - cc) K (fst (\<omega> cc)))"
    proof -
      have b1: "\<beta> \<le> enn2real (exit_val k L T K (fst (\<omega> cc)))"
        by (rule vlow[OF XccB])
      have b2: "T / 2 \<le> T - cc" using ccT2 by linarith
      have c1: "min \<beta> (T / 2) \<le> \<beta>" by (rule min.cobounded1)
      have c2: "min \<beta> (T / 2) \<le> T / 2" by (rule min.cobounded2)
      have d1: "min \<beta> (T / 2)
          \<le> enn2real (exit_val k L T K (fst (\<omega> cc)))"
        using c1 b1 by linarith
      have d2: "min \<beta> (T / 2) \<le> T - cc" using c2 b2 by linarith
      show ?thesis unfolding cap using d1 d2 by simp
    qed
    have "cc + min \<beta> (T / 2)
        \<le> cc + enn2real (exit_val k L (T - cc) K (fst (\<omega> cc)))"
      using vge by linarith
    then show ?case unfolding fn by (intro ennreal_leI) simp
  qed
  have essge: "ennreal (cc + min \<beta> (T / 2)) \<le> ess_inf_time P
      (\<lambda>\<omega>. pexit cc K (\<lambda>t. fst (\<omega> t))
        + (if pexit cc K (\<lambda>t. fst (\<omega> t)) = cc \<and> fst (\<omega> cc) \<in> K
           then enn2real (exit_val k L (T - cc) K (fst (\<omega> cc))) else 0))"
    unfolding ess_inf_time_def
    by (rule Sup_upper) (use AEfun in blast)
  have esle: "ess_inf_time P
      (\<lambda>\<omega>. pexit cc K (\<lambda>t. fst (\<omega> t))
        + (if pexit cc K (\<lambda>t. fst (\<omega> t)) = cc \<and> fst (\<omega> cc) \<in> K
           then enn2real (exit_val k L (T - cc) K (fst (\<omega> cc))) else 0))
      \<le> exit_val k L T K x"
  proof -
    have "ess_inf_time P
        (\<lambda>\<omega>. pexit cc K (\<lambda>t. fst (\<omega> t))
          + (if pexit cc K (\<lambda>t. fst (\<omega> t)) = cc \<and> fst (\<omega> cc) \<in> K
             then enn2real (exit_val k L (T - cc) K (fst (\<omega> cc))) else 0))
        \<le> (SUP P' \<in> exit_class k L T x. ess_inf_time P'
          (\<lambda>\<omega>. pexit cc K (\<lambda>t. fst (\<omega> t))
            + (if pexit cc K (\<lambda>t. fst (\<omega> t)) = cc \<and> fst (\<omega> cc) \<in> K
               then enn2real (exit_val k L (T - cc) K (fst (\<omega> cc)))
               else 0)))"
      by (rule SUP_upper[OF P])
    also have "\<dots> \<le> exit_val k L T K x"
      by (rule exit_val_dpp_sup_ge[OF less_imp_le[OF cc0] ccT L1 Kc])
    finally show ?thesis .
  qed
  have "ennreal (cc + min \<beta> (T / 2)) \<le> exit_val k L T K x"
    by (rule order_trans[OF essge esle])
  moreover have "cc = min (T / 2)
      ((rB\<^sup>2 - (norm (x - y\<^sub>0))\<^sup>2) / (2 * (real CARD('n) - 1)))"
  proof -
    have e: "\<delta>f / 2
        = (rB\<^sup>2 - (norm (x - y\<^sub>0))\<^sup>2) / (2 * (real CARD('n) - 1))"
      unfolding \<delta>f_def \<rho>\<^sub>0_def cn_def
      using cn0 unfolding cn_def by (simp add: mult_ac)
    show ?thesis unfolding cc_def e by (rule refl)
  qed
  ultimately show ?thesis by simp
qed

text \<open>The original ball bound is the case \<open>\<beta> = 0\<close>: the value at the
  exit point is simply dropped.\<close>


(*<*)
end
(*>*)
