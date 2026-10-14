section \<open>The supersolution, case 1: a nonzero gradient\<close>

(*<*)
theory Value_Function_Supersolution_Case_1
  imports
    "Covariation_Constrained_Martingales.Covariation_Class_Euler_Scheme" Value_Function_Subsolution
begin

(*>*)

subsection \<open>Bricks for the Case-1 contradiction\<close>

text \<open>\<open>trace_msub_mat\<close>, \<open>quad_soften_split\<close> live in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


subsection \<open>Exact rotations: a covariance field with no eigenvalue margin\<close>

text \<open>\<open>colmat_matvec\<close> lives in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


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
          linear_continuous_on[OF matrix_vector_mul_bounded_linear] d]) auto
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

text \<open>\<open>rot_cone_ok\<close> lives in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


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

subsection \<open>Orthogonal conjugation preserves the paper's constraint set\<close>

lemma is_proj_conj:
  fixes P R :: "real^'n::finite^'n"
  assumes R: "R ** transpose R = mat 1" and P: "is_proj P"
  shows "is_proj (transpose R ** P ** R)"
proof -
  have symP: "transpose P = P" and idP: "P ** P = P"
    using P unfolding is_proj_def by blast+
  have "transpose (transpose R ** P ** R) = transpose R ** P ** R"
    by (simp add: matrix_transpose_mul matrix_mul_assoc symP)
  moreover have "(transpose R ** P ** R) ** (transpose R ** P ** R) = transpose R ** P ** R"
  proof -
    have "(transpose R ** P ** R) ** (transpose R ** P ** R)
        = transpose R ** P ** (R ** transpose R) ** P ** R"
      by (simp add: matrix_mul_assoc)
    also have "\<dots> = transpose R ** (P ** P) ** R"
      unfolding R by (simp add: matrix_mul_assoc)
    finally show ?thesis unfolding idP .
  qed
  ultimately show ?thesis unfolding is_proj_def ..
qed

lemma trace_conj_orth:
  fixes P R :: "real^'n::finite^'n"
  assumes R: "R ** transpose R = mat 1"
  shows "trace (transpose R ** P ** R) = trace P"
proof -
  have "trace (transpose R ** P ** R) = trace (R ** (transpose R ** P))"
    by (rule trace_mul_sym)
  also have "R ** (transpose R ** P) = P"
    by (metis matrix_mul_assoc R matrix_mul_lid)
  finally show ?thesis .
qed

lemma Pi_proj_conj:
  fixes a R :: "real^'n::finite^'n"
  assumes R: "orthogonal_matrix R"
  shows "Pi_proj (R ** a ** transpose R) m = Pi_proj a m"
proof -
  have o1: "transpose R ** R = mat 1" and o2: "R ** transpose R = mat 1"
    using R unfolding orthogonal_matrix_def by blast+
  have tr: "trace ((R ** a ** transpose R) ** P) = trace (a ** (transpose R ** P ** R))"
    for P :: "real^'n^'n"
    by (rule trace_conjugate[symmetric])
  have "{trace ((R ** a ** transpose R) ** P) | P. is_proj P \<and> trace P = real m}
      = {trace (a ** P) | P. is_proj P \<and> trace P = real m}"
  proof (intro equalityI subsetI)
    fix t assume "t \<in> {trace ((R ** a ** transpose R) ** P) | P. is_proj P \<and> trace P = real m}"
    then obtain P where P: "is_proj P" "trace P = real m"
      and t: "t = trace ((R ** a ** transpose R) ** P)" by blast
    have "is_proj (transpose R ** P ** R)" by (rule is_proj_conj[OF o2 P(1)])
    moreover have "trace (transpose R ** P ** R) = real m"
      using trace_conj_orth[OF o2, of P] P(2) by simp
    ultimately show "t \<in> {trace (a ** P) | P. is_proj P \<and> trace P = real m}"
      unfolding t tr by blast
  next
    fix t assume "t \<in> {trace (a ** P) | P. is_proj P \<and> trace P = real m}"
    then obtain P where P: "is_proj P" "trace P = real m"
      and t: "t = trace (a ** P)" by blast
    have o1': "transpose R ** transpose (transpose R) = mat 1"
      unfolding transpose_transpose by (rule o1)
    have pr: "is_proj (R ** P ** transpose R)"
      using is_proj_conj[OF o1' P(1)] by simp
    have trP: "trace (R ** P ** transpose R) = real m"
      using trace_conj_orth[OF o1', of P] P(2) by simp
    have "transpose R ** (R ** P ** transpose R) ** R
        = (transpose R ** R) ** P ** (transpose R ** R)"
      by (simp add: matrix_mul_assoc)
    then have RPR: "transpose R ** (R ** P ** transpose R) ** R = P"
      unfolding o1 by simp
    have "t = trace ((R ** a ** transpose R) ** (R ** P ** transpose R))"
      unfolding t tr RPR ..
    then show "t \<in> {trace ((R ** a ** transpose R) ** P) | P. is_proj P \<and> trace P = real m}"
      using pr trP by blast
  qed
  then show ?thesis unfolding Pi_proj_def by simp
qed

theorem sconstraint_conj:
  fixes R a :: "real^'n::finite^'n"
  assumes R: "orthogonal_matrix R" and a: "a \<in> sconstraint k L"
  shows "R ** a ** transpose R \<in> sconstraint k L"
proof -
  have o2: "R ** transpose R = mat 1"
    using R unfolding orthogonal_matrix_def by blast
  have psda: "psd a" and uba: "eigen_ub a L"
    and Pia: "\<And>m. k < m \<Longrightarrow> m \<le> CARD('n) \<Longrightarrow> real (m - k) \<le> Pi_proj a m"
    using a unfolding sconstraint_def Pi_constraint_def by auto
  have Amv: "(R ** a ** transpose R) *v z = R *v (a *v (transpose R *v z))" for z
    by (metis matrix_vector_mul_assoc)
  have quad: "z \<bullet> ((R ** a ** transpose R) *v z)
      = (transpose R *v z) \<bullet> (a *v (transpose R *v z))" for z
    unfolding Amv by (rule inner_transpose_matrix)
  have normT: "(transpose R *v z) \<bullet> (transpose R *v z) = z \<bullet> z" for z
    using orth_preserves_inner[of "transpose R" z z] o2 by simp
  have sym: "transpose (R ** a ** transpose R) = R ** a ** transpose R"
    using psda by (simp add: psd_def matrix_transpose_mul matrix_mul_assoc)
  have psdA: "psd (R ** a ** transpose R)"
    unfolding psd_def using sym quad psda unfolding psd_def by simp
  have ubA: "eigen_ub (R ** a ** transpose R) L"
    unfolding eigen_ub_def
  proof
    fix z :: "real^'n"
    have "(transpose R *v z) \<bullet> (a *v (transpose R *v z))
        \<le> L * ((transpose R *v z) \<bullet> (transpose R *v z))"
      using uba unfolding eigen_ub_def by blast
    then show "z \<bullet> ((R ** a ** transpose R) *v z) \<le> L * (z \<bullet> z)"
      unfolding quad normT .
  qed
  have PiA: "real (m - k) \<le> Pi_proj (R ** a ** transpose R) m"
    if "k < m" "m \<le> CARD('n)" for m
    unfolding Pi_proj_conj[OF R] by (rule Pia[OF that])
  show ?thesis
    unfolding sconstraint_def Pi_constraint_def using psdA ubA PiA by simp
qed

text \<open>The field of Case 1, for any set of rates that is invariant under
  orthogonal conjugation: a psd rate \<open>a \<in> S\<close> that annihilates \<open>q\<close> is
  rotated, continuously in \<open>z\<close>, into a rate that annihilates the gradient
  \<open>q + M (z - x)\<close> of the quadratic, at the cost of at most \<open>\<epsilon>\<close> in
  \<open>tr(M a)\<close>.\<close>

theorem covariation_rotSF_exists:
  fixes a M :: "real^'n::finite^'n" and q x :: "real^'n"
    and \<epsilon> r0 :: real
  assumes aS: "a \<in> S" and psda: "psd a" and aq: "a *v q = 0"
    and rot: "\<And>R b. orthogonal_matrix R \<Longrightarrow> b \<in> S \<Longrightarrow> R ** b ** transpose R \<in> S"
    and q0: "q \<noteq> 0"
    and eps: "0 < \<epsilon>" and r00: "0 < r0"
  obtains SF :: "real^'n \<Rightarrow> real^'n^'n" and r :: real where
    "0 < r" and "r \<le> r0"
    and "continuous_on UNIV SF"
    and "\<And>z. SF z ** transpose (SF z) \<in> S"
    and "\<And>z. transpose (SF z)
          *v (q + M *v (closest_point (cball x r) z - x)) = 0"
    and "\<And>z. \<bar>trace (M ** (SF z ** transpose (SF z))) - trace (M ** a)\<bar> \<le> \<epsilon>"
proof -
  have syma: "transpose a = a" using psda unfolding psd_def by blast
  obtain B and f :: "'n \<Rightarrow> real^'n" where Bon: "onormal B" and sp: "span B = UNIV"
    and finB: "finite B" and cardB: "card B = CARD('n)"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
    and bij: "bij_betw f (UNIV :: 'n set) B"
    using symmetric_eigendecomposition[OF syma] by metis
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
    using bounded_linear.pos_bounded[OF matrix_vector_mul_bounded_linear] by blast
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
          linear_continuous_on[OF matrix_vector_mul_bounded_linear] c1]) auto
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
  have inS: "SF z ** transpose (SF z) \<in> S" for z
    unfolding cov by (rule rot[OF rotm_orthogonal aS])
  have kill0: "(SF z ** transpose (SF z)) *v GG z = 0" for z
  proof -
    have o1: "transpose (rotm q (GG z)) ** rotm q (GG z) = mat 1"
      using rotm_orthogonal unfolding orthogonal_matrix_def by blast
    have rq: "rotm q (GG z) *v q = (norm q / norm (GG z)) *\<^sub>R GG z"
      by (rule rotm_apply[OF q0 Gnz okG])
    have cne: "norm q / norm (GG z) \<noteq> 0" using q0 Gnz by simp
    have e1: "(SF z ** transpose (SF z)) *v (rotm q (GG z) *v q)
        = rotm q (GG z) *v (a *v (transpose (rotm q (GG z)) *v (rotm q (GG z) *v q)))"
      unfolding cov by (metis matrix_vector_mul_assoc)
    have e2: "transpose (rotm q (GG z)) *v (rotm q (GG z) *v q) = q"
      by (metis o1 matrix_vector_mul_assoc matrix_vector_mul_lid)
    have "(SF z ** transpose (SF z)) *v (rotm q (GG z) *v q) = 0"
      unfolding e1 e2 aq by simp
    then have "(norm q / norm (GG z)) *\<^sub>R ((SF z ** transpose (SF z)) *v GG z) = 0"
      unfolding rq by (simp add: matrix_vector_mult_scaleR)
    then show ?thesis using cne by simp
  qed
  show ?thesis
  proof (rule that[of r SF])
    show "0 < r" by (rule rpos)
    show "r \<le> r0" by (rule rr0)
    show "continuous_on UNIV SF"
      unfolding SF_def by (rule rotSF_cont[OF less_imp_le[OF rpos] q0 okr])
    show "SF z ** transpose (SF z) \<in> S" for z
      by (rule inS)
    show "transpose (SF z) *v (q + M *v (closest_point (cball x r) z - x)) = 0"
      for z
    proof -
      have a0: "(SF z ** transpose (SF z)) *v GG z = 0"
        by (rule kill0)
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
  @{thm [source] covariation_rotSF_exists}, the Euler limit
  produces a class member whose paths grow along the quadratic, and at the
  stopping time \<open>min cc (pball_exit T x rr)\<close> the DPP functional is at
  least \<open>v(x) + mg\<close> almost surely -- the exit branch is paid by
  \<open>\<gamma> rr\<^sup>2\<close>, the no-exit branch by \<open>cc \<eta> / 2\<close>, and the horizon cap by
  \<open>T - v(x) > 0\<close>, which a nonzero gradient forces.  That contradicts
  @{thm [source] covariation_val_dpp_sup_ge_time}.\<close>

subsection \<open>Case 1, packaged for the envelope form\<close>

text \<open>The contradiction, read back as the positive statement the envelope
  supersolution definition wants: at any interior touching point with a
  nonzero gradient the usc envelope of the operator is at least one, since
  \<open>F \<le> F\<^sup>*\<close> (@{thm [source] ell_op_le_ell_op_usc}) turns a failed envelope
  inequality into a failed plain one.\<close>

subsection \<open>Conditional orthogonality: the kill checked at the point\<close>

text \<open>The Euler increments annihilate a continuous field wherever the field
  is killed by the volatility: the kill condition moves from a global
  hypothesis into the conclusion, checked at each grid point.  This lets a
  field be tangential only away from its singular centre, since the growth
  telescope only ever uses orthogonality at grid points inside the good
  region, where the kill holds.  The proof is an induction on the number
  of steps, with the implication carried through the glue.\<close>


theorem eulerp_orth_increments_cond:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n" and G :: "real^'n \<Rightarrow> real^'n"
    and x :: "real^'n" and h :: real
  assumes h0: "0 < h" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and Sc: "closed S" and Sv: "convex S"
    and SFc: "continuous_on UNIV SF"
    and SFs: "\<And>z. SF z ** transpose (SF z) \<in> S"
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
  have sets\<mu>: "sets ?\<mu>0 = sets (path_borel h :: ('n pairpath) measure)" by simp
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
  let ?Br = "(path_borel r :: ('n pairpath) measure)"
  let ?MR = "(path_borel (T' - r) :: ('n pairpath) measure)"
  let ?K = "\<lambda>\<omega> :: 'n pairpath.
      pair_law_of h (sbmpair (SF (fst (\<omega> r))) h) bm_paths"
  have hT: "T' - r = h" unfolding r_def T'_def by (simp add: algebra_simps)
  have r0: "0 \<le> r" unfolding r_def using h0' by simp
  have rleT: "r \<le> T'" unfolding r_def T'_def
    using h0' by (intro mult_right_mono) simp_all
  have Qc: "?Q \<in> covariation_class S r x"
    unfolding r_def by (rule eulerp_in_class[OF h0 B0 B D0 D Sc Sv SFc SFs])
  have PQ: "prob_space ?Q" by (rule covariation_class_prob[OF Qc])
  have setsQ: "sets ?Q = sets ?Br" by (rule covariation_class_sets[OF Qc])
  have mfst: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
      \<in> borel_measurable borel"
    using measurable_fst[of "borel :: (real^'n) measure"
        "borel :: (real^'n^'n) measure"] by (simp add: borel_prod)
  have eQ: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> r)) \<in> borel_measurable ?Q"
    by (rule measurable_compose[OF pair_law_eval_measurable[OF setsQ] mfst])
  have Kp: "?K \<in> ?Q \<rightarrow>\<^sub>M prob_algebra ?MR"
    unfolding hT by (rule measurable_compose[OF eQ sbm_kernel_package(1)[OF h0 B0 B D0 D Sc SFc SFs]])
  have Ee: "eulerp SF x h (Suc N) = kglue_law' r T' ?K ?Q"
    by (simp add: r_def T'_def)
  have msetP: "{\<omega> \<in> mspace (path_metric T' :: ('n pairpath) metric).
      \<forall>j<Suc (Suc N).
        transpose (SF (fst (\<omega> (real j * h))))
          *v G (fst (\<omega> (real j * h))) = 0 \<longrightarrow>
        G (fst (\<omega> (real j * h))) \<bullet>
          (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0}
      \<in> sets (path_borel T' :: ('n pairpath) measure)"
  proof -
    have spB: "space (path_borel T' :: ('n pairpath) measure)
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

text \<open>The quadratic lower bound along the grid: the kill and the trace margin
  are assumed only on the confinement region, and the conclusion holds
  on the event that the grid stays there.  The conditional orthogonality
  @{thm [source] eulerp_orth_increments_cond} checks the kill at each
  grid point, so no clamp or global hypothesis is needed.  This form
  admits a vector field that is tangential only on an annulus around its
  own centre.\<close>

theorem eulerp_quad_lower_region:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n" and M :: "real^'n^'n"
    and q x :: "real^'n" and h cm :: real and R :: "(real^'n) set"
  assumes h0: "0 < h" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and Sc: "closed S" and Sv: "convex S"
    and SFc: "continuous_on UNIV SF"
    and SFs: "\<And>z. SF z ** transpose (SF z) \<in> S"
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
          linear_continuous_on[OF matrix_vector_mul_bounded_linear] d]) auto
    show ?thesis by (intro continuous_intros mv)
  qed
  note orth = eulerp_orth_increments_cond[OF h0 B0 B D0 D Sc Sv SFc SFs Gc,
      simplified trivial_premise_simps]
  have Qc: "eulerp SF x h N \<in> covariation_class S (real (Suc N) * h) x"
    by (rule eulerp_in_class[OF h0 B0 B D0 D Sc Sv SFc SFs])
  have st: "AE \<omega> in eulerp SF x h N. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    by (rule covariation_class_start[OF Qc])
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
          by (simp add: trace_mult_diff matrix_scalar_ac scalar_matrix_assoc[symmetric] trace_scaleR)
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

text \<open>\<open>quad_diff_bound_gen\<close> lives in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


theorem eulerp_bad_event_null_region:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n" and M :: "real^'n^'n"
    and q x :: "real^'n" and c cm t \<beta> Rn :: real
    and RO :: "(real^'n) set"
  assumes c0: "0 < c" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and Sc: "closed S" and Sv: "convex S"
    and SFc: "continuous_on UNIV SF"
    and SFs: "\<And>z. SF z ** transpose (SF z) \<in> S"
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
  define A where "A = 4 * c * xiC M D / \<beta>\<^sup>2"
  define Bt where "Bt = real (CARD('n)) ^ 5 * 8 * D\<^sup>2 / \<delta>^4"
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
    have bound: "measure (eulerp SF x (?h i) i) ?U
        \<le> A * ?h i + Bt * (?h i)\<^sup>2"
      if hs: "?h i \<le> h\<^sub>0" for i
    proof -
      define h where "h = ?h i"
      have hs': "h \<le> h\<^sub>0" using hs unfolding h_def .
      have h0: "0 < h" unfolding h_def using c0 by simp
      have hc: "real (Suc i) * h = c" unfolding h_def by simp
      let ?Q = "eulerp SF x h i"
      have Qc: "?Q \<in> covariation_class S c x"
        unfolding h_def by (rule eulerp_seq_in_class[OF c0 B0 B D0 D Sc Sv SFc SFs])
      have setsQ: "sets ?Q = sets (path_borel c :: ('n pairpath) measure)"
        by (rule covariation_class_sets[OF Qc])
      have spQ: "space ?Q = mspace (path_metric c :: ('n pairpath) metric)"
        by (rule space_of_path_sets[OF setsQ])
      interpret PQ: prob_space ?Q by (rule covariation_class_prob[OF Qc])
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
      have mE1: "measure ?Q E1 \<le> real m * xiC M D * h\<^sup>2 / (\<beta> / 2)\<^sup>2"
        unfolding E1_def
        by (rule eulerp_Xi_chebyshev[OF h0 B0 B D0 D Sc Sv SFc SFs mSuc b20])
      have mE2: "measure ?Q E2
          \<le> real (CARD('n)) ^ 5 * (8 * D\<^sup>2 * (t - real m * h)\<^sup>2) / \<delta>^4"
        unfolding E2_def
        by (rule covariation_class_increment_tail_norm[OF c0 B0 B D0 D Qc mh0 mh_le tc \<delta>0])
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
        by (rule eulerp_quad_lower_region[OF h0 B0 B D0 D Sc Sv SFc SFs sym kill marg])
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
      have n1: "real m * xiC M D * h\<^sup>2 / (\<beta> / 2)\<^sup>2 \<le> A * h"
      proof -
        have mhc: "real m * h \<le> c"
        proof -
          have "real m \<le> real (Suc i)" using mSuc by simp
          then have "real m * h \<le> real (Suc i) * h"
            using h0 by (intro mult_right_mono) simp_all
          then show ?thesis using hc by simp
        qed
        have e1: "real m * xiC M D * h\<^sup>2 = real m * h * xiC M D * h"
          by (simp add: power2_eq_square algebra_simps)
        have e2: "real m * h * xiC M D * h \<le> c * xiC M D * h"
          by (intro mult_right_mono mult_right_mono[OF mhc xiC_nonneg])
            (use h0 in simp_all)
        have num: "real m * xiC M D * h\<^sup>2 \<le> c * xiC M D * h"
          unfolding e1 by (rule e2)
        have "real m * xiC M D * h\<^sup>2 / (\<beta> / 2)\<^sup>2
            \<le> c * xiC M D * h / (\<beta> / 2)\<^sup>2"
          by (rule divide_right_mono[OF num]) simp
        also have "\<dots> = A * h"
          unfolding A_def using b0 by (simp add: field_simps)
        finally show ?thesis .
      qed
      have n2: "real (CARD('n)) ^ 5 * (8 * D\<^sup>2 * (t - real m * h)\<^sup>2) / \<delta>^4
          \<le> Bt * h\<^sup>2"
      proof -
        have sq: "(t - real m * h)\<^sup>2 \<le> h\<^sup>2"
          using t_mh mh_le by (intro power_mono) simp_all
        have inner8: "8 * D\<^sup>2 * (t - real m * h)\<^sup>2 \<le> 8 * D\<^sup>2 * h\<^sup>2"
          by (intro mult_left_mono[OF sq]) simp
        have "real (CARD('n)) ^ 5 * (8 * D\<^sup>2 * (t - real m * h)\<^sup>2)
            \<le> real (CARD('n)) ^ 5 * (8 * D\<^sup>2 * h\<^sup>2)"
          by (intro mult_left_mono[OF inner8]) simp
        then have "real (CARD('n)) ^ 5
            * (8 * D\<^sup>2 * (t - real m * h)\<^sup>2) / \<delta>^4
            \<le> real (CARD('n)) ^ 5 * (8 * D\<^sup>2 * h\<^sup>2) / \<delta>^4"
          by (intro divide_right_mono) simp_all
        also have "\<dots> = Bt * h\<^sup>2"
          unfolding Bt_def using \<delta>0 by (simp add: field_simps)
        finally show ?thesis .
      qed
      have "measure ?Q ?U \<le> A * h + Bt * h\<^sup>2"
        using s1 s2 mE1 mE2 n1 n2 by linarith
      then show ?thesis unfolding h_def .
    qed
    have hlim: "(\<lambda>i. ?h i) \<longlonglongrightarrow> 0"
      using tendsto_mult[OF tendsto_const LIMSEQ_inverse_real_of_nat, of c]
      by (simp add: divide_inverse)
    have ev: "\<forall>\<^sub>F i in sequentially.
        measure (eulerp SF x (?h i) i) ?U \<le> A * ?h i + Bt * (?h i)\<^sup>2"
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
    have glim: "(\<lambda>i. A * ?h i + Bt * (?h i)\<^sup>2) \<longlonglongrightarrow> 0"
    proof -
      have "(\<lambda>i. A * ?h i + Bt * (?h i)\<^sup>2) \<longlonglongrightarrow> A * 0 + Bt * 0\<^sup>2"
        by (intro tendsto_add tendsto_mult tendsto_const
            tendsto_power hlim)
      then show ?thesis by simp
    qed
    show ?thesis
      by (rule tendsto_sandwich[OF ev0 ev tendsto_const glim])
  qed
qed

subsection \<open>One limit member, one or two quadratics, one region\<close>

text \<open>The region version of the almost-sure growth statement: a limit member
  of the Euler laws gives every quadratic package against the field its
  growth, almost surely, while the path stays in the region.  The weak-limit
  transfer serves every vanishing open event of a single member
  simultaneously, so several growth directions hold together.  For the
  tangential field with \<open>\<plusminus>(2(x-y\<^sub>0), 2\<cdot>1)\<close> this pins \<open>|X\<^sub>t - y\<^sub>0|\<^sup>2\<close> to the
  deterministic line \<open>|x - y\<^sub>0|\<^sup>2 + (n-1) t\<close> while the path stays in the
  region.\<close>

lemma eulerp_limit_member_good_region:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n" and M :: "real^'n^'n"
    and q x :: "real^'n" and c cm Rn :: real
    and RO :: "(real^'n) set" and P :: "('n pairpath) measure"
  assumes c0: "0 < c" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and Sc: "closed S" and Sv: "convex S"
    and SFc: "continuous_on UNIV SF"
    and SFs: "\<And>z. SF z ** transpose (SF z) \<in> S"
    and sym: "transpose M = M"
    and ROo: "open RO"
    and ROb: "\<And>z. z \<in> RO \<Longrightarrow> norm (z - x) \<le> Rn"
    and kill: "\<And>z. z \<in> RO \<Longrightarrow>
        transpose (SF z) *v (q + M *v (z - x)) = 0"
    and marg: "\<And>z. z \<in> RO \<Longrightarrow>
        cm \<le> trace (M ** (SF z ** transpose (SF z)))"
    and P: "P \<in> covariation_class S c x"
    and Praw: "\<forall>U b'. openin (mtopology_of (path_metric c :: ('n pairpath) metric)) U \<longrightarrow>
      (\<lambda>i. measure (eulerp SF x (c / real (Suc i)) i) U) \<longlonglongrightarrow> b' \<longrightarrow>
      measure P U \<le> b'"
  shows "AE \<omega> in P. \<forall>t.
      0 < t \<longrightarrow> t \<le> c \<longrightarrow> (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> RO) \<longrightarrow>
      t * cm / 2 \<le> q \<bullet> (fst (\<omega> t) - x)
        + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x)))"
proof -
  let ?pm = "path_metric c :: ('n pairpath) metric"
  define U1 where "U1 = (\<lambda>r \<beta> :: real. {\<omega> \<in> mspace ?pm.
      (\<forall>s\<in>{0..r}. fst (\<omega> s) \<in> RO)
      \<and> q \<bullet> (fst (\<omega> r) - x)
        + (1/2) * ((fst (\<omega> r) - x) \<bullet> (M *v (fst (\<omega> r) - x)))
        < r * cm / 2 - \<beta>})"
  interpret FP: prob_space P by (rule covariation_class_prob[OF P])
  have setsP: "sets P = sets (borel_of (mtopology_of ?pm))"
    by (rule covariation_class_sets[OF P])
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
      by (rule eulerp_bad_event_null_region[OF c0 B0 B D0 D Sc Sv SFc SFs sym
          ROb kill marg r0 rc inv0])
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
  have sp: "AE \<omega> in P. \<omega> \<in> space P" by (rule AE_space)
  show ?thesis
    using AEall1 sp
  proof (eventually_elim)
    case (elim \<omega>)
    have wm: "\<omega> \<in> mspace ?pm" using elim(2) by (simp add: spaceP)
    have notin1: "\<And>r n. r \<in> I \<Longrightarrow>
        \<omega> \<notin> U1 r (inverse (real (Suc n)))"
      using elim(1) by blast
    show ?case
    proof (intro allI impI)
      fix t assume t0: "0 < t" and tc: "t \<le> c"
        and inb: "\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> RO"
      have rat1: "r * cm / 2 \<le> q \<bullet> (fst (\<omega> r) - x)
          + (1/2) * ((fst (\<omega> r) - x) \<bullet> (M *v (fst (\<omega> r) - x)))"
        if rQ: "r \<in> \<rat>" and r0: "0 < r" and rc: "r \<le> c"
          and rball: "\<forall>s\<in>{0..r}. fst (\<omega> s) \<in> RO" for r
      proof (rule ccontr)
        assume nle: "\<not> r * cm / 2 \<le> q \<bullet> (fst (\<omega> r) - x)
            + (1/2) * ((fst (\<omega> r) - x) \<bullet> (M *v (fst (\<omega> r) - x)))"
        have pos: "0 < r * cm / 2 - (q \<bullet> (fst (\<omega> r) - x)
            + (1/2) * ((fst (\<omega> r) - x) \<bullet> (M *v (fst (\<omega> r) - x))))"
          using nle by simp
        obtain n where nsm: "inverse (real (Suc n))
            < r * cm / 2 - (q \<bullet> (fst (\<omega> r) - x)
              + (1/2) * ((fst (\<omega> r) - x) \<bullet> (M *v (fst (\<omega> r) - x))))"
          using reals_Archimedean[OF pos] by auto
        have drop: "q \<bullet> (fst (\<omega> r) - x)
            + (1/2) * ((fst (\<omega> r) - x) \<bullet> (M *v (fst (\<omega> r) - x)))
            < r * cm / 2 - inverse (real (Suc n))"
          using nsm by linarith
        have "\<omega> \<in> U1 r (inverse (real (Suc n)))"
          unfolding U1_def using wm rball drop by auto
        moreover have "r \<in> I" unfolding I_def using rQ r0 rc by simp
        ultimately show False using notin1 by blast
      qed
      show "t * cm / 2 \<le> q \<bullet> (fst (\<omega> t) - x)
          + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x)))"
      proof (rule quad_good_rat_to_real_region[OF wm rat1 t0 tc])
        fix s assume "s \<in> {0..t}"
        then show "fst (\<omega> s) \<in> RO" using inb by blast
      qed
    qed
  qed
qed

theorem eulerp_limit_good_region:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n" and M :: "real^'n^'n"
    and q x :: "real^'n" and c cm Rn :: real
    and RO :: "(real^'n) set"
  assumes c0: "0 < c" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and Sc: "closed S" and Sv: "convex S"
    and SFc: "continuous_on UNIV SF"
    and SFs: "\<And>z. SF z ** transpose (SF z) \<in> S"
    and sym: "transpose M = M"
    and ROo: "open RO"
    and ROb: "\<And>z. z \<in> RO \<Longrightarrow> norm (z - x) \<le> Rn"
    and kill: "\<And>z. z \<in> RO \<Longrightarrow>
        transpose (SF z) *v (q + M *v (z - x)) = 0"
    and marg: "\<And>z. z \<in> RO \<Longrightarrow>
        cm \<le> trace (M ** (SF z ** transpose (SF z)))"
  shows "\<exists>P \<in> covariation_class S c x. AE \<omega> in P. \<forall>t.
      0 < t \<longrightarrow> t \<le> c \<longrightarrow> (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> RO) \<longrightarrow>
      t * cm / 2 \<le> q \<bullet> (fst (\<omega> t) - x)
        + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x)))"
  using eulerp_weak_limit[OF c0 B0 B D0 D Sc Sv SFc SFs, of x, simplified trivial_premise_simps]
    eulerp_limit_member_good_region[OF c0 B0 B D0 D Sc Sv SFc SFs sym ROo ROb kill marg, simplified trivial_premise_simps]
  by blast

theorem eulerp_limit_good2_region:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n" and M1 M2 :: "real^'n^'n"
    and q1 q2 x :: "real^'n" and c cm1 cm2 Rn :: real
    and RO :: "(real^'n) set"
  assumes c0: "0 < c" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and Sc: "closed S" and Sv: "convex S"
    and SFc: "continuous_on UNIV SF"
    and SFs: "\<And>z. SF z ** transpose (SF z) \<in> S"
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
  shows "\<exists>P \<in> covariation_class S c x. AE \<omega> in P. \<forall>t.
      0 < t \<longrightarrow> t \<le> c \<longrightarrow> (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> RO) \<longrightarrow>
      (t * cm1 / 2 \<le> q1 \<bullet> (fst (\<omega> t) - x)
        + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M1 *v (fst (\<omega> t) - x))))
      \<and> (t * cm2 / 2 \<le> q2 \<bullet> (fst (\<omega> t) - x)
        + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M2 *v (fst (\<omega> t) - x))))"
proof -
  obtain P where P: "P \<in> covariation_class S c x"
    and Praw: "\<forall>U b'. openin (mtopology_of (path_metric c :: ('n pairpath) metric)) U \<longrightarrow>
      (\<lambda>i. measure (eulerp SF x (c / real (Suc i)) i) U) \<longlonglongrightarrow> b' \<longrightarrow>
      measure P U \<le> b'"
    using eulerp_weak_limit[OF c0 B0 B D0 D Sc Sv SFc SFs, simplified trivial_premise_simps] by blast
  have A1: "AE \<omega> in P. \<forall>t. 0 < t \<longrightarrow> t \<le> c \<longrightarrow> (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> RO) \<longrightarrow>
      t * cm1 / 2 \<le> q1 \<bullet> (fst (\<omega> t) - x)
        + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M1 *v (fst (\<omega> t) - x)))"
    by (rule eulerp_limit_member_good_region[OF c0 B0 B D0 D Sc Sv SFc SFs sym1 ROo ROb kill1 marg1 P Praw])
  have A2: "AE \<omega> in P. \<forall>t. 0 < t \<longrightarrow> t \<le> c \<longrightarrow> (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> RO) \<longrightarrow>
      t * cm2 / 2 \<le> q2 \<bullet> (fst (\<omega> t) - x)
        + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M2 *v (fst (\<omega> t) - x)))"
    by (rule eulerp_limit_member_good_region[OF c0 B0 B D0 D Sc Sv SFc SFs sym2 ROo ROb kill2 marg2 P Praw])
  show ?thesis
    by (intro bexI[OF _ P] eventually_mono[OF AE_conjI[OF A1 A2]]) blast
qed

(*<*)
end
(*>*)
