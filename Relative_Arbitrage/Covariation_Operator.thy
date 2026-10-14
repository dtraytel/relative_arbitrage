section \<open>The operator of an abstract constraint set is a geometric operator\<close>

(*<*)
theory Covariation_Operator
  imports
    "Geometric_Viscosity_Comparison.Comparison_Two_Domain" Value_Function_Supersolution
begin
(*>*)

text \<open>The comparison chain of Section 4 holds for every operator of the locale
  @{locale geometric_operator}.  This theory shows that the operator
  \<^const>\<open>covariation_op\<close> of a set \<open>S\<close> of covariation rates is one, as soon as
  \<open>S\<close> is bounded, consists of positive semidefinite matrices, is invariant under
  orthogonal conjugation, and contains, for every gradient \<open>p\<close>, a rate that
  annihilates \<open>p\<close>.  Neither closedness nor convexity of \<open>S\<close> is needed.  The
  continuity of the operator off \<open>p = 0\<close>, which the paper reads off the closed
  formula (3.5) of Lemma 3.1, follows here from the rotation invariance alone:
  near \<open>p\<close>, the gradient \<open>p'\<close> is the image of \<open>p\<close> under a rotation close
  to the identity.\<close>

section \<open>Envelopes from local bounds\<close>

text \<open>Generic facts about the envelopes @{const op_lsc} and @{const op_usc} of
  @{theory Geometric_Viscosity_Comparison.Geometric_Operator}.\<close>

lemma op_lsc_eq_of_local_lower:
  fixes F :: "'a::metric_space \<Rightarrow> 'b::metric_space \<Rightarrow> real"
  assumes lb: "\<And>\<epsilon>. 0 < \<epsilon> \<Longrightarrow> \<exists>e>0. \<forall>w\<in>ball (p, M) e. F p M - \<epsilon> \<le> F (fst w) (snd w)"
  shows "op_lsc F p M = ereal (F p M)"
proof (rule antisym[OF op_lsc_le])
  show "ereal (F p M) \<le> op_lsc F p M"
  proof (rule ereal_le_epsilon2)
    fix \<epsilon> :: real assume \<epsilon>: "0 < \<epsilon>"
    obtain e where e: "0 < e" and le: "\<forall>w\<in>ball (p, M) e. F p M - \<epsilon> \<le> F (fst w) (snd w)"
      using lb[OF \<epsilon>] by blast
    have "ereal (F p M - \<epsilon>) \<le> (INF w \<in> ball (p, M) e. ereal (F (fst w) (snd w)))"
      by (rule INF_greatest) (use le in simp)
    also have "\<dots> \<le> op_lsc F p M"
      unfolding op_lsc_def by (rule SUP_upper) (use e in simp)
    finally have "ereal (F p M - \<epsilon>) + ereal \<epsilon> \<le> op_lsc F p M + ereal \<epsilon>"
      by (rule add_right_mono)
    then show "ereal (F p M) \<le> op_lsc F p M + ereal \<epsilon>" by simp
  qed
qed

lemma op_usc_le_of_ball:
  fixes F :: "'a::metric_space \<Rightarrow> 'b::metric_space \<Rightarrow> real"
  assumes e: "0 < e" and le: "\<And>w. w \<in> ball (p, M) e \<Longrightarrow> F (fst w) (snd w) \<le> c"
  shows "op_usc F p M \<le> ereal c"
  unfolding op_usc_def
  by (rule INF_lower2[of e]) (use e le in \<open>auto intro!: SUP_least\<close>)

lemma op_usc_eq_of_local_upper:
  fixes F :: "'a::metric_space \<Rightarrow> 'b::metric_space \<Rightarrow> real"
  assumes ub: "\<And>\<epsilon>. 0 < \<epsilon> \<Longrightarrow> \<exists>e>0. \<forall>w\<in>ball (p, M) e. F (fst w) (snd w) \<le> F p M + \<epsilon>"
  shows "op_usc F p M = ereal (F p M)"
proof (rule antisym[OF _ op_usc_ge])
  show "op_usc F p M \<le> ereal (F p M)"
  proof (rule ereal_le_epsilon2)
    fix \<epsilon> :: real assume \<epsilon>: "0 < \<epsilon>"
    obtain e where e: "0 < e" and le: "\<forall>w\<in>ball (p, M) e. F (fst w) (snd w) \<le> F p M + \<epsilon>"
      using ub[OF \<epsilon>] by blast
    have "op_usc F p M \<le> ereal (F p M + \<epsilon>)"
      by (rule op_usc_le_of_ball[OF e]) (use le in blast)
    then show "op_usc F p M \<le> ereal (F p M) + ereal \<epsilon>" by simp
  qed
qed

text \<open>At a point of continuity both envelopes equal the operator.\<close>

lemma op_envelopes_eq_of_isCont:
  fixes F :: "'a::metric_space \<Rightarrow> 'b::metric_space \<Rightarrow> real"
  assumes c: "isCont (\<lambda>w. F (fst w) (snd w)) (p, M)"
  shows "op_lsc F p M = ereal (F p M)" and "op_usc F p M = ereal (F p M)"
proof -
  have near: "\<exists>e>0. \<forall>w\<in>ball (p, M) e. \<bar>F (fst w) (snd w) - F p M\<bar> < \<epsilon>"
    if \<epsilon>: "0 < \<epsilon>" for \<epsilon>
  proof -
    obtain e where e: "0 < e"
      and d: "\<And>w. dist w (p, M) < e \<Longrightarrow> dist (F (fst w) (snd w)) (F p M) < \<epsilon>"
      using c[unfolded continuous_at_eps_delta] \<epsilon> by fastforce
    have "\<bar>F (fst w) (snd w) - F p M\<bar> < \<epsilon>" if "w \<in> ball (p, M) e" for w
      using d[of w] that by (simp add: dist_real_def dist_commute)
    then show ?thesis using e by blast
  qed
  show "op_lsc F p M = ereal (F p M)"
  proof (rule op_lsc_eq_of_local_lower)
    fix \<epsilon> :: real assume "0 < \<epsilon>"
    then obtain e where "0 < e" "\<forall>w\<in>ball (p, M) e. \<bar>F (fst w) (snd w) - F p M\<bar> < \<epsilon>"
      using near by blast
    then show "\<exists>e>0. \<forall>w\<in>ball (p, M) e. F p M - \<epsilon> \<le> F (fst w) (snd w)"
      by (intro exI[of _ e]) (auto simp: abs_less_iff)
  qed
  show "op_usc F p M = ereal (F p M)"
  proof (rule op_usc_eq_of_local_upper)
    fix \<epsilon> :: real assume "0 < \<epsilon>"
    then obtain e where "0 < e" "\<forall>w\<in>ball (p, M) e. \<bar>F (fst w) (snd w) - F p M\<bar> < \<epsilon>"
      using near by blast
    then show "\<exists>e>0. \<forall>w\<in>ball (p, M) e. F (fst w) (snd w) \<le> F p M + \<epsilon>"
      by (intro exI[of _ e]) (auto simp: abs_less_iff)
  qed
qed

section \<open>Matrix algebra and continuity\<close>

lemma trace_mult_eq_inner_transpose:
  fixes X a :: "real^'n::finite^'n"
  shows "trace (X ** a) = inner X (transpose a)"
  by (simp add: trace_def matrix_matrix_mult_def inner_vec_def transpose_def)

lemma trace_mult_sym_abs_le:
  fixes X a :: "real^'n::finite^'n"
  assumes sym: "transpose a = a"
  shows "\<bar>trace (X ** a)\<bar> \<le> norm X * norm a"
  using Cauchy_Schwarz_ineq2[of X a] unfolding trace_mult_eq_inner_transpose sym .

lemma tendsto_matrix_mult:
  fixes f g :: "'a \<Rightarrow> real^'n::finite^'n"
  assumes f: "(f \<longlongrightarrow> A) F" and g: "(g \<longlongrightarrow> C) F"
  shows "((\<lambda>x. f x ** g x) \<longlongrightarrow> A ** C) F"
proof (intro vec_tendstoI)
  fix i j
  have "((\<lambda>x. \<Sum>k\<in>UNIV. f x $ i $ k * g x $ k $ j) \<longlongrightarrow> (\<Sum>k\<in>UNIV. A $ i $ k * C $ k $ j)) F"
    by (intro tendsto_sum tendsto_mult tendsto_vec_nth f g)
  then show "((\<lambda>x. (f x ** g x) $ i $ j) \<longlongrightarrow> (A ** C) $ i $ j) F"
    by (simp add: matrix_matrix_mult_def)
qed

lemma tendsto_transpose_matrix:
  fixes f :: "'a \<Rightarrow> real^'n::finite^'n"
  assumes f: "(f \<longlongrightarrow> A) F"
  shows "((\<lambda>x. transpose (f x)) \<longlongrightarrow> transpose A) F"
proof (intro vec_tendstoI)
  fix i j
  have "((\<lambda>x. f x $ j $ i) \<longlongrightarrow> A $ j $ i) F"
    by (intro tendsto_vec_nth f)
  then show "((\<lambda>x. transpose (f x) $ i $ j) \<longlongrightarrow> transpose A $ i $ j) F"
    by (simp add: transpose_def)
qed

text \<open>The two-reflection rotation \<^const>\<open>rotm\<close> carrying \<open>p\<close> onto the ray
  through \<open>w\<close> is the identity at \<open>w = p\<close> and depends continuously on \<open>w\<close>.\<close>

lemma rotm_self_mat: "rotm q q = mat 1"
  by (rule iffD2[OF matrix_eq]) (simp add: rotm_self)

lemma rotm_isCont:
  fixes p :: "real^'n::finite"
  assumes p0: "p \<noteq> 0"
  shows "isCont (rotm p) p"
proof -
  define H where "H = {w :: real^'n. 0 < norm p * norm w + p \<bullet> w}"
  have oH: "open H"
    unfolding H_def by (intro open_Collect_less continuous_intros)
  have pH: "p \<in> H"
    unfolding H_def using p0 by (simp add: dot_square_norm power2_eq_square)
  have cc: "isCont (\<lambda>w. rotm p w *v axis j 1) p" for j
  proof -
    have "continuous_on H (\<lambda>w. rotm p w *v axis j 1)"
      by (rule rotm_vec_cont[OF p0]) (simp add: H_def)
    then show ?thesis using pH unfolding continuous_on_eq_continuous_at[OF oH] by blast
  qed
  have col: "rotm p w $ i $ j = (rotm p w *v axis j 1) $ i" for w i j
    by (simp add: matrix_vector_mult_basis column_def)
  have ent: "((\<lambda>w. rotm p w $ i $ j) \<longlongrightarrow> rotm p p $ i $ j) (at p)" for i j
  proof -
    have "((\<lambda>w. (rotm p w *v axis j 1) $ i) \<longlongrightarrow> (rotm p p *v axis j 1) $ i) (at p)"
      by (rule tendsto_vec_nth) (use cc[of j] in \<open>simp add: isCont_def\<close>)
    then show ?thesis by (simp only: col)
  qed
  show ?thesis
    unfolding isCont_def by (intro vec_tendstoI ent)
qed

section \<open>The real-valued operator\<close>

text \<open>When every gradient is annihilated by some rate in \<open>S\<close> and \<open>S\<close> is
  bounded, the infimum defining \<^const>\<open>covariation_op\<close> is finite; its real
  version is the operator the locale @{locale geometric_operator} expects.\<close>

definition covariation_op_real ::
  "(real^'n::finite^'n) set \<Rightarrow> real^'n \<Rightarrow> real^'n^'n \<Rightarrow> real" where
  "covariation_op_real S p M = Inf ((\<lambda>a. - trace (M ** a) / 2) ` {a \<in> S. a *v p = 0})"

lemma covariation_trace_le:
  fixes M a :: "real^'n::finite^'n"
  assumes B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and Spsd: "\<And>a. a \<in> S \<Longrightarrow> psd a" and a: "a \<in> S"
  shows "\<bar>trace (M ** a)\<bar> \<le> norm M * B"
proof -
  have "\<bar>trace (M ** a)\<bar> \<le> norm M * norm a"
    by (rule trace_mult_sym_abs_le) (use Spsd[OF a] in \<open>simp add: psd_def\<close>)
  also have "\<dots> \<le> norm M * B"
    by (rule mult_left_mono[OF B[OF a] norm_ge_zero])
  finally show ?thesis .
qed

lemma covariation_op_real_bdd_below:
  fixes M :: "real^'n::finite^'n"
  assumes B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and Spsd: "\<And>a. a \<in> S \<Longrightarrow> psd a"
  shows "bdd_below ((\<lambda>a. - trace (M ** a) / 2) ` {a \<in> S. a *v p = 0})"
proof (rule bdd_belowI2[of _ "- (norm M * B) / 2"])
  fix a assume "a \<in> {a \<in> S. a *v p = 0}"
  then have a: "a \<in> S" by simp
  have "\<bar>trace (M ** a)\<bar> \<le> norm M * B" by (rule covariation_trace_le[OF B Spsd a])
  then show "- (norm M * B) / 2 \<le> - trace (M ** a) / 2" by (simp add: abs_le_iff)
qed

lemma covariation_op_real_le_witness:
  fixes M a :: "real^'n::finite^'n"
  assumes B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and Spsd: "\<And>a. a \<in> S \<Longrightarrow> psd a"
    and a: "a \<in> S" and ap: "a *v p = 0"
  shows "covariation_op_real S p M \<le> - trace (M ** a) / 2"
  unfolding covariation_op_real_def
  by (rule cInf_lower[OF _ covariation_op_real_bdd_below[OF B Spsd]]) (use a ap in blast)

lemma covariation_op_real_greatest:
  fixes M :: "real^'n::finite^'n" and p :: "real^'n"
  assumes kill: "\<And>p :: real^'n. \<exists>a\<in>S. a *v p = 0"
    and ge: "\<And>a. a \<in> S \<Longrightarrow> a *v p = 0 \<Longrightarrow> c \<le> - trace (M ** a) / 2"
  shows "c \<le> covariation_op_real S p M"
  unfolding covariation_op_real_def
  by (rule cInf_greatest) (use kill[of p] ge in auto)

lemma ereal_covariation_op_real:
  fixes M :: "real^'n::finite^'n" and p :: "real^'n"
  assumes B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and Spsd: "\<And>a. a \<in> S \<Longrightarrow> psd a"
    and kill: "\<And>p :: real^'n. \<exists>a\<in>S. a *v p = 0"
  shows "ereal (covariation_op_real S p M) = covariation_op S p M"
proof -
  have ne: "(\<lambda>a. - trace (M ** a) / 2) ` {a \<in> S. a *v p = 0} \<noteq> {}"
    using kill[of p] by blast
  have bdd: "bdd_below ((\<lambda>a. - trace (M ** a) / 2) ` {a \<in> S. a *v p = 0})"
    by (rule covariation_op_real_bdd_below[OF B Spsd])
  show ?thesis
    unfolding covariation_op_real_def covariation_op_def ereal_Inf'[OF bdd ne] image_image ..
qed

text \<open>The operator is Lipschitz in the Hessian, with constant \<open>B/2\<close>, and
  bounded above by \<open>B |M|/2\<close>.\<close>

lemma covariation_op_real_lipschitz:
  fixes M N :: "real^'n::finite^'n" and p :: "real^'n"
  assumes B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and Spsd: "\<And>a. a \<in> S \<Longrightarrow> psd a"
    and kill: "\<And>p :: real^'n. \<exists>a\<in>S. a *v p = 0"
  shows "covariation_op_real S p M \<le> covariation_op_real S p N + B / 2 * norm (M - N)"
proof -
  have "covariation_op_real S p M - B / 2 * norm (M - N) \<le> covariation_op_real S p N"
  proof (rule covariation_op_real_greatest[OF kill])
    fix a assume a: "a \<in> S" and ap: "a *v p = 0"
    have "covariation_op_real S p M \<le> - trace (M ** a) / 2"
      by (rule covariation_op_real_le_witness[OF B Spsd a ap])
    moreover have "\<bar>trace ((M - N) ** a)\<bar> \<le> norm (M - N) * B"
      by (rule covariation_trace_le[OF B Spsd a])
    moreover have "trace ((M - N) ** a) = trace (M ** a) - trace (N ** a)"
      by (simp add: matrix_mul_diff_left trace_sub)
    ultimately show "covariation_op_real S p M - B / 2 * norm (M - N) \<le> - trace (N ** a) / 2"
      by (simp add: abs_le_iff algebra_simps)
  qed
  then show ?thesis by simp
qed

lemma covariation_op_real_upper:
  fixes M :: "real^'n::finite^'n" and p :: "real^'n"
  assumes B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and Spsd: "\<And>a. a \<in> S \<Longrightarrow> psd a"
    and kill: "\<And>p :: real^'n. \<exists>a\<in>S. a *v p = 0"
  shows "covariation_op_real S p M \<le> B / 2 * norm M"
proof -
  obtain a where a: "a \<in> S" and ap: "a *v p = 0" using kill[of p] by blast
  have "covariation_op_real S p M \<le> - trace (M ** a) / 2"
    by (rule covariation_op_real_le_witness[OF B Spsd a ap])
  moreover have "\<bar>trace (M ** a)\<bar> \<le> norm M * B"
    by (rule covariation_trace_le[OF B Spsd a])
  ultimately show ?thesis by (simp add: abs_le_iff algebra_simps)
qed

section \<open>The invariances\<close>

lemma covariation_op_real_dilation:
  fixes M :: "real^'n::finite^'n" and p :: "real^'n"
  assumes c: "c \<noteq> 0"
  shows "covariation_op_real S (c *\<^sub>R p) M = covariation_op_real S p M"
proof -
  have "{a \<in> S. a *v (c *\<^sub>R p) = 0} = {a \<in> S. a *v p = 0}"
    using c by (simp add: matrix_vector_mult_scaleR)
  then show ?thesis unfolding covariation_op_real_def by simp
qed

lemma covariation_op_real_rotation:
  fixes M R :: "real^'n::finite^'n" and p :: "real^'n"
  assumes rot: "\<And>R b. orthogonal_matrix R \<Longrightarrow> b \<in> S \<Longrightarrow> R ** b ** transpose R \<in> S"
    and orth: "orthogonal_matrix R"
  shows "covariation_op_real S (R *v p) (R ** M ** transpose R) = covariation_op_real S p M"
proof -
  have o1: "transpose R ** R = mat 1" and o2: "R ** transpose R = mat 1"
    using orth unfolding orthogonal_matrix_def by blast+
  have pback: "transpose R *v (R *v p) = p"
    by (metis o1 matrix_vector_mul_assoc matrix_vector_mul_lid)
  have bij: "(\<lambda>a. R ** a ** transpose R) ` {a \<in> S. a *v p = 0} = {a \<in> S. a *v (R *v p) = 0}"
  proof
    show "(\<lambda>a. R ** a ** transpose R) ` {a \<in> S. a *v p = 0} \<subseteq> {a \<in> S. a *v (R *v p) = 0}"
    proof clarify
      fix a assume a: "a \<in> S" and ap: "a *v p = 0"
      have "(R ** a ** transpose R) *v (R *v p) = R *v (a *v ((transpose R ** R) *v p))"
        by (simp add: matrix_vector_mul_assoc matrix_mul_assoc)
      also have "\<dots> = 0" by (simp add: o1 ap)
      finally show "R ** a ** transpose R \<in> S \<and> (R ** a ** transpose R) *v (R *v p) = 0"
        using rot[OF orth a] by blast
    qed
    show "{a \<in> S. a *v (R *v p) = 0} \<subseteq> (\<lambda>a. R ** a ** transpose R) ` {a \<in> S. a *v p = 0}"
    proof clarify
      fix b assume b: "b \<in> S" and bp: "b *v (R *v p) = 0"
      have inS: "transpose R ** b ** R \<in> S"
        using rot[of "transpose R" b] orth b by simp
      have "(transpose R ** b ** R) *v p = transpose R *v (b *v (R *v p))"
        by (metis matrix_vector_mul_assoc)
      also have "\<dots> = 0" by (simp add: bp)
      finally have kp: "(transpose R ** b ** R) *v p = 0" .
      have "b = R ** (transpose R ** b ** R) ** transpose R"
        by (rule conj_orth_inv[OF orth, symmetric])
      then show "b \<in> (\<lambda>a. R ** a ** transpose R) ` {a \<in> S. a *v p = 0}"
        using inS kp by (metis (mono_tags, lifting) image_eqI mem_Collect_eq)
    qed
  qed
  have treq: "trace ((R ** M ** transpose R) ** (R ** a ** transpose R)) = trace (M ** a)"
    for a :: "real^'n^'n"
  proof -
    have "(R ** M ** transpose R) ** (R ** a ** transpose R)
        = R ** M ** (transpose R ** R) ** a ** transpose R"
      by (simp add: matrix_mul_assoc)
    also have "\<dots> = R ** (M ** a) ** transpose R"
      unfolding o1 by (simp add: matrix_mul_assoc)
    finally have "trace ((R ** M ** transpose R) ** (R ** a ** transpose R))
        = trace (R ** (M ** a) ** transpose R)" by simp
    also have "\<dots> = trace (transpose R ** (R ** (M ** a)))"
      by (rule trace_mul_sym)
    also have "\<dots> = trace ((transpose R ** R) ** (M ** a))"
      by (simp add: matrix_mul_assoc)
    also have "\<dots> = trace (M ** a)" unfolding o1 by simp
    finally show ?thesis .
  qed
  have "(\<lambda>a. - trace ((R ** M ** transpose R) ** a) / 2) ` {a \<in> S. a *v (R *v p) = 0}
      = (\<lambda>a. - trace (M ** a) / 2) ` {a \<in> S. a *v p = 0}"
    unfolding bij[symmetric] image_image
    by (rule image_cong[OF refl]) (simp add: treq)
  then show ?thesis unfolding covariation_op_real_def by simp
qed

section \<open>Continuity off the origin\<close>

text \<open>Near \<open>p \<noteq> 0\<close>, \<open>F(p', M') = F(p, R\<^sup>T M' R)\<close> with \<open>R = rotm p p'\<close>, by
  the two invariances, and \<open>R\<^sup>T M' R \<rightarrow> M\<close>; the Lipschitz bound in the Hessian
  concludes.\<close>

lemma covariation_op_real_isCont:
  fixes M :: "real^'n::finite^'n" and p :: "real^'n"
  assumes B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and Spsd: "\<And>a. a \<in> S \<Longrightarrow> psd a"
    and rot: "\<And>R b. orthogonal_matrix R \<Longrightarrow> b \<in> S \<Longrightarrow> R ** b ** transpose R \<in> S"
    and kill: "\<And>p :: real^'n. \<exists>a\<in>S. a *v p = 0"
    and p0: "p \<noteq> 0"
  shows "isCont (\<lambda>w. covariation_op_real S (fst w) (snd w)) (p, M)"
proof -
  define F where "F = covariation_op_real S"
  have B0: "0 \<le> B"
  proof -
    obtain a where "a \<in> S" using kill[of 0] by blast
    then show ?thesis using B norm_ge_zero[of a] by (meson order_trans)
  qed
  define G where "G = (\<lambda>w :: (real^'n) \<times> (real^'n^'n).
    transpose (rotm p (fst w)) ** snd w ** rotm p (fst w))"
  have Rlim: "((\<lambda>w :: (real^'n) \<times> (real^'n^'n). rotm p (fst w)) \<longlongrightarrow> mat 1) (at (p, M))"
  proof -
    have "((\<lambda>w :: (real^'n) \<times> (real^'n^'n). fst w) \<longlongrightarrow> p) (at (p, M))"
      using tendsto_fst[OF tendsto_ident_at[of "(p, M)" UNIV]] by simp
    from isCont_tendsto_compose[OF rotm_isCont[OF p0] this]
    show ?thesis by (simp add: rotm_self_mat)
  qed
  have Glim: "(G \<longlongrightarrow> M) (at (p, M))"
  proof -
    have "((\<lambda>w :: (real^'n) \<times> (real^'n^'n). snd w) \<longlongrightarrow> M) (at (p, M))"
      using tendsto_snd[OF tendsto_ident_at[of "(p, M)" UNIV]] by simp
    from tendsto_matrix_mult[OF tendsto_matrix_mult[OF tendsto_transpose_matrix[OF Rlim] this] Rlim]
    show ?thesis unfolding G_def by simp
  qed
  have lip: "dist (F p N) (F p N') \<le> B / 2 * dist N N'" for N N'
  proof -
    have "F p N \<le> F p N' + B / 2 * norm (N - N')"
      unfolding F_def by (rule covariation_op_real_lipschitz[OF B Spsd kill])
    moreover have "F p N' \<le> F p N + B / 2 * norm (N' - N)"
      unfolding F_def by (rule covariation_op_real_lipschitz[OF B Spsd kill])
    then have "F p N' \<le> F p N + B / 2 * norm (N - N')"
      by (simp add: norm_minus_commute)
    ultimately have "\<bar>F p N - F p N'\<bar> \<le> B / 2 * norm (N - N')"
      unfolding abs_le_iff by linarith
    then show ?thesis by (simp add: dist_real_def dist_norm)
  qed
  have "continuous_on UNIV (F p)"
    by (rule lipschitz_on_continuous_on[OF lipschitz_onI[of UNIV "F p" "B / 2"]])
      (use lip B0 in auto)
  then have Fc: "isCont (F p) M"
    unfolding continuous_on_eq_continuous_at[OF open_UNIV] by blast
  have lim1: "((\<lambda>w. F p (G w)) \<longlongrightarrow> F p M) (at (p, M))"
    by (rule isCont_tendsto_compose[OF Fc Glim])
  define H where "H = {w :: real^'n. 0 < norm p * norm w + p \<bullet> w}"
  have oH: "open H"
    unfolding H_def by (intro open_Collect_less continuous_intros)
  have pH: "p \<in> H"
    unfolding H_def using p0 by (simp add: dot_square_norm power2_eq_square)
  have eqH: "F (fst w) (snd w) = F p (G w)" if wH: "fst w \<in> H" for w
  proof -
    define q where "q = fst w"
    define N where "N = snd w"
    define R where "R = rotm p q"
    have pos: "0 < norm p * norm q + p \<bullet> q" using wH unfolding H_def q_def by simp
    have q0: "q \<noteq> 0" using pos by auto
    have orth: "orthogonal_matrix R" unfolding R_def by (rule rotm_orthogonal)
    have Rp: "R *v p = (norm p / norm q) *\<^sub>R q"
      unfolding R_def by (rule rotm_apply[OF p0 q0 pos])
    have c0: "norm p / norm q \<noteq> 0" using p0 q0 by simp
    have "F p (G w) = F p (transpose R ** N ** R)"
      unfolding G_def R_def q_def N_def ..
    also have "\<dots> = F (R *v p) (R ** (transpose R ** N ** R) ** transpose R)"
      unfolding F_def by (rule covariation_op_real_rotation[OF rot orth, symmetric])
    also have "\<dots> = F ((norm p / norm q) *\<^sub>R q) N"
      unfolding Rp conj_orth_inv[OF orth] ..
    also have "\<dots> = F q N"
      unfolding F_def by (rule covariation_op_real_dilation[OF c0])
    finally show ?thesis unfolding q_def N_def by simp
  qed
  have "eventually (\<lambda>w. w \<in> H \<times> UNIV) (nhds (p, M))"
    by (rule eventually_nhds_in_open) (use oH pH in \<open>simp_all add: open_Times\<close>)
  then have "eventually (\<lambda>w. w \<in> H \<times> UNIV) (at (p, M))"
    unfolding eventually_at_filter by (rule eventually_mono) simp
  then have ev: "eventually (\<lambda>w. F p (G w) = F (fst w) (snd w)) (at (p, M))"
    by (rule eventually_mono) (use eqH in \<open>auto simp: mem_Times_iff\<close>)
  have "((\<lambda>w. F (fst w) (snd w)) \<longlongrightarrow> F p M) (at (p, M))"
    by (rule Lim_transform_eventually[OF lim1 ev])
  then show ?thesis unfolding isCont_def F_def by simp
qed

section \<open>The instance\<close>

theorem covariation_op_real_geometric_operator:
  assumes B: "\<And>a :: real^'n::finite^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and Spsd: "\<And>a. a \<in> S \<Longrightarrow> psd a"
    and rot: "\<And>R b. orthogonal_matrix R \<Longrightarrow> b \<in> S \<Longrightarrow> R ** b ** transpose R \<in> S"
    and kill: "\<And>p :: real^'n. \<exists>a\<in>S. a *v p = 0"
  shows "geometric_operator (covariation_op_real S :: real^'n \<Rightarrow> real^'n^'n \<Rightarrow> real)"
proof (rule geometric_operator.intro)
  define F where "F = (covariation_op_real S :: real^'n \<Rightarrow> real^'n^'n \<Rightarrow> real)"
  have B0: "0 \<le> B"
  proof -
    obtain a where "a \<in> S" using kill[of 0] by blast
    then show ?thesis using B norm_ge_zero[of a] by (meson order_trans)
  qed
  have upper: "F q N \<le> B / 2 * norm N" for q N
    unfolding F_def by (rule covariation_op_real_upper[OF B Spsd kill])
  have lipF: "F q N \<le> F q N' + B / 2 * norm (N - N')" for q N N'
    unfolding F_def by (rule covariation_op_real_lipschitz[OF B Spsd kill])
  show "covariation_op_real S p N \<le> covariation_op_real S p M" if "psd (N - M)"
    for N M :: "real^'n^'n" and p :: "real^'n"
  proof (rule covariation_op_real_greatest[OF kill])
    fix a assume a: "a \<in> S" and ap: "a *v p = 0"
    have "covariation_op_real S p N \<le> - trace (N ** a) / 2"
      by (rule covariation_op_real_le_witness[OF B Spsd a ap])
    moreover have "0 \<le> trace ((N - M) ** a)"
      by (rule trace_mult_psd_nonneg[OF that Spsd[OF a]])
    moreover have "trace ((N - M) ** a) = trace (N ** a) - trace (M ** a)"
      by (simp add: matrix_mul_diff_left trace_sub)
    ultimately show "covariation_op_real S p N \<le> - trace (M ** a) / 2" by simp
  qed
  show "covariation_op_real S p (t *\<^sub>R M) = t * covariation_op_real S p M" if t: "0 < t"
    for t and M :: "real^'n^'n" and p :: "real^'n"
  proof -
    have pt: "- trace ((t *\<^sub>R M) ** a) / 2 = t * (- trace (M ** a) / 2)"
      for a :: "real^'n^'n"
    proof -
      have "(t *\<^sub>R M) ** a = t *\<^sub>R (M ** a)"
        by (rule scalar_matrix_assoc[symmetric])
      then show ?thesis by (simp add: trace_scaleR)
    qed
    have img: "(\<lambda>a. - trace ((t *\<^sub>R M) ** a) / 2) ` {a \<in> S. a *v p = 0}
        = (\<lambda>x. t * x) ` ((\<lambda>a. - trace (M ** a) / 2) ` {a \<in> S. a *v p = 0})"
      unfolding image_image using pt by simp
    show ?thesis
      unfolding covariation_op_real_def img
      by (rule cInf_mult_pos[OF t _ covariation_op_real_bdd_below[OF B Spsd]])
        (use kill[of p] in blast)
  qed
  show "covariation_op_real S (c *\<^sub>R p) M = covariation_op_real S p M" if "0 < c"
    for c and M :: "real^'n^'n" and p :: "real^'n"
    by (rule covariation_op_real_dilation) (use that in simp)
  show "covariation_op_real S (R *v p) (R ** M ** transpose R) = covariation_op_real S p M"
    if "orthogonal_matrix R" for R M :: "real^'n^'n" and p :: "real^'n"
    by (rule covariation_op_real_rotation[OF rot that])
  show "\<exists>C. \<forall>(p :: real^'n) (M :: real^'n^'n) \<delta>. 0 \<le> \<delta> \<longrightarrow>
      covariation_op_real S p M \<le> covariation_op_real S p (M + \<delta> *\<^sub>R mat 1) + C * \<delta>"
  proof (intro exI allI impI)
    fix p :: "real^'n" and M :: "real^'n^'n" and \<delta> :: real
    assume d: "0 \<le> \<delta>"
    have "F p M \<le> F p (M + \<delta> *\<^sub>R mat 1) + B / 2 * norm (M - (M + \<delta> *\<^sub>R mat 1))"
      by (rule lipF)
    also have "norm (M - (M + \<delta> *\<^sub>R mat 1)) = \<delta> * norm (mat 1 :: real^'n^'n)"
      using d by simp
    finally show "covariation_op_real S p M
        \<le> covariation_op_real S p (M + \<delta> *\<^sub>R mat 1) + B / 2 * norm (mat 1 :: real^'n^'n) * \<delta>"
      unfolding F_def by (simp add: algebra_simps)
  qed
  show "op_lsc (covariation_op_real S) p M = ereal (covariation_op_real S p M)"
    if "transpose M = M" "p \<noteq> 0" for M :: "real^'n^'n" and p :: "real^'n"
    by (rule op_envelopes_eq_of_isCont(1)[OF covariation_op_real_isCont[OF B Spsd rot kill that(2)]])
  show "op_usc (covariation_op_real S) p M = ereal (covariation_op_real S p M)"
    if "transpose M = M" "p \<noteq> 0" for M :: "real^'n^'n" and p :: "real^'n"
    by (rule op_envelopes_eq_of_isCont(2)[OF covariation_op_real_isCont[OF B Spsd rot kill that(2)]])
  show "op_lsc (covariation_op_real S) 0 M = ereal (covariation_op_real S 0 M)"
    for M :: "real^'n^'n"
  proof (rule op_lsc_eq_of_local_lower)
    fix \<epsilon> :: real assume \<epsilon>: "0 < \<epsilon>"
    define e where "e = \<epsilon> / (B / 2 + 1)"
    have e0: "0 < e" unfolding e_def using \<epsilon> B0 by simp
    have Be: "B / 2 * e \<le> \<epsilon>"
    proof -
      have "B / 2 * e \<le> (B / 2 + 1) * e" using e0 by (intro mult_right_mono) simp_all
      also have "\<dots> = \<epsilon>" unfolding e_def using B0 by simp
      finally show ?thesis .
    qed
    have "F 0 M - \<epsilon> \<le> F (fst w) (snd w)" if w: "w \<in> ball (0, M) e" for w
    proof -
      have "F 0 (snd w) \<le> F (fst w) (snd w)"
        unfolding F_def
      proof (rule covariation_op_real_greatest[OF kill])
        fix a assume "a \<in> S" "a *v fst w = 0"
        then show "covariation_op_real S 0 (snd w) \<le> - trace (snd w ** a) / 2"
          by (intro covariation_op_real_le_witness[OF B Spsd]) simp_all
      qed
      moreover have "F 0 M \<le> F 0 (snd w) + B / 2 * norm (M - snd w)" by (rule lipF)
      moreover have "norm (M - snd w) < e"
        using w dist_snd_le[of "(0, M)" w] by (simp add: dist_norm)
      then have "B / 2 * norm (M - snd w) \<le> B / 2 * e"
        using B0 by (intro mult_left_mono) simp_all
      ultimately show ?thesis using Be by linarith
    qed
    then show "\<exists>e>0. \<forall>w\<in>ball (0, M) e.
        covariation_op_real S 0 M - \<epsilon> \<le> covariation_op_real S (fst w) (snd w)"
      using e0 unfolding F_def by blast
  qed
  have usc_bound: "op_usc (covariation_op_real S) q N0 \<le> ereal (1 / 2)"
    if e0: "0 < e" and small: "\<And>N. dist N N0 < e \<Longrightarrow> B * norm N \<le> 1" for q N0 and e :: real
  proof (rule op_usc_le_of_ball[OF e0])
    fix w assume "w \<in> ball (q, N0) e"
    then have "dist (snd w) N0 < e"
      using dist_snd_le[of w "(q, N0)"] by (simp add: dist_commute)
    then have "B * norm (snd w) \<le> 1" by (rule small)
    then show "covariation_op_real S (fst w) (snd w) \<le> 1 / 2"
      using upper[of "fst w" "snd w"] unfolding F_def by simp
  qed
  show "op_usc (covariation_op_real S) (0 :: real^'n) (0 :: real^'n^'n) < 1"
  proof -
    have "op_usc (covariation_op_real S) (0 :: real^'n) (0 :: real^'n^'n) \<le> ereal (1 / 2)"
    proof (rule usc_bound)
      show "0 < 1 / (B + 1)" using B0 by simp
      fix N :: "real^'n^'n" assume "dist N 0 < 1 / (B + 1)"
      then have "norm N \<le> 1 / (B + 1)" by simp
      then have "B * norm N \<le> B * (1 / (B + 1))" using B0 by (intro mult_left_mono)
      also have "\<dots> \<le> 1" using B0 by (simp add: field_simps)
      finally show "B * norm N \<le> 1" .
    qed
    also have "\<dots> < 1" by simp
    finally show ?thesis .
  qed
  show "\<exists>\<delta>>0. \<delta> < 1 \<and> (\<forall>q :: real^'n. op_usc (covariation_op_real S) q (0 - \<delta> *\<^sub>R mat 1) < 1)"
  proof (intro exI conjI allI)
    define K where "K = B * (norm (mat 1 :: real^'n^'n) + 1)"
    have K0: "0 \<le> K" unfolding K_def using B0 by simp
    define \<delta> where "\<delta> = 1 / (K + 2)"
    show d0: "0 < \<delta>" unfolding \<delta>_def using K0 by simp
    show "\<delta> < 1" unfolding \<delta>_def using K0 by simp
    have Kd: "K * \<delta> \<le> 1" unfolding \<delta>_def using K0 by (simp add: field_simps)
    fix q :: "real^'n"
    have "op_usc (covariation_op_real S) q (0 - \<delta> *\<^sub>R mat 1) \<le> ereal (1 / 2)"
    proof (rule usc_bound[OF d0])
      fix N :: "real^'n^'n" assume dN: "dist N (0 - \<delta> *\<^sub>R mat 1) < \<delta>"
      have "norm N \<le> norm (0 - \<delta> *\<^sub>R mat 1 :: real^'n^'n) + dist N (0 - \<delta> *\<^sub>R mat 1)"
        using norm_triangle_ineq[of "0 - \<delta> *\<^sub>R mat 1" "N - (0 - \<delta> *\<^sub>R mat 1)"]
        by (simp add: dist_norm)
      also have "\<dots> \<le> \<delta> * norm (mat 1 :: real^'n^'n) + \<delta>"
        using dN d0 by simp
      finally have "norm N \<le> \<delta> * (norm (mat 1 :: real^'n^'n) + 1)"
        by (simp add: algebra_simps)
      then have "B * norm N \<le> B * (\<delta> * (norm (mat 1 :: real^'n^'n) + 1))"
        using B0 by (intro mult_left_mono)
      also have "\<dots> = K * \<delta>" unfolding K_def by (simp add: algebra_simps)
      finally show "B * norm N \<le> 1" using Kd by linarith
    qed
    also have "\<dots> < 1" by simp
    finally show "op_usc (covariation_op_real S) q (0 - \<delta> *\<^sub>R mat 1) < 1" .
  qed
qed

section \<open>The envelopes of \<^const>\<open>covariation_op\<close>\<close>

text \<open>\<open>F\<^sub>*\<close> of the \<^typ>\<open>ereal\<close>-valued operator, the dual of
  \<^const>\<open>covariation_op_usc\<close>; under the hypotheses of the instance both are the
  envelopes of the real-valued operator.\<close>

definition covariation_op_lsc ::
  "(real^'n::finite^'n) set \<Rightarrow> real^'n \<Rightarrow> real^'n^'n \<Rightarrow> ereal" where
  "covariation_op_lsc S p M
     = (SUP e \<in> {0<..}. INF w \<in> ball (p, M) e. covariation_op S (fst w) (snd w))"

lemma op_lsc_covariation_op_real:
  assumes B: "\<And>a :: real^'n::finite^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and Spsd: "\<And>a. a \<in> S \<Longrightarrow> psd a"
    and kill: "\<And>p :: real^'n. \<exists>a\<in>S. a *v p = 0"
  shows "op_lsc (covariation_op_real S) = covariation_op_lsc S"
  by (intro ext) (simp add: op_lsc_def covariation_op_lsc_def
      ereal_covariation_op_real[OF B Spsd kill])

lemma op_usc_covariation_op_real:
  assumes B: "\<And>a :: real^'n::finite^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and Spsd: "\<And>a. a \<in> S \<Longrightarrow> psd a"
    and kill: "\<And>p :: real^'n. \<exists>a\<in>S. a *v p = 0"
  shows "op_usc (covariation_op_real S) = covariation_op_usc S"
  by (intro ext) (simp add: op_usc_def covariation_op_usc_def
      ereal_covariation_op_real[OF B Spsd kill])

lemma covariation_op_lsc_le: "covariation_op_lsc S p M \<le> covariation_op S p M"
  unfolding covariation_op_lsc_def
proof (rule SUP_least)
  fix e :: real assume "e \<in> {0<..}"
  then have "(p, M) \<in> ball (p, M) e" by simp
  then show "(INF w \<in> ball (p, M) e. covariation_op S (fst w) (snd w)) \<le> covariation_op S p M"
    by (rule INF_lower2) simp
qed

lemma ell_op_lsc_eq_covariation_op_lsc:
  assumes k1: "1 \<le> k" and kn: "k < CARD('n::finite)" and L1: "1 \<le> L"
  shows "ell_op_lsc k L = covariation_op_lsc (sconstraint k L :: (real^'n^'n) set)"
  by (intro ext) (simp add: ell_op_lsc_eq_op_lsc op_lsc_def covariation_op_lsc_def
      ell_op_eq_covariation_op[OF k1 kn L1])

section \<open>Proposition 4.1 for an abstract constraint set\<close>

text \<open>Uniqueness on an expandable \<open>K\<close>, for Definition 3.1 with the operator
  \<^const>\<open>covariation_op\<close> \<open>S\<close> and its envelopes; each function may have its
  own bound.\<close>

theorem covariation_op_uniqueness_expandable:
  fixes u w :: "real^'n::finite \<Rightarrow> real" and K :: "(real^'n) set"
  assumes B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and Spsd: "\<And>a. a \<in> S \<Longrightarrow> psd a"
    and rot: "\<And>R b. orthogonal_matrix R \<Longrightarrow> b \<in> S \<Longrightarrow> R ** b ** transpose R \<in> S"
    and kill: "\<And>p :: real^'n. \<exists>a\<in>S. a *v p = 0"
    and cK: "compact K" and neK: "K \<noteq> {}" and expK: "expandable K"
    and uscu: "\<And>c z. u z < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> u y < c"
    and uscw: "\<And>c z. w z < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> w y < c"
    and Bu: "\<And>y. \<bar>u y\<bar> \<le> Cu" and Bw: "\<And>y. \<bar>w y\<bar> \<le> Cw"
    and subu: "visc_subsol_gen test_fun_C2 (\<lambda>_. principal K) (covariation_op_lsc S)
      (interior K \<union> {x \<in> K - interior K. 0 < u x}) u"
    and supu: "visc_supersol_gen test_fun_C2 (\<lambda>_. principal K) (covariation_op_usc S)
      (interior K \<union> {x \<in> K - interior K. lsc_env u x < 0}) (lsc_env u)"
    and subw: "visc_subsol_gen test_fun_C2 (\<lambda>_. principal K) (covariation_op_lsc S)
      (interior K \<union> {x \<in> K - interior K. 0 < w x}) w"
    and supw: "visc_supersol_gen test_fun_C2 (\<lambda>_. principal K) (covariation_op_usc S)
      (interior K \<union> {x \<in> K - interior K. lsc_env w x < 0}) (lsc_env w)"
    and x: "x \<in> K"
  shows "u x = w x"
proof -
  have GO: "geometric_operator (covariation_op_real S :: real^'n \<Rightarrow> real^'n^'n \<Rightarrow> real)"
    by (rule covariation_op_real_geometric_operator[OF B Spsd rot kill])
  have lscF: "op_lsc (covariation_op_real S) = covariation_op_lsc S"
    by (rule op_lsc_covariation_op_real[OF B Spsd kill])
  have uscF: "op_usc (covariation_op_real S) = covariation_op_usc S"
    by (rule op_usc_covariation_op_real[OF B Spsd kill])
  have Bu': "\<bar>u y\<bar> \<le> max Cu Cw" and Bw': "\<bar>w y\<bar> \<le> max Cu Cw" for y
    using Bu[of y] Bw[of y] by (simp_all add: le_max_iff_disj)
  show ?thesis
    by (rule geometric_operator.uniqueness_expandable[OF GO cK neK expK uscu uscw Bu' Bw'
          subu[folded lscF] supu[folded uscF] subw[folded lscF] supw[folded uscF] x])
qed

text \<open>The sphere-tangential rates \<open>I - u u\<^sup>T\<close> annihilate every gradient, so a
  set containing them satisfies the last hypothesis of the instance.\<close>

lemma tangential_rates_kill:
  fixes S :: "(real^'n::finite^'n) set"
  assumes tan1: "\<And>u :: real^'n. norm u \<le> 1 \<Longrightarrow>
      tanpU (mat 1) u ** transpose (tanpU (mat 1) u) \<in> S"
  shows "\<exists>a\<in>S. a *v p = 0"
proof (cases "p = 0")
  case True
  then show ?thesis using tan1[of 0] by auto
next
  case False
  define u where "u = (1 / norm p) *\<^sub>R p"
  have nu: "norm u = 1" unfolding u_def using False by simp
  have uu: "u \<bullet> u = 1" using nu by (simp add: dot_square_norm)
  define P where "P = tanpU (mat 1) u"
  have Psym: "transpose P = P"
    unfolding P_def by (rule tanpU_sym) simp
  have Pu: "P *v u = 0"
    unfolding P_def tanpU_mv by (simp add: uu)
  have pu: "p = norm p *\<^sub>R u" unfolding u_def using False by simp
  have Pp: "P *v p = 0"
    by (subst pu) (simp add: matrix_vector_mult_scaleR Pu)
  have "(P ** transpose P) *v p = P *v (P *v p)"
    unfolding Psym by (simp add: matrix_vector_mul_assoc)
  also have "\<dots> = 0" by (simp add: Pp)
  finally show ?thesis using tan1[of u] nu unfolding P_def by auto
qed

(*<*)
end
(*>*)
