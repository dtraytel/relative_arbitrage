section \<open>Geometric operators: the interface of the comparison chain\<close>

(*<*)
theory Geometric_Operator
  imports
    "Second_Order_Viscosity_Analysis.Viscosity_Solutions"
    "Semicontinuous_Analysis.Semicontinuous_Envelopes"
    "Semicontinuous_Analysis.Semicontinuity"
    "Symmetric_Matrix_Spectra.Householder_Rotation"
begin
(*>*)

text \<open>
  The comparison principles of the following theories hold for every
  real-valued second-order operator \<open>F(p, M)\<close> on \<open>\<real>\<^sup>n \<times> \<real>\<^sup>n\<^sup>\<times>\<^sup>n\<close> with the
  properties collected in the locale \<open>geometric_operator\<close> below: degenerate
  ellipticity, positive homogeneity in \<open>M\<close>, invariance under positive
  dilations of \<open>p\<close> and under rotations, a bound on the effect of shifting
  \<open>M\<close> by a multiple of the identity, continuity off \<open>p = 0\<close> (the
  semicontinuous envelopes agree with \<open>F\<close> there), \<open>F\<^sub>* = F\<close> at \<open>p = 0\<close>, and
  \<open>F\<^sup>* < 1\<close> at \<open>(0, 0)\<close> and uniformly at \<open>(q, - \<delta> I)\<close> for some \<open>\<delta>\<close>.  These
  are exactly the properties of the operator that the comparison argument
  reads; the equation is \<open>F = 1\<close>.
\<close>

section \<open>The semicontinuous envelopes of an operator\<close>

text \<open>\<open>F\<^sub>*(z) = lim\<^bsub>e\<down>0\<^esub> inf\<^bsub>|w-z|<e\<^esub> F(w)\<close> and dually, as \<^typ>\<open>ereal\<close>-valued
  functions with no side conditions; the limits are monotone in \<open>e\<close>, so
  they are a supremum and an infimum.\<close>

definition op_lsc :: "('a::metric_space \<Rightarrow> 'b::metric_space \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ereal"
  where "op_lsc F p M = (SUP e \<in> {0<..}. INF w \<in> ball (p, M) e. ereal (F (fst w) (snd w)))"

definition op_usc :: "('a::metric_space \<Rightarrow> 'b::metric_space \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ereal"
  where "op_usc F p M = (INF e \<in> {0<..}. SUP w \<in> ball (p, M) e. ereal (F (fst w) (snd w)))"

lemma op_lsc_le: "op_lsc F p M \<le> ereal (F p M)"
  unfolding op_lsc_def
proof (rule SUP_least)
  fix e :: real assume "e \<in> {0<..}"
  then have "(p, M) \<in> ball (p, M) e" by simp
  then show "(INF w \<in> ball (p, M) e. ereal (F (fst w) (snd w))) \<le> ereal (F p M)"
    by (rule INF_lower2) simp
qed

lemma op_usc_ge: "ereal (F p M) \<le> op_usc F p M"
  unfolding op_usc_def
proof (rule INF_greatest)
  fix e :: real assume "e \<in> {0<..}"
  then have "(p, M) \<in> ball (p, M) e" by simp
  then show "ereal (F p M) \<le> (SUP w \<in> ball (p, M) e. ereal (F (fst w) (snd w)))"
    by (rule SUP_upper2) simp
qed

text \<open>A bound at points arbitrarily close to \<open>(p, M)\<close> is a bound on the
  envelope at \<open>(p, M)\<close>.\<close>

lemma op_lsc_le_of_nearby:
  assumes b: "\<And>e. 0 < e \<Longrightarrow> \<exists>p' M'. dist (p', M') (p, M) < e \<and> F p' M' \<le> c"
  shows "op_lsc F p M \<le> ereal c"
  unfolding op_lsc_def
proof (rule SUP_least)
  fix e :: real assume "e \<in> {0<..}"
  then obtain p' M' where "(p', M') \<in> ball (p, M) e" and "F p' M' \<le> c"
    using b[of e] by (auto simp: dist_commute)
  then show "(INF w \<in> ball (p, M) e. ereal (F (fst w) (snd w))) \<le> ereal c"
    by (intro INF_lower2) auto
qed

lemma op_usc_ge_of_nearby:
  assumes b: "\<And>e. 0 < e \<Longrightarrow> \<exists>p' M'. dist (p', M') (p, M) < e \<and> c \<le> F p' M'"
  shows "ereal c \<le> op_usc F p M"
  unfolding op_usc_def
proof (rule INF_greatest)
  fix e :: real assume "e \<in> {0<..}"
  then obtain p' M' where "(p', M') \<in> ball (p, M) e" and "c \<le> F p' M'"
    using b[of e] by (auto simp: dist_commute)
  then show "ereal c \<le> (SUP w \<in> ball (p, M) e. ereal (F (fst w) (snd w)))"
    by (intro SUP_upper2) auto
qed

text \<open>\<open>F\<^sup>*\<close> is upper semicontinuous by construction, so the inequality
  \<open>\<ge> 1\<close> passes through limits in \<open>(p, M)\<close>: this moves a conclusion
  obtained at perturbed jets back to the jet of interest.\<close>

lemma op_usc_ge_one_limit:
  assumes ge: "\<And>j. 1 \<le> op_usc F (ps j) (Ms j)"
    and lim: "(\<lambda>j. (ps j, Ms j)) \<longlonglongrightarrow> (p0, M0)"
  shows "1 \<le> op_usc F p0 M0"
  unfolding op_usc_def
proof (rule INF_greatest)
  fix e :: real assume "e \<in> {0<..}"
  then have e0: "0 < e" by simp
  have "\<forall>\<^sub>F j in sequentially. dist (ps j, Ms j) (p0, M0) < e / 2"
    by (rule tendstoD[OF lim]) (use e0 in simp)
  then obtain j where j: "dist (ps j, Ms j) (p0, M0) < e / 2"
    by (auto simp: eventually_sequentially)
  have sub: "ball (ps j, Ms j) (e / 2) \<subseteq> ball (p0, M0) e"
  proof
    fix w assume "w \<in> ball (ps j, Ms j) (e / 2)"
    then have "dist (ps j, Ms j) w < e / 2" by simp
    then have "dist (p0, M0) w < e"
      using j dist_triangle[of "(p0, M0)" w "(ps j, Ms j)"] by (simp add: dist_commute)
    then show "w \<in> ball (p0, M0) e" by simp
  qed
  have "(1 :: ereal) \<le> op_usc F (ps j) (Ms j)" by (rule ge)
  also have "\<dots> \<le> (SUP w \<in> ball (ps j, Ms j) (e / 2). ereal (F (fst w) (snd w)))"
    unfolding op_usc_def by (rule INF_lower) (use e0 in simp)
  also have "\<dots> \<le> (SUP w \<in> ball (p0, M0) e. ereal (F (fst w) (snd w)))"
    by (rule SUP_subset_mono[OF sub order_refl])
  finally show "1 \<le> (SUP w \<in> ball (p0, M0) e. ereal (F (fst w) (snd w)))" .
qed

text \<open>The special case used twice: the inequality \<open>\<ge> 1\<close> at every softened
  Hessian \<open>H - \<delta> I\<close> survives \<open>\<delta> \<rightarrow> 0\<close>.\<close>

lemma op_usc_ge_one_shift:
  fixes F :: "real^'n::finite \<Rightarrow> real^'n^'n \<Rightarrow> real" and H :: "real^'n^'n"
  assumes ge: "\<And>\<delta>. 0 < \<delta> \<Longrightarrow> 1 \<le> op_usc F p (H - \<delta> *\<^sub>R mat 1)"
  shows "1 \<le> op_usc F p H"
proof (rule op_usc_ge_one_limit[where ps = "\<lambda>_. p"
      and Ms = "\<lambda>j. H - (1 / real (Suc j)) *\<^sub>R mat 1"])
  show "1 \<le> op_usc F p (H - (1 / real (Suc j)) *\<^sub>R mat 1)" for j
    by (rule ge) simp
  have "(\<lambda>j. 1 / real (Suc j)) \<longlonglongrightarrow> 0"
    using LIMSEQ_inverse_real_of_nat by (simp add: divide_inverse)
  from tendsto_diff[OF tendsto_const tendsto_scaleR[OF this tendsto_const]]
  have "(\<lambda>j. H - (1 / real (Suc j)) *\<^sub>R (mat 1 :: real^'n^'n)) \<longlonglongrightarrow> H"
    by simp
  then show "(\<lambda>j. (p, H - (1 / real (Suc j)) *\<^sub>R mat 1)) \<longlonglongrightarrow> (p, H)"
    by (rule tendsto_Pair[OF tendsto_const])
qed

subsection \<open>Transporting the upper envelope along an invariance\<close>

text \<open>If \<open>\<Psi>\<close> preserves \<open>f\<close> and is bi-Lipschitz at \<open>z\<close> in the weak sense of
  the two ball inclusions, the ball envelope of \<open>f\<close> takes the same value at
  \<open>\<Psi> z\<close> as at \<open>z\<close>.\<close>

lemma ball_usc_env_transfer:
  fixes \<Psi> :: "'a::metric_space \<Rightarrow> 'a" and f :: "'a \<Rightarrow> ereal"
  assumes F: "\<And>v. f (\<Psi> v) = f v"
    and a0: "0 < a" and b0: "0 < b"
    and sub1: "\<And>e. 0 < e \<Longrightarrow> \<Psi> ` ball z (e / a) \<subseteq> ball (\<Psi> z) e"
    and sub2: "\<And>e. 0 < e \<Longrightarrow> ball (\<Psi> z) (b * e) \<subseteq> \<Psi> ` ball z e"
  shows "(INF e \<in> {0<..}. SUP w \<in> ball (\<Psi> z) e. f w)
       = (INF e \<in> {0<..}. SUP w \<in> ball z e. f w)"
    (is "?A = ?B")
proof (rule antisym)
  have le1: "(SUP w \<in> ball (\<Psi> z) (b * e). f w) \<le> (SUP w \<in> ball z e. f w)"
    if e0: "0 < e" for e
  proof -
    have "(SUP w \<in> ball (\<Psi> z) (b * e). f w) \<le> (SUP w \<in> \<Psi> ` ball z e. f w)"
      by (rule SUP_subset_mono[OF sub2[OF e0]]) simp
    also have "\<dots> = (SUP v \<in> ball z e. f (\<Psi> v))"
      by (simp add: image_image)
    also have "\<dots> = (SUP v \<in> ball z e. f v)"
      by (rule SUP_cong[OF refl]) (rule F)
    finally show ?thesis .
  qed
  have "?A = (INF e \<in> (\<lambda>e. e / inverse b) ` {0<..}. SUP w \<in> ball (\<Psi> z) e. f w)"
    unfolding pos_image_scale[OF positive_imp_inverse_positive[OF b0]] by (rule refl)
  also have "\<dots> = (INF e \<in> {0<..}. SUP w \<in> ball (\<Psi> z) (b * e). f w)"
    using b0 by (simp add: image_image divide_inverse mult.commute)
  also have "\<dots> \<le> ?B" by (rule INF_mono) (use le1 in blast)
  finally show "?A \<le> ?B" .
next
  have le2: "(SUP w \<in> ball z (e / a). f w) \<le> (SUP w \<in> ball (\<Psi> z) e. f w)"
    if e0: "0 < e" for e
  proof -
    have "(SUP w \<in> ball z (e / a). f w) = (SUP v \<in> ball z (e / a). f (\<Psi> v))"
      by (rule SUP_cong[OF refl]) (rule F[symmetric])
    also have "\<dots> = (SUP w \<in> \<Psi> ` ball z (e / a). f w)"
      by (simp add: image_image)
    also have "\<dots> \<le> (SUP w \<in> ball (\<Psi> z) e. f w)"
      by (rule SUP_subset_mono[OF sub1[OF e0]]) simp
    finally show ?thesis .
  qed
  have "?B = (INF e \<in> (\<lambda>e. e / a) ` {0<..}. SUP w \<in> ball z e. f w)"
    unfolding pos_image_scale[OF a0] by (rule refl)
  also have "\<dots> = (INF e \<in> {0<..}. SUP w \<in> ball z (e / a). f w)"
    by (simp add: image_image)
  also have "\<dots> \<le> ?A" by (rule INF_mono) (use le2 in blast)
  finally show "?B \<le> ?A" .
qed

text \<open>The two invariances of \<open>F\<close> that pass to \<open>F\<^sup>*\<close>, as the comparison on
  expandable sets needs them:
  positive dilations of the gradient and rotations.\<close>

lemma op_usc_dilation:
  fixes F :: "real^'n::finite \<Rightarrow> real^'n^'n \<Rightarrow> real"
  assumes inv: "\<And>p M. F (c *\<^sub>R p) M = F p M" and c0: "0 < c"
  shows "op_usc F (c *\<^sub>R p) M = op_usc F p M"
proof -
  define \<Psi> :: "((real^'n) \<times> (real^'n^'n)) \<Rightarrow> ((real^'n) \<times> (real^'n^'n))"
    where "\<Psi> = (\<lambda>v. (c *\<^sub>R fst v, snd v))"
  have F: "ereal (F (fst (\<Psi> v)) (snd (\<Psi> v))) = ereal (F (fst v) (snd v))" for v
    unfolding \<Psi>_def by (simp add: inv)
  have mx0: "0 < max c 1" using c0 by simp
  have mn0: "0 < min c 1" using c0 by simp
  have sub1: "\<Psi> ` ball (p, M) (e / max c 1) \<subseteq> ball (\<Psi> (p, M)) e" if e0: "0 < e" for e
  proof
    fix w assume "w \<in> \<Psi> ` ball (p, M) (e / max c 1)"
    then obtain v where vb: "v \<in> ball (p, M) (e / max c 1)" and wv: "w = \<Psi> v" by auto
    have dvz: "dist (p, M) v < e / max c 1" using vb by simp
    have "dist (\<Psi> (p, M)) (\<Psi> v) \<le> max c 1 * dist (p, M) v"
      unfolding \<Psi>_def by (rule dist_prod_scale_fst(1)[OF c0])
    also have "\<dots> < max c 1 * (e / max c 1)"
      by (rule mult_strict_left_mono[OF dvz mx0])
    also have "\<dots> = e" using mx0 by simp
    finally show "w \<in> ball (\<Psi> (p, M)) e" unfolding wv by simp
  qed
  have sub2: "ball (\<Psi> (p, M)) (min c 1 * e) \<subseteq> \<Psi> ` ball (p, M) e" if e0: "0 < e" for e
  proof
    fix w assume wb: "w \<in> ball (\<Psi> (p, M)) (min c 1 * e)"
    define v where "v = ((inverse c) *\<^sub>R fst w, snd w)"
    have wv: "\<Psi> v = w" unfolding \<Psi>_def v_def using c0 by simp
    have "min c 1 * dist (p, M) v \<le> dist (\<Psi> (p, M)) (\<Psi> v)"
      unfolding \<Psi>_def by (rule dist_prod_scale_fst(2)[OF c0])
    also have "\<dots> < min c 1 * e" unfolding wv using wb by simp
    finally have "dist (p, M) v < e" using mn0 by simp
    then have "v \<in> ball (p, M) e" by simp
    then show "w \<in> \<Psi> ` ball (p, M) e" using wv by (metis image_eqI)
  qed
  have "(INF e \<in> {0<..}. SUP w \<in> ball (\<Psi> (p, M)) e. ereal (F (fst w) (snd w)))
      = (INF e \<in> {0<..}. SUP w \<in> ball (p, M) e. ereal (F (fst w) (snd w)))"
    by (rule ball_usc_env_transfer[where f = "\<lambda>w. ereal (F (fst w) (snd w))" and \<Psi> = \<Psi>,
          OF F mx0 mn0 sub1 sub2])
  then show ?thesis unfolding op_usc_def \<Psi>_def by simp
qed

lemma op_usc_rotation:
  fixes F :: "real^'n::finite \<Rightarrow> real^'n^'n \<Rightarrow> real" and R :: "real^'n^'n"
  assumes inv: "\<And>p M. F (R *v p) (R ** M ** transpose R) = F p M"
    and orth: "orthogonal_matrix R"
  shows "op_usc F (R *v p) (R ** M ** transpose R) = op_usc F p M"
proof -
  define \<Psi> :: "((real^'n) \<times> (real^'n^'n)) \<Rightarrow> ((real^'n) \<times> (real^'n^'n))"
    where "\<Psi> = (\<lambda>v. (R *v fst v, R ** snd v ** transpose R))"
  have F: "ereal (F (fst (\<Psi> v)) (snd (\<Psi> v))) = ereal (F (fst v) (snd v))" for v
    unfolding \<Psi>_def by (simp add: inv)
  have isom: "dist (\<Psi> v) (\<Psi> v') = dist v v'" for v v'
  proof -
    have p1: "R *v fst v - R *v fst v' = R *v (fst v - fst v')"
      by (rule matrix_vector_mult_diff_distrib[symmetric])
    have p2: "R ** snd v ** transpose R - R ** snd v' ** transpose R
        = R ** (snd v - snd v') ** transpose R"
      by (simp add: matrix_mul_diff_right matrix_mul_diff_left)
    show ?thesis
      unfolding \<Psi>_def dist_prod_def dist_norm
      by (simp add: p1 p2 norm_orthogonal_matrix_vector[OF orth]
          norm_conj_orthogonal[OF orth])
  qed
  have one: "(0 :: real) < 1" by simp
  have sub1: "\<Psi> ` ball (p, M) (e / 1) \<subseteq> ball (\<Psi> (p, M)) e" if e0: "0 < e" for e
  proof
    fix w assume "w \<in> \<Psi> ` ball (p, M) (e / 1)"
    then obtain v where vb: "v \<in> ball (p, M) (e / 1)" and wv: "w = \<Psi> v" by auto
    have "dist (\<Psi> (p, M)) (\<Psi> v) = dist (p, M) v" by (rule isom)
    also have "\<dots> < e" using vb by simp
    finally show "w \<in> ball (\<Psi> (p, M)) e" unfolding wv by simp
  qed
  have sub2: "ball (\<Psi> (p, M)) (1 * e) \<subseteq> \<Psi> ` ball (p, M) e" if e0: "0 < e" for e
  proof
    fix w assume wb: "w \<in> ball (\<Psi> (p, M)) (1 * e)"
    define v where "v = (transpose R *v fst w, transpose R ** snd w ** R)"
    have fstv: "R *v fst v = fst w"
      unfolding v_def fst_conv by (rule matvec_orth_inv[OF orth])
    have sndv: "R ** snd v ** transpose R = snd w"
      unfolding v_def snd_conv by (rule conj_orth_inv[OF orth])
    have wv: "\<Psi> v = w"
      unfolding \<Psi>_def using fstv sndv by simp
    have "dist (p, M) v = dist (\<Psi> (p, M)) (\<Psi> v)" by (rule isom[symmetric])
    also have "\<dots> < e" unfolding wv using wb by simp
    finally have "v \<in> ball (p, M) e" by simp
    then show "w \<in> \<Psi> ` ball (p, M) e" using wv by (metis image_eqI)
  qed
  have "(INF e \<in> {0<..}. SUP w \<in> ball (\<Psi> (p, M)) e. ereal (F (fst w) (snd w)))
      = (INF e \<in> {0<..}. SUP w \<in> ball (p, M) e. ereal (F (fst w) (snd w)))"
    by (rule ball_usc_env_transfer[where f = "\<lambda>w. ereal (F (fst w) (snd w))" and \<Psi> = \<Psi>,
          OF F one one sub1 sub2])
  then show ?thesis unfolding op_usc_def \<Psi>_def by simp
qed

section \<open>The locale\<close>

text \<open>The equation is \<open>F(Du, D\<^sup>2u) = 1\<close>.  The assumptions are the properties
  of \<open>F\<close> that the comparison chain reads, and nothing else.\<close>

locale geometric_operator =
  fixes F :: "real^'n::finite \<Rightarrow> real^'n^'n \<Rightarrow> real"
  assumes elliptic: "psd (N - M) \<Longrightarrow> F p N \<le> F p M"
    and homogeneous: "0 < t \<Longrightarrow> F p (t *\<^sub>R M) = t * F p M"
    and dilation: "0 < c \<Longrightarrow> F (c *\<^sub>R p) M = F p M"
    and rotation: "orthogonal_matrix R \<Longrightarrow> F (R *v p) (R ** M ** transpose R) = F p M"
    and shift_bound: "\<exists>C. \<forall>p M \<delta>. 0 \<le> \<delta> \<longrightarrow> F p M \<le> F p (M + \<delta> *\<^sub>R mat 1) + C * \<delta>"
    and lsc_off_zero: "transpose M = M \<Longrightarrow> p \<noteq> 0 \<Longrightarrow> op_lsc F p M = ereal (F p M)"
    and usc_off_zero: "transpose M = M \<Longrightarrow> p \<noteq> 0 \<Longrightarrow> op_usc F p M = ereal (F p M)"
    and lsc_at_zero: "op_lsc F 0 M = ereal (F 0 M)"
    and usc_zero_lt_one: "op_usc F 0 0 < 1"
    and usc_small_shift: "\<exists>\<delta>>0. \<delta> < 1 \<and> (\<forall>q. op_usc F q (0 - \<delta> *\<^sub>R mat 1) < 1)"
begin

abbreviation F_lsc :: "real^'n \<Rightarrow> real^'n^'n \<Rightarrow> ereal" where "F_lsc \<equiv> op_lsc F"
abbreviation F_usc :: "real^'n \<Rightarrow> real^'n^'n \<Rightarrow> ereal" where "F_usc \<equiv> op_usc F"

text \<open>The six viscosity notions the chain uses, all instances of the generic
  predicates of @{theory Second_Order_Viscosity_Analysis.Viscosity_Solutions}:
  local touching by a \<^const>\<open>test_fun_at\<close> test function with \<open>F\<close> itself
  (\<open>subsol\<close>) or with \<open>F\<^sup>*\<close> (\<open>supersol_usc\<close>), and touching over a set \<open>K\<close> by
  a \<^const>\<open>test_fun_at\<close> (\<open>_env\<close>) or a \<^const>\<open>test_fun_C2\<close> (\<open>_env2\<close>) test
  function, with the envelopes \<open>F\<^sub>*\<close> and \<open>F\<^sup>*\<close>.\<close>

abbreviation subsol :: "(real^'n) set \<Rightarrow> (real^'n \<Rightarrow> real) \<Rightarrow> bool" where
  "subsol \<equiv> visc_subsol_gen test_fun_at nhds (\<lambda>p M. ereal (F p M))"

abbreviation supersol_usc :: "(real^'n) set \<Rightarrow> (real^'n \<Rightarrow> real) \<Rightarrow> bool" where
  "supersol_usc \<equiv> visc_supersol_gen test_fun_at nhds F_usc"

abbreviation subsol_env :: "(real^'n) set \<Rightarrow> (real^'n) set \<Rightarrow> (real^'n \<Rightarrow> real) \<Rightarrow> bool" where
  "subsol_env K \<equiv> visc_subsol_gen test_fun_at (\<lambda>_. principal K) F_lsc"

abbreviation supersol_env :: "(real^'n) set \<Rightarrow> (real^'n) set \<Rightarrow> (real^'n \<Rightarrow> real) \<Rightarrow> bool" where
  "supersol_env K \<equiv> visc_supersol_gen test_fun_at (\<lambda>_. principal K) F_usc"

abbreviation subsol_env2 :: "(real^'n) set \<Rightarrow> (real^'n) set \<Rightarrow> (real^'n \<Rightarrow> real) \<Rightarrow> bool" where
  "subsol_env2 K \<equiv> visc_subsol_gen test_fun_C2 (\<lambda>_. principal K) F_lsc"

abbreviation supersol_env2 :: "(real^'n) set \<Rightarrow> (real^'n) set \<Rightarrow> (real^'n \<Rightarrow> real) \<Rightarrow> bool" where
  "supersol_env2 K \<equiv> visc_supersol_gen test_fun_C2 (\<lambda>_. principal K) F_usc"

text \<open>Their elementary forms.\<close>

lemma subsol_iff:
  "subsol \<Omega> u \<longleftrightarrow>
     (\<forall>x\<in>\<Omega>. \<forall>\<phi> g H. test_fun_at \<phi> g H x \<longrightarrow>
        (\<exists>e>0. \<forall>y \<in> ball x e. u y - \<phi> y \<le> u x - \<phi> x) \<longrightarrow> F (g x) H \<le> 1)"
  by (simp add: visc_subsol_gen_nhds)

lemma supersol_usc_iff:
  "supersol_usc \<Omega> w \<longleftrightarrow>
     (\<forall>x\<in>\<Omega>. \<forall>\<phi> g H. test_fun_at \<phi> g H x \<longrightarrow>
        (\<exists>e>0. \<forall>y \<in> ball x e. w x - \<phi> x \<le> w y - \<phi> y) \<longrightarrow> 1 \<le> F_usc (g x) H)"
  by (rule visc_supersol_gen_nhds)

lemma subsol_env_iff:
  "subsol_env K \<Omega> u \<longleftrightarrow>
     (\<forall>x\<in>\<Omega>. \<forall>\<phi> g H. test_fun_at \<phi> g H x \<longrightarrow>
        (\<forall>y\<in>K. u y - \<phi> y \<le> u x - \<phi> x) \<longrightarrow> F_lsc (g x) H \<le> 1)"
  by (rule visc_subsol_gen_principal)

lemma supersol_env_iff:
  "supersol_env K \<Omega> u \<longleftrightarrow>
     (\<forall>x\<in>\<Omega>. \<forall>\<phi> g H. test_fun_at \<phi> g H x \<longrightarrow>
        (\<forall>y\<in>K. u x - \<phi> x \<le> u y - \<phi> y) \<longrightarrow> 1 \<le> F_usc (g x) H)"
  by (rule visc_supersol_gen_principal)

lemma subsol_env2_iff:
  "subsol_env2 K \<Omega> u \<longleftrightarrow>
     (\<forall>x\<in>\<Omega>. \<forall>\<phi> g H. test_fun_C2 \<phi> g H x \<longrightarrow>
        (\<forall>y\<in>K. u y - \<phi> y \<le> u x - \<phi> x) \<longrightarrow> F_lsc (g x) H \<le> 1)"
  by (rule visc_subsol_gen_principal)

lemma supersol_env2_iff:
  "supersol_env2 K \<Omega> u \<longleftrightarrow>
     (\<forall>x\<in>\<Omega>. \<forall>\<phi> g H. test_fun_C2 \<phi> g H x \<longrightarrow>
        (\<forall>y\<in>K. u x - \<phi> x \<le> u y - \<phi> y) \<longrightarrow> 1 \<le> F_usc (g x) H)"
  by (rule visc_supersol_gen_principal)

text \<open>The two interface clauses in the form the chain applies them.\<close>

lemma usc_small_shift_lt_one:
  obtains \<delta> :: real where "0 < \<delta>" and "\<delta> < 1"
    and "\<And>q. F_usc q (0 - \<delta> *\<^sub>R mat 1) < 1"
  using usc_small_shift by blast

lemma shift_bound_pos:
  "\<exists>C>0. \<forall>p M \<delta>. 0 \<le> \<delta> \<longrightarrow> F p M \<le> F p (M + \<delta> *\<^sub>R mat 1) + C * \<delta>"
proof -
  obtain C where C: "\<forall>p M \<delta>. 0 \<le> \<delta> \<longrightarrow> F p M \<le> F p (M + \<delta> *\<^sub>R mat 1) + C * \<delta>"
    using shift_bound by blast
  have "F p M \<le> F p (M + \<delta> *\<^sub>R mat 1) + max C 1 * \<delta>" if d: "0 \<le> \<delta>" for p M \<delta>
  proof -
    have "C * \<delta> \<le> max C 1 * \<delta>" using d by (intro mult_right_mono) auto
    moreover have "F p M \<le> F p (M + \<delta> *\<^sub>R mat 1) + C * \<delta>" using C d by blast
    ultimately show ?thesis by linarith
  qed
  then show ?thesis by (intro exI[of _ "max C 1"]) auto
qed

lemma usc_dilation: "0 < c \<Longrightarrow> F_usc (c *\<^sub>R p) M = F_usc p M"
  by (rule op_usc_dilation) (use dilation in auto)

lemma usc_rotation:
  "orthogonal_matrix R \<Longrightarrow> F_usc (R *v p) (R ** M ** transpose R) = F_usc p M"
  by (rule op_usc_rotation) (use rotation in auto)

end

(*<*)
end
(*>*)
