section \<open>Sup-convolutions\<close>

(*<*)
theory Sup_Convolution
  imports
    Alexandrov
    "Semicontinuous_Analysis.Semicontinuity"
begin

(*>*)

text \<open>
  The sup-convolution \<open>u\<^sup>\<epsilon>(x) = SUP y. u y - |x - y|\<^sup>2/(2\<epsilon>)\<close> of a
  bounded function is semiconvex; this feeds Jensen's lemma and the
  theorem on sums below.
\<close>
definition supconv :: "('a::euclidean_space \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> real" where
  "supconv u \<epsilon> x = (SUP y. u y - (dist x y)\<^sup>2 / (2*\<epsilon>))"

lemma supconv_bdd_above:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> B" and e: "0 < \<epsilon>"
  shows "bdd_above (range (\<lambda>y. u y - (dist x y)\<^sup>2 / (2*\<epsilon>)))"
proof (rule bdd_aboveI[of _ B])
  fix z assume "z \<in> range (\<lambda>y. u y - (dist x y)\<^sup>2 / (2*\<epsilon>))"
  then obtain y where zy: "z = u y - (dist x y)\<^sup>2 / (2*\<epsilon>)" by blast
  have "0 \<le> (dist x y)\<^sup>2 / (2*\<epsilon>)"
    using e by simp
  thus "z \<le> B" unfolding zy using B[of y] by linarith
qed

lemma supconv_ge:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> B" and e: "0 < \<epsilon>"
  shows "u x \<le> supconv u \<epsilon> x"
proof -
  have "u x = u x - (dist x x)\<^sup>2 / (2*\<epsilon>)" by simp
  also have "\<dots> \<le> supconv u \<epsilon> x"
    unfolding supconv_def
    by (intro cSUP_upper supconv_bdd_above[OF B e]) simp
  finally show ?thesis .
qed

lemma supconv_le:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> B" and e: "0 < \<epsilon>"
  shows "supconv u \<epsilon> x \<le> B"
  unfolding supconv_def
proof (rule cSUP_least)
  show "(UNIV :: 'a set) \<noteq> {}" by simp
  fix y :: 'a
  have "0 \<le> (dist x y)\<^sup>2 / (2*\<epsilon>)" using e by simp
  thus "u y - (dist x y)\<^sup>2 / (2*\<epsilon>) \<le> B" using B[of y] by linarith
qed

subsection \<open>Attainment for upper semicontinuous data\<close>

text \<open>For bounded usc \<open>u\<close> the supremum defining \<open>supconv u \<epsilon> x\<close> is attained:
  the competitor \<open>y \<mapsto> u y - dist\<^sup>2/(2\<epsilon>)\<close> is usc, and outside the ball of
  radius \<open>\<surd>(max 0 (2\<epsilon>(B - u x))) + 1\<close> it is already below its value at \<open>x\<close>,
  so its maximum over that compact ball is global.\<close>

lemma supconv_attained_usc:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> B" and e: "0 < \<epsilon>"
    and usc: "\<And>c z. u z < c \<Longrightarrow> \<exists>d>0. \<forall>y. dist z y < d \<longrightarrow> u y < c"
  shows "\<exists>ys. supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
proof -
  define g where "g = (\<lambda>y. u y - (dist x y)\<^sup>2 / (2*\<epsilon>))"
  have gusc: "\<exists>d>0. \<forall>y. dist z y < d \<longrightarrow> g y < c" if lt: "g z < c" for c z
  proof -
    define \<eta> where "\<eta> = (c - g z)/2"
    have \<eta>: "0 < \<eta>" using lt by (simp add: \<eta>_def)
    obtain d1 where d1: "0 < d1" "\<And>y. dist z y < d1 \<Longrightarrow> u y < u z + \<eta>"
      using usc[of z "u z + \<eta>"] \<eta> by auto
    have "continuous (at z) (\<lambda>y. (dist x y)\<^sup>2 / (2*\<epsilon>))"
      by (intro continuous_intros) (use e in simp)
    then obtain d2 where d2: "0 < d2"
      "\<And>y. dist y z < d2 \<Longrightarrow> \<bar>(dist x y)\<^sup>2 / (2*\<epsilon>) - (dist x z)\<^sup>2 / (2*\<epsilon>)\<bar> < \<eta>"
      using \<eta> unfolding continuous_at_eps_delta dist_real_def by blast
    have "g y < c" if "dist z y < min d1 d2" for y
    proof -
      have "u y < u z + \<eta>" using d1(2)[of y] that by simp
      moreover have "(dist x z)\<^sup>2 / (2*\<epsilon>) - \<eta> < (dist x y)\<^sup>2 / (2*\<epsilon>)"
        using d2(2)[of y] that by (simp add: dist_commute abs_less_iff)
      ultimately show ?thesis using \<eta>_def unfolding g_def by argo
    qed
    then show ?thesis using d1(1) d2(1) by (intro exI[of _ "min d1 d2"]) auto
  qed
  define R where "R = sqrt (max 0 (2*\<epsilon>*(B - u x))) + 1"
  have R0: "0 < R" unfolding R_def by (simp add: add_nonneg_pos)
  obtain ys where ysc: "ys \<in> cball x R" and mxb: "\<And>y. y \<in> cball x R \<Longrightarrow> g y \<le> g ys"
    using usc_attains_sup_compact[OF gusc compact_cball, of x R] R0 by force
  have glob: "g y \<le> g ys" for y
  proof (cases "dist x y \<le> R")
    case False
    then have "(sqrt (max 0 (2*\<epsilon>*(B - u x))))\<^sup>2 < (dist x y)\<^sup>2"
      unfolding R_def by (intro power_strict_mono) auto
    then have "B - u x < (dist x y)\<^sup>2 / (2*\<epsilon>)"
      using e by (simp add: pos_less_divide_eq mult.commute)
    then have "g y < g x" using B[of y] unfolding g_def by simp
    then show ?thesis using mxb[of x] R0 by simp
  qed (simp add: mxb)
  have "supconv u \<epsilon> x = g ys"
    unfolding supconv_def
  proof (rule antisym)
    show "(SUP y. u y - (dist x y)\<^sup>2 / (2*\<epsilon>)) \<le> g ys"
      by (rule cSUP_least) (use glob in \<open>auto simp: g_def\<close>)
    show "g ys \<le> (SUP y. u y - (dist x y)\<^sup>2 / (2*\<epsilon>))"
      unfolding g_def by (intro cSUP_upper supconv_bdd_above[OF B e]) auto
  qed
  then show ?thesis unfolding g_def by blast
qed

text \<open>The sup-convolution inherits \<open>u\<close>'s Lipschitz constant exactly, for
  every \<open>\<epsilon>\<close>.\<close>

lemma supconv_lipschitz_le:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> Bu" and e: "0 < \<epsilon>"
    and lip: "\<And>p q. \<bar>u p - u q\<bar> \<le> L * norm (p - q)"
  shows "supconv u \<epsilon> x \<le> supconv u \<epsilon> y + L * norm (x - y)"
  unfolding supconv_def
proof (rule cSUP_least)
  show "(UNIV :: 'a set) \<noteq> {}" by simp
  fix z :: 'a
  define z' where "z' = z + (y - x)"
  have dz: "dist y z' = dist x z"
    unfolding z'_def dist_norm by (simp add: algebra_simps)
  have nz: "norm (z - z') = norm (x - y)"
    unfolding z'_def by (simp add: algebra_simps norm_minus_commute)
  have "u z - u z' \<le> L * norm (x - y)"
    using lip[of z z'] unfolding nz by linarith
  then have step: "u z - (dist x z)\<^sup>2 / (2*\<epsilon>)
      \<le> (u z' - (dist y z')\<^sup>2 / (2*\<epsilon>)) + L * norm (x - y)"
    unfolding dz by linarith
  have "u z' - (dist y z')\<^sup>2 / (2*\<epsilon>)
      \<le> (SUP w. u w - (dist y w)\<^sup>2 / (2*\<epsilon>))"
    by (rule cSUP_upper[OF UNIV_I supconv_bdd_above[OF B e]])
  with step show "u z - (dist x z)\<^sup>2 / (2*\<epsilon>)
      \<le> (SUP w. u w - (dist y w)\<^sup>2 / (2*\<epsilon>)) + L * norm (x - y)"
    by linarith
qed

theorem supconv_lipschitz:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> Bu" and e: "0 < \<epsilon>"
    and lip: "\<And>p q. \<bar>u p - u q\<bar> \<le> L * norm (p - q)"
  shows "\<bar>supconv u \<epsilon> x - supconv u \<epsilon> y\<bar> \<le> L * norm (x - y)"
proof (rule abs_leI)
  show "supconv u \<epsilon> x - supconv u \<epsilon> y \<le> L * norm (x - y)"
    using supconv_lipschitz_le[OF B e lip, of x y] by linarith
  have "supconv u \<epsilon> y \<le> supconv u \<epsilon> x + L * norm (y - x)"
    by (rule supconv_lipschitz_le[OF B e lip])
  then show "- (supconv u \<epsilon> x - supconv u \<epsilon> y) \<le> L * norm (x - y)"
    by (simp add: norm_minus_commute)
qed

text \<open>A Lipschitz function is approximated by its sup-convolution at rate
  \<open>supconv u \<epsilon> x \<le> u x + \<epsilon>*L\<^sup>2/2\<close>.\<close>

lemma supconv_le_of_lipschitz:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes e: "0 < \<epsilon>"
    and lip: "\<And>p q. \<bar>u p - u q\<bar> \<le> L * norm (p - q)"
  shows "supconv u \<epsilon> x \<le> u x + \<epsilon> * L\<^sup>2 / 2"
  unfolding supconv_def
proof (rule cSUP_least)
  show "(UNIV :: 'a set) \<noteq> {}" by simp
  fix y :: 'a
  have lipd: "u y - u x \<le> L * dist x y"
  proof -
    have "\<bar>u y - u x\<bar> \<le> L * norm (y - x)" by (rule lip)
    then show ?thesis
      by (simp add: dist_norm norm_minus_commute)
  qed
  have key: "L * dist x y - (dist x y)\<^sup>2 / (2*\<epsilon>) \<le> \<epsilon> * L\<^sup>2 / 2"
  proof -
    have e2: "0 < 2*\<epsilon>" using e by simp
    have sq: "0 \<le> (dist x y - \<epsilon>*L)\<^sup>2" by simp
    have nn: "0 \<le> (dist x y - \<epsilon>*L)\<^sup>2 / (2*\<epsilon>)"
      using sq e2 by simp
    have exp: "(dist x y - \<epsilon>*L)\<^sup>2 / (2*\<epsilon>)
        = (dist x y)\<^sup>2 / (2*\<epsilon>) - L * dist x y + \<epsilon> * L\<^sup>2 / 2"
      using e by (simp add: power2_diff power2_eq_square field_simps)
    from nn show ?thesis unfolding exp by linarith
  qed
  show "u y - (dist x y)\<^sup>2 / (2*\<epsilon>) \<le> u x + \<epsilon> * L\<^sup>2 / 2"
    using lipd key by linarith
qed

lemma convex_on_cSUP:
  fixes f :: "'b \<Rightarrow> 'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "\<And>y. convex_on UNIV (f y)"
    and bdd: "\<And>x. bdd_above (range (\<lambda>y. f y x))"
  shows "convex_on UNIV (\<lambda>x. SUP y. f y x)"
proof (intro convex_onI)
  show "convex (UNIV :: 'a set)" by (rule convex_UNIV)
  fix x1 x2 :: 'a and t :: real
  assume t: "0 < t" "t < 1"
  have t01: "0 \<le> t" "t \<le> 1" using t by linarith+
  show "(SUP y. f y ((1 - t) *\<^sub>R x1 + t *\<^sub>R x2))
      \<le> (1 - t) * (SUP y. f y x1) + t * (SUP y. f y x2)"
  proof (rule cSUP_least)
    show "(UNIV :: 'b set) \<noteq> {}" by simp
  next
    fix y :: 'b
    have "f y ((1 - t) *\<^sub>R x1 + t *\<^sub>R x2) \<le> (1 - t) * f y x1 + t * f y x2"
      using convex_onD[OF cvx, of t x1 x2] t01 by simp
    also have "\<dots> \<le> (1 - t) * (SUP y. f y x1) + t * (SUP y. f y x2)"
      by (intro add_mono mult_left_mono cSUP_upper bdd rangeI) (use t01 in simp_all)
    finally show "f y ((1 - t) *\<^sub>R x1 + t *\<^sub>R x2)
        \<le> (1 - t) * (SUP y. f y x1) + t * (SUP y. f y x2)" .
  qed
qed

lemma convex_on_affine_inner:
  fixes c :: "'a::euclidean_space" and a :: real
  shows "convex_on UNIV (\<lambda>x. a + inner x c)"
proof (intro convex_onI)
  show "convex (UNIV :: 'a set)" by (rule convex_UNIV)
  fix x1 x2 :: 'a and t :: real
  assume t: "0 < t" "t < 1"
  show "a + inner ((1 - t) *\<^sub>R x1 + t *\<^sub>R x2) c
      \<le> (1 - t) * (a + inner x1 c) + t * (a + inner x2 c)"
    by (simp add: algebra_simps)
qed
lemma supconv_square_decomp:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes e: "0 < \<epsilon>"
  shows "u y - (dist x y)\<^sup>2 / (2*\<epsilon>) + (norm x)\<^sup>2 / (2*\<epsilon>)
      = (u y - (norm y)\<^sup>2 / (2*\<epsilon>)) + inner x (y /\<^sub>R \<epsilon>)"
  using e norm_sq_diff_expand[of x y]
  by (simp add: dist_norm field_simps)

theorem supconv_semiconvex:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> B" and e: "0 < \<epsilon>"
  shows "convex_on UNIV (\<lambda>x. supconv u \<epsilon> x + (norm x)\<^sup>2 / (2*\<epsilon>))"
proof -
  have rep: "supconv u \<epsilon> x + (norm x)\<^sup>2 / (2*\<epsilon>)
      = (SUP y. (u y - (norm y)\<^sup>2 / (2*\<epsilon>)) + inner x (y /\<^sub>R \<epsilon>))" for x
  proof -
    have "supconv u \<epsilon> x + (norm x)\<^sup>2 / (2*\<epsilon>)
        = (SUP y. u y - (dist x y)\<^sup>2 / (2*\<epsilon>)) + (norm x)\<^sup>2 / (2*\<epsilon>)"
      unfolding supconv_def by (rule refl)
    also have "\<dots> = (SUP y. (u y - (dist x y)\<^sup>2 / (2*\<epsilon>)) + (norm x)\<^sup>2 / (2*\<epsilon>))"
      using Sup_add_eq[OF supconv_bdd_above[OF B e, where x = x] UNIV_not_empty,
          of "(norm x)\<^sup>2 / (2*\<epsilon>)"]
      by (simp add: add.commute)
    also have "\<dots> = (SUP y. (u y - (norm y)\<^sup>2 / (2*\<epsilon>)) + inner x (y /\<^sub>R \<epsilon>))"
      by (intro SUP_cong refl) (simp add: supconv_square_decomp[OF e])
    finally show ?thesis .
  qed
  have bddx: "bdd_above (range (\<lambda>y. (u y - (norm y)\<^sup>2 / (2*\<epsilon>)) + inner x (y /\<^sub>R \<epsilon>)))"
    for x
  proof -
    have eq: "(\<lambda>y. (u y - (norm y)\<^sup>2 / (2*\<epsilon>)) + inner x (y /\<^sub>R \<epsilon>))
        = (\<lambda>y. (u y - (dist x y)\<^sup>2 / (2*\<epsilon>)) + (norm x)\<^sup>2 / (2*\<epsilon>))"
      by (intro ext) (simp add: supconv_square_decomp[OF e])
    show ?thesis
      unfolding eq
    proof (rule bdd_aboveI[of _ "B + (norm x)\<^sup>2 / (2*\<epsilon>)"])
      fix z assume "z \<in> range (\<lambda>y. (u y - (dist x y)\<^sup>2 / (2*\<epsilon>)) + (norm x)\<^sup>2 / (2*\<epsilon>))"
      then obtain y where zy: "z = (u y - (dist x y)\<^sup>2 / (2*\<epsilon>)) + (norm x)\<^sup>2 / (2*\<epsilon>)"
        by blast
      have "0 \<le> (dist x y)\<^sup>2 / (2*\<epsilon>)" using e by simp
      thus "z \<le> B + (norm x)\<^sup>2 / (2*\<epsilon>)"
        unfolding zy using B[of y] by linarith
    qed
  qed
  show ?thesis
    unfolding rep
    by (intro convex_on_cSUP convex_on_affine_inner bddx)
qed

text \<open>Near-optimizers of the sup-convolution lie within an explicit
  \<open>\<epsilon>\<close>-dependent radius controlled by the oscillation of \<open>u\<close>.\<close>

lemma supconv_near_optimizer:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> B" and e: "0 < \<epsilon>" and d: "0 < \<delta>"
  obtains y where "supconv u \<epsilon> x \<le> u y - (dist x y)\<^sup>2 / (2*\<epsilon>) + \<delta>"
    and "(dist x y)\<^sup>2 \<le> 2*\<epsilon>*(B - u x + \<delta>)"
proof -
  have lt: "supconv u \<epsilon> x - \<delta> < supconv u \<epsilon> x" using d by simp
  have "\<exists>y. supconv u \<epsilon> x - \<delta> < u y - (dist x y)\<^sup>2 / (2*\<epsilon>)"
    using lt unfolding supconv_def
    by (subst (asm) less_cSUP_iff[OF _ supconv_bdd_above[OF B e]]) auto
  then obtain y where y: "supconv u \<epsilon> x - \<delta> < u y - (dist x y)\<^sup>2 / (2*\<epsilon>)"
    by blast
  have h1: "supconv u \<epsilon> x \<le> u y - (dist x y)\<^sup>2 / (2*\<epsilon>) + \<delta>"
    using y by linarith
  have h2: "(dist x y)\<^sup>2 \<le> 2*\<epsilon>*(B - u x + \<delta>)"
  proof -
    have "u x \<le> supconv u \<epsilon> x" by (rule supconv_ge[OF B e])
    with h1 have "(dist x y)\<^sup>2 / (2*\<epsilon>) \<le> u y - u x + \<delta>" by linarith
    also have "\<dots> \<le> B - u x + \<delta>" using B[of y] by linarith
    finally have "(dist x y)\<^sup>2 / (2*\<epsilon>) \<le> B - u x + \<delta>" .
    thus ?thesis using e by (simp add: field_simps)
  qed
  show thesis by (rule that[OF h1 h2])
qed

text \<open>At a point of upper semicontinuity, the sup-convolution converges to
  \<open>u\<close> as \<open>\<epsilon> \<rightarrow> 0\<^sup>+\<close>, the near-optimizer localizing in a ball of radius
  \<open>O(\<surd>\<epsilon>)\<close>; the lower bound is \<open>supconv_ge\<close>.\<close>

lemma supconv_tendsto:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> B"
    and usc: "\<And>c. u x < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist x y < e \<longrightarrow> u y < c"
  shows "((\<lambda>\<epsilon>. supconv u \<epsilon> x) \<longlongrightarrow> u x) (at_right 0)"
proof (rule tendstoI)
  fix \<eta> :: real assume \<eta>: "0 < \<eta>"
  define \<delta> where "\<delta> = min (\<eta>/2) 1"
  have \<delta>pos: "0 < \<delta>" and \<delta>le: "\<delta> \<le> \<eta>/2" and \<delta>1: "\<delta> \<le> 1"
    using \<eta> by (auto simp: \<delta>_def)
  obtain r where r: "0 < r" and rb': "\<And>y. dist x y < r \<Longrightarrow> u y < u x + \<eta>/2"
    using usc[of "u x + \<eta>/2"] \<eta> by auto
  define C where "C = B - u x + 1"
  have C: "0 < C" using B[of x] by (simp add: C_def)
  define \<epsilon>\<^sub>0 where "\<epsilon>\<^sub>0 = r\<^sup>2 / (2*C)"
  have \<epsilon>\<^sub>0: "0 < \<epsilon>\<^sub>0" using r C by (simp add: \<epsilon>\<^sub>0_def)
  have main: "dist (supconv u \<epsilon> x) (u x) < \<eta>"
    if e: "0 < \<epsilon>" and elt: "\<epsilon> < \<epsilon>\<^sub>0" for \<epsilon>
  proof -
    obtain y where h1: "supconv u \<epsilon> x \<le> u y - (dist x y)\<^sup>2 / (2*\<epsilon>) + \<delta>"
      and h2: "(dist x y)\<^sup>2 \<le> 2*\<epsilon>*(B - u x + \<delta>)"
      by (rule supconv_near_optimizer[OF B e \<delta>pos])
    have "2*\<epsilon>*(B - u x + \<delta>) \<le> 2*\<epsilon>*C"
      using \<delta>1 e by (intro mult_left_mono) (auto simp: C_def)
    with h2 have "(dist x y)\<^sup>2 \<le> 2*\<epsilon>*C" by linarith
    also have "\<dots> < r\<^sup>2"
      using elt C by (simp add: \<epsilon>\<^sub>0_def field_simps)
    finally have dsq: "(dist x y)\<^sup>2 < r\<^sup>2" .
    have dxy: "dist x y < r"
    proof (rule ccontr)
      assume "\<not> dist x y < r"
      hence "r\<^sup>2 \<le> (dist x y)\<^sup>2" using r by (intro power_mono) auto
      thus False using dsq by linarith
    qed
    have nn: "0 \<le> (dist x y)\<^sup>2 / (2*\<epsilon>)" using e by simp
    have "supconv u \<epsilon> x \<le> u y + \<delta>" using h1 nn by linarith
    also have "\<dots> < u x + \<eta>/2 + \<eta>/2"
      using rb'[OF dxy] \<delta>le by linarith
    finally have ub: "supconv u \<epsilon> x < u x + \<eta>" by simp
    have lb: "u x \<le> supconv u \<epsilon> x" by (rule supconv_ge[OF B e])
    show ?thesis using ub lb by (simp add: dist_real_def)
  qed
  have "eventually (\<lambda>\<epsilon>. \<epsilon> \<in> {0<..<\<epsilon>\<^sub>0}) (at_right (0::real))"
    by (rule eventually_at_right_real[OF \<epsilon>\<^sub>0])
  thus "eventually (\<lambda>\<epsilon>. dist (supconv u \<epsilon> x) (u x) < \<eta>) (at_right 0)"
    by (rule eventually_mono) (use main in auto)
qed


subsection \<open>Composing the three big theorems on the sup-convolution\<close>

text \<open>\<open>supconv_semiconvex\<close> delivers semiconvexity in the form
  \<open>(norm x)\<^sup>2 / (2*\<epsilon>)\<close>, while \<open>jensen_lemma\<close> and \<open>semiconvex_alexandrov\<close>
  consume it as \<open>(c/2) * (norm x)\<^sup>2\<close>.  The two agree with \<open>c = 1/\<epsilon>\<close>;
  restating it once here lets the three theorems compose without
  re-deriving anything.\<close>

lemma supconv_semiconvex':
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> B" and e: "0 < \<epsilon>"
  shows "convex_on UNIV (\<lambda>x. supconv u \<epsilon> x + ((1/\<epsilon>)/2) * (norm x)\<^sup>2)"
proof -
  have eq: "(\<lambda>x::'a. supconv u \<epsilon> x + ((1/\<epsilon>)/2) * (norm x)\<^sup>2)
      = (\<lambda>x. supconv u \<epsilon> x + (norm x)\<^sup>2 / (2*\<epsilon>))"
  proof (rule ext)
    fix x :: 'a
    have "((1/\<epsilon>)/2) * (norm x)\<^sup>2 = (norm x)\<^sup>2 / (2*\<epsilon>)"
      by (simp add: field_simps)
    thus "supconv u \<epsilon> x + ((1/\<epsilon>)/2) * (norm x)\<^sup>2
        = supconv u \<epsilon> x + (norm x)\<^sup>2 / (2*\<epsilon>)" by simp
  qed
  show ?thesis unfolding eq by (rule supconv_semiconvex[OF B e])
qed

text \<open>The sup-convolution is continuous, being semiconvex.\<close>

theorem supconv_continuous:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> B" and e: "0 < \<epsilon>"
  shows "continuous_on UNIV (supconv u \<epsilon>)"
  by (rule semiconvex_continuous[OF supconv_semiconvex'[OF B e]])

text \<open>The sup-convolution of any bounded-above function is twice
  differentiable almost everywhere: the fact that supplies genuine
  second derivatives at the perturbed maximizer produced by Jensen's
  lemma.\<close>

corollary supconv_alexandrov:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> B" and e: "0 < \<epsilon>"
  shows "negligible {y. \<not> (\<exists>p X. bounded_linear X \<and> (\<forall>v w. v \<bullet> X w = w \<bullet> X v)
      \<and> ((\<lambda>k. (supconv u \<epsilon> (y + k) - supconv u \<epsilon> y - p \<bullet> k - (k \<bullet> X k)/2)
          / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0))}"
  by (rule semiconvex_alexandrov[OF supconv_semiconvex'[OF B e]])

text \<open>Jensen's lemma applies verbatim: the set of points maximizing a
  small linear perturbation of the sup-convolution is not negligible, so
  it meets the full-measure set of the previous corollary --- exactly
  where the theorem on sums reads off its matrices.\<close>

text \<open>The engine of Crandall--Ishii: Jensen's lemma gives perturbed
  maximizers positive measure, Alexandrov's gives twice differentiable
  points full measure, so the two sets meet.  A single point is
  simultaneously a perturbed maximizer and a point of genuine
  second-order expansion, which is how the theorem on sums produces its
  matrices.\<close>

text \<open>Second-order conditions at an interior maximum: a second-order
  expansion with data \<open>(q, X)\<close> at an interior maximizer forces \<open>q = 0\<close>
  and \<open>X\<close> negative semidefinite, both from the same limit
  \<open>R (t *\<^sub>R v) / t\<^sup>2 \<longrightarrow> 0\<close>, dividing the maximality inequality by \<open>t\<close> and
  by \<open>t\<^sup>2\<close>.  This upgrades the Alexandrov expansion at the Jensen point
  into a genuine second-order jet.\<close>

lemma second_order_interior_max:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes blX: "bounded_linear X"
    and \<delta>: "0 < \<delta>"
    and xmax: "\<And>k. norm k < \<delta> \<Longrightarrow> f (x + k) \<le> f x"
    and exp: "((\<lambda>k. (f (x + k) - f x - q \<bullet> k - (k \<bullet> X k)/2) / (norm k)\<^sup>2)
        \<longlongrightarrow> 0) (at 0)"
  shows "q \<bullet> v = 0 \<and> v \<bullet> X v \<le> 0"
proof -
  define R where "R = (\<lambda>k. f (x + k) - f x - q \<bullet> k - (k \<bullet> X k)/2)"
  have linX: "X (t *\<^sub>R w) = t *\<^sub>R X w" for t :: real and w
    using blX by (simp add: linear_simps)
  have quad: "(t *\<^sub>R w) \<bullet> X (t *\<^sub>R w) = t\<^sup>2 * (w \<bullet> X w)" for t :: real and w
    unfolding linX by (simp add: power2_eq_square)
  have Rexp: "R (t *\<^sub>R w)
      = f (x + t *\<^sub>R w) - f x - t * (q \<bullet> w) - t\<^sup>2 * (w \<bullet> X w)/2"
    for t :: real and w
    unfolding R_def quad by simp
  have key: "q \<bullet> w \<le> 0 \<and> (q \<bullet> w = 0 \<longrightarrow> w \<bullet> X w \<le> 0)" if wnz: "w \<noteq> 0" for w
  proof -
    have nw: "0 < norm w" using wnz by simp
    have nwsq: "(norm w)\<^sup>2 \<noteq> 0" using nw by simp
    have flt: "filterlim (\<lambda>t::real. t *\<^sub>R w) (at 0) (at_right 0)"
    proof (rule filterlim_atI)
      have "((\<lambda>t::real. t *\<^sub>R w) \<longlongrightarrow> 0 *\<^sub>R w) (at_right 0)"
        by (intro tendsto_intros)
      thus "((\<lambda>t::real. t *\<^sub>R w) \<longlongrightarrow> 0) (at_right 0)" by simp
      show "\<forall>\<^sub>F t in at_right (0::real). t *\<^sub>R w \<noteq> 0"
        using eventually_at_right_less by (rule eventually_mono) (use wnz in simp)
    qed
    have lim2: "((\<lambda>t. R (t *\<^sub>R w) / (norm (t *\<^sub>R w))\<^sup>2) \<longlongrightarrow> 0) (at_right 0)"
      unfolding R_def by (rule filterlim_compose[OF exp flt])
    have prod: "((\<lambda>t. (R (t *\<^sub>R w) / (norm (t *\<^sub>R w))\<^sup>2) * (norm w)\<^sup>2)
        \<longlongrightarrow> 0 * (norm w)\<^sup>2) (at_right 0)"
      by (rule tendsto_mult[OF lim2 tendsto_const])
    have rw: "(R (t *\<^sub>R w) / (norm (t *\<^sub>R w))\<^sup>2) * (norm w)\<^sup>2 = R (t *\<^sub>R w) / t\<^sup>2"
      for t :: real
    proof -
      have "(norm (t *\<^sub>R w))\<^sup>2 = t\<^sup>2 * (norm w)\<^sup>2"
        by (simp add: power_mult_distrib)
      thus ?thesis using nwsq by simp
    qed
    have lim3: "((\<lambda>t. R (t *\<^sub>R w) / t\<^sup>2) \<longlongrightarrow> 0) (at_right 0)"
      using prod unfolding rw by simp
    have lim4: "((\<lambda>t. (R (t *\<^sub>R w) / t\<^sup>2) * t) \<longlongrightarrow> 0 * 0) (at_right 0)"
      by (rule tendsto_mult[OF lim3]) simp
    have rw2: "(R (t *\<^sub>R w) / t\<^sup>2) * t = R (t *\<^sub>R w) / t" for t :: real
      by (cases "t = 0") (auto simp: power2_eq_square)
    have lim5: "((\<lambda>t. R (t *\<^sub>R w) / t) \<longlongrightarrow> 0) (at_right 0)"
      using lim4 unfolding rw2 by simp
    have small: "\<forall>\<^sub>F t in at_right (0::real).
        R (t *\<^sub>R w) + t * (q \<bullet> w) + t\<^sup>2 * (w \<bullet> X w)/2 \<le> 0 \<and> 0 < t"
    proof (rule eventually_mono[OF eventually_conj[OF
        eventually_at_right_real[OF divide_pos_pos[OF \<delta> nw]] eventually_at_right_less]])
      fix t :: real assume t: "t \<in> {0<..<\<delta>/norm w} \<and> 0 < t"
      hence t0: "0 < t" and tlt: "t < \<delta>/norm w" by auto
      have "norm (t *\<^sub>R w) = t * norm w" using t0 by simp
      also have "\<dots> < \<delta>" using tlt nw by (simp add: field_simps)
      finally have "f (x + t *\<^sub>R w) \<le> f x" by (rule xmax)
      thus "R (t *\<^sub>R w) + t * (q \<bullet> w) + t\<^sup>2 * (w \<bullet> X w)/2 \<le> 0 \<and> 0 < t"
        unfolding Rexp using t0 by simp
    qed
    have g1: "\<forall>\<^sub>F t in at_right (0::real).
        R (t *\<^sub>R w) / t + (q \<bullet> w) + t * (w \<bullet> X w)/2 \<le> 0"
    proof (rule eventually_mono[OF small])
      fix t :: real
      assume "R (t *\<^sub>R w) + t * (q \<bullet> w) + t\<^sup>2 * (w \<bullet> X w)/2 \<le> 0 \<and> 0 < t"
      hence ineq: "R (t *\<^sub>R w) + t * (q \<bullet> w) + t\<^sup>2 * (w \<bullet> X w)/2 \<le> 0"
        and t0: "0 < t" by auto
      have "(R (t *\<^sub>R w) + t * (q \<bullet> w) + t\<^sup>2 * (w \<bullet> X w)/2) / t
          = R (t *\<^sub>R w) / t + (q \<bullet> w) + t * (w \<bullet> X w)/2"
        using t0 by (simp add: field_simps power2_eq_square)
      moreover have "(R (t *\<^sub>R w) + t * (q \<bullet> w) + t\<^sup>2 * (w \<bullet> X w)/2) / t \<le> 0"
        using ineq t0 by (simp add: divide_nonpos_pos)
      ultimately show "R (t *\<^sub>R w) / t + (q \<bullet> w) + t * (w \<bullet> X w)/2 \<le> 0" by simp
    qed
    have c1: "((\<lambda>t. R (t *\<^sub>R w) / t + (q \<bullet> w) + t * (w \<bullet> X w)/2)
        \<longlongrightarrow> 0 + (q \<bullet> w) + 0 * (w \<bullet> X w)/2) (at_right 0)"
      by (intro tendsto_intros lim5) simp
    have qle: "q \<bullet> w \<le> 0"
      by (rule tendsto_upperbound[OF _ g1])
        (use c1 in \<open>simp_all\<close>)
    have hess: "w \<bullet> X w \<le> 0" if qz: "q \<bullet> w = 0"
    proof -
      have g2: "\<forall>\<^sub>F t in at_right (0::real).
          R (t *\<^sub>R w) / t\<^sup>2 + (w \<bullet> X w)/2 \<le> 0"
      proof (rule eventually_mono[OF small])
        fix t :: real
        assume "R (t *\<^sub>R w) + t * (q \<bullet> w) + t\<^sup>2 * (w \<bullet> X w)/2 \<le> 0 \<and> 0 < t"
        hence ineq: "R (t *\<^sub>R w) + t * (q \<bullet> w) + t\<^sup>2 * (w \<bullet> X w)/2 \<le> 0"
          and t0: "0 < t" by auto
        have i2: "R (t *\<^sub>R w) + t\<^sup>2 * (w \<bullet> X w)/2 \<le> 0" using ineq qz by simp
        have "(R (t *\<^sub>R w) + t\<^sup>2 * (w \<bullet> X w)/2) / t\<^sup>2
            = R (t *\<^sub>R w) / t\<^sup>2 + (w \<bullet> X w)/2"
          using t0 by (simp add: field_simps)
        moreover have "(R (t *\<^sub>R w) + t\<^sup>2 * (w \<bullet> X w)/2) / t\<^sup>2 \<le> 0"
          using i2 t0 by (simp add: divide_nonpos_pos)
        ultimately show "R (t *\<^sub>R w) / t\<^sup>2 + (w \<bullet> X w)/2 \<le> 0" by simp
      qed
      have c2: "((\<lambda>t. R (t *\<^sub>R w) / t\<^sup>2 + (w \<bullet> X w)/2)
          \<longlongrightarrow> 0 + (w \<bullet> X w)/2) (at_right 0)"
        by (intro tendsto_intros lim3)
      have "(w \<bullet> X w)/2 \<le> 0"
        by (rule tendsto_upperbound[OF _ g2])
          (use c2 in \<open>simp_all\<close>)
      thus ?thesis by simp
    qed
    show ?thesis using qle hess by blast
  qed
  show ?thesis
  proof (cases "v = 0")
    case True
    have "X 0 = 0" using blX by (simp add: linear_simps)
    thus ?thesis unfolding True by simp
  next
    case False
    have nv: "- v \<noteq> 0" using False by simp
    have le1: "q \<bullet> v \<le> 0" using key[OF False] by blast
    have le2: "q \<bullet> (- v) \<le> 0" using key[OF nv] by blast
    have qz: "q \<bullet> v = 0" using le1 le2 by simp
    have "v \<bullet> X v \<le> 0" using key[OF False] qz by blast
    with qz show ?thesis by blast
  qed
qed



subsection \<open>The second-order necessary condition at a local minimum\<close>

text \<open>The classical first- and second-order conditions at a local minimum of
  \<open>\<psi>\<close> whose gradient \<open>g\<close> is differentiable at \<open>x\<close> with Hessian \<open>H\<close>: \<open>g x = 0\<close>
  and \<open>H\<close> is positive semidefinite.  The latter is \<open>second_order_interior_max\<close>
  for \<open>-\<psi>\<close> restricted to a line, once the gradient condition has been turned
  into a second-order expansion along that line.\<close>

lemma local_min_gradient_zero:
  fixes \<psi> :: "'a::euclidean_space \<Rightarrow> real"
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

text \<open>Along a line, a gradient differentiable at \<open>x\<close> gives a second-order
  (Peano) expansion of \<open>\<psi>\<close>: the error of the quadratic Taylor polynomial is
  \<open>o(t\<^sup>2)\<close>, by the mean value theorem applied to the error itself.\<close>

lemma peano_expansion_along_line:
  fixes \<psi> :: "real^'n::finite \<Rightarrow> real" and g :: "real^'n \<Rightarrow> real^'n"
    and H :: "real^'n^'n"
  assumes e: "0 < e"
    and deriv: "\<And>y. y \<in> ball x e \<Longrightarrow> (\<psi> has_derivative (\<lambda>h. g y \<bullet> h)) (at y)"
    and hess: "(g has_derivative (\<lambda>h. H *v h)) (at x)"
  shows "((\<lambda>t. (\<psi> (x + t *\<^sub>R h) - \<psi> x - t * (g x \<bullet> h) - t\<^sup>2 * (h \<bullet> (H *v h)) / 2)
      / t\<^sup>2) \<longlongrightarrow> 0) (at 0)"
proof (rule tendstoI)
  fix \<epsilon> :: real assume \<epsilon>: "0 < \<epsilon>"
  define K where "K = (norm h)\<^sup>2 + 1"
  have K0: "0 < K" and hK: "(norm h)\<^sup>2 \<le> K"
    unfolding K_def using zero_le_power2[of "norm h"] by linarith+
  define c where "c = \<epsilon> / (2 * K)"
  have c: "0 < c"
    unfolding c_def using \<epsilon> K0 by simp
  have cK: "c * K = \<epsilon> / 2"
    unfolding c_def using K0 by simp
  obtain r where r: "0 < r"
    and rg: "\<And>y. norm (y - x) < r \<Longrightarrow> norm (g y - g x - H *v (y - x)) \<le> c * norm (y - x)"
    using hess c unfolding has_derivative_at_alt by blast
  have nh: "0 < norm h + 1"
    using norm_ge_zero[of h] by linarith
  define d where "d = min r e / (norm h + 1)"
  have d: "0 < d"
    unfolding d_def using r e nh by simp
  have small: "norm (s *\<^sub>R h) < min r e" if "\<bar>s\<bar> < d" for s
  proof -
    have "norm (s *\<^sub>R h) \<le> \<bar>s\<bar> * (norm h + 1)"
      by (simp add: mult_left_mono)
    also have "\<dots> < min r e"
      using that nh by (simp add: d_def pos_less_divide_eq)
    finally show ?thesis .
  qed
  define D where "D = (\<lambda>s. (g (x + s *\<^sub>R h) - g x - H *v (s *\<^sub>R h)) \<bullet> h)"
  define R where "R = (\<lambda>s. \<psi> (x + s *\<^sub>R h) - s * (g x \<bullet> h) - s * s * (h \<bullet> (H *v h)) / 2)"
  have Rd: "(R has_real_derivative D s) (at s)" if s: "\<bar>s\<bar> < d" for s
  proof -
    have 1: "((\<lambda>s. x + s *\<^sub>R h) has_derivative (\<lambda>s. s *\<^sub>R h)) (at s)"
      by (auto intro!: derivative_eq_intros)
    have 2: "(\<psi> has_derivative (\<lambda>k. g (x + s *\<^sub>R h) \<bullet> k)) (at (x + s *\<^sub>R h))"
      by (rule deriv) (use small[OF s] in \<open>simp add: dist_norm\<close>)
    have "((\<lambda>s. \<psi> (x + s *\<^sub>R h)) has_derivative (\<lambda>u. g (x + s *\<^sub>R h) \<bullet> (u *\<^sub>R h))) (at s)"
      using diff_chain_at[OF 1 2] by (simp add: o_def)
    then have 3: "((\<lambda>s. \<psi> (x + s *\<^sub>R h)) has_real_derivative (g (x + s *\<^sub>R h) \<bullet> h)) (at s)"
      unfolding has_field_derivative_def
      by (rule has_derivative_eq_rhs) (simp add: fun_eq_iff mult.commute)
    have Ds: "D s = g (x + s *\<^sub>R h) \<bullet> h - g x \<bullet> h - s * (h \<bullet> (H *v h))"
      by (simp add: D_def inner_diff_left matrix_vector_mult_scaleR inner_commute[of "H *v h" h])
    have 4: "((\<lambda>s. s * (g x \<bullet> h)) has_real_derivative (g x \<bullet> h)) (at s)"
      by (auto intro!: derivative_eq_intros)
    have 5: "((\<lambda>s. s * s * (h \<bullet> (H *v h)) / 2) has_real_derivative s * (h \<bullet> (H *v h))) (at s)"
      by (auto intro!: derivative_eq_intros simp: algebra_simps)
    show ?thesis
      unfolding R_def Ds by (intro DERIV_diff 3 4 5)
  qed
  have key: "dist ((\<psi> (x + t *\<^sub>R h) - \<psi> x - t * (g x \<bullet> h)
      - t\<^sup>2 * (h \<bullet> (H *v h)) / 2) / t\<^sup>2) 0 < \<epsilon>"
    if t0: "t \<noteq> 0" and td: "\<bar>t\<bar> < d" for t
  proof -
    obtain z where z: "\<bar>z\<bar> \<le> \<bar>t\<bar>" and Rz: "R t - R 0 = t * D z"
    proof (cases "0 < t")
      case True
      have "\<exists>z. 0 < z \<and> z < t \<and> R t - R 0 = (t - 0) * D z"
        by (rule MVT2[OF True Rd]) (use td in auto)
      then show thesis
        using that by force
    next
      case False
      with t0 have neg: "t < 0"
        by simp
      have "\<exists>z. t < z \<and> z < 0 \<and> R 0 - R t = (0 - t) * D z"
        by (rule MVT2[OF neg Rd]) (use td in auto)
      then obtain z where "t < z" "z < 0" "R 0 - R t = (0 - t) * D z"
        by blast
      then show thesis
        by (intro that[of z]) (auto simp: algebra_simps)
    qed
    have zd: "\<bar>z\<bar> < d"
      using z td by linarith
    have "norm (z *\<^sub>R h) < r"
      using small[OF zd] by simp
    then have "norm (g (x + z *\<^sub>R h) - g x - H *v (z *\<^sub>R h)) \<le> c * norm (z *\<^sub>R h)"
      using rg[of "x + z *\<^sub>R h"] by simp
    then have "\<bar>D z\<bar> \<le> c * norm (z *\<^sub>R h) * norm h"
      unfolding D_def by (rule order_trans[OF Cauchy_Schwarz_ineq2 mult_right_mono]) simp
    also have "\<dots> \<le> c * (\<bar>t\<bar> * norm h) * norm h"
      using z c by (intro mult_right_mono mult_left_mono) (auto intro: mult_right_mono)
    also have "\<dots> = c * (norm h)\<^sup>2 * \<bar>t\<bar>"
      by (simp add: power2_eq_square)
    also have "\<dots> \<le> c * K * \<bar>t\<bar>"
      using c hK by (intro mult_right_mono mult_left_mono) auto
    finally have Dz: "\<bar>D z\<bar> \<le> \<epsilon> / 2 * \<bar>t\<bar>"
      unfolding cK .
    have "\<bar>R t - R 0\<bar> \<le> \<epsilon> / 2 * t\<^sup>2"
    proof -
      have "\<bar>R t - R 0\<bar> = \<bar>t\<bar> * \<bar>D z\<bar>"
        unfolding Rz by (rule abs_mult)
      also have "\<dots> \<le> \<bar>t\<bar> * (\<epsilon> / 2 * \<bar>t\<bar>)"
        by (rule mult_left_mono[OF Dz]) simp
      also have "\<dots> = \<epsilon> / 2 * t\<^sup>2"
        by (simp add: power2_eq_square abs_mult_self)
      finally show ?thesis .
    qed
    moreover have "R t - R 0 = \<psi> (x + t *\<^sub>R h) - \<psi> x - t * (g x \<bullet> h) - t\<^sup>2 * (h \<bullet> (H *v h)) / 2"
      by (simp add: R_def power2_eq_square)
    moreover have "0 < \<epsilon> * t\<^sup>2"
      using t0 \<epsilon> by simp
    ultimately have "\<bar>\<psi> (x + t *\<^sub>R h) - \<psi> x - t * (g x \<bullet> h) - t\<^sup>2 * (h \<bullet> (H *v h)) / 2\<bar>
        < \<epsilon> * t\<^sup>2"
      by linarith
    then show "dist ((\<psi> (x + t *\<^sub>R h) - \<psi> x - t * (g x \<bullet> h)
        - t\<^sup>2 * (h \<bullet> (H *v h)) / 2) / t\<^sup>2) 0 < \<epsilon>"
      using t0 by (simp add: dist_real_def abs_divide divide_less_eq)
  qed
  show "\<forall>\<^sub>F t in at 0. dist ((\<psi> (x + t *\<^sub>R h) - \<psi> x - t * (g x \<bullet> h)
      - t\<^sup>2 * (h \<bullet> (H *v h)) / 2) / t\<^sup>2) 0 < \<epsilon>"
    unfolding eventually_at
    by (intro exI[of _ d] conjI d ballI impI key) auto
qed

lemma local_min_hessian_psd:
  fixes \<psi> :: "real^'n::finite \<Rightarrow> real" and g :: "real^'n \<Rightarrow> real^'n"
    and H :: "real^'n^'n"
  assumes e_pos: "0 < e"
    and deriv: "\<And>y. y \<in> ball x e \<Longrightarrow> (\<psi> has_derivative (\<lambda>h. g y \<bullet> h)) (at y)"
    and hess: "(g has_derivative (\<lambda>h. H *v h)) (at x)"
    and min: "\<And>y. y \<in> ball x e \<Longrightarrow> \<psi> x \<le> \<psi> y"
  shows "0 \<le> h \<bullet> (H *v h)"
proof -
  define d where "d = e / (norm h + 1)"
  have d: "0 < d"
    unfolding d_def using e_pos by (simp add: add_nonneg_pos)
  have mx: "- \<psi> (x + (0 + t) *\<^sub>R h) \<le> - \<psi> (x + 0 *\<^sub>R h)" if "norm t < d" for t :: real
  proof -
    have nh: "0 < norm h + 1"
      using norm_ge_zero[of h] by linarith
    have "norm (t *\<^sub>R h) \<le> \<bar>t\<bar> * (norm h + 1)"
      by (simp add: mult_left_mono)
    also have "\<dots> < e"
      using that nh by (simp add: d_def pos_less_divide_eq)
    finally show ?thesis
      using min[of "x + t *\<^sub>R h"] by (simp add: dist_norm)
  qed
  have peano: "((\<lambda>t. - ((\<psi> (x + t *\<^sub>R h) - \<psi> x - t * (g x \<bullet> h)
      - t\<^sup>2 * (h \<bullet> (H *v h)) / 2) / t\<^sup>2)) \<longlongrightarrow> 0) (at 0)"
    using tendsto_minus[OF peano_expansion_along_line[OF e_pos deriv hess, of h]]
    unfolding minus_zero .
  have eq: "(- \<psi> (x + (0 + t) *\<^sub>R h) - - \<psi> (x + 0 *\<^sub>R h) - (- (g x \<bullet> h)) \<bullet> t
      - (t \<bullet> (- (h \<bullet> (H *v h)) * t)) / 2) / (norm t)\<^sup>2
      = - ((\<psi> (x + t *\<^sub>R h) - \<psi> x - t * (g x \<bullet> h)
      - t\<^sup>2 * (h \<bullet> (H *v h)) / 2) / t\<^sup>2)" for t :: real
  proof -
    have "- \<psi> (x + (0 + t) *\<^sub>R h) - - \<psi> (x + 0 *\<^sub>R h) - (- (g x \<bullet> h)) \<bullet> t
        - (t \<bullet> (- (h \<bullet> (H *v h)) * t)) / 2
        = - (\<psi> (x + t *\<^sub>R h) - \<psi> x - t * (g x \<bullet> h) - t\<^sup>2 * (h \<bullet> (H *v h)) / 2)"
      by (simp add: inner_real_def power2_eq_square algebra_simps)
    then show ?thesis
      by (simp only: real_norm_def power2_abs divide_minus_left)
  qed
  have "((\<lambda>t. (- \<psi> (x + (0 + t) *\<^sub>R h) - - \<psi> (x + 0 *\<^sub>R h) - (- (g x \<bullet> h)) \<bullet> t
      - (t \<bullet> (- (h \<bullet> (H *v h)) * t)) / 2) / (norm t)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    unfolding eq by (rule peano)
  from second_order_interior_max[OF bounded_linear_mult_right d mx this, of 1]
  show ?thesis
    by simp
qed

(*<*)
end
(*>*)
