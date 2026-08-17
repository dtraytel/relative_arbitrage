section \<open>Sup-convolutions\<close>

(*<*)
theory Sup_Convolution
  imports Jensen_Lemma
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

lemma cSUP_plus_const:
  fixes g :: "'b \<Rightarrow> real" and c :: real
  assumes bdd: "bdd_above (range g)"
  shows "(SUP y. g y) + c = (SUP y. g y + c)"
proof (rule antisym)
  have ne: "(UNIV :: 'b set) \<noteq> {}" by simp
  have bdd2: "bdd_above (range (\<lambda>y. g y + c))"
  proof -
    from bdd obtain M where M: "\<And>y. g y \<le> M" by (auto simp: bdd_above_def)
    show ?thesis by (rule bdd_aboveI[of _ "M + c"]) (use M in auto)
  qed
  have up: "g y \<le> (SUP y. g y + c) - c" for y
  proof -
    have "g y + c \<le> (SUP y. g y + c)"
      by (intro cSUP_upper bdd2 rangeI) simp
    thus ?thesis by linarith
  qed
  have "(SUP y. g y) \<le> (SUP y. g y + c) - c"
    by (intro cSUP_least ne up)
  thus "(SUP y. g y) + c \<le> (SUP y. g y + c)" by linarith
  have le2: "g y + c \<le> (SUP y. g y) + c" for y
    by (intro add_right_mono cSUP_upper bdd rangeI) simp
  show "(SUP y. g y + c) \<le> (SUP y. g y) + c"
    by (intro cSUP_least ne le2)
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
proof -
  have "(dist x y)\<^sup>2 = (norm x)\<^sup>2 - 2 * inner x y + (norm y)\<^sup>2"
    by (simp add: dist_norm power2_norm_eq_inner inner_diff_left inner_diff_right
        inner_commute)
  hence "(dist x y)\<^sup>2 / (2*\<epsilon>)
      = (norm x)\<^sup>2 / (2*\<epsilon>) - inner x y / \<epsilon> + (norm y)\<^sup>2 / (2*\<epsilon>)"
    using e by (simp add: field_simps)
  moreover have "inner x (y /\<^sub>R \<epsilon>) = inner x y / \<epsilon>"
    by (simp add: divide_inverse mult.commute)
  ultimately show ?thesis by simp
qed

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
      by (rule cSUP_plus_const[OF supconv_bdd_above[OF B e]])
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

text \<open>The sup-convolution is continuous: it is a finite convex function
  (continuous by \<open>convex_on_continuous\<close>) minus the smooth \<open>|x|\<^sup>2/(2\<epsilon>)\<close>.\<close>

theorem supconv_continuous:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> B" and e: "0 < \<epsilon>"
  shows "continuous_on UNIV (supconv u \<epsilon>)"
proof -
  have g: "continuous_on UNIV (\<lambda>x. supconv u \<epsilon> x + (norm x)\<^sup>2 / (2*\<epsilon>))"
    by (rule convex_on_continuous[OF open_UNIV supconv_semiconvex[OF B e]])
  have h: "continuous_on UNIV (\<lambda>x :: 'a. (norm x)\<^sup>2 / (2*\<epsilon>))"
    using e by (intro continuous_intros) simp
  have eq: "supconv u \<epsilon> = (\<lambda>x. (supconv u \<epsilon> x + (norm x)\<^sup>2 / (2*\<epsilon>))
      - (norm x)\<^sup>2 / (2*\<epsilon>))"
    by (rule ext) simp
  show ?thesis
    by (subst eq) (intro continuous_on_diff g h)
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

text \<open>At a point of continuity, the sup-convolution converges to \<open>u\<close> as
  \<open>\<epsilon> \<rightarrow> 0\<^sup>+\<close>, the near-optimizer localizing in a ball of radius
  \<open>O(\<surd>\<epsilon>)\<close>.\<close>

lemma supconv_tendsto:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> B" and cont: "continuous (at x) u"
  shows "((\<lambda>\<epsilon>. supconv u \<epsilon> x) \<longlongrightarrow> u x) (at_right 0)"
proof (rule tendstoI)
  fix \<eta> :: real assume \<eta>: "0 < \<eta>"
  define \<delta> where "\<delta> = min (\<eta>/2) 1"
  have \<delta>pos: "0 < \<delta>" and \<delta>le: "\<delta> \<le> \<eta>/2" and \<delta>1: "\<delta> \<le> 1"
    using \<eta> by (auto simp: \<delta>_def)
  have "eventually (\<lambda>y. dist (u y) (u x) < \<eta>/2) (at x)"
    by (rule tendstoD[OF cont[unfolded continuous_at]]) (use \<eta> in simp)
  then obtain r where r: "0 < r"
    and rb: "\<And>y. y \<noteq> x \<Longrightarrow> dist y x < r \<Longrightarrow> dist (u y) (u x) < \<eta>/2"
    unfolding eventually_at by blast
  have rb': "u y < u x + \<eta>/2" if "dist x y < r" for y
  proof (cases "y = x")
    case True thus ?thesis using \<eta> by simp
  next
    case False
    hence "dist (u y) (u x) < \<eta>/2"
      using rb[OF False] that by (metis dist_commute)
    thus ?thesis unfolding dist_real_def abs_diff_less_iff by linarith
  qed
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

corollary supconv_jensen:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> B" and e: "0 < \<epsilon>"
    and rho: "0 < \<rho>" "\<rho> < r"
    and bnd: "\<And>y. y \<in> cball \<xi> r \<Longrightarrow> \<rho> \<le> dist y \<xi> \<Longrightarrow> supconv u \<epsilon> y \<le> m"
    and d: "0 < d" and small: "2 * d * r < supconv u \<epsilon> \<xi> - m"
  shows "\<not> negligible {x \<in> cball \<xi> r. \<exists>p. norm p \<le> d
      \<and> (\<forall>y \<in> cball \<xi> r. supconv u \<epsilon> y + p \<bullet> y \<le> supconv u \<epsilon> x + p \<bullet> x)}"
proof -
  have cpos: "0 < 1/\<epsilon>" using e by simp
  show ?thesis
    by (rule jensen_lemma[OF supconv_semiconvex'[OF B e] cpos rho(1) rho(2)
        bnd d small])
qed

text \<open>The engine of Crandall--Ishii: Jensen's lemma gives perturbed
  maximizers positive measure, Alexandrov's gives twice differentiable
  points full measure, so the two sets meet.  A single point is
  simultaneously a perturbed maximizer and a point of genuine
  second-order expansion, which is how the theorem on sums produces its
  matrices.\<close>

theorem supconv_jensen_alexandrov_point:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> B" and e: "0 < \<epsilon>"
    and rho: "0 < \<rho>" "\<rho> < r"
    and bnd: "\<And>y. y \<in> cball \<xi> r \<Longrightarrow> \<rho> \<le> dist y \<xi> \<Longrightarrow> supconv u \<epsilon> y \<le> m"
    and d: "0 < d" and small: "2 * d * r < supconv u \<epsilon> \<xi> - m"
  shows "\<exists>x \<in> cball \<xi> r.
      (\<exists>p. norm p \<le> d
         \<and> (\<forall>y \<in> cball \<xi> r. supconv u \<epsilon> y + p \<bullet> y \<le> supconv u \<epsilon> x + p \<bullet> x))
    \<and> (\<exists>q X. bounded_linear X \<and> (\<forall>v w. v \<bullet> X w = w \<bullet> X v)
         \<and> ((\<lambda>k. (supconv u \<epsilon> (x + k) - supconv u \<epsilon> x - q \<bullet> k - (k \<bullet> X k)/2)
             / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0))"
proof -
  define J where "J = {x \<in> cball \<xi> r. \<exists>p. norm p \<le> d
      \<and> (\<forall>y \<in> cball \<xi> r. supconv u \<epsilon> y + p \<bullet> y \<le> supconv u \<epsilon> x + p \<bullet> x)}"
  define N where "N = {y. \<not> (\<exists>q X. bounded_linear X \<and> (\<forall>v w. v \<bullet> X w = w \<bullet> X v)
      \<and> ((\<lambda>k. (supconv u \<epsilon> (y + k) - supconv u \<epsilon> y - q \<bullet> k - (k \<bullet> X k)/2)
          / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0))}"
  have nJ: "\<not> negligible J"
    unfolding J_def by (rule supconv_jensen[OF B e rho(1) rho(2) bnd d small])
  have nN: "negligible N"
    unfolding N_def by (rule supconv_alexandrov[OF B e])
  have "\<not> (J \<subseteq> N)"
  proof
    assume sub: "J \<subseteq> N"
    have "negligible J" by (rule negligible_subset[OF nN sub])
    with nJ show False ..
  qed
  then obtain x where xJ: "x \<in> J" and xN: "x \<notin> N" by blast
  show ?thesis
  proof (rule bexI)
    show "x \<in> cball \<xi> r" using xJ unfolding J_def by blast
    show "(\<exists>p. norm p \<le> d
           \<and> (\<forall>y \<in> cball \<xi> r. supconv u \<epsilon> y + p \<bullet> y \<le> supconv u \<epsilon> x + p \<bullet> x))
        \<and> (\<exists>q X. bounded_linear X \<and> (\<forall>v w. v \<bullet> X w = w \<bullet> X v)
             \<and> ((\<lambda>k. (supconv u \<epsilon> (x + k) - supconv u \<epsilon> x - q \<bullet> k - (k \<bullet> X k)/2)
                 / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0))"
      using xJ xN unfolding J_def N_def by blast
  qed
qed

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


(*<*)
end
(*>*)
