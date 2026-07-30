section \<open>Sup-convolutions\<close>

text \<open>
  Phase E of the plan (STATUS.md): the Crandall--Ishii development. This
  theory is E1, the sup-convolution
  \<open>u\<^sup>\<epsilon>(x) = SUP y. u y - |x - y|\<^sup>2/(2\<epsilon>)\<close> of a bounded function, and its
  basic calculus: it dominates \<open>u\<close>, is bounded by \<open>u\<close>'s bound, and — the
  load-bearing structural fact — adding \<open>|x|\<^sup>2/(2\<epsilon>)\<close> makes it CONVEX, because
  the sup-convolution is a supremum of AFFINE functions of \<open>x\<close> after
  completing the square. Semiconvexity is what feeds Jensen's lemma and the
  theorem on sums downstream (E2-E5).
\<close>

theory Sup_Convolution
  imports "HOL-Analysis.Analysis"
begin

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

text \<open>Continuity of the sup-convolution, with no Lipschitz computation: it
  is the difference of a finite convex function (continuous by
  \<open>convex_on_continuous\<close>) and the smooth \<open>|x|\<^sup>2/(2\<epsilon>)\<close>.\<close>

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

text \<open>The attainment ("magic") estimate: near-optimizers of the
  sup-convolution lie within an explicit \<open>\<epsilon>\<close>-dependent radius, controlled by
  the oscillation of \<open>u\<close>. This is what sends the doubled points of the
  theorem on sums back together as \<open>\<epsilon> \<rightarrow> 0\<close>.\<close>

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

text \<open>At a point of continuity, the sup-convolution converges to the
  function as \<open>\<epsilon> \<rightarrow> 0\<^sup>+\<close>: the near-optimizer localizes in a ball of radius
  \<open>O(\<surd>\<epsilon>)\<close> around \<open>x\<close>, where continuity pins \<open>u\<close> near \<open>u x\<close>.\<close>

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

section \<open>Subgradients of convex functions\<close>

text \<open>
  Phase E3a of the plan (STATUS.md): the convex-analytic foundations of the
  Crandall--Ishii development. Subgradients of finite convex functions on
  Euclidean space: definition, monotonicity of the subdifferential, and the
  meat: nonemptiness via a supporting hyperplane to the epigraph. These feed
  the proximal map/Minty resolvent (E3b), which reduces Alexandrov's theorem
  to Rademacher's (E3c--d).
\<close>

definition subdiff :: "('a::euclidean_space \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "subdiff f x = {p. \<forall>y. f x + p \<bullet> (y - x) \<le> f y}"

lemma subdiffI: "(\<And>y. f x + p \<bullet> (y - x) \<le> f y) \<Longrightarrow> p \<in> subdiff f x"
  by (simp add: subdiff_def)

lemma subdiffD: "p \<in> subdiff f x \<Longrightarrow> f x + p \<bullet> (y - x) \<le> f y"
  by (simp add: subdiff_def)

text \<open>Monotonicity of the subdifferential map: the defining inequalities at
  \<open>x\<close> and \<open>y\<close>, added crosswise, kill the function values.\<close>

lemma subdiff_monotone:
  assumes p: "p \<in> subdiff f x" and q: "q \<in> subdiff f y"
  shows "0 \<le> (p - q) \<bullet> (x - y)"
proof -
  have 1: "f x + p \<bullet> (y - x) \<le> f y" by (rule subdiffD[OF p])
  have 2: "f y + q \<bullet> (x - y) \<le> f x" by (rule subdiffD[OF q])
  have "p \<bullet> (y - x) + q \<bullet> (x - y) \<le> 0" using 1 2 by linarith
  thus ?thesis by (simp add: algebra_simps)
qed

text \<open>The epigraph of a finite convex function on Euclidean space is closed
  (the function is continuous) and convex, and \<open>(x, f x)\<close> lies on its
  frontier; the supporting hyperplane there cannot be vertical, and after
  normalization its horizontal part is a subgradient.\<close>

lemma closed_epigraph_UNIV:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cf: "continuous_on UNIV f"
  shows "closed (epigraph UNIV f)"
proof -
  have "epigraph UNIV f = {z. f (fst z) - snd z \<le> 0}"
    by (auto simp: epigraph_def)
  moreover have "closed {z :: 'a \<times> real. f (fst z) - snd z \<le> 0}"
    by (intro closed_Collect_le continuous_on_diff continuous_on_snd
        continuous_on_compose2[OF cf continuous_on_fst]) auto
  ultimately show ?thesis by simp
qed

lemma epigraph_frontier_point:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cf: "continuous_on UNIV f"
  shows "(x, f x) \<in> frontier (epigraph UNIV f)"
proof -
  have mem: "(x, f x) \<in> epigraph UNIV f" by (simp add: mem_epigraph)
  have "(x, f x) \<notin> interior (epigraph UNIV f)"
  proof
    assume "(x, f x) \<in> interior (epigraph UNIV f)"
    then obtain e where e: "0 < e"
      and sub: "ball (x, f x) e \<subseteq> epigraph UNIV f"
      by (auto simp: mem_interior)
    have "dist (x, f x) (x, f x - e/2) = e/2"
      using e by (simp add: dist_Pair_Pair dist_real_def)
    hence "(x, f x - e/2) \<in> ball (x, f x) e" using e by simp
    with sub have "(x, f x - e/2) \<in> epigraph UNIV f" by blast
    thus False using e by (simp add: mem_epigraph)
  qed
  with mem show ?thesis
    by (simp add: frontier_def closure_def)
qed

theorem subdiff_nonempty:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "subdiff f x \<noteq> {}"
proof -
  have cf: "continuous_on UNIV f"
    by (rule convex_on_continuous[OF open_UNIV cvx])
  have cvxE: "convex (epigraph UNIV f)"
    by (rule convex_epigraphI[OF cvx])
  have clE: "closed (epigraph UNIV f)"
    by (rule closed_epigraph_UNIV[OF cf])
  obtain a where a0: "a \<noteq> 0"
    and sup: "\<And>z. z \<in> closure (epigraph UNIV f) \<Longrightarrow>
      a \<bullet> (x, f x) \<le> a \<bullet> z"
    using supporting_hyperplane_frontier[OF cvxE epigraph_frontier_point[OF cf]]
    by blast
  obtain p\<^sub>0 c where ac: "a = (p\<^sub>0, c)" by (cases a) auto
  have supE: "p\<^sub>0 \<bullet> x + c * f x \<le> p\<^sub>0 \<bullet> y + c * t" if "f y \<le> t" for y t
  proof -
    have "(y, t) \<in> epigraph UNIV f" using that by (simp add: mem_epigraph)
    hence "a \<bullet> (x, f x) \<le> a \<bullet> (y, t)"
      by (intro sup) (simp add: clE)
    thus ?thesis by (simp add: ac inner_prod_def)
  qed
  have c0: "0 \<le> c"
    using supE[of x "f x + 1"] by (simp add: ring_distribs)
  have cpos: "0 < c"
  proof (rule ccontr)
    assume "\<not> 0 < c"
    with c0 have c: "c = 0" by simp
    have all: "\<And>y. p\<^sub>0 \<bullet> x \<le> p\<^sub>0 \<bullet> y"
      using supE[OF order_refl] c by simp
    have "p\<^sub>0 \<bullet> x \<le> p\<^sub>0 \<bullet> (x - p\<^sub>0)" by (rule all)
    hence "p\<^sub>0 \<bullet> p\<^sub>0 \<le> 0" by (simp add: inner_diff_right)
    hence "(norm p\<^sub>0)\<^sup>2 = 0"
      using zero_le_power2[of "norm p\<^sub>0"] by (simp add: dot_square_norm)
    hence "p\<^sub>0 = 0" by simp
    with c ac a0 show False by (simp add: zero_prod_def)
  qed
  have "(-1/c) *\<^sub>R p\<^sub>0 \<in> subdiff f x"
  proof (rule subdiffI)
    fix y
    have "p\<^sub>0 \<bullet> x + c * f x \<le> p\<^sub>0 \<bullet> y + c * f y"
      by (rule supE[OF order_refl])
    hence "f x + (p\<^sub>0 \<bullet> x - p\<^sub>0 \<bullet> y) / c \<le> f y"
      using cpos by (simp add: field_simps)
    thus "f x + ((-1/c) *\<^sub>R p\<^sub>0) \<bullet> (y - x) \<le> f y"
      using cpos by (simp add: inner_diff_right field_simps)
  qed
  thus ?thesis by blast
qed

subsection \<open>The proximal map\<close>

text \<open>E3b: for a finite convex function, \<open>y \<mapsto> f y + dist x y\<^sup>2/2\<close> attains a
  unique minimum (the proximal point). The affine lower bound from a
  subgradient makes the objective coercive, so a sublevel set is compact.\<close>

lemma prox_attained:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "\<exists>y. \<forall>z. f y + (dist x y)\<^sup>2/2 \<le> f z + (dist x z)\<^sup>2/2"
proof -
  have cf: "continuous_on UNIV f"
    by (rule convex_on_continuous[OF open_UNIV cvx])
  obtain p where p: "p \<in> subdiff f 0"
    using subdiff_nonempty[OF cvx] by blast
  have lower: "\<And>y. f 0 + p \<bullet> y \<le> f y"
    using subdiffD[OF p] by simp
  define g where "g = (\<lambda>y. f y + (dist x y)\<^sup>2/2)"
  have cg: "continuous_on UNIV g"
    unfolding g_def by (intro continuous_intros cf) simp
  define D where "D = g x - f 0 - p \<bullet> x + (norm p)\<^sup>2"
  define R where "R = 2 * sqrt (max D 0 + 1)"
  have Rpos: "0 < R" by (simp add: R_def)
  have Rsq: "4 * (max D 0 + 1) = R\<^sup>2"
    by (simp add: R_def power_mult_distrib)
  define S where "S = {y. g y \<le> g x}"
  have xS: "x \<in> S" by (simp add: S_def)
  have Sclosed: "closed S"
    unfolding S_def by (intro closed_Collect_le cg continuous_on_const)
  have Sball: "S \<subseteq> cball x R"
  proof
    fix y assume "y \<in> S"
    hence gy: "g y \<le> g x" by (simp add: S_def)
    have t_eq: "dist x y = norm (y - x)"
      by (simp add: dist_norm norm_minus_commute)
    have "f 0 + p \<bullet> y + (dist x y)\<^sup>2/2 \<le> g y"
      unfolding g_def using lower[of y] by simp
    with gy have base: "f 0 + p \<bullet> y + (dist x y)\<^sup>2/2 \<le> g x" by linarith
    have split: "p \<bullet> y = p \<bullet> (y - x) + p \<bullet> x"
      by (simp add: inner_diff_right)
    have cs: "- (norm p * norm (y - x)) \<le> p \<bullet> (y - x)"
      using Cauchy_Schwarz_ineq2[of p "y - x"] by linarith
    have amgm: "norm p * norm (y - x) \<le> (norm (y - x))\<^sup>2/4 + (norm p)\<^sup>2"
    proof -
      have "0 \<le> (norm (y - x)/2 - norm p)\<^sup>2" by simp
      thus ?thesis by (simp add: power2_diff power_divide mult.commute)
    qed
    have "(dist x y)\<^sup>2/2 \<le> g x - f 0 - p \<bullet> x + norm p * norm (y - x)"
      using base split cs by linarith
    hence "(dist x y)\<^sup>2/2 \<le> g x - f 0 - p \<bullet> x + (norm (y - x))\<^sup>2/4 + (norm p)\<^sup>2"
      using amgm by linarith
    hence "(dist x y)\<^sup>2/4 \<le> D"
      unfolding D_def t_eq by linarith
    hence "(dist x y)\<^sup>2 \<le> 4 * D" by linarith
    hence "(dist x y)\<^sup>2 \<le> 4 * (max D 0 + 1)"
      by (auto simp: max_def)
    hence dsq: "(dist x y)\<^sup>2 \<le> R\<^sup>2" using Rsq by linarith
    have "dist x y \<le> R"
    proof (rule ccontr)
      assume "\<not> dist x y \<le> R"
      hence "R\<^sup>2 < (dist x y)\<^sup>2"
        using Rpos by (intro power_strict_mono) auto
      thus False using dsq by linarith
    qed
    thus "y \<in> cball x R" by simp
  qed
  have Scompact: "compact S"
    using Sclosed Sball bounded_cball bounded_subset
    by (metis compact_eq_bounded_closed)
  obtain y where yS: "y \<in> S" and ymin: "\<And>z. z \<in> S \<Longrightarrow> g y \<le> g z"
    using continuous_attains_inf[OF Scompact _ continuous_on_subset[OF cg subset_UNIV]] xS
    by blast
  have glob: "g y \<le> g z" for z
  proof (cases "z \<in> S")
    case True thus ?thesis by (rule ymin)
  next
    case False
    hence "g x < g z" by (simp add: S_def)
    thus ?thesis using ymin[OF xS] by linarith
  qed
  thus ?thesis unfolding g_def by blast
qed

text \<open>Uniqueness of the proximal point, by strict convexity of the quadratic
  penalty: the midpoint of two distinct minimizers would beat them both.\<close>

lemma midpoint_dist_identity:
  fixes x y\<^sub>1 y\<^sub>2 :: "'a::euclidean_space"
  shows "(dist x ((y\<^sub>1 + y\<^sub>2) /\<^sub>R 2))\<^sup>2
    = ((dist x y\<^sub>1)\<^sup>2 + (dist x y\<^sub>2)\<^sup>2)/2 - (dist y\<^sub>1 y\<^sub>2)\<^sup>2/4"
  unfolding dist_norm power2_norm_eq_inner
  by (simp add: inner_diff_left inner_diff_right inner_add_left inner_add_right
      inner_commute) argo

lemma prox_unique:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
    and m1: "\<And>z. f y\<^sub>1 + (dist x y\<^sub>1)\<^sup>2/2 \<le> f z + (dist x z)\<^sup>2/2"
    and m2: "\<And>z. f y\<^sub>2 + (dist x y\<^sub>2)\<^sup>2/2 \<le> f z + (dist x z)\<^sup>2/2"
  shows "y\<^sub>1 = y\<^sub>2"
proof (rule ccontr)
  assume ne: "y\<^sub>1 \<noteq> y\<^sub>2"
  define m where "m = (y\<^sub>1 + y\<^sub>2) /\<^sub>R 2"
  have m_cvx: "m = (1 - (1/2::real)) *\<^sub>R y\<^sub>1 + (1/2) *\<^sub>R y\<^sub>2"
    by (simp add: m_def scaleR_add_right)
  have fm: "f m \<le> (f y\<^sub>1 + f y\<^sub>2)/2"
    using convex_onD[OF cvx, of "1/2" y\<^sub>1 y\<^sub>2] by (simp add: m_cvx)
  have eq12: "f y\<^sub>1 + (dist x y\<^sub>1)\<^sup>2/2 = f y\<^sub>2 + (dist x y\<^sub>2)\<^sup>2/2"
    using m1[of y\<^sub>2] m2[of y\<^sub>1] by linarith
  have dpos: "0 < (dist y\<^sub>1 y\<^sub>2)\<^sup>2"
    using ne by simp
  have par: "(dist x m)\<^sup>2 = ((dist x y\<^sub>1)\<^sup>2 + (dist x y\<^sub>2)\<^sup>2)/2 - (dist y\<^sub>1 y\<^sub>2)\<^sup>2/4"
    unfolding m_def by (rule midpoint_dist_identity)
  have min_m: "f y\<^sub>1 + (dist x y\<^sub>1)\<^sup>2/2 \<le> f m + (dist x m)\<^sup>2/2"
    by (rule m1)
  show False using fm eq12 dpos par min_m by argo
qed

definition prox :: "('a::euclidean_space \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "prox f x = (THE y. \<forall>z. f y + (dist x y)\<^sup>2/2 \<le> f z + (dist x z)\<^sup>2/2)"

lemma prox_min:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "f (prox f x) + (dist x (prox f x))\<^sup>2/2 \<le> f z + (dist x z)\<^sup>2/2"
proof -
  obtain y where y: "\<forall>z. f y + (dist x y)\<^sup>2/2 \<le> f z + (dist x z)\<^sup>2/2"
    using prox_attained[OF cvx] by blast
  have "prox f x = y"
    unfolding prox_def
  proof (rule the_equality)
    show "\<forall>z. f y + (dist x y)\<^sup>2/2 \<le> f z + (dist x z)\<^sup>2/2" by (rule y)
    fix y' assume y': "\<forall>z. f y' + (dist x y')\<^sup>2/2 \<le> f z + (dist x z)\<^sup>2/2"
    show "y' = y"
    proof (rule prox_unique[OF cvx, of y' x y])
      show "\<And>z. f y' + (dist x y')\<^sup>2/2 \<le> f z + (dist x z)\<^sup>2/2"
        using y' by blast
      show "\<And>z. f y + (dist x y)\<^sup>2/2 \<le> f z + (dist x z)\<^sup>2/2"
        using y by blast
    qed
  qed
  thus ?thesis using y by simp
qed

text \<open>The proximal characterization: \<open>x - prox f x\<close> is a subgradient at the
  proximal point. Convexity converts the quadratic minimality error into a
  linear inequality via a \<open>t \<rightarrow> 0\<close> perturbation.\<close>

lemma prox_step_expand:
  fixes x y z :: "'a::euclidean_space"
  shows "(dist x (y + t *\<^sub>R (z - y)))\<^sup>2
    = (dist x y)\<^sup>2 - 2*t*((x - y) \<bullet> (z - y)) + t\<^sup>2*(dist y z)\<^sup>2"
  unfolding dist_norm power2_norm_eq_inner
  by (simp add: inner_commute power2_eq_square algebra_simps)

lemma minimizer_subdiff:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
    and min: "\<And>z. f y + (dist x y)\<^sup>2/2 \<le> f z + (dist x z)\<^sup>2/2"
  shows "x - y \<in> subdiff f y"
proof (rule subdiffI)
  fix z
  show "f y + (x - y) \<bullet> (z - y) \<le> f z"
  proof (rule field_le_epsilon)
    fix e :: real assume e: "0 < e"
    define d2 where "d2 = (dist y z)\<^sup>2"
    have d2nn: "0 \<le> d2" by (simp add: d2_def)
    define t where "t = min 1 (e / (d2 + 1))"
    have tpos: "0 < t" and t1: "t \<le> 1"
      using e d2nn by (auto simp: t_def)
    have te: "t * d2 \<le> e"
    proof -
      have "t * d2 \<le> (e / (d2 + 1)) * d2"
        using d2nn by (intro mult_right_mono) (auto simp: t_def)
      also have "\<dots> \<le> e"
        using e d2nn by (simp add: field_simps)
      finally show ?thesis .
    qed
    define I where "I = (x - y) \<bullet> (z - y)"
    define m where "m = y + t *\<^sub>R (z - y)"
    have m_cvx: "m = (1 - t) *\<^sub>R y + t *\<^sub>R z"
      by (simp add: m_def algebra_simps)
    have fm: "f m \<le> (1 - t) * f y + t * f z"
      using convex_onD[OF cvx, of t y z] tpos t1 by (simp add: m_cvx)
    have fm': "f m \<le> f y - t * f y + t * f z"
      using fm by (simp add: algebra_simps)
    have dm: "(dist x m)\<^sup>2 = (dist x y)\<^sup>2 - 2*(t*I) + t\<^sup>2*d2"
      using prox_step_expand[of x y t z]
      by (simp add: m_def d2_def I_def)
    have minm: "f y + (dist x y)\<^sup>2/2 \<le> f m + (dist x m)\<^sup>2/2" by (rule min)
    have h1: "2*(f y) \<le> 2*(f m) - 2*(t*I) + t\<^sup>2*d2"
      using minm dm by linarith
    have h1': "2*(f y) \<le> 2*(f m) - 2*(t*I) + t*(t*d2)"
      using h1 by (simp add: power2_eq_square mult.assoc)
    have h4: "2*(t*I) \<le> 2*(t*(f z)) - 2*(t*(f y)) + t*(t*d2)"
      using h1' fm' by argo
    have h5: "t*(2*I) \<le> t*(2*(f z) - 2*(f y) + t*d2)"
      using h4 by (simp add: algebra_simps)
    have h6: "2*I \<le> 2*(f z) - 2*(f y) + t*d2"
      by (rule mult_left_le_imp_le[OF h5 tpos])
    show "f y + (x - y) \<bullet> (z - y) \<le> f z + e"
      using h6 te e unfolding I_def[symmetric] by linarith
  qed
qed

lemma prox_subdiff:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "x - prox f x \<in> subdiff f (prox f x)"
  by (rule minimizer_subdiff[OF cvx prox_min[OF cvx]])

text \<open>Minty: \<open>id + subdiff f\<close> is surjective, witnessed by the proximal
  point; and the resolvent \<open>prox f\<close> is nonexpansive (1-Lipschitz), by
  monotonicity of the subdifferential. Rademacher's theorem will therefore
  apply to it \<comment> \<open>the route to Alexandrov (E3c--d)\<close>.\<close>

theorem minty_surjective:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "\<exists>y p. p \<in> subdiff f y \<and> y + p = x"
  using prox_subdiff[OF cvx, of x] by (intro exI) auto

theorem prox_nonexpansive:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "dist (prox f x\<^sub>1) (prox f x\<^sub>2) \<le> dist x\<^sub>1 x\<^sub>2"
proof -
  define y\<^sub>1 where "y\<^sub>1 = prox f x\<^sub>1"
  define y\<^sub>2 where "y\<^sub>2 = prox f x\<^sub>2"
  have s1: "x\<^sub>1 - y\<^sub>1 \<in> subdiff f y\<^sub>1"
    unfolding y\<^sub>1_def by (rule prox_subdiff[OF cvx])
  have s2: "x\<^sub>2 - y\<^sub>2 \<in> subdiff f y\<^sub>2"
    unfolding y\<^sub>2_def by (rule prox_subdiff[OF cvx])
  have mono: "0 \<le> ((x\<^sub>1 - y\<^sub>1) - (x\<^sub>2 - y\<^sub>2)) \<bullet> (y\<^sub>1 - y\<^sub>2)"
    by (rule subdiff_monotone[OF s1 s2])
  have key: "(norm (y\<^sub>1 - y\<^sub>2))\<^sup>2 \<le> (x\<^sub>1 - x\<^sub>2) \<bullet> (y\<^sub>1 - y\<^sub>2)"
    using mono by (simp add: power2_norm_eq_inner inner_commute algebra_simps)
  show ?thesis
  proof (cases "y\<^sub>1 = y\<^sub>2")
    case True thus ?thesis by (simp add: y\<^sub>1_def[symmetric] y\<^sub>2_def[symmetric])
  next
    case False
    have "(norm (y\<^sub>1 - y\<^sub>2))\<^sup>2 \<le> norm (x\<^sub>1 - x\<^sub>2) * norm (y\<^sub>1 - y\<^sub>2)"
      using key Cauchy_Schwarz_ineq2[of "x\<^sub>1 - x\<^sub>2" "y\<^sub>1 - y\<^sub>2"] by linarith
    hence "norm (y\<^sub>1 - y\<^sub>2) \<le> norm (x\<^sub>1 - x\<^sub>2)"
      using False by (simp add: power2_eq_square mult_le_cancel_right)
    thus ?thesis by (simp add: y\<^sub>1_def[symmetric] y\<^sub>2_def[symmetric] dist_norm)
  qed
qed

subsection \<open>Rademacher, dimension one\<close>

text \<open>E3c opener: a Lipschitz function on the line is differentiable almost
  everywhere. The hard analytic core is the distribution's
  \<open>Lebesgue_differentiation_thm\<close> (bounded variation \<Rightarrow> a.e. differentiable);
  Lipschitz \<Rightarrow> absolutely continuous \<Rightarrow> BV on each compact interval, and a
  countable union of the interval statements covers the line. The codomain
  may be any Euclidean space \<comment> \<open>used for the resolvent later\<close>.\<close>

theorem lipschitz_differentiable_ae_1d:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes lip: "\<And>x y. norm (f x - f y) \<le> B * \<bar>x - y\<bar>"
  shows "negligible {x. \<not> f differentiable (at x)}"
proof -
  have seg: "negligible {x \<in> {-real n..real n}. \<not> f differentiable (at x)}"
    for n :: nat
  proof -
    have ac: "absolutely_continuous_on {-real n..real n} f"
      by (rule Lipschitz_imp_absolutely_continuous) (rule lip)
    have bv: "has_bounded_variation_on f {-real n..real n}"
      by (rule absolutely_continuous_on_imp_has_bounded_variation_on[OF ac])
        (rule bounded_closed_interval)
    show ?thesis
      by (rule Lebesgue_differentiation_thm[OF _ bv]) (rule is_interval_cc)
  qed
  have cover: "{x. \<not> f differentiable (at x)}
      = (\<Union>n. {x \<in> {-real n..real n}. \<not> f differentiable (at x)})"
  proof -
    have "\<exists>n :: nat. x \<in> {-real n..real n}" for x :: real
    proof -
      obtain n :: nat where "\<bar>x\<bar> \<le> real n"
        using real_arch_simple by blast
      thus ?thesis by (intro exI[of _ n]) auto
    qed
    thus ?thesis by auto
  qed
  show ?thesis
    unfolding cover by (rule negligible_Union_nat) (use seg in auto)
qed

text \<open>Sections of a Lipschitz map along any line are Lipschitz curves, so
  they are differentiable at a.e. parameter \<comment> \<open>the slicing input to the
  Fubini step of Rademacher's theorem\<close>.\<close>

lemma lipschitz_line_section_diff_ae:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes lip: "\<And>x y. norm (f x - f y) \<le> B * norm (x - y)"
  shows "negligible {t. \<not> (\<lambda>s. f (x + s *\<^sub>R v)) differentiable (at t)}"
proof (rule lipschitz_differentiable_ae_1d[of _ "B * norm v"])
  fix s s' :: real
  have nrm: "norm (s *\<^sub>R v - s' *\<^sub>R v) = norm v * \<bar>s - s'\<bar>"
  proof -
    have "s *\<^sub>R v - s' *\<^sub>R v = (s - s') *\<^sub>R v"
      by (simp add: scaleR_left_diff_distrib)
    thus ?thesis by (simp add: mult.commute)
  qed
  have "norm (f (x + s *\<^sub>R v) - f (x + s' *\<^sub>R v))
      \<le> B * norm ((x + s *\<^sub>R v) - (x + s' *\<^sub>R v))"
    by (rule lip)
  also have "\<dots> = B * norm v * \<bar>s - s'\<bar>"
    using nrm by (simp add: mult.assoc)
  finally show "norm (f (x + s *\<^sub>R v) - f (x + s' *\<^sub>R v))
      \<le> B * norm v * \<bar>s - s'\<bar>" .
qed

subsection \<open>Measurability of the directional-derivative set\<close>

text \<open>R2a: the set of points at which the difference quotient along a fixed
  direction converges is Borel. The usual proof indexes the Cauchy criterion
  by rationals to keep the family countable; that is unnecessary here,
  because an intersection of ARBITRARILY many closed sets is closed. Only
  the two accuracy indices need to be countable.\<close>

definition dquot :: "('a::euclidean_space \<Rightarrow> 'b::banach) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> real \<Rightarrow> 'b"
  where "dquot f v x t = (f (x + t *\<^sub>R v) - f x) /\<^sub>R t"

definition dlim_set :: "('a::euclidean_space \<Rightarrow> 'b::banach) \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "dlim_set f v = {x. \<exists>L. ((\<lambda>t. dquot f v x t) \<longlongrightarrow> L) (at 0)}"

lemma continuous_on_dquot:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes cf: "continuous_on UNIV f"
  shows "continuous_on UNIV (\<lambda>x. dquot f v x t)"
  unfolding dquot_def
  by (intro continuous_intros continuous_on_compose2[OF cf] cf) auto

lemma closed_dquot_pair:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes cf: "continuous_on UNIV f"
  shows "closed {x. dist (dquot f v x s) (dquot f v x t) \<le> c}"
  by (intro closed_Collect_le continuous_on_const
      continuous_on_dist[OF continuous_on_dquot[OF cf] continuous_on_dquot[OF cf]])

definition dcrit :: "('a::euclidean_space \<Rightarrow> 'b::banach) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a set"
  where "dcrit f v k m = {x. \<forall>s t. 0 < \<bar>s\<bar> \<and> \<bar>s\<bar> \<le> 1/Suc m \<and> 0 < \<bar>t\<bar> \<and> \<bar>t\<bar> \<le> 1/Suc m
      \<longrightarrow> dist (dquot f v x s) (dquot f v x t) \<le> 1/Suc k}"

lemma closed_dcrit:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes cf: "continuous_on UNIV f"
  shows "closed (dcrit f v k m)"
proof -
  define P where "P = {p :: real \<times> real. 0 < \<bar>fst p\<bar> \<and> \<bar>fst p\<bar> \<le> 1/Suc m
      \<and> 0 < \<bar>snd p\<bar> \<and> \<bar>snd p\<bar> \<le> 1/Suc m}"
  have "dcrit f v k m
      = (\<Inter>p\<in>P. {x. dist (dquot f v x (fst p)) (dquot f v x (snd p)) \<le> 1/Suc k})"
    unfolding dcrit_def P_def by auto
  moreover have "closed (\<Inter>p\<in>P. {x. dist (dquot f v x (fst p)) (dquot f v x (snd p))
      \<le> 1/Suc k})"
    by (intro closed_INT ballI closed_dquot_pair[OF cf])
  ultimately show ?thesis by simp
qed

lemma dlim_set_eq_dcrit:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  shows "dlim_set f v = (\<Inter>k. \<Union>m. dcrit f v k m)"
proof (rule set_eqI, rule iffI)
  fix x assume "x \<in> dlim_set f v"
  then obtain L where L: "((\<lambda>t. dquot f v x t) \<longlongrightarrow> L) (at 0)"
    unfolding dlim_set_def by blast
  show "x \<in> (\<Inter>k. \<Union>m. dcrit f v k m)"
  proof (rule INT_I)
    fix k :: nat
    define e where "e = (1/Suc k)/2"
    have e: "0 < e" by (simp add: e_def)
    have ee: "e + e = 1/Suc k" unfolding e_def by (rule field_sum_of_halves)
    have "eventually (\<lambda>t. dist (dquot f v x t) L < e) (at 0)"
      by (rule tendstoD[OF L e])
    then obtain d where d: "0 < d"
      and db: "\<And>t. t \<noteq> 0 \<Longrightarrow> dist t 0 < d \<Longrightarrow> dist (dquot f v x t) L < e"
      unfolding eventually_at by blast
    obtain m where m: "1/Suc m < d"
      using nat_approx_posE[OF d] by blast
    have "x \<in> dcrit f v k m"
      unfolding dcrit_def
    proof (intro CollectI allI impI)
      fix s t assume st: "0 < \<bar>s\<bar> \<and> \<bar>s\<bar> \<le> 1/Suc m \<and> 0 < \<bar>t\<bar> \<and> \<bar>t\<bar> \<le> 1/Suc m"
      have s1: "dist (dquot f v x s) L < e"
        using st m by (intro db) (auto simp: dist_real_def)
      have t1: "dist (dquot f v x t) L < e"
        using st m by (intro db) (auto simp: dist_real_def)
      have "dist (dquot f v x s) (dquot f v x t)
          \<le> dist (dquot f v x s) L + dist L (dquot f v x t)"
        by (rule dist_triangle)
      also have "\<dots> < e + e" using s1 t1 by (simp add: dist_commute)
      finally show "dist (dquot f v x s) (dquot f v x t) \<le> 1/Suc k"
        using ee by linarith
    qed
    thus "x \<in> (\<Union>m. dcrit f v k m)" by blast
  qed
next
  fix x assume xC: "x \<in> (\<Inter>k. \<Union>m. dcrit f v k m)"
  have crit: "\<exists>m. x \<in> dcrit f v k m" for k using xC by blast
  define g where "g = (\<lambda>n. dquot f v x (1/Suc n))"
  have gcrit: "dist (g p) (g q) \<le> 1/Suc k" if "x \<in> dcrit f v k m" "m \<le> p" "m \<le> q"
    for k m p q
  proof -
    have "1/Suc p \<le> 1/Suc m" and "1/Suc q \<le> 1/Suc m"
      using that by (auto simp: divide_simps)
    thus ?thesis using that(1) unfolding dcrit_def g_def by simp
  qed
  have cau: "Cauchy g"
  proof (rule metric_CauchyI)
    fix e :: real assume e: "0 < e"
    obtain k where k: "1/Suc k < e" using nat_approx_posE[OF e] by blast
    obtain m where m: "x \<in> dcrit f v k m" using crit by blast
    show "\<exists>M. \<forall>p\<ge>M. \<forall>q\<ge>M. dist (g p) (g q) < e"
    proof (intro exI[of _ m] allI impI)
      fix p q assume "m \<le> p" "m \<le> q"
      have "dist (g p) (g q) \<le> 1/Suc k"
        by (rule gcrit[OF m]) (use \<open>m \<le> p\<close> \<open>m \<le> q\<close> in auto)
      thus "dist (g p) (g q) < e" using k by linarith
    qed
  qed
  obtain L where gL: "g \<longlonglongrightarrow> L"
    using Cauchy_convergent[OF cau] unfolding convergent_def by blast
  have "((\<lambda>t. dquot f v x t) \<longlongrightarrow> L) (at 0)"
  proof (rule tendstoI)
    fix e :: real assume e: "0 < e"
    have e2: "0 < e/2" using e by simp
    obtain k where k: "1/Suc k < e/2" using nat_approx_posE[OF e2] by blast
    obtain m where m: "x \<in> dcrit f v k m" using crit by blast
    obtain N where N: "\<And>n. N \<le> n \<Longrightarrow> dist (g n) L < e/2"
      using gL e2 unfolding lim_sequentially by blast
    define n where "n = max N m"
    have nN: "N \<le> n" and nm: "m \<le> n" by (auto simp: n_def)
    have gn: "dist (g n) L < e/2" by (rule N[OF nN])
    have main: "dist (dquot f v x t) L < e" if t: "0 < \<bar>t\<bar>" "\<bar>t\<bar> \<le> 1/Suc m"
      for t :: real
    proof -
      have le: "1/Suc n \<le> 1/Suc m" using nm by (auto simp: divide_simps)
      have half: "dist (dquot f v x t) (g n) \<le> 1/Suc k"
        using t le m unfolding dcrit_def g_def by simp
      have "dist (dquot f v x t) L \<le> dist (dquot f v x t) (g n) + dist (g n) L"
        by (rule dist_triangle)
      also have "\<dots> < 1/Suc k + e/2" using half gn by linarith
      also have "\<dots> < e" using k by linarith
      finally show ?thesis .
    qed
    show "eventually (\<lambda>t. dist (dquot f v x t) L < e) (at 0)"
      unfolding eventually_at
      by (intro exI[of _ "1/Suc m"] conjI)
        (auto simp: dist_real_def intro!: main)
  qed
  thus "x \<in> dlim_set f v" unfolding dlim_set_def by blast
qed

theorem borel_dlim_set:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes cf: "continuous_on UNIV f"
  shows "dlim_set f v \<in> sets borel"
proof -
  have inner: "(\<Union>m. dcrit f v k m) \<in> sets borel" for k
    by (intro sets.countable_UN) (auto intro: borel_closed closed_dcrit[OF cf])
  have "(\<Inter>k. \<Union>m. dcrit f v k m) \<in> sets borel"
    by (intro sets.countable_INT'[OF countableI_type]) (use inner in auto)
  thus ?thesis unfolding dlim_set_eq_dcrit .
qed

subsection \<open>From one-dimensional sections to null sets\<close>

text \<open>R2b: a Borel set all of whose lines in a fixed basis direction are
  negligible is itself negligible. This is Fubini for \<open>lborel\<close>, reached
  through \<open>lborel_eq\<close> (Lebesgue measure is the image of a finite product of
  copies of \<open>lborel\<close> under the coordinate isomorphism) and the
  peel-one-coordinate identity \<open>product_nn_integral_insert\<close>. Borel-ness is
  essential, not cosmetic: a set with all sections null need not be null
  without it.\<close>

lemma negligible_iff_null_lborel:
  fixes S :: "'a::euclidean_space set"
  assumes S: "S \<in> sets borel"
  shows "negligible S \<longleftrightarrow> S \<in> null_sets lborel"
proof -
  have "S \<in> sets lborel" using S by simp
  from null_sets_completion_iff[OF this]
  show ?thesis by (simp add: negligible_iff_null_sets)
qed

lemma coord_iso_measurable:
  "(\<lambda>f. \<Sum>b\<in>Basis. f b *\<^sub>R b) \<in> (\<Pi>\<^sub>M b\<in>(Basis :: 'a::euclidean_space set). lborel)
      \<rightarrow>\<^sub>M (borel :: 'a measure)"
  by (intro borel_measurable_sum borel_measurable_scaleR
      measurable_component_singleton) auto

lemma coord_iso_update:
  fixes b :: "'a::euclidean_space"
  assumes b: "b \<in> Basis"
  shows "(\<Sum>c\<in>Basis. (w(b := y)) c *\<^sub>R c)
       = (\<Sum>c\<in>Basis - {b}. w c *\<^sub>R c) + y *\<^sub>R b"
proof -
  have "(\<Sum>c\<in>Basis. (w(b := y)) c *\<^sub>R c)
      = (w(b := y)) b *\<^sub>R b + (\<Sum>c\<in>Basis - {b}. (w(b := y)) c *\<^sub>R c)"
    using b by (intro sum.remove) auto
  also have "(\<Sum>c\<in>Basis - {b}. (w(b := y)) c *\<^sub>R c)
      = (\<Sum>c\<in>Basis - {b}. w c *\<^sub>R c)"
    by (rule sum.cong) auto
  finally show ?thesis by (simp add: add.commute)
qed

theorem negligible_of_basis_sections:
  fixes N :: "'a::euclidean_space set"
  assumes N: "N \<in> sets borel" and b: "b \<in> Basis"
    and sec: "\<And>z. negligible {t. z + t *\<^sub>R b \<in> N}"
  shows "negligible N"
proof -
  interpret PSF: product_sigma_finite "\<lambda>_::'a. (lborel :: real measure)"
    by unfold_locales
  define P :: "('a \<Rightarrow> real) measure"
    where "P = (\<Pi>\<^sub>M c\<in>(Basis :: 'a set). (lborel :: real measure))"
  define Q :: "('a \<Rightarrow> real) measure"
    where "Q = (\<Pi>\<^sub>M c\<in>(Basis - {b} :: 'a set). (lborel :: real measure))"
  define g :: "('a \<Rightarrow> real) \<Rightarrow> 'a"
    where "g = (\<lambda>f. \<Sum>c\<in>Basis. f c *\<^sub>R (c :: 'a))"
  have gmeas: "g \<in> P \<rightarrow>\<^sub>M (borel :: 'a measure)"
    unfolding P_def g_def by (rule coord_iso_measurable)
  define A :: "('a \<Rightarrow> real) set" where "A = g -` N \<inter> space P"
  have Asets: "A \<in> sets P"
    unfolding A_def using measurable_sets[OF gmeas N] by simp
  have ind_meas: "(\<lambda>w. indicator A w :: ennreal) \<in> borel_measurable P"
    using Asets by measurable
  have Bas: "insert b (Basis - {b}) = (Basis :: 'a set)" using b by blast
  have inner0: "(\<integral>\<^sup>+y. indicator A (w(b := y)) \<partial>(lborel :: real measure)) = 0"
    if w: "w \<in> space Q" for w
  proof -
    define z where "z = (\<Sum>c\<in>Basis - {b}. w c *\<^sub>R (c :: 'a))"
    have upd: "w(b := y) \<in> space P" for y
      unfolding P_def using w b
      by (auto simp: Q_def space_PiM PiE_iff extensional_def)
    have gupd: "g (w(b := y)) = z + y *\<^sub>R b" for y
      unfolding g_def z_def by (rule coord_iso_update[OF b])
    have sec_eq: "{y. w(b := y) \<in> A} = {t. z + t *\<^sub>R b \<in> N}"
      unfolding A_def using upd gupd by auto
    have secB: "{t. z + t *\<^sub>R b \<in> N} \<in> sets borel"
    proof -
      have m: "(\<lambda>t. z + t *\<^sub>R b) \<in> borel_measurable borel"
        by (intro borel_measurable_add borel_measurable_scaleR) auto
      have "(\<lambda>t. z + t *\<^sub>R b) -` N \<inter> space (borel :: real measure) \<in> sets borel"
        by (rule measurable_sets[OF m N])
      thus ?thesis by (simp add: vimage_def)
    qed
    have null: "{t. z + t *\<^sub>R b \<in> N} \<in> null_sets (lborel :: real measure)"
      using negligible_iff_null_lborel[OF secB] sec[of z] by simp
    have ind_eq: "(\<lambda>y. indicator A (w(b := y)) :: ennreal)
        = indicator {y. w(b := y) \<in> A}"
      by (auto simp: indicator_def)
    have setmem: "{y. w(b := y) \<in> A} \<in> sets (lborel :: real measure)"
      using secB sec_eq by simp
    have "(\<integral>\<^sup>+y. indicator A (w(b := y)) \<partial>(lborel :: real measure))
        = emeasure lborel {y. w(b := y) \<in> A}"
      unfolding ind_eq using setmem by simp
    also have "\<dots> = 0" using null unfolding sec_eq by (simp add: null_sets_def)
    finally show ?thesis .
  qed
  have PP: "P = (\<Pi>\<^sub>M c\<in>insert b (Basis - {b}). (lborel :: real measure))"
    unfolding P_def by (simp only: Bas)
  have fub: "(\<integral>\<^sup>+w. indicator A w \<partial>P)
      = (\<integral>\<^sup>+w. (\<integral>\<^sup>+y. indicator A (w(b := y)) \<partial>(lborel :: real measure)) \<partial>Q)"
    unfolding PP Q_def
    by (rule PSF.product_nn_integral_insert) (use ind_meas[unfolded PP] in auto)
  have "emeasure P A = (\<integral>\<^sup>+w. indicator A w \<partial>P)"
    using Asets by simp
  also have "\<dots> = (\<integral>\<^sup>+w. (\<integral>\<^sup>+y. indicator A (w(b := y))
      \<partial>(lborel :: real measure)) \<partial>Q)"
    by (rule fub)
  also have "\<dots> = (\<integral>\<^sup>+w. 0 \<partial>Q)"
    by (rule nn_integral_cong) (use inner0 in simp)
  also have "\<dots> = 0" by simp
  finally have PA: "emeasure P A = 0" .
  have "emeasure (lborel :: 'a measure) N = emeasure (distr P borel g) N"
    unfolding P_def g_def by (subst lborel_eq) (rule refl)
  also have "\<dots> = emeasure P A"
    unfolding A_def by (rule emeasure_distr[OF gmeas N])
  finally have "emeasure (lborel :: 'a measure) N = 0" using PA by simp
  hence "N \<in> null_sets (lborel :: 'a measure)"
    using N by (simp add: null_sets_def)
  thus ?thesis using negligible_iff_null_lborel[OF N] by simp
qed
subsection \<open>Directional derivatives exist almost everywhere\<close>

text \<open>R2c: assembling the pieces. A differentiable curve has a difference
  quotient with a limit \<comment> \<open>the derivative applied to \<open>1\<close>, since a bounded
  linear map on the line is scaling\<close>.\<close>

lemma dquot_tendsto_vector_derivative:
  fixes phi :: "real \<Rightarrow> 'b::real_normed_vector"
  assumes d: "phi differentiable (at t)"
  shows "((\<lambda>h. (phi (t + h) - phi t) /\<^sub>R h)
      \<longlongrightarrow> vector_derivative phi (at t)) (at 0)"
proof -
  define L where "L = vector_derivative phi (at t)"
  have D: "(phi has_derivative (\<lambda>h. h *\<^sub>R L)) (at t)"
    using d unfolding L_def
    by (metis has_vector_derivative_def vector_derivative_works)
  have Dh: "(\<lambda>h. h *\<^sub>R L) h = h *\<^sub>R L" for h by simp
  have lim0: "((\<lambda>h. norm (phi (t + h) - phi t - h *\<^sub>R L) / norm h)
      \<longlongrightarrow> 0) (at 0)"
    using D unfolding has_derivative_at by blast
  have ne: "eventually (\<lambda>h::real. h \<noteq> 0) (at 0)"
    unfolding eventually_at by (intro exI[of _ 1]) auto
  have eq: "eventually (\<lambda>h. norm (phi (t + h) - phi t - h *\<^sub>R L) / norm h
      = norm ((phi (t + h) - phi t) /\<^sub>R h - L)) (at 0)"
    using ne
  proof (eventually_elim)
    case (elim h)
    hence h: "h \<noteq> 0" .
    have "(phi (t + h) - phi t) /\<^sub>R h - L
        = (phi (t + h) - phi t - h *\<^sub>R L) /\<^sub>R h"
      using h by (simp add: scaleR_diff_right)
    hence "norm ((phi (t + h) - phi t) /\<^sub>R h - L)
        = norm (phi (t + h) - phi t - h *\<^sub>R L) / \<bar>h\<bar>"
      by (simp add: divide_inverse mult.commute)
    thus ?case by simp
  qed
  have "((\<lambda>h. norm ((phi (t + h) - phi t) /\<^sub>R h - L)) \<longlongrightarrow> 0) (at 0)"
    by (rule Lim_transform_eventually[OF lim0 eq])
  hence "((\<lambda>h. (phi (t + h) - phi t) /\<^sub>R h - L) \<longlongrightarrow> 0) (at 0)"
    by (simp add: tendsto_norm_zero_iff)
  hence "((\<lambda>h. (phi (t + h) - phi t) /\<^sub>R h) \<longlongrightarrow> L) (at 0)"
    by (simp add: Lim_null[symmetric])
  thus ?thesis unfolding L_def .
qed

lemma dquot_of_differentiable:
  fixes phi :: "real \<Rightarrow> 'b::real_normed_vector"
  assumes d: "phi differentiable (at t)"
  shows "\<exists>L. ((\<lambda>h. (phi (t + h) - phi t) /\<^sub>R h) \<longlongrightarrow> L) (at 0)"
  using dquot_tendsto_vector_derivative[OF d] by blast

lemma lipschitz_continuous_on_UNIV:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes lip: "\<And>x y. norm (f x - f y) \<le> B * norm (x - y)"
  shows "continuous_on UNIV f"
proof -
  define C where "C = max B 1"
  have C: "0 < C" by (simp add: C_def)
  have lipC: "norm (f x - f y) \<le> C * norm (x - y)" for x y
  proof -
    have "B * norm (x - y) \<le> C * norm (x - y)"
      by (intro mult_right_mono) (auto simp: C_def)
    thus ?thesis using lip[of x y] by linarith
  qed
  show ?thesis
    unfolding continuous_on_iff
  proof (intro ballI allI impI)
    fix x :: 'a and e :: real assume e: "0 < e"
    show "\<exists>d>0. \<forall>x'\<in>UNIV. dist x' x < d \<longrightarrow> dist (f x') (f x) < e"
    proof (intro exI[of _ "e/C"] conjI ballI impI)
      show "0 < e/C" using e C by simp
      fix x' :: 'a assume "dist x' x < e/C"
      hence "C * dist x' x < e" using C by (simp add: field_simps)
      moreover have "dist (f x') (f x) \<le> C * dist x' x"
        using lipC[of x' x] by (simp add: dist_norm)
      ultimately show "dist (f x') (f x) < e" by linarith
    qed
  qed
qed

theorem negligible_no_dderiv_basis:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::{euclidean_space,banach}"
  assumes lip: "\<And>x y. norm (f x - f y) \<le> B * norm (x - y)" and b: "b \<in> Basis"
  shows "negligible (- dlim_set f b)"
proof (rule negligible_of_basis_sections[OF _ b])
  have cf: "continuous_on UNIV f" by (rule lipschitz_continuous_on_UNIV[OF lip])
  show "- dlim_set f b \<in> sets borel"
  proof -
    have "space (borel :: 'a measure) - dlim_set f b \<in> sets borel"
      by (rule sets.compl_sets[OF borel_dlim_set[OF cf]])
    thus ?thesis by (simp add: Compl_eq_Diff_UNIV)
  qed
  fix z :: 'a
  have sub: "{t. z + t *\<^sub>R b \<in> - dlim_set f b}
      \<subseteq> {t. \<not> (\<lambda>s. f (z + s *\<^sub>R b)) differentiable (at t)}"
  proof (rule subsetI, rule CollectI, rule notI)
    fix t assume tz: "t \<in> {t. z + t *\<^sub>R b \<in> - dlim_set f b}"
      and dt: "(\<lambda>s. f (z + s *\<^sub>R b)) differentiable (at t)"
    define x where "x = z + t *\<^sub>R b"
    have shift: "z + (t + h) *\<^sub>R b = x + h *\<^sub>R b" for h
      unfolding x_def by (simp add: algebra_simps)
    obtain L where L: "((\<lambda>h. (f (z + (t + h) *\<^sub>R b) - f (z + t *\<^sub>R b)) /\<^sub>R h)
        \<longlongrightarrow> L) (at 0)"
      using dquot_of_differentiable[OF dt] by blast
    have "((\<lambda>h. dquot f b x h) \<longlongrightarrow> L) (at 0)"
      using L unfolding dquot_def shift x_def[symmetric] by simp
    hence "x \<in> dlim_set f b" unfolding dlim_set_def by blast
    thus False using tz unfolding x_def by simp
  qed
  have "negligible {t. \<not> (\<lambda>s. f (z + s *\<^sub>R b)) differentiable (at t)}"
    by (rule lipschitz_line_section_diff_ae[where B = B and f = f]) (rule lip)
  thus "negligible {t. z + t *\<^sub>R b \<in> - dlim_set f b}"
    by (rule negligible_subset[OF _ sub])
qed

text \<open>R2': arbitrary directions. An orthogonal map carries a scaled basis
  vector to any prescribed \<open>v \<noteq> 0\<close>; pulling \<open>f\<close> back along it turns the
  \<open>v\<close>-quotient into a basis-direction quotient, and negligibility is
  invariant under invertible linear images.\<close>

lemma dlim_set_precompose:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes T: "linear T"
  shows "dlim_set (f \<circ> T) u = T -` dlim_set f (T u)"
proof (rule set_eqI)
  fix x
  have Tadd: "T (x + t *\<^sub>R u) = T x + t *\<^sub>R T u" for t
  proof -
    have "T (x + t *\<^sub>R u) = T x + T (t *\<^sub>R u)"
      using T unfolding linear_iff by simp
    also have "T (t *\<^sub>R u) = t *\<^sub>R T u"
      using T unfolding linear_iff by simp
    finally show ?thesis .
  qed
  have q: "dquot (f \<circ> T) u x t = dquot f (T u) (T x) t" for t
    unfolding dquot_def o_def by (simp add: Tadd)
  have qf: "dquot (f \<circ> T) u x = dquot f (T u) (T x)"
    by (rule ext) (rule q)
  have lhs: "(x \<in> dlim_set (f \<circ> T) u)
      = (\<exists>L. (dquot (f \<circ> T) u x \<longlongrightarrow> L) (at 0))"
    unfolding dlim_set_def by simp
  have rhs: "(x \<in> T -` dlim_set f (T u))
      = (\<exists>L. (dquot f (T u) (T x) \<longlongrightarrow> L) (at 0))"
    unfolding dlim_set_def by simp
  show "(x \<in> dlim_set (f \<circ> T) u) = (x \<in> T -` dlim_set f (T u))"
    unfolding lhs rhs qf by (rule refl)
qed

theorem negligible_no_dderiv:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::{euclidean_space,banach}"
  assumes lip: "\<And>x y. norm (f x - f y) \<le> B * norm (x - y)" and v: "v \<noteq> 0"
  shows "negligible (- dlim_set f v)"
proof -
  obtain b :: 'a where b: "b \<in> Basis" using nonempty_Basis by blast
  have nb: "norm b = 1" using b by (rule norm_Basis)
  have nvb: "norm (norm v *\<^sub>R b) = norm v" using nb by simp
  obtain S where S: "orthogonal_transformation S" and Sb: "S (norm v *\<^sub>R b) = v"
    using orthogonal_transformation_exists[OF nvb] by blast
  have Slin: "linear S" by (rule orthogonal_transformation_linear[OF S])
  have Sinj: "inj S" by (rule orthogonal_transformation_inj[OF S])
  have Ssurj: "surj S" by (rule orthogonal_transformation_surj[OF S])
  have Snorm: "norm (S x) = norm x" for x
    using S unfolding orthogonal_transformation by blast
  have Sadd: "S (x + y) = S x + S y" for x y
    using Slin unfolding linear_iff by simp
  have Sscale: "S (c *\<^sub>R x) = c *\<^sub>R S x" for c x
    using Slin unfolding linear_iff by simp
  define T where "T = (\<lambda>x. S (norm v *\<^sub>R x))"
  have vpos: "norm v \<noteq> 0" using v by simp
  have Tlin: "linear T"
  proof (rule linearI)
    fix x y :: 'a
    have "T (x + y) = S (norm v *\<^sub>R x + norm v *\<^sub>R y)"
      unfolding T_def by (simp add: scaleR_add_right)
    thus "T (x + y) = T x + T y" unfolding T_def by (simp add: Sadd)
  next
    fix c :: real and x :: 'a
    have "T (c *\<^sub>R x) = S (c *\<^sub>R (norm v *\<^sub>R x))"
      unfolding T_def by (simp add: mult.commute)
    thus "T (c *\<^sub>R x) = c *\<^sub>R T x" unfolding T_def by (simp add: Sscale)
  qed
  have Tb: "T b = v" unfolding T_def by (rule Sb)
  have Tinj: "inj T"
  proof (rule injI)
    fix x y assume eq: "T x = T y"
    have e2: "S (norm v *\<^sub>R x) = S (norm v *\<^sub>R y)" using eq unfolding T_def .
    have "norm v *\<^sub>R x = norm v *\<^sub>R y" by (rule injD[OF Sinj e2])
    thus "x = y" using vpos by simp
  qed
  have Tsurj: "surj T"
    unfolding surj_def
  proof (rule allI)
    fix z :: 'a
    obtain w where w: "z = S w" using surjD[OF Ssurj] by blast
    have "T ((1/norm v) *\<^sub>R w) = S ((norm v * (1/norm v)) *\<^sub>R w)"
      unfolding T_def by simp
    also have "\<dots> = S w" using vpos by simp
    finally show "\<exists>x. z = T x" using w by (intro exI[of _ "(1/norm v) *\<^sub>R w"]) simp
  qed
  have lipT: "norm ((f \<circ> T) x - (f \<circ> T) y) \<le> (B * norm v) * norm (x - y)" for x y
  proof -
    have Tdiff: "T x - T y = S (norm v *\<^sub>R (x - y))"
      unfolding T_def by (simp add: Sadd Sscale scaleR_diff_right
          linear_diff[OF Slin])
    have "norm ((f \<circ> T) x - (f \<circ> T) y) \<le> B * norm (T x - T y)"
      unfolding o_def by (rule lip)
    also have "norm (T x - T y) = norm v * norm (x - y)"
      unfolding Tdiff by (simp add: Snorm)
    finally show ?thesis by (simp add: mult.assoc)
  qed
  have neg: "negligible (T -` (- dlim_set f v))"
  proof -
    have "negligible (- dlim_set (f \<circ> T) b)"
      by (rule negligible_no_dderiv_basis[OF lipT b])
    moreover have "- dlim_set (f \<circ> T) b = T -` (- dlim_set f v)"
      using dlim_set_precompose[OF Tlin, of f b] Tb by (simp add: vimage_Compl)
    ultimately show ?thesis by simp
  qed
  have img: "T ` (T -` (- dlim_set f v)) = - dlim_set f v"
    by (rule surj_image_vimage_eq[OF Tsurj])
  have "negligible (T ` (T -` (- dlim_set f v)))"
    by (subst negligible_linear_image_eq[OF Tlin Tinj]) (rule neg)
  thus ?thesis unfolding img .
qed

subsection \<open>The directional derivative as a measurable function\<close>

text \<open>R3a: name the directional derivative by the SEQUENTIAL limit along
  \<open>t = 1/(n+1)\<close>. Where the filter limit exists the two agree, so nothing is
  lost; the gain is that measurability is then immediate from
  \<open>borel_measurable_lim_metric\<close>, which handles the non-convergent points
  internally \<comment> \<open>no restriction to \<open>dlim_set\<close> needed in the statement\<close>.\<close>

definition ddir :: "('a::euclidean_space \<Rightarrow> 'b::banach) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b"
  where "ddir f v x = lim (\<lambda>n. dquot f v x (inverse (real (Suc n))))"

lemma filterlim_inverse_Suc:
  "filterlim (\<lambda>n. inverse (real (Suc n))) (at (0::real)) sequentially"
  unfolding filterlim_at
  by (intro conjI LIMSEQ_inverse_real_of_nat) auto

lemma ddir_tendsto:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes x: "x \<in> dlim_set f v"
  shows "((\<lambda>t. dquot f v x t) \<longlongrightarrow> ddir f v x) (at 0)"
proof -
  obtain L where L: "((\<lambda>t. dquot f v x t) \<longlongrightarrow> L) (at 0)"
    using x unfolding dlim_set_def by blast
  have "(\<lambda>n. dquot f v x (inverse (real (Suc n)))) \<longlonglongrightarrow> L"
    by (rule filterlim_compose[OF L filterlim_inverse_Suc])
  hence "ddir f v x = L" unfolding ddir_def by (rule limI)
  thus ?thesis using L by simp
qed

lemma borel_measurable_ddir:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::{banach,second_countable_topology}"
  assumes cf: "continuous_on UNIV f"
  shows "ddir f v \<in> borel_measurable borel"
  unfolding ddir_def
  by (intro borel_measurable_lim_metric borel_measurable_continuous_onI
      continuous_on_dquot[OF cf])

text \<open>The Lipschitz bound passes to the derivative: \<open>|D_v f| \<le> B |v|\<close>
  wherever it exists. This is what makes \<open>ddir\<close> integrable on boxes, the
  input to the R3 integral identity.\<close>

lemma norm_ddir_le:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes lip: "\<And>x y. norm (f x - f y) \<le> B * norm (x - y)"
    and x: "x \<in> dlim_set f v"
  shows "norm (ddir f v x) \<le> B * norm v"
proof -
  have q: "norm (dquot f v x t) \<le> B * norm v" if t: "t \<noteq> 0" for t
  proof -
    have "norm (dquot f v x t) = norm (f (x + t *\<^sub>R v) - f x) / \<bar>t\<bar>"
      unfolding dquot_def by (simp add: divide_inverse mult.commute)
    also have "\<dots> \<le> (B * norm (t *\<^sub>R v)) / \<bar>t\<bar>"
      using lip[of "x + t *\<^sub>R v" x] t by (intro divide_right_mono) auto
    also have "\<dots> = B * norm v"
      using t by simp
    finally show ?thesis .
  qed
  have ev: "eventually (\<lambda>t. norm (dquot f v x t) \<le> B * norm v) (at (0::real))"
  proof -
    have "eventually (\<lambda>t::real. t \<noteq> 0) (at 0)"
      unfolding eventually_at by (intro exI[of _ 1]) auto
    thus ?thesis by (eventually_elim) (use q in blast)
  qed
  have "((\<lambda>t. norm (dquot f v x t)) \<longlongrightarrow> norm (ddir f v x)) (at 0)"
    by (intro tendsto_norm ddir_tendsto[OF x])
  thus ?thesis
    by (rule tendsto_upperbound[OF _ ev]) simp
qed

subsection \<open>Fundamental theorem of calculus along a line\<close>

text \<open>R3b: on a line, a Lipschitz function is absolutely continuous, and its
  a.e. derivative is exactly \<open>ddir\<close>. So the distribution's FTC for absolutely
  continuous functions integrates \<open>ddir\<close> back to increments of \<open>f\<close>. This is
  the analytic heart of the linearity step: it converts a statement about
  derivatives into one about integrals, where Fubini can act.\<close>

lemma ddir_line_eq:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes d: "(\<lambda>s. f (z + s *\<^sub>R v)) differentiable (at t)"
  shows "z + t *\<^sub>R v \<in> dlim_set f v"
    and "ddir f v (z + t *\<^sub>R v)
       = vector_derivative (\<lambda>s. f (z + s *\<^sub>R v)) (at t)"
proof -
  define phi where "phi = (\<lambda>s. f (z + s *\<^sub>R v))"
  define x where "x = z + t *\<^sub>R v"
  have shift: "z + (t + h) *\<^sub>R v = x + h *\<^sub>R v" for h
    unfolding x_def by (simp add: algebra_simps)
  have q: "dquot f v x = (\<lambda>h. (phi (t + h) - phi t) /\<^sub>R h)"
    unfolding dquot_def phi_def x_def[symmetric] shift by (rule refl)
  have L: "(dquot f v x \<longlongrightarrow> vector_derivative phi (at t)) (at 0)"
    unfolding q using d unfolding phi_def
    by (rule dquot_tendsto_vector_derivative)
  thus mem: "x \<in> dlim_set f v" unfolding dlim_set_def by blast
  have "(dquot f v x \<longlongrightarrow> ddir f v x) (at 0)" by (rule ddir_tendsto[OF mem])
  from tendsto_unique[OF at_neq_bot this L]
  show "ddir f v x = vector_derivative phi (at t)" .
qed

theorem ftc_along_line:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::{euclidean_space,banach}"
  assumes lip: "\<And>x y. norm (f x - f y) \<le> B * norm (x - y)" and ac: "a \<le> c"
  shows "((\<lambda>s. ddir f v (z + s *\<^sub>R v))
      has_integral (f (z + c *\<^sub>R v) - f (z + a *\<^sub>R v))) {a..c}"
proof -
  define phi where "phi = (\<lambda>s. f (z + s *\<^sub>R v))"
  define S where "S = {s. \<not> phi differentiable (at s)}"
  have lipphi: "norm (phi s - phi s') \<le> (B * norm v) * \<bar>s - s'\<bar>" for s s'
  proof -
    have nrm: "norm (s *\<^sub>R v - s' *\<^sub>R v) = norm v * \<bar>s - s'\<bar>"
    proof -
      have "s *\<^sub>R v - s' *\<^sub>R v = (s - s') *\<^sub>R v"
        by (simp add: scaleR_left_diff_distrib)
      thus ?thesis by (simp add: mult.commute)
    qed
    have "norm (phi s - phi s') \<le> B * norm ((z + s *\<^sub>R v) - (z + s' *\<^sub>R v))"
      unfolding phi_def by (rule lip)
    also have "\<dots> = B * norm v * \<bar>s - s'\<bar>"
      using nrm by (simp add: mult.assoc)
    finally show ?thesis .
  qed
  have Sneg: "negligible S"
    unfolding S_def phi_def
    by (rule lipschitz_line_section_diff_ae[where B = B and f = f]) (rule lip)
  have acphi: "absolutely_continuous_on {a..c} phi"
    by (rule Lipschitz_imp_absolutely_continuous) (use lipphi in blast)
  have vd: "(phi has_vector_derivative ddir f v (z + s *\<^sub>R v))
      (at s within {a..c})" if s: "s \<in> {a..c} - S" for s
  proof -
    have ds: "phi differentiable (at s)" using s unfolding S_def by simp
    have "ddir f v (z + s *\<^sub>R v) = vector_derivative phi (at s)"
      unfolding phi_def by (rule ddir_line_eq(2)[OF ds[unfolded phi_def]])
    moreover have "(phi has_vector_derivative vector_derivative phi (at s)) (at s)"
      using ds by (simp add: vector_derivative_works)
    ultimately show ?thesis by (simp add: has_vector_derivative_at_within)
  qed
  have "((\<lambda>s. ddir f v (z + s *\<^sub>R v)) has_integral (phi c - phi a)) {a..c}"
    by (rule fundamental_theorem_of_calculus_absolutely_continuous
        [OF Sneg ac acphi]) (use vd in blast)
  thus ?thesis unfolding phi_def .
qed

subsection \<open>Structure of the direction map\<close>

text \<open>R4a: what the direction map \<open>v \<mapsto> D_v f x\<close> satisfies BEFORE linearity
  is known — positive homogeneity, and a Lipschitz estimate in \<open>v\<close> with the
  SAME constant as \<open>f\<close>. The latter is what lets a dense set of directions
  control all directions in the final step of Rademacher's theorem.\<close>

lemma dquot_scale:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes c: "c \<noteq> 0" and t: "t \<noteq> 0"
  shows "dquot f (c *\<^sub>R v) x t = c *\<^sub>R dquot f v x (c * t)"
proof -
  have arg: "x + t *\<^sub>R (c *\<^sub>R v) = x + (c * t) *\<^sub>R v"
    by (simp add: mult.commute)
  have "dquot f (c *\<^sub>R v) x t = (f (x + (c * t) *\<^sub>R v) - f x) /\<^sub>R t"
    unfolding dquot_def arg by (rule refl)
  also have "\<dots> = c *\<^sub>R ((f (x + (c * t) *\<^sub>R v) - f x) /\<^sub>R (c * t))"
    using c t by simp
  finally show ?thesis unfolding dquot_def .
qed

lemma ddir_scale:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes x: "x \<in> dlim_set f v" and c: "c \<noteq> 0"
  shows "x \<in> dlim_set f (c *\<^sub>R v)"
    and "ddir f (c *\<^sub>R v) x = c *\<^sub>R ddir f v x"
proof -
  have flim: "filterlim (\<lambda>t. c * t) (at 0) (at (0::real))"
    unfolding filterlim_at
  proof (intro conjI)
    have "((\<lambda>t. c * t) \<longlongrightarrow> c * 0) (at (0::real))"
      by (intro tendsto_intros)
    thus "((\<lambda>t. c * t) \<longlongrightarrow> 0) (at (0::real))" by simp
    have "eventually (\<lambda>t::real. t \<noteq> 0) (at 0)"
      unfolding eventually_at by (intro exI[of _ 1]) auto
    thus "eventually (\<lambda>t::real. c * t \<in> UNIV \<and> c * t \<noteq> 0) (at 0)"
      by (rule eventually_mono) (use c in simp)
  qed
  have "((\<lambda>t. dquot f v x (c * t)) \<longlongrightarrow> ddir f v x) (at 0)"
    by (rule filterlim_compose[OF ddir_tendsto[OF x] flim])
  hence sc: "((\<lambda>t. c *\<^sub>R dquot f v x (c * t)) \<longlongrightarrow> c *\<^sub>R ddir f v x) (at 0)"
    by (intro tendsto_intros)
  have ev: "eventually (\<lambda>t. c *\<^sub>R dquot f v x (c * t)
      = dquot f (c *\<^sub>R v) x t) (at (0::real))"
  proof -
    have "eventually (\<lambda>t::real. t \<noteq> 0) (at 0)"
      unfolding eventually_at by (intro exI[of _ 1]) auto
    thus ?thesis by (eventually_elim) (simp add: dquot_scale[OF c])
  qed
  have lim: "(dquot f (c *\<^sub>R v) x \<longlongrightarrow> c *\<^sub>R ddir f v x) (at 0)"
    by (rule Lim_transform_eventually[OF sc ev])
  thus mem: "x \<in> dlim_set f (c *\<^sub>R v)" unfolding dlim_set_def by blast
  have "(dquot f (c *\<^sub>R v) x \<longlongrightarrow> ddir f (c *\<^sub>R v) x) (at 0)"
    by (rule ddir_tendsto[OF mem])
  from tendsto_unique[OF at_neq_bot this lim]
  show "ddir f (c *\<^sub>R v) x = c *\<^sub>R ddir f v x" .
qed

lemma ddir_lipschitz_in_direction:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes lip: "\<And>x y. norm (f x - f y) \<le> B * norm (x - y)"
    and xu: "x \<in> dlim_set f u" and xv: "x \<in> dlim_set f v"
  shows "norm (ddir f u x - ddir f v x) \<le> B * norm (u - v)"
proof -
  have q: "norm (dquot f u x t - dquot f v x t) \<le> B * norm (u - v)"
    if t: "t \<noteq> 0" for t
  proof -
    have "dquot f u x t - dquot f v x t
        = (f (x + t *\<^sub>R u) - f (x + t *\<^sub>R v)) /\<^sub>R t"
      unfolding dquot_def by (simp add: scaleR_diff_right)
    hence "norm (dquot f u x t - dquot f v x t)
        = norm (f (x + t *\<^sub>R u) - f (x + t *\<^sub>R v)) / \<bar>t\<bar>"
      by (simp add: divide_inverse mult.commute)
    also have "\<dots> \<le> (B * norm ((x + t *\<^sub>R u) - (x + t *\<^sub>R v))) / \<bar>t\<bar>"
      using lip[of "x + t *\<^sub>R u" "x + t *\<^sub>R v"] t
      by (intro divide_right_mono) auto
    also have "(x + t *\<^sub>R u) - (x + t *\<^sub>R v) = t *\<^sub>R (u - v)"
      by (simp add: scaleR_diff_right)
    also have "(B * norm (t *\<^sub>R (u - v))) / \<bar>t\<bar> = B * norm (u - v)"
      using t by simp
    finally show ?thesis .
  qed
  have ev: "eventually (\<lambda>t. norm (dquot f u x t - dquot f v x t)
      \<le> B * norm (u - v)) (at (0::real))"
  proof -
    have "eventually (\<lambda>t::real. t \<noteq> 0) (at 0)"
      unfolding eventually_at by (intro exI[of _ 1]) auto
    thus ?thesis by (eventually_elim) (use q in blast)
  qed
  have "((\<lambda>t. norm (dquot f u x t - dquot f v x t))
      \<longlongrightarrow> norm (ddir f u x - ddir f v x)) (at 0)"
    by (intro tendsto_norm tendsto_diff ddir_tendsto[OF xu] ddir_tendsto[OF xv])
  thus ?thesis by (rule tendsto_upperbound[OF _ ev]) simp
qed

text \<open>R4b: a countable family of directions can be handled simultaneously —
  the set where any of them fails is a countable union of negligible sets.\<close>

theorem negligible_no_dderiv_countable:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::{euclidean_space,banach}"
  assumes lip: "\<And>x y. norm (f x - f y) \<le> B * norm (x - y)"
    and V: "countable V" and V0: "\<And>v. v \<in> V \<Longrightarrow> v \<noteq> 0"
  shows "negligible (- (\<Inter>v\<in>V. dlim_set f v))"
proof -
  have "- (\<Inter>v\<in>V. dlim_set f v) = (\<Union>v\<in>V. - dlim_set f v)" by simp
  moreover have "negligible (\<Union>v\<in>V. - dlim_set f v)"
  proof (rule negligible_countable_Union)
    show "countable ((\<lambda>v. - dlim_set f v) ` V)" using V by (rule countable_image)
    fix S assume "S \<in> (\<lambda>v. - dlim_set f v) ` V"
    then obtain v where v: "v \<in> V" and Seq: "S = - dlim_set f v" by blast
    show "negligible S"
      unfolding Seq using V0[OF v] by (intro negligible_no_dderiv[OF lip])
  qed
  ultimately show ?thesis by simp
qed

subsection \<open>From directional to full differentiability\<close>

text \<open>R4c \<comment> \<open>the last step of Rademacher's theorem\<close>. If at a point the
  directional derivatives along a DENSE set of directions exist and agree
  with a bounded linear map, then a Lipschitz function is (Fr\'echet)
  differentiable there. The mechanism is compactness of the unit sphere: the
  difference quotients are equi-Lipschitz in the direction, so pointwise
  control on a dense set upgrades to uniform control over the sphere, which
  is exactly the \<open>o(\<bar>h\<bar>)\<close> estimate. Nothing here needs measure theory; it
  isolates the remaining analytic gap (R3, linearity a.e.) as the ONLY
  missing ingredient of Rademacher.\<close>

theorem differentiable_of_dense_linear_ddir:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes lip: "\<And>y z. norm (f y - f z) \<le> B * norm (y - z)"
    and B0: "0 \<le> B"
    and T: "bounded_linear T"
    and dense: "\<And>v \<epsilon>. 0 < \<epsilon> \<Longrightarrow> \<exists>w\<in>D. norm (v - w) < \<epsilon>"
    and der: "\<And>w. w \<in> D \<Longrightarrow> ((\<lambda>t. dquot f w x t) \<longlongrightarrow> T w) (at 0)"
  shows "(f has_derivative T) (at x)"
  unfolding has_derivative_at
proof (intro conjI T tendstoI)
  fix \<epsilon> :: real assume \<epsilon>: "0 < \<epsilon>"
  have Tlin: "linear T" using T unfolding bounded_linear_def by simp
  obtain K where K: "0 < K" and Tb: "\<And>y. norm (T y) \<le> norm y * K"
    using bounded_linear.pos_bounded[OF T] by blast
  define C where "C = B + K + 1"
  have C: "0 < C" using B0 K by (simp add: C_def)
  define \<delta> where "\<delta> = \<epsilon> / (3 * C)"
  have \<delta>: "0 < \<delta>" using \<epsilon> C by (simp add: \<delta>_def)
  have cover: "sphere (0::'a) 1 \<subseteq> (\<Union>w\<in>D. ball w \<delta>)"
  proof
    fix v assume "v \<in> sphere (0::'a) 1"
    obtain w where w: "w \<in> D" and lt: "norm (v - w) < \<delta>"
      using dense[OF \<delta>, of v] by blast
    show "v \<in> (\<Union>w\<in>D. ball w \<delta>)"
      using w lt by (auto simp: dist_norm norm_minus_commute)
  qed
  obtain W where WD: "W \<subseteq> D" and Wfin: "finite W"
    and Wcover: "sphere (0::'a) 1 \<subseteq> (\<Union>w\<in>W. ball w \<delta>)"
    by (rule compactE_image[OF compact_sphere _ cover]) auto
  obtain b :: 'a where b: "b \<in> Basis" using nonempty_Basis by blast
  have "b \<in> sphere (0::'a) 1" using norm_Basis[OF b] by simp
  hence Wne: "W \<noteq> {}" using Wcover by blast
  have "\<forall>w\<in>W. \<exists>d>0. \<forall>t. t \<noteq> 0 \<longrightarrow> \<bar>t\<bar> < d
      \<longrightarrow> norm (dquot f w x t - T w) < \<epsilon>/3"
  proof
    fix w assume "w \<in> W"
    hence wD: "w \<in> D" using WD by blast
    have "eventually (\<lambda>t. dist (dquot f w x t) (T w) < \<epsilon>/3) (at 0)"
      using \<epsilon> by (intro tendstoD[OF der[OF wD]]) simp
    then obtain d where d: "0 < d"
      and db: "\<And>t. t \<noteq> 0 \<Longrightarrow> dist t 0 < d \<Longrightarrow> dist (dquot f w x t) (T w) < \<epsilon>/3"
      unfolding eventually_at by blast
    show "\<exists>d>0. \<forall>t. t \<noteq> 0 \<longrightarrow> \<bar>t\<bar> < d \<longrightarrow> norm (dquot f w x t - T w) < \<epsilon>/3"
      using d db by (intro exI[of _ d]) (auto simp: dist_norm dist_real_def)
  qed
  then obtain dd where dd: "\<And>w. w \<in> W \<Longrightarrow> 0 < dd w"
    and ddb: "\<And>w t. w \<in> W \<Longrightarrow> t \<noteq> 0 \<Longrightarrow> \<bar>t\<bar> < dd w
      \<Longrightarrow> norm (dquot f w x t - T w) < \<epsilon>/3"
    by (auto dest!: bchoice)
  define d0 where "d0 = Min (dd ` W)"
  have d0: "0 < d0" unfolding d0_def using Wfin Wne dd by auto
  have d0le: "\<And>w. w \<in> W \<Longrightarrow> d0 \<le> dd w" unfolding d0_def using Wfin by simp
  have main: "norm (f (x + h) - f x - T h) / norm h < \<epsilon>"
    if h: "h \<noteq> 0" "norm h < d0" for h
  proof -
    define t where "t = norm h"
    define v where "v = h /\<^sub>R norm h"
    have tpos: "0 < t" using h unfolding t_def by simp
    have hv: "h = t *\<^sub>R v" unfolding t_def v_def using h by simp
    have nv: "norm v = 1" unfolding v_def using h by simp
    hence vsp: "v \<in> sphere (0::'a) 1" by simp
    obtain w where wW: "w \<in> W" and lt: "norm (v - w) < \<delta>"
      using Wcover vsp by (auto simp: dist_norm norm_minus_commute)
    have Th: "T h = t *\<^sub>R T v"
    proof -
      have "T h = T (t *\<^sub>R v)" using hv by simp
      thus ?thesis using Tlin unfolding linear_iff by simp
    qed
    have qeq: "norm (f (x + h) - f x - T h) / norm h
        = norm (dquot f v x t - T v)"
    proof -
      have "dquot f v x t - T v = (f (x + h) - f x - T h) /\<^sub>R t"
        unfolding dquot_def hv[symmetric] Th
        using tpos by (simp add: scaleR_diff_right)
      thus ?thesis using tpos unfolding t_def
        by (simp add: divide_inverse mult.commute)
    qed
    have step1: "norm (dquot f v x t - dquot f w x t) \<le> B * norm (v - w)"
    proof -
      have "dquot f v x t - dquot f w x t
          = (f (x + t *\<^sub>R v) - f (x + t *\<^sub>R w)) /\<^sub>R t"
        unfolding dquot_def by (simp add: scaleR_diff_right)
      hence "norm (dquot f v x t - dquot f w x t)
          = norm (f (x + t *\<^sub>R v) - f (x + t *\<^sub>R w)) / \<bar>t\<bar>"
        by (simp add: divide_inverse mult.commute)
      also have "\<dots> \<le> (B * norm ((x + t *\<^sub>R v) - (x + t *\<^sub>R w))) / \<bar>t\<bar>"
        using lip[of "x + t *\<^sub>R v" "x + t *\<^sub>R w"] tpos
        by (intro divide_right_mono) auto
      also have "(x + t *\<^sub>R v) - (x + t *\<^sub>R w) = t *\<^sub>R (v - w)"
        by (simp add: scaleR_diff_right)
      also have "(B * norm (t *\<^sub>R (v - w))) / \<bar>t\<bar> = B * norm (v - w)"
        using tpos by simp
      finally show ?thesis .
    qed
    have step2: "norm (dquot f w x t - T w) < \<epsilon>/3"
      using ddb[OF wW] tpos h d0le[OF wW] unfolding t_def by simp
    have step3: "norm (T w - T v) \<le> norm (v - w) * K"
    proof -
      have "T w - T v = T (w - v)"
        using Tlin by (simp add: linear_diff)
      thus ?thesis using Tb[of "w - v"] by (simp add: norm_minus_commute)
    qed
    have tri: "norm (dquot f v x t - T v)
        \<le> norm (dquot f v x t - dquot f w x t)
          + norm (dquot f w x t - T w) + norm (T w - T v)"
      using norm_triangle_ineq[of "dquot f v x t - dquot f w x t"
          "dquot f w x t - T v"]
        norm_triangle_ineq[of "dquot f w x t - T w" "T w - T v"]
      by simp
    have prod_le: "B * norm (v - w) + norm (v - w) * K \<le> C * \<delta>"
    proof -
      have "B * norm (v - w) + norm (v - w) * K = (B + K) * norm (v - w)"
        by (simp add: algebra_simps)
      also have "\<dots> \<le> C * norm (v - w)"
        using B0 K by (intro mult_right_mono) (auto simp: C_def)
      also have "\<dots> \<le> C * \<delta>" using lt C by (intro mult_left_mono) auto
      finally show ?thesis .
    qed
    have Cd: "C * \<delta> = \<epsilon>/3" using C by (simp add: \<delta>_def)
    have "norm (dquot f v x t - T v) < \<epsilon>/3 + \<epsilon>/3"
      using tri step1 step2 step3 prod_le Cd by linarith
    thus ?thesis unfolding qeq using \<epsilon> by linarith
  qed
  show "eventually (\<lambda>h. dist (norm (f (x + h) - f x - T h) / norm h) 0 < \<epsilon>)
      (at 0)"
    unfolding eventually_at
    by (intro exI[of _ d0] conjI d0)
      (auto simp: dist_norm dist_real_def intro!: main)
qed

subsection \<open>Additivity in the direction: reduction to a shifted limit\<close>

text \<open>R3 begins with an exact algebraic split of the \<open>(u+v)\<close>-quotient into a
  \<open>u\<close>-quotient at \<open>x\<close> and a \<open>v\<close>-quotient at the SHIFTED point \<open>x + t u\<close>.
  Everything analytic in R3 is then concentrated in one statement: that the
  shifted \<open>v\<close>-quotient still converges to \<open>D_v f x\<close>. Pointwise that is false
  in general \<comment> \<open>\<open>D_v f\<close> need not be continuous\<close>; it holds after integration,
  which is why R3 is a statement about a.e. \<open>x\<close> rather than about each \<open>x\<close>.\<close>

lemma dquot_add_split:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes t: "t \<noteq> 0"
  shows "dquot f (u + v) x t = dquot f v (x + t *\<^sub>R u) t + dquot f u x t"
proof -
  have arg: "x + t *\<^sub>R u + t *\<^sub>R v = x + t *\<^sub>R (u + v)"
    by (simp add: algebra_simps)
  have tel: "(f (x + t *\<^sub>R u + t *\<^sub>R v) - f (x + t *\<^sub>R u))
      + (f (x + t *\<^sub>R u) - f x) = f (x + t *\<^sub>R (u + v)) - f x"
    unfolding arg by simp
  have "dquot f v (x + t *\<^sub>R u) t + dquot f u x t
      = ((f (x + t *\<^sub>R u + t *\<^sub>R v) - f (x + t *\<^sub>R u))
        + (f (x + t *\<^sub>R u) - f x)) /\<^sub>R t"
    unfolding dquot_def by (rule scaleR_add_right[symmetric])
  also have "\<dots> = (f (x + t *\<^sub>R (u + v)) - f x) /\<^sub>R t"
    unfolding tel by (rule refl)
  finally show ?thesis unfolding dquot_def by simp
qed

lemma ddir_add_of_shifted_limit:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes xu: "x \<in> dlim_set f u"
    and shift: "((\<lambda>t. dquot f v (x + t *\<^sub>R u) t) \<longlongrightarrow> ddir f v x) (at 0)"
  shows "x \<in> dlim_set f (u + v)"
    and "ddir f (u + v) x = ddir f u x + ddir f v x"
proof -
  have sum: "((\<lambda>t. dquot f v (x + t *\<^sub>R u) t + dquot f u x t)
      \<longlongrightarrow> ddir f v x + ddir f u x) (at 0)"
    by (intro tendsto_add shift ddir_tendsto[OF xu])
  have ev: "eventually (\<lambda>t. dquot f v (x + t *\<^sub>R u) t + dquot f u x t
      = dquot f (u + v) x t) (at (0::real))"
  proof -
    have "eventually (\<lambda>t::real. t \<noteq> 0) (at 0)"
      unfolding eventually_at by (intro exI[of _ 1]) auto
    thus ?thesis by (rule eventually_mono) (simp add: dquot_add_split)
  qed
  have lim: "(dquot f (u + v) x \<longlongrightarrow> ddir f v x + ddir f u x) (at 0)"
    by (rule Lim_transform_eventually[OF sum ev])
  thus mem: "x \<in> dlim_set f (u + v)" unfolding dlim_set_def by blast
  have "(dquot f (u + v) x \<longlongrightarrow> ddir f (u + v) x) (at 0)"
    by (rule ddir_tendsto[OF mem])
  from tendsto_unique[OF at_neq_bot this lim]
  show "ddir f (u + v) x = ddir f u x + ddir f v x" by simp
qed

subsection \<open>Boxes move continuously under translation\<close>

text \<open>The measure-theoretic half of R3's error estimate: a box and its small
  translate overlap in almost all of their volume. \<open>Int_interval\<close> makes the
  overlap a box again, so its content is an explicit product, and the
  \<open>max 0\<close> form below is valid whether or not the overlap is degenerate \<comment>
  \<open>which removes the case split from the limit argument.\<close>\<close>

lemma inner_sum_scaleR_Basis:
  fixes j :: "'a::euclidean_space"
  assumes j: "j \<in> Basis"
  shows "(\<Sum>i\<in>Basis. c i *\<^sub>R i) \<bullet> j = c j"
proof -
  have "(\<Sum>i\<in>Basis. c i *\<^sub>R i) \<bullet> j = (\<Sum>i\<in>Basis. c i * (i \<bullet> j))"
    by (simp add: inner_sum_left)
  also have "\<dots> = (\<Sum>i\<in>Basis. if i = j then c i else 0)"
    using j by (intro sum.cong[OF refl]) (auto simp: inner_Basis)
  also have "\<dots> = c j" using j by simp
  finally show ?thesis .
qed

lemma content_box_int_translate:
  fixes a b w :: "'a::euclidean_space"
  shows "content (cbox a b \<inter> cbox (a + w) (b + w))
       = (\<Prod>i\<in>Basis. max 0 (min (b \<bullet> i) ((b + w) \<bullet> i)
            - max (a \<bullet> i) ((a + w) \<bullet> i)))"
proof -
  define L :: 'a where "L = (\<Sum>i\<in>Basis. max (a \<bullet> i) ((a + w) \<bullet> i) *\<^sub>R i)"
  define U :: 'a where "U = (\<Sum>i\<in>Basis. min (b \<bullet> i) ((b + w) \<bullet> i) *\<^sub>R i)"
  have Lc: "L \<bullet> j = max (a \<bullet> j) ((a + w) \<bullet> j)" if "j \<in> Basis" for j :: 'a
    unfolding L_def by (rule inner_sum_scaleR_Basis[OF that])
  have Uc: "U \<bullet> j = min (b \<bullet> j) ((b + w) \<bullet> j)" if "j \<in> Basis" for j :: 'a
    unfolding U_def by (rule inner_sum_scaleR_Basis[OF that])
  have box_eq: "cbox a b \<inter> cbox (a + w) (b + w) = cbox L U"
    unfolding L_def U_def by (rule Int_interval)
  show ?thesis
  proof (cases "\<forall>i\<in>Basis. L \<bullet> i \<le> U \<bullet> i")
    case True
    have "content (cbox L U) = (\<Prod>i\<in>Basis. U \<bullet> i - L \<bullet> i)"
      using True by (simp add: content_cbox_cases)
    also have "\<dots> = (\<Prod>i\<in>Basis. max 0 (min (b \<bullet> i) ((b + w) \<bullet> i)
        - max (a \<bullet> i) ((a + w) \<bullet> i)))"
    proof (rule prod.cong[OF refl])
      fix i :: 'a assume i: "i \<in> Basis"
      have nn: "0 \<le> U \<bullet> i - L \<bullet> i" using True i by simp
      show "U \<bullet> i - L \<bullet> i = max 0 (min (b \<bullet> i) ((b + w) \<bullet> i)
          - max (a \<bullet> i) ((a + w) \<bullet> i))"
        using nn Lc[OF i] Uc[OF i] by simp
    qed
    finally show ?thesis unfolding box_eq .
  next
    case False
    then obtain i :: 'a where i: "i \<in> Basis" and lt: "U \<bullet> i < L \<bullet> i" by force
    have c0: "content (cbox L U) = 0"
      using i lt by (simp add: content_cbox_cases) force
    have p0: "(\<Prod>i\<in>Basis. max 0 (min (b \<bullet> i) ((b + w) \<bullet> i)
        - max (a \<bullet> i) ((a + w) \<bullet> i))) = 0"
    proof (rule prod_zero[OF finite_Basis])
      show "\<exists>i\<in>Basis. max 0 (min (b \<bullet> i) ((b + w) \<bullet> i)
          - max (a \<bullet> i) ((a + w) \<bullet> i)) = 0"
        using i lt Lc[OF i] Uc[OF i] by (intro bexI[of _ i]) auto
    qed
    show ?thesis unfolding box_eq using c0 p0 by simp
  qed
qed

theorem content_box_int_translate_tendsto:
  fixes a b :: "'a::euclidean_space"
  shows "((\<lambda>w. content (cbox a b \<inter> cbox (a + w) (b + w)))
      \<longlongrightarrow> content (cbox a b)) (at (0::'a))"
proof -
  define F where "F = (\<lambda>w :: 'a. \<Prod>i\<in>Basis. max 0 (min (b \<bullet> i) ((b + w) \<bullet> i)
      - max (a \<bullet> i) ((a + w) \<bullet> i)))"
  have lim: "(F \<longlongrightarrow> F 0) (at (0::'a))"
    unfolding F_def by (intro tendsto_intros)
  have F0: "F 0 = content (cbox a b)"
  proof -
    have step: "F 0 = (\<Prod>i\<in>Basis. max 0 (b \<bullet> i - a \<bullet> i))"
      unfolding F_def by simp
    show ?thesis
    proof (cases "\<forall>i\<in>Basis. a \<bullet> i \<le> b \<bullet> i")
      case True
      hence "(\<Prod>i\<in>Basis. max 0 (b \<bullet> i - a \<bullet> i)) = (\<Prod>i\<in>Basis. b \<bullet> i - a \<bullet> i)"
        by (intro prod.cong[OF refl]) auto
      thus ?thesis using True step by (simp add: content_cbox_cases)
    next
      case False
      then obtain i :: 'a where i: "i \<in> Basis" and lt: "b \<bullet> i < a \<bullet> i" by force
      have "(\<Prod>i\<in>Basis. max 0 (b \<bullet> i - a \<bullet> i)) = 0"
        by (rule prod_zero[OF finite_Basis]) (use i lt in force)
      moreover have "content (cbox a b) = 0"
        using i lt by (simp add: content_cbox_cases) force
      ultimately show ?thesis using step by simp
    qed
  qed
  have eq: "(\<lambda>w. content (cbox a b \<inter> cbox (a + w) (b + w))) = F"
    unfolding F_def by (rule ext) (rule content_box_int_translate)
  show ?thesis unfolding eq F0[symmetric] by (rule lim)
qed

subsection \<open>Vanishing integrals over boxes force a.e. vanishing\<close>

text \<open>R3 step 4. A bounded Borel function whose integral over every open box
  is zero vanishes almost everywhere. The two densities \<open>g\<^sup>+\<close> and \<open>g\<^sup>-\<close> define
  finite measures agreeing on the \<open>\<inter>\<close>-stable generator of boxes, so
  \<open>measure_eqI_generator_eq\<close> makes them agree on ALL Borel sets; testing on
  \<open>{g > 0}\<close> and \<open>{g < 0}\<close> then kills \<open>g\<close>. The bound is what makes the two
  densities finite on the exhausting boxes.\<close>

lemma AE_zero_of_box_integrals_zero:
  fixes g :: "'a::euclidean_space \<Rightarrow> real"
  assumes gm: "g \<in> borel_measurable borel"
    and gb: "AE x in lborel. \<bar>g x\<bar> \<le> M"
    and box0: "\<And>l u. (\<integral>\<^sup>+x. ennreal (g x) * indicator (box l u) x \<partial>lborel)
      = (\<integral>\<^sup>+x. ennreal (- g x) * indicator (box l u) x \<partial>lborel)"
  shows "AE x in lborel. g x = 0"
proof -
  define P where "P = density (lborel :: 'a measure) (\<lambda>x. ennreal (g x))"
  define N where "N = density (lborel :: 'a measure) (\<lambda>x. ennreal (- g x))"
  have Pm: "(\<lambda>x. ennreal (g x)) \<in> borel_measurable lborel"
    using gm by measurable
  have Nm: "(\<lambda>x. ennreal (- g x)) \<in> borel_measurable lborel"
    using gm by measurable
  have Pem: "emeasure P A = (\<integral>\<^sup>+x. ennreal (g x) * indicator A x \<partial>lborel)"
    if "A \<in> sets borel" for A
    unfolding P_def using Pm that by (simp add: emeasure_density)
  have Nem: "emeasure N A = (\<integral>\<^sup>+x. ennreal (- g x) * indicator A x \<partial>lborel)"
    if "A \<in> sets borel" for A
    unfolding N_def using Nm that by (simp add: emeasure_density)
  have fin: "emeasure P A \<le> ennreal M * emeasure lborel A" if "A \<in> sets borel" for A
  proof -
    have aeb: "AE x in lborel. ennreal (g x) * indicator A x
        \<le> ennreal M * indicator A x"
      using gb by (eventually_elim)
        (auto intro!: mult_right_mono ennreal_leI simp: abs_le_iff)
    have "(\<integral>\<^sup>+x. ennreal (g x) * indicator A x \<partial>lborel)
        \<le> (\<integral>\<^sup>+x. ennreal M * indicator A x \<partial>lborel)"
      by (rule nn_integral_mono_AE[OF aeb])
    also have "\<dots> = ennreal M * emeasure lborel A"
      using that by (simp add: nn_integral_cmult_indicator)
    finally show ?thesis using Pem[OF that] by simp
  qed
  have PN: "P = N"
  proof (rule measure_eqI_generator_eq)
    let ?E = "range (\<lambda>(a, b). box a b :: 'a set)"
    show "Int_stable ?E" by (auto simp: Int_stable_def box_Int_box)
    show "?E \<subseteq> Pow UNIV" by simp
    show "sets P = sigma_sets UNIV ?E"
      unfolding P_def by (simp add: borel_eq_box)
    show "sets N = sigma_sets UNIV ?E"
      unfolding N_def by (simp add: borel_eq_box)
    let ?A = "\<lambda>n::nat. box (- (real n *\<^sub>R One)) (real n *\<^sub>R One) :: 'a set"
    show "range ?A \<subseteq> ?E" by auto
    show "(\<Union>i. ?A i) = UNIV" by (rule UN_box_eq_UNIV)
    show "emeasure P (?A i) \<noteq> \<infinity>" for i
    proof -
      have le: "emeasure P (?A i) \<le> ennreal M * emeasure lborel (?A i)"
        by (rule fin) simp
      have ne: "ennreal M * emeasure lborel (?A i) \<noteq> \<infinity>"
        by (simp add: ennreal_mult_eq_top_iff)
      show ?thesis using le ne by (auto simp: top_unique)
    qed
    show "emeasure P X = emeasure N X" if "X \<in> ?E" for X
    proof -
      from that obtain ab :: "'a \<times> 'a"
        where Xab: "X = (case ab of (a, b) \<Rightarrow> box a b)" by blast
      obtain l u :: 'a where X: "X = box l u"
        using Xab by (cases ab) simp
      show ?thesis unfolding X
        using Pem[of "box l u"] Nem[of "box l u"] box0[of l u] by simp
    qed
  qed
  have pos: "AE x in lborel. \<not> (0 < g x)"
  proof -
    define S where "S = {x. 0 < g x}"
    have Ssets: "S \<in> sets borel" unfolding S_def using gm by measurable
    have zeroN: "(\<lambda>x. ennreal (- g x) * indicator S x) = (\<lambda>x. 0)"
      by (rule ext) (auto simp: S_def indicator_def ennreal_neg)
    have "(\<integral>\<^sup>+x. ennreal (- g x) * indicator S x \<partial>lborel) = 0"
      unfolding zeroN by simp
    hence "emeasure P S = 0" using Nem[OF Ssets] Pem[OF Ssets] PN by simp
    hence "(\<integral>\<^sup>+x. ennreal (g x) * indicator S x \<partial>lborel) = 0"
      using Pem[OF Ssets] by simp
    hence "AE x in lborel. ennreal (g x) * indicator S x = 0"
      using Ssets gm by (subst (asm) nn_integral_0_iff_AE) auto
    thus ?thesis by (auto simp: S_def indicator_def)
  qed
  have neg: "AE x in lborel. \<not> (g x < 0)"
  proof -
    define S where "S = {x. g x < 0}"
    have Ssets: "S \<in> sets borel" unfolding S_def using gm by measurable
    have zeroP: "(\<lambda>x. ennreal (g x) * indicator S x) = (\<lambda>x. 0)"
      by (rule ext) (auto simp: S_def indicator_def ennreal_neg)
    have "(\<integral>\<^sup>+x. ennreal (g x) * indicator S x \<partial>lborel) = 0"
      unfolding zeroP by simp
    hence "emeasure N S = 0" using Nem[OF Ssets] Pem[OF Ssets] PN by simp
    hence "(\<integral>\<^sup>+x. ennreal (- g x) * indicator S x \<partial>lborel) = 0"
      using Nem[OF Ssets] by simp
    hence "AE x in lborel. ennreal (- g x) * indicator S x = 0"
      using Ssets gm by (subst (asm) nn_integral_0_iff_AE) auto
    thus ?thesis by (auto simp: S_def indicator_def)
  qed
  show ?thesis using pos neg by eventually_elim linarith
qed

text \<open>Two reusable facts for R3's dominated-convergence step: the difference
  quotients are uniformly bounded by the Lipschitz constant (the dominating
  function) and Borel measurable in \<open>x\<close> for each fixed \<open>t\<close>.\<close>

lemma norm_dquot_le:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes lip: "\<And>y z. norm (f y - f z) \<le> B * norm (y - z)" and t: "t \<noteq> 0"
  shows "norm (dquot f v x t) \<le> B * norm v"
proof -
  have "norm (dquot f v x t) = norm (f (x + t *\<^sub>R v) - f x) / \<bar>t\<bar>"
    unfolding dquot_def by (simp add: divide_inverse mult.commute)
  also have "\<dots> \<le> (B * norm (t *\<^sub>R v)) / \<bar>t\<bar>"
    using lip[of "x + t *\<^sub>R v" x] t by (intro divide_right_mono) auto
  also have "\<dots> = B * norm v" using t by simp
  finally show ?thesis .
qed

lemma borel_measurable_dquot:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::{banach,second_countable_topology}"
  assumes cf: "continuous_on UNIV f"
  shows "(\<lambda>x. dquot f v x t) \<in> borel_measurable borel"
  by (rule borel_measurable_continuous_onI[OF continuous_on_dquot[OF cf]])

subsection \<open>Box integrals of difference quotients converge\<close>

text \<open>R3 step 2. Because \<open>ddir\<close> was DEFINED as the limit along
  \<open>t = 1/(n+1)\<close>, the dominated convergence theorem applies to exactly that
  sequence with no reparametrisation: the quotients converge a.e. (Rademacher
  R2', which supplies the null set) and are dominated by the constant
  \<open>B |v|\<close> on a box, which is integrable because a box has finite measure.\<close>

lemma ddir_LIMSEQ:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes x: "x \<in> dlim_set f v"
  shows "(\<lambda>n. dquot f v x (inverse (real (Suc n)))) \<longlonglongrightarrow> ddir f v x"
  by (rule filterlim_compose[OF ddir_tendsto[OF x] filterlim_inverse_Suc])

theorem box_integral_dquot_tendsto:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes lip: "\<And>y z. norm (f y - f z) \<le> B * norm (y - z)"
    and v: "v \<noteq> 0" and S: "S \<in> sets borel" and Sfin: "emeasure lborel S < \<infinity>"
  shows "(\<lambda>n. (\<integral>x. dquot f v x (inverse (real (Suc n))) * indicator S x \<partial>lborel))
      \<longlonglongrightarrow> (\<integral>x. ddir f v x * indicator S x \<partial>lborel)"
proof -
  have cf: "continuous_on UNIV f" by (rule lipschitz_continuous_on_UNIV[OF lip])
  define w where "w = (\<lambda>x. (B * norm v) * indicator S x :: real)"
  have wint: "integrable lborel w"
    unfolding w_def using S Sfin by (intro integrable_mult_right) simp
  have sm: "(\<lambda>x. dquot f v x (inverse (real (Suc n))) * indicator S x)
      \<in> borel_measurable lborel" for n
    using borel_measurable_dquot[OF cf] S by measurable
  have fm: "(\<lambda>x. ddir f v x * indicator S x) \<in> borel_measurable lborel"
    using borel_measurable_ddir[OF cf] S by measurable
  have lim: "AE x in lborel. (\<lambda>n. dquot f v x (inverse (real (Suc n)))
      * indicator S x) \<longlonglongrightarrow> ddir f v x * indicator S x"
  proof -
    have cB: "- dlim_set f v \<in> sets borel"
    proof -
      have "space (borel :: 'a measure) - dlim_set f v \<in> sets borel"
        by (rule sets.compl_sets[OF borel_dlim_set[OF cf]])
      thus ?thesis by (simp add: Compl_eq_Diff_UNIV)
    qed
    have "negligible (- dlim_set f v)" by (rule negligible_no_dderiv[OF lip v])
    hence "- dlim_set f v \<in> null_sets lborel"
      using negligible_iff_null_lborel[OF cB] by simp
    hence ae: "AE x in lborel. x \<in> dlim_set f v"
      by (simp add: eventually_ae_filter) blast
    show ?thesis
    proof (rule eventually_mono[OF ae])
      fix x assume x: "x \<in> dlim_set f v"
      have h: "(\<lambda>n. dquot f v x (inverse (real (Suc n)))) \<longlonglongrightarrow> ddir f v x"
        by (rule ddir_LIMSEQ[OF x])
      show "(\<lambda>n. dquot f v x (inverse (real (Suc n))) * indicator S x)
          \<longlonglongrightarrow> ddir f v x * indicator S x"
        by (rule tendsto_mult[OF h tendsto_const])
    qed
  qed
  have bound: "AE x in lborel. norm (dquot f v x (inverse (real (Suc n)))
      * indicator S x) \<le> w x" for n
  proof (rule AE_I2)
    fix x
    have t: "inverse (real (Suc n)) \<noteq> 0" by simp
    have "norm (dquot f v x (inverse (real (Suc n))) * indicator S x)
        \<le> (B * norm v) * \<bar>indicator S x :: real\<bar>"
      using norm_dquot_le[OF lip t, of v x]
      by (simp add: abs_mult mult_right_mono)
    thus "norm (dquot f v x (inverse (real (Suc n))) * indicator S x) \<le> w x"
      unfolding w_def by (simp add: indicator_def)
  qed
  show ?thesis
    by (rule integral_dominated_convergence[OF fm sm wint lim bound])
qed

subsection \<open>Translating the box instead of the integrand\<close>

text \<open>The other half of R3 step 2: the shifted quotient integrates over a
  shifted box. Translation invariance of Lebesgue measure is
  \<open>lborel_distr_plus\<close>; composing it with \<open>integral_distr\<close> moves the shift from
  the integrand onto the domain, and the indicator identity below keeps the
  domain a box.\<close>

lemma indicator_box_translate:
  fixes x c l r :: "'a::euclidean_space"
  shows "(indicator (box (l + c) (r + c)) (x + c) :: real) = indicator (box l r) x"
proof -
  have "(x + c \<in> box (l + c) (r + c)) = (x \<in> box l r)"
    by (auto simp: mem_box inner_add_left)
  thus ?thesis by (simp add: indicator_def)
qed

theorem integral_translate_box:
  fixes h :: "'a::euclidean_space \<Rightarrow> real"
  assumes hm: "h \<in> borel_measurable borel"
  shows "(\<integral>x. h (x + c) * indicator (box l r) x \<partial>lborel)
       = (\<integral>y. h y * indicator (box (l + c) (r + c)) y \<partial>lborel)"
proof -
  define g where "g = (\<lambda>y. h y * indicator (box (l + c) (r + c)) y :: real)"
  have gm: "g \<in> borel_measurable borel" unfolding g_def using hm by measurable
  have meas: "(+) c \<in> (lborel :: 'a measure) \<rightarrow>\<^sub>M (borel :: 'a measure)"
    by measurable
  have "integral\<^sup>L (distr lborel borel ((+) c)) g
      = integral\<^sup>L lborel (\<lambda>x. g ((+) c x))"
    by (rule integral_distr[OF meas gm])
  hence step: "integral\<^sup>L lborel g = integral\<^sup>L lborel (\<lambda>x. g (c + x))"
    by (simp add: lborel_distr_plus)
  have pt: "g (c + x) = h (x + c) * indicator (box l r) x" for x
  proof -
    have "g (c + x) = h (x + c) * indicator (box (l + c) (r + c)) (x + c)"
      unfolding g_def by (simp add: add.commute)
    thus ?thesis by (simp add: indicator_box_translate)
  qed
  have "integral\<^sup>L lborel (\<lambda>x. g (c + x))
      = (\<integral>x. h (x + c) * indicator (box l r) x \<partial>lborel)"
    by (simp add: pt)
  thus ?thesis using step unfolding g_def by simp
qed

subsection \<open>The additivity identity at the level of box integrals\<close>

text \<open>R3 step 3. Integrating the algebraic split over a box and moving the
  shift onto the domain gives an EXACT identity for every \<open>t \<noteq> 0\<close>: the
  \<open>(u+v)\<close>-quotient over a box equals the \<open>v\<close>-quotient over the translated box
  plus the \<open>u\<close>-quotient over the original one. Letting \<open>t \<rightarrow> 0\<close> in it is what
  finally produces a.e. additivity.\<close>

lemma dquot_indicator_bound:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes lip: "\<And>y z. norm (f y - f z) \<le> B * norm (y - z)" and t: "t \<noteq> 0"
  shows "norm (dquot f v y t * indicator S x)
       \<le> norm ((\<bar>B\<bar> * norm v) * indicator S x)"
proof -
  have h1: "\<bar>dquot f v y t\<bar> \<le> \<bar>B\<bar> * norm v"
  proof -
    have "\<bar>dquot f v y t\<bar> \<le> B * norm v"
      using norm_dquot_le[OF lip t, of v y] by simp
    also have "\<dots> \<le> \<bar>B\<bar> * norm v" by (intro mult_right_mono) auto
    finally show ?thesis .
  qed
  have "norm (dquot f v y t * indicator S x)
      = \<bar>dquot f v y t\<bar> * \<bar>indicator S x :: real\<bar>"
    by (simp add: abs_mult)
  also have "\<dots> \<le> (\<bar>B\<bar> * norm v) * \<bar>indicator S x :: real\<bar>"
    using h1 by (intro mult_right_mono) auto
  also have "\<dots> = norm ((\<bar>B\<bar> * norm v) * indicator S x)"
    by (simp add: abs_mult)
  finally show ?thesis .
qed

lemma integrable_dquot_indicator:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes lip: "\<And>y z. norm (f y - f z) \<le> B * norm (y - z)"
    and t: "t \<noteq> 0" and S: "S \<in> sets borel" and Sfin: "emeasure lborel S < top"
  shows "integrable lborel (\<lambda>x. dquot f v x t * indicator S x)"
proof (rule Bochner_Integration.integrable_bound)
  show "integrable lborel (\<lambda>x. (\<bar>B\<bar> * norm v) * indicator S x :: real)"
    using S Sfin by (intro integrable_mult_right) simp
  have cf: "continuous_on UNIV f" by (rule lipschitz_continuous_on_UNIV[OF lip])
  show "(\<lambda>x. dquot f v x t * indicator S x) \<in> borel_measurable lborel"
    using borel_measurable_dquot[OF cf] S by measurable
  show "AE x in lborel. norm (dquot f v x t * indicator S x)
      \<le> norm ((\<bar>B\<bar> * norm v) * indicator S x)"
    by (rule AE_I2) (rule dquot_indicator_bound[OF lip t])
qed

theorem box_integral_add_split:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes lip: "\<And>y z. norm (f y - f z) \<le> B * norm (y - z)" and t: "t \<noteq> 0"
  shows "(\<integral>x. dquot f (u + v) x t * indicator (box l r) x \<partial>lborel)
       = (\<integral>y. dquot f v y t
            * indicator (box (l + t *\<^sub>R u) (r + t *\<^sub>R u)) y \<partial>lborel)
       + (\<integral>x. dquot f u x t * indicator (box l r) x \<partial>lborel)"
proof -
  have cf: "continuous_on UNIV f" by (rule lipschitz_continuous_on_UNIV[OF lip])
  have fin: "emeasure lborel (box l r :: 'a set) < top"
    by (simp add: emeasure_lborel_box_eq)
  have iu: "integrable lborel (\<lambda>x. dquot f u x t * indicator (box l r) x)"
    by (rule integrable_dquot_indicator[OF lip t _ fin]) simp
  have ishift: "integrable lborel
      (\<lambda>x. dquot f v (x + t *\<^sub>R u) t * indicator (box l r) x)"
  proof (rule Bochner_Integration.integrable_bound)
    show "integrable lborel
        (\<lambda>x. (\<bar>B\<bar> * norm v) * indicator (box l r) x :: real)"
      using fin by (intro integrable_mult_right) simp
    show "(\<lambda>x. dquot f v (x + t *\<^sub>R u) t * indicator (box l r) x)
        \<in> borel_measurable lborel"
      using borel_measurable_dquot[OF cf, of v t] by measurable
    show "AE x in lborel. norm (dquot f v (x + t *\<^sub>R u) t
        * indicator (box l r) x)
        \<le> norm ((\<bar>B\<bar> * norm v) * indicator (box l r) x)"
      by (rule AE_I2) (rule dquot_indicator_bound[OF lip t])
  qed
  have split: "(\<lambda>x. dquot f (u + v) x t * indicator (box l r) x)
      = (\<lambda>x. dquot f v (x + t *\<^sub>R u) t * indicator (box l r) x
          + dquot f u x t * indicator (box l r) x)"
    by (rule ext) (simp add: dquot_add_split[OF t] algebra_simps)
  have "(\<integral>x. dquot f (u + v) x t * indicator (box l r) x \<partial>lborel)
      = (\<integral>x. dquot f v (x + t *\<^sub>R u) t * indicator (box l r) x \<partial>lborel)
      + (\<integral>x. dquot f u x t * indicator (box l r) x \<partial>lborel)"
    unfolding split by (rule Bochner_Integration.integral_add[OF ishift iu])
  moreover have "(\<integral>x. dquot f v (x + t *\<^sub>R u) t * indicator (box l r) x \<partial>lborel)
      = (\<integral>y. dquot f v y t
          * indicator (box (l + t *\<^sub>R u) (r + t *\<^sub>R u)) y \<partial>lborel)"
    by (rule integral_translate_box) (rule borel_measurable_dquot[OF cf])
  ultimately show ?thesis by simp
qed

subsection \<open>L1 convergence of the quotients\<close>

text \<open>The first half of the moving-box estimate: the quotients converge to
  \<open>ddir\<close> not merely pointwise a.e. but in L1 of any finite-measure set. That
  is what lets the domain wobble by \<open>t u\<close> without breaking the limit \<comment>
  \<open>pointwise convergence alone would not survive a moving domain\<close>.\<close>

theorem L1_dquot_tendsto:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes lip: "\<And>y z. norm (f y - f z) \<le> B * norm (y - z)"
    and v: "v \<noteq> 0" and S: "S \<in> sets borel" and Sfin: "emeasure lborel S < top"
  shows "(\<lambda>n. (\<integral>x. \<bar>dquot f v x (inverse (real (Suc n))) - ddir f v x\<bar>
      * indicator S x \<partial>lborel)) \<longlonglongrightarrow> 0"
proof -
  have cf: "continuous_on UNIV f" by (rule lipschitz_continuous_on_UNIV[OF lip])
  have ae: "AE x in lborel. x \<in> dlim_set f v"
  proof -
    have cB: "- dlim_set f v \<in> sets borel"
    proof -
      have "space (borel :: 'a measure) - dlim_set f v \<in> sets borel"
        by (rule sets.compl_sets[OF borel_dlim_set[OF cf]])
      thus ?thesis by (simp add: Compl_eq_Diff_UNIV)
    qed
    have "negligible (- dlim_set f v)" by (rule negligible_no_dderiv[OF lip v])
    hence "- dlim_set f v \<in> null_sets lborel"
      using negligible_iff_null_lborel[OF cB] by simp
    thus ?thesis by (simp add: eventually_ae_filter) blast
  qed
  define w where "w = (\<lambda>x. (2 * \<bar>B\<bar> * norm v) * indicator S x :: real)"
  have wint: "integrable lborel w"
    unfolding w_def using S Sfin by (intro integrable_mult_right) simp
  have sm: "(\<lambda>x. \<bar>dquot f v x (inverse (real (Suc n))) - ddir f v x\<bar>
      * indicator S x) \<in> borel_measurable lborel" for n
    using borel_measurable_dquot[OF cf] borel_measurable_ddir[OF cf] S
    by measurable
  have lim: "AE x in lborel. (\<lambda>n. \<bar>dquot f v x (inverse (real (Suc n)))
      - ddir f v x\<bar> * indicator S x) \<longlonglongrightarrow> 0 * indicator S x"
  proof (rule eventually_mono[OF ae])
    fix x assume x: "x \<in> dlim_set f v"
    have h: "(\<lambda>n. dquot f v x (inverse (real (Suc n)))) \<longlonglongrightarrow> ddir f v x"
      by (rule ddir_LIMSEQ[OF x])
    have "(\<lambda>n. \<bar>dquot f v x (inverse (real (Suc n))) - ddir f v x\<bar>)
        \<longlonglongrightarrow> \<bar>ddir f v x - ddir f v x\<bar>"
      by (intro tendsto_rabs tendsto_diff h tendsto_const)
    hence "(\<lambda>n. \<bar>dquot f v x (inverse (real (Suc n))) - ddir f v x\<bar>)
        \<longlonglongrightarrow> 0" by simp
    thus "(\<lambda>n. \<bar>dquot f v x (inverse (real (Suc n))) - ddir f v x\<bar>
        * indicator S x) \<longlonglongrightarrow> 0 * indicator S x"
      by (rule tendsto_mult[OF _ tendsto_const])
  qed
  have bound: "AE x in lborel. norm (\<bar>dquot f v x (inverse (real (Suc n)))
      - ddir f v x\<bar> * indicator S x) \<le> w x" for n
  proof (rule eventually_mono[OF ae])
    fix x assume x: "x \<in> dlim_set f v"
    have t: "inverse (real (Suc n)) \<noteq> 0" by simp
    have q: "\<bar>dquot f v x (inverse (real (Suc n)))\<bar> \<le> \<bar>B\<bar> * norm v"
    proof -
      have "\<bar>dquot f v x (inverse (real (Suc n)))\<bar> \<le> B * norm v"
        using norm_dquot_le[OF lip t, of v x] by simp
      also have "\<dots> \<le> \<bar>B\<bar> * norm v" by (intro mult_right_mono) auto
      finally show ?thesis .
    qed
    have d: "\<bar>ddir f v x\<bar> \<le> \<bar>B\<bar> * norm v"
    proof -
      have "\<bar>ddir f v x\<bar> \<le> B * norm v"
        using norm_ddir_le[OF lip x] by simp
      also have "\<dots> \<le> \<bar>B\<bar> * norm v" by (intro mult_right_mono) auto
      finally show ?thesis .
    qed
    have "\<bar>dquot f v x (inverse (real (Suc n))) - ddir f v x\<bar>
        \<le> 2 * \<bar>B\<bar> * norm v" using q d by linarith
    hence "\<bar>dquot f v x (inverse (real (Suc n))) - ddir f v x\<bar>
        * \<bar>indicator S x :: real\<bar> \<le> (2 * \<bar>B\<bar> * norm v)
        * \<bar>indicator S x :: real\<bar>"
      by (intro mult_right_mono) auto
    thus "norm (\<bar>dquot f v x (inverse (real (Suc n))) - ddir f v x\<bar>
        * indicator S x) \<le> w x"
      unfolding w_def by (simp add: abs_mult indicator_def)
  qed
  have "(\<lambda>n. (\<integral>x. \<bar>dquot f v x (inverse (real (Suc n))) - ddir f v x\<bar>
      * indicator S x \<partial>lborel)) \<longlonglongrightarrow> (\<integral>x. 0 * indicator S x \<partial>lborel)"
    by (rule integral_dominated_convergence[OF _ sm wint lim bound]) simp
  thus ?thesis by simp
qed

subsection \<open>The defect of a translated box vanishes\<close>

text \<open>The second half of the moving-box estimate. Translating a box does not
  change its content, and the overlap content is continuous, so the DEFECT
  \<open>2(content B - content (B \<inter> (B+w)))\<close> \<comment> \<open>which dominates the measure of the
  symmetric difference\<close> tends to \<open>0\<close>.\<close>

lemma content_box_translate:
  fixes a b w :: "'a::euclidean_space"
  shows "content (box (a + w) (b + w)) = content (box a b)"
proof -
  have cond: "(\<forall>i\<in>Basis. (a + w) \<bullet> i \<le> (b + w) \<bullet> i)
      \<longleftrightarrow> (\<forall>i\<in>Basis. a \<bullet> i \<le> b \<bullet> i)"
    by (simp add: inner_add_left)
  have fac: "(\<Prod>i\<in>Basis. (b + w) \<bullet> i - (a + w) \<bullet> i)
      = (\<Prod>i\<in>Basis. b \<bullet> i - a \<bullet> i)"
    by (rule prod.cong[OF refl]) (simp add: inner_add_left)
  show ?thesis
    unfolding content_box_cases using cond fac by simp
qed

theorem box_translate_defect_tendsto:
  fixes a b :: "'a::euclidean_space"
  shows "((\<lambda>w. 2 * (content (cbox a b)
      - content (cbox a b \<inter> cbox (a + w) (b + w)))) \<longlongrightarrow> 0) (at (0::'a))"
proof -
  have inner: "((\<lambda>w. content (cbox a b \<inter> cbox (a + w) (b + w)))
      \<longlongrightarrow> content (cbox a b :: 'a set)) (at (0::'a))"
    by (rule content_box_int_translate_tendsto)
  have "((\<lambda>w. content (cbox a b :: 'a set)
      - content (cbox a b \<inter> cbox (a + w) (b + w)))
      \<longlongrightarrow> content (cbox a b :: 'a set) - content (cbox a b :: 'a set))
      (at (0::'a))"
    by (rule tendsto_diff[OF tendsto_const inner])
  from tendsto_mult[OF tendsto_const this]
  have "((\<lambda>w. 2 * (content (cbox a b :: 'a set)
      - content (cbox a b \<inter> cbox (a + w) (b + w))))
      \<longlongrightarrow> 2 * (content (cbox a b :: 'a set)
        - content (cbox a b :: 'a set))) (at (0::'a))" .
  thus ?thesis by simp
qed

text \<open>An indicator identity for the symmetric difference, used by the
  moving-domain estimate.\<close>

lemma indicator_diff_abs:
  fixes A C :: "'a set"
  shows "\<bar>(indicator A x :: real) - indicator C x\<bar>
       = indicator A x + indicator C x - 2 * indicator (A \<inter> C) x"
  by (simp add: indicator_def)
text \<open>Two small building blocks for the moving-domain bound: integrability of
  a bounded function restricted to a finite-measure set, and the integral of
  the symmetric-difference combination of indicators.\<close>

lemma integrable_bounded_indicator:
  fixes h :: "'a::euclidean_space \<Rightarrow> real"
  assumes hm: "h \<in> borel_measurable borel" and hb: "\<And>x. \<bar>h x\<bar> \<le> M"
    and S: "S \<in> sets borel" and Sfin: "emeasure lborel S < top"
  shows "integrable lborel (\<lambda>x. h x * indicator S x)"
proof (rule Bochner_Integration.integrable_bound)
  show "integrable lborel (\<lambda>x. \<bar>M\<bar> * indicator S x :: real)"
    using S Sfin by (intro integrable_mult_right) simp
  show "(\<lambda>x. h x * indicator S x) \<in> borel_measurable lborel"
    using hm S by measurable
  show "AE x in lborel. norm (h x * indicator S x)
      \<le> norm (\<bar>M\<bar> * indicator S x)"
  proof (rule AE_I2)
    fix x
    have "\<bar>h x\<bar> \<le> \<bar>M\<bar>" using hb[of x] by simp
    hence "\<bar>h x\<bar> * \<bar>indicator S x :: real\<bar>
        \<le> \<bar>M\<bar> * \<bar>indicator S x :: real\<bar>"
      by (intro mult_right_mono) auto
    thus "norm (h x * indicator S x) \<le> norm (\<bar>M\<bar> * indicator S x)"
      by (simp add: abs_mult)
  qed
qed

lemma integral_indicator_symdiff:
  fixes A C :: "'a::euclidean_space set"
  assumes A: "A \<in> sets borel" and Afin: "emeasure lborel A < top"
    and C: "C \<in> sets borel" and Cfin: "emeasure lborel C < top"
  shows "(\<integral>x. (indicator A x :: real) + indicator C x
      - 2 * indicator (A \<inter> C) x \<partial>lborel)
      = measure lborel A + measure lborel C - 2 * measure lborel (A \<inter> C)"
proof -
  have AC: "A \<inter> C \<in> sets borel" using A C by simp
  have ACfin: "emeasure lborel (A \<inter> C) < top"
    by (rule le_less_trans[OF emeasure_mono[of "A \<inter> C" A]]) (use A Afin in auto)
  have iA: "integrable lborel (\<lambda>x. indicator A x :: real)"
    using A Afin by simp
  have iC: "integrable lborel (\<lambda>x. indicator C x :: real)"
    using C Cfin by simp
  have iAC: "integrable lborel (\<lambda>x. indicator (A \<inter> C) x :: real)"
    using AC ACfin by simp
  show ?thesis
    using iA iC iAC A C AC
    by simp
qed

text \<open>The moving-domain bound: replacing the domain of integration by
  another set changes the integral of a bounded function by at most the bound
  times the measure of the symmetric difference.\<close>

theorem integral_domain_shift_bound:
  fixes h :: "'a::euclidean_space \<Rightarrow> real"
  assumes hm: "h \<in> borel_measurable borel" and hb: "\<And>x. \<bar>h x\<bar> \<le> M"
    and A: "A \<in> sets borel" and Afin: "emeasure lborel A < top"
    and C: "C \<in> sets borel" and Cfin: "emeasure lborel C < top"
  shows "\<bar>(\<integral>x. h x * indicator A x \<partial>lborel)
       - (\<integral>x. h x * indicator C x \<partial>lborel)\<bar>
       \<le> \<bar>M\<bar> * (measure lborel A + measure lborel C
           - 2 * measure lborel (A \<inter> C))"
proof -
  have AC: "A \<inter> C \<in> sets borel" using A C by simp
  have ACfin: "emeasure lborel (A \<inter> C) < top"
    by (rule le_less_trans[OF emeasure_mono[of "A \<inter> C" A]]) (use A Afin in auto)
  have iA: "integrable lborel (\<lambda>x. h x * indicator A x)"
    by (rule integrable_bounded_indicator[OF hm hb A Afin])
  have iC: "integrable lborel (\<lambda>x. h x * indicator C x)"
    by (rule integrable_bounded_indicator[OF hm hb C Cfin])
  have idiff: "integrable lborel (\<lambda>x. h x * indicator A x - h x * indicator C x)"
    by (rule Bochner_Integration.integrable_diff[OF iA iC])
  have iAi: "integrable lborel (\<lambda>x. indicator A x :: real)" using A Afin by simp
  have iCi: "integrable lborel (\<lambda>x. indicator C x :: real)" using C Cfin by simp
  have iACi: "integrable lborel (\<lambda>x. indicator (A \<inter> C) x :: real)"
    using AC ACfin by simp
  have idom: "integrable lborel (\<lambda>x. \<bar>M\<bar> * ((indicator A x :: real)
      + indicator C x - 2 * indicator (A \<inter> C) x))"
    using iAi iCi iACi by (intro integrable_mult_right) simp
  have ptb: "\<bar>h x * indicator A x - h x * indicator C x\<bar>
      \<le> \<bar>M\<bar> * ((indicator A x :: real) + indicator C x
        - 2 * indicator (A \<inter> C) x)" for x
  proof -
    have fac: "h x * (indicator A x :: real) - h x * indicator C x
        = h x * ((indicator A x :: real) - indicator C x)"
      by (simp add: right_diff_distrib)
    have "\<bar>h x * (indicator A x :: real) - h x * indicator C x\<bar>
        = \<bar>h x\<bar> * \<bar>(indicator A x :: real) - indicator C x\<bar>"
      unfolding fac by (rule abs_mult)
    also have "\<dots> \<le> \<bar>M\<bar> * \<bar>(indicator A x :: real) - indicator C x\<bar>"
      using hb[of x] by (intro mult_right_mono) auto
    also have "\<bar>(indicator A x :: real) - indicator C x\<bar>
        = indicator A x + indicator C x - 2 * indicator (A \<inter> C) x"
      by (rule indicator_diff_abs)
    finally show ?thesis by simp
  qed
  have "\<bar>(\<integral>x. h x * indicator A x - h x * indicator C x \<partial>lborel)\<bar>
      \<le> (\<integral>x. \<bar>M\<bar> * ((indicator A x :: real) + indicator C x
          - 2 * indicator (A \<inter> C) x) \<partial>lborel)"
  proof -
    have "\<bar>(\<integral>x. h x * indicator A x - h x * indicator C x \<partial>lborel)\<bar>
        \<le> (\<integral>x. \<bar>h x * indicator A x - h x * indicator C x\<bar> \<partial>lborel)"
      by (rule integral_abs_bound)
    also have "\<dots> \<le> (\<integral>x. \<bar>M\<bar> * ((indicator A x :: real) + indicator C x
        - 2 * indicator (A \<inter> C) x) \<partial>lborel)"
      using ptb idom idiff by (intro integral_mono) auto
    finally show ?thesis .
  qed
  moreover have "(\<integral>x. \<bar>M\<bar> * ((indicator A x :: real) + indicator C x
      - 2 * indicator (A \<inter> C) x) \<partial>lborel)
      = \<bar>M\<bar> * (measure lborel A + measure lborel C
          - 2 * measure lborel (A \<inter> C))"
    using integral_indicator_symdiff[OF A Afin C Cfin] by simp
  moreover have "\<bar>(\<integral>x. h x * indicator A x
      - h x * indicator C x \<partial>lborel)\<bar>
      = \<bar>(\<integral>x. h x * indicator A x \<partial>lborel)
      - (\<integral>x. h x * indicator C x \<partial>lborel)\<bar>"
    using Bochner_Integration.integral_diff[OF iA iC] by simp
  ultimately show ?thesis by linarith
qed

subsection \<open>Open and closed boxes, and the defect along a sequence\<close>

text \<open>Two conveniences for the limit passage. Integrals over an open box and
  its closure agree, because they differ on the frontier, which is negligible
  \<comment> \<open>this reconciles the open boxes of the Borel generator with the closed
  boxes of the overlap estimate\<close>. And the defect along the sequence
  \<open>w\<^sub>n = u/(n+1)\<close> tends to zero.\<close>

lemma integral_box_cbox_eq:
  fixes h :: "'a::euclidean_space \<Rightarrow> real"
  assumes hm: "h \<in> borel_measurable borel"
  shows "(\<integral>x. h x * indicator (box a b) x \<partial>lborel)
       = (\<integral>x. h x * indicator (cbox a b) x \<partial>lborel)"
proof (rule integral_cong_AE)
  show "(\<lambda>x. h x * indicator (box a b) x) \<in> borel_measurable lborel"
    using hm by measurable
  show "(\<lambda>x. h x * indicator (cbox a b) x) \<in> borel_measurable lborel"
    using hm by measurable
  have negl: "negligible (cbox a b - box a b :: 'a set)"
    by (rule negligible_frontier_interval)
  have sB: "(cbox a b - box a b :: 'a set) \<in> sets borel" by simp
  have "(cbox a b - box a b :: 'a set) \<in> null_sets lborel"
    using negligible_iff_null_lborel[OF sB] negl by simp
  hence "AE x in lborel. x \<notin> (cbox a b - box a b :: 'a set)"
    by (simp add: eventually_ae_filter) blast
  thus "AE x in lborel. h x * indicator (box a b) x
      = h x * indicator (cbox a b) x"
    by (rule eventually_mono)
      (auto simp: indicator_def dest: subsetD[OF box_subset_cbox])
qed

lemma filterlim_scaleR_inverse_Suc:
  fixes u :: "'a::real_normed_vector"
  assumes u: "u \<noteq> 0"
  shows "filterlim (\<lambda>n. inverse (real (Suc n)) *\<^sub>R u) (at 0) sequentially"
  unfolding filterlim_at
proof (intro conjI)
  have "((\<lambda>n. inverse (real (Suc n)) *\<^sub>R u) \<longlongrightarrow> 0 *\<^sub>R u) sequentially"
    by (intro tendsto_intros LIMSEQ_inverse_real_of_nat)
  thus "((\<lambda>n. inverse (real (Suc n)) *\<^sub>R u) \<longlongrightarrow> 0) sequentially" by simp
  show "eventually (\<lambda>n. inverse (real (Suc n)) *\<^sub>R u \<in> UNIV
      \<and> inverse (real (Suc n)) *\<^sub>R u \<noteq> 0) sequentially"
    using u by simp
qed

theorem defect_seq_tendsto:
  fixes a b u :: "'a::euclidean_space"
  assumes u: "u \<noteq> 0"
  shows "(\<lambda>n. 2 * (content (cbox a b)
      - content (cbox a b \<inter> cbox (a + inverse (real (Suc n)) *\<^sub>R u)
          (b + inverse (real (Suc n)) *\<^sub>R u)))) \<longlonglongrightarrow> 0"
  by (rule filterlim_compose[OF box_translate_defect_tendsto
        filterlim_scaleR_inverse_Suc[OF u]])

subsection \<open>The limit over a moving box\<close>

text \<open>The heart of R3's limit passage: the quotient integrated over the
  TRANSLATED box still converges to the integral of \<open>ddir\<close> over the original
  one. The error splits into a domain part, bounded by the uniform quotient
  bound times the defect, and a fixed-domain part, which is ordinary
  dominated convergence.\<close>

lemma content_cbox_translate:
  fixes a b w :: "'a::euclidean_space"
  shows "content (cbox (a + w) (b + w)) = content (cbox a b)"
proof -
  have cond: "(\<forall>i\<in>Basis. (a + w) \<bullet> i \<le> (b + w) \<bullet> i)
      \<longleftrightarrow> (\<forall>i\<in>Basis. a \<bullet> i \<le> b \<bullet> i)"
    by (simp add: inner_add_left)
  have fac: "(\<Prod>i\<in>Basis. (b + w) \<bullet> i - (a + w) \<bullet> i)
      = (\<Prod>i\<in>Basis. b \<bullet> i - a \<bullet> i)"
    by (rule prod.cong[OF refl]) (simp add: inner_add_left)
  show ?thesis
    unfolding content_cbox_cases using cond fac by simp
qed

theorem shifted_box_integral_tendsto:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes lip: "\<And>y z. norm (f y - f z) \<le> B * norm (y - z)"
    and v: "v \<noteq> 0" and u: "u \<noteq> 0"
  shows "(\<lambda>n. (\<integral>y. dquot f v y (inverse (real (Suc n)))
        * indicator (cbox (a + inverse (real (Suc n)) *\<^sub>R u)
            (b + inverse (real (Suc n)) *\<^sub>R u)) y \<partial>lborel))
      \<longlonglongrightarrow> (\<integral>x. ddir f v x * indicator (cbox a b) x \<partial>lborel)"
proof -
  have cf: "continuous_on UNIV f" by (rule lipschitz_continuous_on_UNIV[OF lip])
  define t where "t = (\<lambda>n::nat. inverse (real (Suc n)))"
  define A where "A = (\<lambda>n. cbox (a + t n *\<^sub>R u) (b + t n *\<^sub>R u) :: 'a set)"
  define C where "C = (cbox a b :: 'a set)"
  define q where "q = (\<lambda>n x. dquot f v x (t n))"
  define D where "D = ddir f v"
  have tne: "t n \<noteq> 0" for n by (simp add: t_def)
  have Afin: "emeasure lborel (A n) < top" for n
    unfolding A_def by (simp add: emeasure_lborel_cbox_eq)
  have Cfin: "emeasure lborel C < top"
    unfolding C_def by (simp add: emeasure_lborel_cbox_eq)
  have qm: "q n \<in> borel_measurable borel" for n
    unfolding q_def using borel_measurable_dquot[OF cf] by simp
  have qb: "\<bar>q n x\<bar> \<le> B * norm v" for n x
    unfolding q_def using norm_dquot_le[OF lip tne, of v x] by simp
  have dom: "\<bar>(\<integral>y. q n y * indicator (A n) y \<partial>lborel)
      - (\<integral>y. q n y * indicator C y \<partial>lborel)\<bar>
      \<le> \<bar>B * norm v\<bar> * (2 * (content C - content (C \<inter> A n)))" for n
  proof -
    have "\<bar>(\<integral>y. q n y * indicator (A n) y \<partial>lborel)
        - (\<integral>y. q n y * indicator C y \<partial>lborel)\<bar>
        \<le> \<bar>B * norm v\<bar> * (measure lborel (A n) + measure lborel C
            - 2 * measure lborel (A n \<inter> C))"
      by (rule integral_domain_shift_bound[OF qm qb _ Afin _ Cfin])
        (auto simp: A_def C_def)
    moreover have "measure lborel (A n) = content C"
      unfolding A_def C_def by (rule content_cbox_translate)
    moreover have "A n \<inter> C = C \<inter> A n" by blast
    ultimately show ?thesis by simp
  qed
  have defect: "(\<lambda>n. \<bar>B * norm v\<bar> * (2 * (content C - content (C \<inter> A n))))
      \<longlonglongrightarrow> \<bar>B * norm v\<bar> * 0"
    unfolding C_def A_def t_def
    by (intro tendsto_mult tendsto_const defect_seq_tendsto[OF u])
  have fixed: "(\<lambda>n. (\<integral>y. q n y * indicator C y \<partial>lborel))
      \<longlonglongrightarrow> (\<integral>x. D x * indicator C x \<partial>lborel)"
    unfolding q_def D_def t_def C_def
    by (rule box_integral_dquot_tendsto[OF lip v]) (auto simp: Cfin[unfolded C_def])
  have cmp: "(\<lambda>n. (\<integral>y. q n y * indicator (A n) y \<partial>lborel)
      - (\<integral>x. D x * indicator C x \<partial>lborel)) \<longlonglongrightarrow> 0"
  proof (rule Lim_null_comparison)
    show "(\<lambda>n. \<bar>B * norm v\<bar> * (2 * (content C - content (C \<inter> A n)))
        + \<bar>(\<integral>y. q n y * indicator C y \<partial>lborel)
          - (\<integral>x. D x * indicator C x \<partial>lborel)\<bar>) \<longlonglongrightarrow> 0"
    proof -
      have "(\<lambda>n. (\<integral>y. q n y * indicator C y \<partial>lborel)
          - (\<integral>x. D x * indicator C x \<partial>lborel))
          \<longlonglongrightarrow> (\<integral>x. D x * indicator C x \<partial>lborel)
            - (\<integral>x. D x * indicator C x \<partial>lborel)"
        by (intro tendsto_diff fixed tendsto_const)
      hence z0: "(\<lambda>n. (\<integral>y. q n y * indicator C y \<partial>lborel)
          - (\<integral>x. D x * indicator C x \<partial>lborel)) \<longlonglongrightarrow> 0" by simp
      have z2: "(\<lambda>n. \<bar>(\<integral>y. q n y * indicator C y \<partial>lborel)
          - (\<integral>x. D x * indicator C x \<partial>lborel)\<bar>) \<longlonglongrightarrow> 0"
        using tendsto_rabs[OF z0] by simp
      have z1: "(\<lambda>n. \<bar>B * norm v\<bar>
          * (2 * (content C - content (C \<inter> A n)))) \<longlonglongrightarrow> 0"
        using defect by simp
      show ?thesis using tendsto_add[OF z1 z2] by simp
    qed
    show "eventually (\<lambda>n. norm ((\<integral>y. q n y * indicator (A n) y \<partial>lborel)
        - (\<integral>x. D x * indicator C x \<partial>lborel))
        \<le> \<bar>B * norm v\<bar> * (2 * (content C - content (C \<inter> A n)))
          + \<bar>(\<integral>y. q n y * indicator C y \<partial>lborel)
            - (\<integral>x. D x * indicator C x \<partial>lborel)\<bar>) sequentially"
    proof (rule always_eventually, rule allI)
      fix n
      show "norm ((\<integral>y. q n y * indicator (A n) y \<partial>lborel)
          - (\<integral>x. D x * indicator C x \<partial>lborel))
          \<le> \<bar>B * norm v\<bar> * (2 * (content C - content (C \<inter> A n)))
            + \<bar>(\<integral>y. q n y * indicator C y \<partial>lborel)
              - (\<integral>x. D x * indicator C x \<partial>lborel)\<bar>"
        using dom[of n] by simp
    qed
  qed
  from cmp show ?thesis
    unfolding q_def A_def C_def D_def t_def
    by (simp add: Lim_null[symmetric])
qed

subsection \<open>Additivity of the box integrals of the derivative\<close>

text \<open>R3, assembled: passing to the limit in the exact identity
  `box_integral_add_split` \<comment> \<open>whose three terms converge by
  `box_integral_dquot_tendsto` and `shifted_box_integral_tendsto`\<close> turns it
  into additivity of the box integrals of \<open>ddir\<close> itself. Uniqueness of
  sequential limits does the rest.\<close>

theorem box_integral_ddir_add:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes lip: "\<And>y z. norm (f y - f z) \<le> B * norm (y - z)"
    and u: "u \<noteq> 0" and v: "v \<noteq> 0" and uv: "u + v \<noteq> 0"
  shows "(\<integral>x. ddir f (u + v) x * indicator (cbox a b) x \<partial>lborel)
       = (\<integral>x. ddir f v x * indicator (cbox a b) x \<partial>lborel)
       + (\<integral>x. ddir f u x * indicator (cbox a b) x \<partial>lborel)"
proof -
  have cf: "continuous_on UNIV f" by (rule lipschitz_continuous_on_UNIV[OF lip])
  define t where "t = (\<lambda>n::nat. inverse (real (Suc n)))"
  have tne: "t n \<noteq> 0" for n by (simp add: t_def)
  have Cfin: "emeasure lborel (cbox a b :: 'a set) < top"
    by (simp add: emeasure_lborel_cbox_eq)
  have split: "(\<integral>x. dquot f (u + v) x (t n) * indicator (cbox a b) x \<partial>lborel)
      = (\<integral>y. dquot f v y (t n)
          * indicator (cbox (a + t n *\<^sub>R u) (b + t n *\<^sub>R u)) y \<partial>lborel)
      + (\<integral>x. dquot f u x (t n) * indicator (cbox a b) x \<partial>lborel)" for n
  proof -
    have "(\<integral>x. dquot f (u + v) x (t n) * indicator (box a b) x \<partial>lborel)
        = (\<integral>y. dquot f v y (t n)
            * indicator (box (a + t n *\<^sub>R u) (b + t n *\<^sub>R u)) y \<partial>lborel)
        + (\<integral>x. dquot f u x (t n) * indicator (box a b) x \<partial>lborel)"
      by (rule box_integral_add_split[OF lip tne])
    thus ?thesis
      using integral_box_cbox_eq[OF borel_measurable_dquot[OF cf],
          of "u + v" "t n" a b]
        integral_box_cbox_eq[OF borel_measurable_dquot[OF cf],
          of v "t n" "a + t n *\<^sub>R u" "b + t n *\<^sub>R u"]
        integral_box_cbox_eq[OF borel_measurable_dquot[OF cf],
          of u "t n" a b]
      by simp
  qed
  have limL: "(\<lambda>n. (\<integral>x. dquot f (u + v) x (t n)
      * indicator (cbox a b) x \<partial>lborel))
      \<longlonglongrightarrow> (\<integral>x. ddir f (u + v) x * indicator (cbox a b) x \<partial>lborel)"
    unfolding t_def
    by (rule box_integral_dquot_tendsto[OF lip uv]) (auto simp: Cfin)
  have limU: "(\<lambda>n. (\<integral>x. dquot f u x (t n) * indicator (cbox a b) x \<partial>lborel))
      \<longlonglongrightarrow> (\<integral>x. ddir f u x * indicator (cbox a b) x \<partial>lborel)"
    unfolding t_def
    by (rule box_integral_dquot_tendsto[OF lip u]) (auto simp: Cfin)
  have limV: "(\<lambda>n. (\<integral>y. dquot f v y (t n)
      * indicator (cbox (a + t n *\<^sub>R u) (b + t n *\<^sub>R u)) y \<partial>lborel))
      \<longlonglongrightarrow> (\<integral>x. ddir f v x * indicator (cbox a b) x \<partial>lborel)"
    unfolding t_def by (rule shifted_box_integral_tendsto[OF lip v u])
  have "(\<lambda>n. (\<integral>x. dquot f (u + v) x (t n)
      * indicator (cbox a b) x \<partial>lborel))
      \<longlonglongrightarrow> (\<integral>x. ddir f v x * indicator (cbox a b) x \<partial>lborel)
        + (\<integral>x. ddir f u x * indicator (cbox a b) x \<partial>lborel)"
    unfolding split by (rule tendsto_add[OF limV limU])
  from LIMSEQ_unique[OF limL this] show ?thesis .
qed

subsection \<open>From a vanishing integral to balanced positive and negative parts\<close>

text \<open>The bookkeeping bridge between the Bochner statement produced by R3 and
  the ennreal statement consumed by `AE_zero_of_box_integrals_zero`: for an
  integrable function with vanishing integral, the positive and negative
  parts have equal (finite) nonnegative integrals.\<close>

lemma nn_integral_pos_neg_eq_of_integral_zero:
  fixes h :: "'a::euclidean_space \<Rightarrow> real"
  assumes ih: "integrable lborel h" and z: "(\<integral>x. h x \<partial>lborel) = 0"
  shows "(\<integral>\<^sup>+x. ennreal (h x) \<partial>lborel)
       = (\<integral>\<^sup>+x. ennreal (- h x) \<partial>lborel)"
proof -
  define p where "p = (\<lambda>x. max (h x) 0)"
  define m where "m = (\<lambda>x. max (- h x) 0)"
  have ip: "integrable lborel p" unfolding p_def using ih by simp
  have im: "integrable lborel m" unfolding m_def using ih by simp
  have hpm: "h x = p x - m x" for x by (simp add: p_def m_def)
  have "(\<integral>x. p x \<partial>lborel) - (\<integral>x. m x \<partial>lborel)
      = (\<integral>x. p x - m x \<partial>lborel)"
    by (rule Bochner_Integration.integral_diff[OF ip im, symmetric])
  also have "\<dots> = (\<integral>x. h x \<partial>lborel)" using hpm by simp
  finally have eq: "(\<integral>x. p x \<partial>lborel) = (\<integral>x. m x \<partial>lborel)"
    using z by simp
  have pnn: "AE x in lborel. 0 \<le> p x" by (simp add: p_def)
  have mnn: "AE x in lborel. 0 \<le> m x" by (simp add: m_def)
  have "(\<integral>\<^sup>+x. ennreal (h x) \<partial>lborel) = (\<integral>\<^sup>+x. ennreal (p x) \<partial>lborel)"
    by (intro nn_integral_cong) (simp add: p_def max_def ennreal_neg)
  also have "\<dots> = ennreal ((\<integral>x. p x \<partial>lborel))"
    by (rule nn_integral_eq_integral[OF ip pnn])
  also have "\<dots> = ennreal ((\<integral>x. m x \<partial>lborel))" using eq by simp
  also have "\<dots> = (\<integral>\<^sup>+x. ennreal (m x) \<partial>lborel)"
    by (rule nn_integral_eq_integral[OF im mnn, symmetric])
  also have "\<dots> = (\<integral>\<^sup>+x. ennreal (- h x) \<partial>lborel)"
    by (intro nn_integral_cong) (simp add: m_def max_def ennreal_neg)
  finally show ?thesis .
qed

lemma ennreal_mult_indicator_eq:
  fixes g :: "'a \<Rightarrow> real"
  shows "ennreal (g x * indicator S x) = ennreal (g x) * indicator S x"
  by (simp add: indicator_def)

subsection \<open>R3: almost-everywhere additivity in the direction\<close>

lemma AE_dlim_set:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes lip: "\<And>y z. norm (f y - f z) \<le> B * norm (y - z)" and v: "v \<noteq> 0"
  shows "AE x in lborel. x \<in> dlim_set f v"
proof -
  have cf: "continuous_on UNIV f" by (rule lipschitz_continuous_on_UNIV[OF lip])
  have cB: "- dlim_set f v \<in> sets borel"
  proof -
    have "space (borel :: 'a measure) - dlim_set f v \<in> sets borel"
      by (rule sets.compl_sets[OF borel_dlim_set[OF cf]])
    thus ?thesis by (simp add: Compl_eq_Diff_UNIV)
  qed
  have "negligible (- dlim_set f v)" by (rule negligible_no_dderiv[OF lip v])
  hence "- dlim_set f v \<in> null_sets lborel"
    using negligible_iff_null_lborel[OF cB] by simp
  thus ?thesis by (simp add: eventually_ae_filter) blast
qed

lemma integrable_ddir_indicator:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes lip: "\<And>y z. norm (f y - f z) \<le> B * norm (y - z)" and v: "v \<noteq> 0"
    and S: "S \<in> sets borel" and Sfin: "emeasure lborel S < top"
  shows "integrable lborel (\<lambda>x. ddir f v x * indicator S x)"
proof (rule Bochner_Integration.integrable_bound)
  have cf: "continuous_on UNIV f" by (rule lipschitz_continuous_on_UNIV[OF lip])
  show "integrable lborel (\<lambda>x. (\<bar>B\<bar> * norm v) * indicator S x :: real)"
    using S Sfin by (intro integrable_mult_right) simp
  show "(\<lambda>x. ddir f v x * indicator S x) \<in> borel_measurable lborel"
    using borel_measurable_ddir[OF cf] S by measurable
  show "AE x in lborel. norm (ddir f v x * indicator S x)
      \<le> norm ((\<bar>B\<bar> * norm v) * indicator S x)"
  proof (rule eventually_mono[OF AE_dlim_set[OF lip v]])
    fix x assume x: "x \<in> dlim_set f v"
    have "\<bar>ddir f v x\<bar> \<le> \<bar>B\<bar> * norm v"
    proof -
      have "\<bar>ddir f v x\<bar> \<le> B * norm v" using norm_ddir_le[OF lip x] by simp
      also have "\<dots> \<le> \<bar>B\<bar> * norm v" by (intro mult_right_mono) auto
      finally show ?thesis .
    qed
    hence "\<bar>ddir f v x\<bar> * \<bar>indicator S x :: real\<bar>
        \<le> (\<bar>B\<bar> * norm v) * \<bar>indicator S x :: real\<bar>"
      by (intro mult_right_mono) auto
    thus "norm (ddir f v x * indicator S x)
        \<le> norm ((\<bar>B\<bar> * norm v) * indicator S x)"
      by (simp add: abs_mult)
  qed
qed

text \<open>R3 COMPLETE: the direction map of a Lipschitz function is additive
  almost everywhere. Every box integral of the defect vanishes
  (`box_integral_ddir_add`), the defect is a.e. bounded, and boxes generate
  the Borel sets, so the defect itself vanishes a.e.\<close>

theorem ddir_add_AE:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes lip: "\<And>y z. norm (f y - f z) \<le> B * norm (y - z)"
    and u: "u \<noteq> 0" and v: "v \<noteq> 0" and uv: "u + v \<noteq> 0"
  shows "AE x in lborel. ddir f (u + v) x = ddir f u x + ddir f v x"
proof -
  have cf: "continuous_on UNIV f" by (rule lipschitz_continuous_on_UNIV[OF lip])
  define g where "g = (\<lambda>x. ddir f (u + v) x - ddir f v x - ddir f u x)"
  define M where "M = \<bar>B\<bar> * norm (u + v) + \<bar>B\<bar> * norm v + \<bar>B\<bar> * norm u"
  have gm: "g \<in> borel_measurable borel"
    unfolding g_def using borel_measurable_ddir[OF cf] by measurable
  have gb: "AE x in lborel. \<bar>g x\<bar> \<le> M"
  proof -
    have bnd: "\<bar>ddir f w x\<bar> \<le> \<bar>B\<bar> * norm w"
      if "w \<noteq> 0" "x \<in> dlim_set f w" for w x
    proof -
      have "\<bar>ddir f w x\<bar> \<le> B * norm w"
        using norm_ddir_le[OF lip that(2)] by simp
      also have "\<dots> \<le> \<bar>B\<bar> * norm w" by (intro mult_right_mono) auto
      finally show ?thesis .
    qed
    have "AE x in lborel. x \<in> dlim_set f (u + v) \<and> x \<in> dlim_set f v
        \<and> x \<in> dlim_set f u"
      using AE_dlim_set[OF lip uv] AE_dlim_set[OF lip v] AE_dlim_set[OF lip u]
      by eventually_elim auto
    thus ?thesis
    proof (rule eventually_mono)
      fix x assume mem: "x \<in> dlim_set f (u + v) \<and> x \<in> dlim_set f v
          \<and> x \<in> dlim_set f u"
      have b1: "\<bar>ddir f (u + v) x\<bar> \<le> \<bar>B\<bar> * norm (u + v)"
        using bnd[OF uv] mem by blast
      have b2: "\<bar>ddir f v x\<bar> \<le> \<bar>B\<bar> * norm v" using bnd[OF v] mem by blast
      have b3: "\<bar>ddir f u x\<bar> \<le> \<bar>B\<bar> * norm u" using bnd[OF u] mem by blast
      show "\<bar>g x\<bar> \<le> M" unfolding g_def M_def using b1 b2 b3 by linarith
    qed
  qed
  have box0: "(\<integral>\<^sup>+x. ennreal (g x) * indicator (box l r) x \<partial>lborel)
      = (\<integral>\<^sup>+x. ennreal (- g x) * indicator (box l r) x \<partial>lborel)" for l r
  proof -
    have Bfin: "emeasure lborel (box l r :: 'a set) < top"
      by (simp add: emeasure_lborel_box_eq)
    have Bsets: "(box l r :: 'a set) \<in> sets borel" by simp
    have ig: "integrable lborel (\<lambda>x. g x * indicator (box l r) x)"
    proof (rule Bochner_Integration.integrable_bound)
      show "integrable lborel (\<lambda>x. \<bar>M\<bar> * indicator (box l r) x :: real)"
        using Bsets Bfin by (intro integrable_mult_right) simp
      show "(\<lambda>x. g x * indicator (box l r) x) \<in> borel_measurable lborel"
        using gm Bsets by measurable
      show "AE x in lborel. norm (g x * indicator (box l r) x)
          \<le> norm (\<bar>M\<bar> * indicator (box l r) x)"
      proof (rule eventually_mono[OF gb])
        fix x assume "\<bar>g x\<bar> \<le> M"
        hence "\<bar>g x\<bar> * \<bar>indicator (box l r) x :: real\<bar>
            \<le> \<bar>M\<bar> * \<bar>indicator (box l r) x :: real\<bar>"
          by (intro mult_right_mono) auto
        thus "norm (g x * indicator (box l r) x)
            \<le> norm (\<bar>M\<bar> * indicator (box l r) x)"
          by (simp add: abs_mult)
      qed
    qed
    have zero: "(\<integral>x. g x * indicator (box l r) x \<partial>lborel) = 0"
    proof -
      have iuv: "integrable lborel
          (\<lambda>x. ddir f (u + v) x * indicator (box l r) x)"
        by (rule integrable_ddir_indicator[OF lip uv Bsets Bfin])
      have iv: "integrable lborel (\<lambda>x. ddir f v x * indicator (box l r) x)"
        by (rule integrable_ddir_indicator[OF lip v Bsets Bfin])
      have iu: "integrable lborel (\<lambda>x. ddir f u x * indicator (box l r) x)"
        by (rule integrable_ddir_indicator[OF lip u Bsets Bfin])
      have split: "(\<lambda>x. g x * indicator (box l r) x)
          = (\<lambda>x. ddir f (u + v) x * indicator (box l r) x
              - (ddir f v x * indicator (box l r) x
                + ddir f u x * indicator (box l r) x))"
        by (rule ext) (simp add: g_def algebra_simps)
      have "(\<integral>x. g x * indicator (box l r) x \<partial>lborel)
          = (\<integral>x. ddir f (u + v) x * indicator (box l r) x \<partial>lborel)
          - ((\<integral>x. ddir f v x * indicator (box l r) x \<partial>lborel)
            + (\<integral>x. ddir f u x * indicator (box l r) x \<partial>lborel))"
        unfolding split using iuv iv iu by simp
      moreover have "(\<integral>x. ddir f (u + v) x * indicator (box l r) x \<partial>lborel)
          = (\<integral>x. ddir f v x * indicator (box l r) x \<partial>lborel)
          + (\<integral>x. ddir f u x * indicator (box l r) x \<partial>lborel)"
        using box_integral_ddir_add[OF lip u v uv, of l r]
          integral_box_cbox_eq[OF borel_measurable_ddir[OF cf], of "u + v" l r]
          integral_box_cbox_eq[OF borel_measurable_ddir[OF cf], of v l r]
          integral_box_cbox_eq[OF borel_measurable_ddir[OF cf], of u l r]
        by simp
      ultimately show ?thesis by simp
    qed
    have base: "(\<integral>\<^sup>+x. ennreal (g x * indicator (box l r) x) \<partial>lborel)
        = (\<integral>\<^sup>+x. ennreal (- (g x * indicator (box l r) x)) \<partial>lborel)"
      by (rule nn_integral_pos_neg_eq_of_integral_zero[OF ig zero])
    have cvP: "(\<integral>\<^sup>+x. ennreal (g x * indicator (box l r) x) \<partial>lborel)
        = (\<integral>\<^sup>+x. ennreal (g x) * indicator (box l r) x \<partial>lborel)"
      by (intro nn_integral_cong) (simp add: indicator_def)
    have cvN: "(\<integral>\<^sup>+x. ennreal (- (g x * indicator (box l r) x)) \<partial>lborel)
        = (\<integral>\<^sup>+x. ennreal (- g x) * indicator (box l r) x \<partial>lborel)"
      by (intro nn_integral_cong) (simp add: indicator_def)
    show ?thesis using base cvP cvN by simp
  qed
  have "AE x in lborel. g x = 0"
    by (rule AE_zero_of_box_integrals_zero[OF gm gb box0])
  thus ?thesis by (auto simp: g_def)
qed

subsection \<open>Towards Rademacher: the candidate derivative\<close>

text \<open>The linear map that will serve as the derivative at a good point: the
  one determined by the directional derivatives along the (finitely many)
  basis vectors. It is bounded linear for any choice of coefficients, so this
  costs nothing; the work is in showing it AGREES with \<open>ddir\<close> on a dense set
  of directions, which is what a.e. additivity and homogeneity give.\<close>

lemma bounded_linear_coord_combination:
  fixes c :: "'a::euclidean_space \<Rightarrow> real"
  shows "bounded_linear (\<lambda>v. \<Sum>b\<in>Basis. (v \<bullet> b) * c b)"
proof
  fix v w :: 'a
  show "(\<Sum>b\<in>Basis. ((v + w) \<bullet> b) * c b)
      = (\<Sum>b\<in>Basis. (v \<bullet> b) * c b) + (\<Sum>b\<in>Basis. (w \<bullet> b) * c b)"
    by (simp add: algebra_simps sum.distrib)
next
  fix r :: real and v :: 'a
  show "(\<Sum>b\<in>Basis. ((r *\<^sub>R v) \<bullet> b) * c b)
      = r *\<^sub>R (\<Sum>b\<in>Basis. (v \<bullet> b) * c b)"
    by (simp add: sum_distrib_left algebra_simps)
next
  define K where "K = (\<Sum>b\<in>Basis. \<bar>c b\<bar>)"
  have "\<bar>\<Sum>b\<in>Basis. (v \<bullet> b) * c b\<bar> \<le> norm v * K" for v :: 'a
  proof -
    have "\<bar>\<Sum>b\<in>Basis. (v \<bullet> b) * c b\<bar> \<le> (\<Sum>b\<in>Basis. \<bar>(v \<bullet> b) * c b\<bar>)"
      by (rule sum_abs)
    also have "\<dots> = (\<Sum>b\<in>Basis. \<bar>v \<bullet> b\<bar> * \<bar>c b\<bar>)"
      by (simp add: abs_mult)
    also have "\<dots> \<le> (\<Sum>b\<in>Basis. norm v * \<bar>c b\<bar>)"
      by (intro sum_mono mult_right_mono) (auto simp: Basis_le_norm)
    also have "\<dots> = norm v * K" unfolding K_def by (simp add: sum_distrib_left)
    finally show ?thesis .
  qed
  thus "\<exists>K. \<forall>v :: 'a. norm (\<Sum>b\<in>Basis. (v \<bullet> b) * c b) \<le> norm v * K"
    by (intro exI[of _ K]) simp
qed

subsection \<open>A countable dense set of directions\<close>

text \<open>Rational combinations of the basis. Countable because the basis is
  finite and the rationals are countable; dense because \<open>norm_le_l1\<close> reduces
  the error to a finite sum of coordinate errors, each of which a rational can
  make as small as we like.\<close>

definition rat_dirs :: "'a::euclidean_space set"
  where "rat_dirs = (\<lambda>c. \<Sum>b\<in>Basis. c b *\<^sub>R b) ` (Basis \<rightarrow>\<^sub>E \<rat>)"

lemma countable_rat_dirs: "countable (rat_dirs :: 'a::euclidean_space set)"
  unfolding rat_dirs_def
  by (intro countable_image countable_PiE finite_Basis) (rule countable_rat)

lemma rat_dirs_dense:
  fixes v :: "'a::euclidean_space"
  assumes e: "0 < e"
  shows "\<exists>w\<in>rat_dirs. norm (v - w) < e"
proof -
  define n where "n = card (Basis :: 'a set)"
  have n: "0 < n" unfolding n_def by (simp add: card_gt_0_iff)
  define d where "d = e / (real n + 1)"
  have d: "0 < d" using e n by (simp add: d_def)
  have "\<forall>b\<in>Basis. \<exists>q\<in>\<rat>. \<bar>v \<bullet> b - q\<bar> < d"
  proof
    fix b :: 'a assume "b \<in> Basis"
    obtain q where q: "q \<in> \<rat>" and lt: "v \<bullet> b - d < q" "q < v \<bullet> b + d"
      using Rats_dense_in_real[of "v \<bullet> b - d" "v \<bullet> b + d"] d by force
    show "\<exists>q\<in>\<rat>. \<bar>v \<bullet> b - q\<bar> < d" using q lt by force
  qed
  hence bex: "\<forall>b\<in>Basis. \<exists>q. q \<in> \<rat> \<and> \<bar>v \<bullet> b - q\<bar> < d" by blast
  obtain c0 where c0all: "\<forall>b\<in>Basis. c0 b \<in> \<rat>
      \<and> \<bar>v \<bullet> b - c0 b\<bar> < d"
    using bchoice[OF bex] by blast
  have c0: "c0 b \<in> \<rat>" if "b \<in> Basis" for b using c0all that by blast
  have c0d: "\<bar>v \<bullet> b - c0 b\<bar> < d" if "b \<in> Basis" for b using c0all that by blast
  define c where "c = (\<lambda>b. if b \<in> Basis then c0 b else undefined)"
  have cPiE: "c \<in> (Basis \<rightarrow>\<^sub>E \<rat>)"
    unfolding c_def using c0 by (intro PiE_I) auto
  define w where "w = (\<Sum>b\<in>Basis. c b *\<^sub>R (b :: 'a))"
  have wmem: "w \<in> rat_dirs" unfolding w_def rat_dirs_def using cPiE by blast
  have wc: "w \<bullet> b = c b" if "b \<in> Basis" for b
    unfolding w_def by (rule inner_sum_scaleR_Basis[OF that])
  have "norm (v - w) \<le> (\<Sum>b\<in>Basis. \<bar>(v - w) \<bullet> b\<bar>)" by (rule norm_le_l1)
  also have "\<dots> = (\<Sum>b\<in>Basis. \<bar>v \<bullet> b - c b\<bar>)"
    by (rule sum.cong[OF refl]) (simp add: inner_diff_left wc)
  also have "\<dots> < (\<Sum>b\<in>(Basis :: 'a set). d)"
  proof (rule sum_strict_mono)
    show "finite (Basis :: 'a set)" by simp
    show "(Basis :: 'a set) \<noteq> {}" by simp
    fix b :: 'a assume b: "b \<in> Basis"
    show "\<bar>v \<bullet> b - c b\<bar> < d" using c0d[OF b] b by (simp add: c_def)
  qed
  also have "(\<Sum>b\<in>(Basis :: 'a set). d) = real n * d"
    unfolding n_def by simp
  also have "\<dots> < e" using e n by (simp add: d_def field_simps)
  finally show ?thesis using wmem by blast
qed

subsection \<open>All countably many conditions hold at almost every point\<close>

text \<open>`AE_ball_countable` turns the countably many separate a.e. statements
  \<comment> \<open>existence along each rational direction, additivity for each pair,
  homogeneity for each rational scalar\<close> into a single a.e. statement. This
  is the step that makes the pointwise argument of
  `differentiable_of_dense_linear_ddir` available at almost every point.\<close>

lemma AE_all_rat_dirs:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes lip: "\<And>y z. norm (f y - f z) \<le> B * norm (y - z)"
  shows "AE x in lborel. \<forall>w \<in> rat_dirs - {0}. x \<in> dlim_set f w"
proof -
  have V: "countable (rat_dirs - {0} :: 'a set)"
    using countable_rat_dirs by simp
  have all: "\<forall>w \<in> rat_dirs - {0}. AE x in lborel. x \<in> dlim_set f w"
    using AE_dlim_set[OF lip] by blast
  show ?thesis unfolding AE_ball_countable[OF V] by (rule all)
qed

lemma AE_add_rat_dirs:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes lip: "\<And>y z. norm (f y - f z) \<le> B * norm (y - z)"
  shows "AE x in lborel. \<forall>p \<in> (rat_dirs - {0}) \<times> (rat_dirs - {0}).
      fst p + snd p \<noteq> 0
      \<longrightarrow> ddir f (fst p + snd p) x = ddir f (fst p) x + ddir f (snd p) x"
proof -
  have V: "countable ((rat_dirs - {0}) \<times> (rat_dirs - {0}) :: ('a \<times> 'a) set)"
    using countable_rat_dirs by (intro countable_SIGMA) auto
  have all: "\<forall>p \<in> (rat_dirs - {0}) \<times> (rat_dirs - {0}).
      AE x in lborel. fst p + snd p \<noteq> 0
        \<longrightarrow> ddir f (fst p + snd p) x = ddir f (fst p) x + ddir f (snd p) x"
  proof
    fix p :: "'a \<times> 'a"
    assume p: "p \<in> (rat_dirs - {0}) \<times> (rat_dirs - {0})"
    have u: "fst p \<noteq> 0" and v: "snd p \<noteq> 0" using p by auto
    show "AE x in lborel. fst p + snd p \<noteq> 0
        \<longrightarrow> ddir f (fst p + snd p) x = ddir f (fst p) x + ddir f (snd p) x"
    proof (cases "fst p + snd p = 0")
      case True thus ?thesis by simp
    next
      case False
      have "AE x in lborel. ddir f (fst p + snd p) x
          = ddir f (fst p) x + ddir f (snd p) x"
        by (rule ddir_add_AE[OF lip u v False])
      thus ?thesis by (rule eventually_mono) simp
    qed
  qed
  show ?thesis unfolding AE_ball_countable[OF V] by (rule all)
qed

lemma AE_scale_rat_dirs:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes lip: "\<And>y z. norm (f y - f z) \<le> B * norm (y - z)"
  shows "AE x in lborel. \<forall>w \<in> rat_dirs - {0}. x \<in> dlim_set f w
      \<longrightarrow> (\<forall>c \<in> \<rat> - {0}. ddir f (c *\<^sub>R w) x = c *\<^sub>R ddir f w x)"
proof -
  have V: "countable (rat_dirs - {0} :: 'a set)"
    using countable_rat_dirs by simp
  have all: "\<forall>w \<in> rat_dirs - {0}. AE x in lborel. x \<in> dlim_set f w
      \<longrightarrow> (\<forall>c \<in> \<rat> - {0}. ddir f (c *\<^sub>R w) x = c *\<^sub>R ddir f w x)"
  proof
    fix w :: 'a assume w: "w \<in> rat_dirs - {0}"
    have ae: "AE x in lborel. x \<in> dlim_set f w"
      using AE_dlim_set[OF lip] w by blast
    show "AE x in lborel. x \<in> dlim_set f w
        \<longrightarrow> (\<forall>c \<in> \<rat> - {0}. ddir f (c *\<^sub>R w) x = c *\<^sub>R ddir f w x)"
    proof (rule eventually_mono[OF ae])
      fix x assume x: "x \<in> dlim_set f w"
      show "x \<in> dlim_set f w
          \<longrightarrow> (\<forall>c \<in> \<rat> - {0}. ddir f (c *\<^sub>R w) x = c *\<^sub>R ddir f w x)"
      proof (intro impI ballI)
        fix c :: real assume c: "c \<in> \<rat> - {0}"
        show "ddir f (c *\<^sub>R w) x = c *\<^sub>R ddir f w x"
          by (rule ddir_scale(2)[OF x]) (use c in auto)
      qed
    qed
  qed
  show ?thesis unfolding AE_ball_countable[OF V] by (rule all)
qed

subsection \<open>Coordinates of partial basis combinations\<close>

text \<open>The bookkeeping the final induction needs: a partial combination of
  basis vectors has the expected coordinates, and therefore vanishes only if
  all its coefficients do. The latter is what guarantees that the partial sums
  in the induction stay NONZERO once zero coefficients are skipped \<comment> \<open>which
  matters because additivity of \<open>ddir\<close> is only available for nonzero
  directions\<close>.\<close>

lemma inner_sum_scaleR_subset:
  fixes j :: "'a::euclidean_space"
  assumes S: "S \<subseteq> Basis" and j: "j \<in> S"
  shows "(\<Sum>b\<in>S. c b *\<^sub>R b) \<bullet> j = c j"
proof -
  have fin: "finite S" using S finite_Basis by (rule finite_subset)
  have "(\<Sum>b\<in>S. c b *\<^sub>R b) \<bullet> j = (\<Sum>b\<in>S. c b * (b \<bullet> j))"
    by (simp add: inner_sum_left)
  also have "\<dots> = (\<Sum>b\<in>S. if b = j then c b else 0)"
  proof (rule sum.cong[OF refl])
    fix b assume b: "b \<in> S"
    have "b \<in> Basis" using b S by blast
    moreover have "j \<in> Basis" using j S by blast
    ultimately show "c b * (b \<bullet> j) = (if b = j then c b else 0)"
      by (auto simp: inner_Basis)
  qed
  also have "\<dots> = c j" using fin j by simp
  finally show ?thesis .
qed

lemma coeffs_zero_of_sum_zero:
  fixes j :: "'a::euclidean_space"
  assumes S: "S \<subseteq> Basis" and z: "(\<Sum>b\<in>S. c b *\<^sub>R b) = 0" and j: "j \<in> S"
  shows "c j = 0"
proof -
  have "c j = (\<Sum>b\<in>S. c b *\<^sub>R b) \<bullet> j"
    by (rule inner_sum_scaleR_subset[OF S j, symmetric])
  also have "\<dots> = 0" unfolding z by simp
  finally show ?thesis .
qed

subsection \<open>Membership facts for the rational directions\<close>

text \<open>The induction over the basis needs its partial sums to be legitimate
  rational directions, and needs the basis vectors themselves to be among
  them. Both come from exhibiting the coefficient function explicitly and
  extending it by zero outside the index set.\<close>

lemma partial_rat_dir_mem:
  fixes c :: "'a::euclidean_space \<Rightarrow> real"
  assumes c: "c \<in> Basis \<rightarrow>\<^sub>E \<rat>" and S: "S \<subseteq> Basis"
  shows "(\<Sum>b\<in>S. c b *\<^sub>R b) \<in> rat_dirs"
proof -
  define c' where "c' = (\<lambda>b :: 'a. if b \<in> Basis
      then (if b \<in> S then c b else (0::real)) else undefined)"
  have c'PiE: "c' \<in> Basis \<rightarrow>\<^sub>E \<rat>"
    unfolding c'_def using c by (intro PiE_I) auto
  have eq: "(\<Sum>b\<in>Basis. c' b *\<^sub>R b) = (\<Sum>b\<in>S. c b *\<^sub>R b)"
    by (rule sum.mono_neutral_cong_right[OF finite_Basis S])
      (use S in \<open>auto simp: c'_def\<close>)
  show ?thesis unfolding rat_dirs_def
    by (rule image_eqI[OF _ c'PiE]) (use eq in simp)
qed

lemma Basis_subset_rat_dirs:
  fixes b :: "'a::euclidean_space"
  assumes b: "b \<in> Basis"
  shows "b \<in> rat_dirs"
proof -
  define c where "c = (\<lambda>b' :: 'a. if b' \<in> Basis
      then (if b' = b then (1::real) else 0) else undefined)"
  have cPiE: "c \<in> Basis \<rightarrow>\<^sub>E \<rat>" unfolding c_def by (intro PiE_I) auto
  have "(\<Sum>b'\<in>Basis. c b' *\<^sub>R b') = (\<Sum>b'\<in>Basis. if b' = b then b' else 0)"
    by (rule sum.cong[OF refl]) (simp add: c_def)
  also have "\<dots> = b" using b by simp
  finally have eq: "(\<Sum>b'\<in>Basis. c b' *\<^sub>R b') = b" .
  show ?thesis unfolding rat_dirs_def
    by (rule image_eqI[OF _ cPiE]) (use eq in simp)
qed

subsection \<open>The direction map is linear at a good point\<close>

text \<open>The induction that turns pairwise additivity and homogeneity into the
  full coordinate formula. Zero coefficients are skipped so that every partial
  sum stays nonzero \<comment> \<open>legitimate by `coeffs_zero_of_sum_zero`\<close>, which is
  what keeps the additivity hypothesis applicable.\<close>

lemma ddir_rat_dir_sum:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes gd: "\<forall>w \<in> rat_dirs - {0}. x \<in> dlim_set f w"
    and gadd: "\<forall>p \<in> (rat_dirs - {0}) \<times> (rat_dirs - {0}).
        fst p + snd p \<noteq> 0
        \<longrightarrow> ddir f (fst p + snd p) x = ddir f (fst p) x + ddir f (snd p) x"
    and gsc: "\<forall>w \<in> rat_dirs - {0}. x \<in> dlim_set f w
        \<longrightarrow> (\<forall>q \<in> \<rat> - {0}. ddir f (q *\<^sub>R w) x = q *\<^sub>R ddir f w x)"
    and c: "c \<in> Basis \<rightarrow>\<^sub>E \<rat>"
    and S: "finite S" "S \<subseteq> Basis"
  shows "(\<Sum>b\<in>S. c b *\<^sub>R b) \<noteq> 0
      \<longrightarrow> ddir f (\<Sum>b\<in>S. c b *\<^sub>R b) x = (\<Sum>b\<in>S. c b * ddir f b x)"
  using S
proof (induct S)
  case empty thus ?case by simp
next
  case (insert b0 S')
  have sub: "insert b0 S' \<subseteq> Basis" by (rule insert.prems)
  have b0B: "b0 \<in> Basis" and S'B: "S' \<subseteq> Basis" using sub by auto
  have IH: "(\<Sum>b\<in>S'. c b *\<^sub>R b) \<noteq> 0
      \<longrightarrow> ddir f (\<Sum>b\<in>S'. c b *\<^sub>R b) x = (\<Sum>b\<in>S'. c b * ddir f b x)"
    by (rule insert.hyps(3)[OF S'B])
  have Wsplit: "(\<Sum>b\<in>insert b0 S'. c b *\<^sub>R b)
      = c b0 *\<^sub>R b0 + (\<Sum>b\<in>S'. c b *\<^sub>R b)"
    using insert.hyps(1,2) by simp
  have Ssplit: "(\<Sum>b\<in>insert b0 S'. c b * ddir f b x)
      = c b0 * ddir f b0 x + (\<Sum>b\<in>S'. c b * ddir f b x)"
    using insert.hyps(1,2) by simp
  have cQ: "c b0 \<in> \<rat>" using c b0B by blast
  have b0mem: "b0 \<in> rat_dirs - {0}"
    using Basis_subset_rat_dirs[OF b0B] b0B by (auto simp: nonzero_Basis)
  have hom: "ddir f (c b0 *\<^sub>R b0) x = c b0 * ddir f b0 x" if q: "c b0 \<noteq> 0"
  proof -
    have "x \<in> dlim_set f b0" using gd b0mem by blast
    hence "\<forall>q \<in> \<rat> - {0}. ddir f (q *\<^sub>R b0) x = q *\<^sub>R ddir f b0 x"
      using gsc b0mem by blast
    thus ?thesis using cQ q by simp
  qed
  have scmem: "c b0 *\<^sub>R b0 \<in> rat_dirs"
  proof -
    have "(\<Sum>b\<in>{b0}. c b *\<^sub>R b) \<in> rat_dirs"
      by (rule partial_rat_dir_mem[OF c]) (use b0B in simp)
    thus ?thesis by simp
  qed
  have W'mem: "(\<Sum>b\<in>S'. c b *\<^sub>R b) \<in> rat_dirs"
    by (rule partial_rat_dir_mem[OF c S'B])
  show ?case
  proof (intro impI)
    assume Wne: "(\<Sum>b\<in>insert b0 S'. c b *\<^sub>R b) \<noteq> 0"
    show "ddir f (\<Sum>b\<in>insert b0 S'. c b *\<^sub>R b) x
        = (\<Sum>b\<in>insert b0 S'. c b * ddir f b x)"
    proof (cases "c b0 = 0")
      case True
      have W'ne: "(\<Sum>b\<in>S'. c b *\<^sub>R b) \<noteq> 0" using Wne Wsplit True by simp
      have "ddir f (\<Sum>b\<in>insert b0 S'. c b *\<^sub>R b) x
          = ddir f (\<Sum>b\<in>S'. c b *\<^sub>R b) x"
        using Wsplit True by simp
      also have "\<dots> = (\<Sum>b\<in>S'. c b * ddir f b x)" using IH W'ne by simp
      finally show ?thesis using Ssplit True by simp
    next
      case False
      show ?thesis
      proof (cases "(\<Sum>b\<in>S'. c b *\<^sub>R b) = 0")
        case True
        have zsum: "(\<Sum>b\<in>S'. c b * ddir f b x) = 0"
        proof (rule sum.neutral, rule ballI)
          fix b assume b: "b \<in> S'"
          have "c b = 0" by (rule coeffs_zero_of_sum_zero[OF S'B True b])
          thus "c b * ddir f b x = 0" by simp
        qed
        have "ddir f (\<Sum>b\<in>insert b0 S'. c b *\<^sub>R b) x
            = ddir f (c b0 *\<^sub>R b0) x" using Wsplit True by simp
        also have "\<dots> = c b0 * ddir f b0 x" by (rule hom[OF False])
        finally show ?thesis using Ssplit zsum by simp
      next
        case False
        have p: "(c b0 *\<^sub>R b0, (\<Sum>b\<in>S'. c b *\<^sub>R b))
            \<in> (rat_dirs - {0}) \<times> (rat_dirs - {0})"
          using scmem W'mem False \<open>c b0 \<noteq> 0\<close> b0mem by auto
        have "ddir f (c b0 *\<^sub>R b0 + (\<Sum>b\<in>S'. c b *\<^sub>R b)) x
            = ddir f (c b0 *\<^sub>R b0) x + ddir f (\<Sum>b\<in>S'. c b *\<^sub>R b) x"
          using gadd p Wne Wsplit by auto
        also have "ddir f (c b0 *\<^sub>R b0) x = c b0 * ddir f b0 x"
          by (rule hom[OF \<open>c b0 \<noteq> 0\<close>])
        also have "ddir f (\<Sum>b\<in>S'. c b *\<^sub>R b) x
            = (\<Sum>b\<in>S'. c b * ddir f b x)" using IH False by simp
        finally show ?thesis using Wsplit Ssplit by simp
      qed
    qed
  qed
qed

subsection \<open>Rademacher's theorem\<close>

text \<open>Everything assembled: a Lipschitz function on a Euclidean space is
  differentiable almost everywhere. At almost every point the directional
  derivatives exist along all rational directions and depend linearly on the
  direction there; that linear dependence extends to all directions by
  density and the uniform Lipschitz control, which is exactly Fr\'echet
  differentiability.\<close>

theorem rademacher_AE:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes lip: "\<And>y z. norm (f y - f z) \<le> B * norm (y - z)"
  shows "AE x in lborel. f differentiable (at x)"
proof -
  have lipA: "norm (f y - f z) \<le> \<bar>B\<bar> * norm (y - z)" for y z
  proof -
    have "B * norm (y - z) \<le> \<bar>B\<bar> * norm (y - z)"
      by (intro mult_right_mono) auto
    thus ?thesis using lip[of y z] by linarith
  qed
  have "AE x in lborel. (\<forall>w \<in> rat_dirs - {0}. x \<in> dlim_set f w)
      \<and> (\<forall>p \<in> (rat_dirs - {0}) \<times> (rat_dirs - {0}). fst p + snd p \<noteq> 0
          \<longrightarrow> ddir f (fst p + snd p) x
              = ddir f (fst p) x + ddir f (snd p) x)
      \<and> (\<forall>w \<in> rat_dirs - {0}. x \<in> dlim_set f w
          \<longrightarrow> (\<forall>q \<in> \<rat> - {0}. ddir f (q *\<^sub>R w) x = q *\<^sub>R ddir f w x))"
    using AE_all_rat_dirs[OF lip] AE_add_rat_dirs[OF lip] AE_scale_rat_dirs[OF lip]
    by eventually_elim blast
  thus ?thesis
  proof (rule eventually_mono)
    fix x :: 'a
    assume good: "(\<forall>w \<in> rat_dirs - {0}. x \<in> dlim_set f w)
      \<and> (\<forall>p \<in> (rat_dirs - {0}) \<times> (rat_dirs - {0}). fst p + snd p \<noteq> 0
          \<longrightarrow> ddir f (fst p + snd p) x
              = ddir f (fst p) x + ddir f (snd p) x)
      \<and> (\<forall>w \<in> rat_dirs - {0}. x \<in> dlim_set f w
          \<longrightarrow> (\<forall>q \<in> \<rat> - {0}. ddir f (q *\<^sub>R w) x = q *\<^sub>R ddir f w x))"
    have gd: "\<forall>w \<in> rat_dirs - {0}. x \<in> dlim_set f w" using good by blast
    have gadd: "\<forall>p \<in> (rat_dirs - {0}) \<times> (rat_dirs - {0}). fst p + snd p \<noteq> 0
        \<longrightarrow> ddir f (fst p + snd p) x
            = ddir f (fst p) x + ddir f (snd p) x" using good by blast
    have gsc: "\<forall>w \<in> rat_dirs - {0}. x \<in> dlim_set f w
        \<longrightarrow> (\<forall>q \<in> \<rat> - {0}. ddir f (q *\<^sub>R w) x = q *\<^sub>R ddir f w x)"
      using good by blast
    define T where "T = (\<lambda>v :: 'a. \<Sum>b\<in>Basis. (v \<bullet> b) * ddir f b x)"
    have Tlin: "bounded_linear T"
      unfolding T_def by (rule bounded_linear_coord_combination)
    have der: "((\<lambda>t. dquot f w x t) \<longlongrightarrow> T w) (at 0)"
      if w: "w \<in> rat_dirs" for w
    proof (cases "w = 0")
      case True
      have q0: "dquot f w x t = 0" for t
        unfolding dquot_def True by simp
      have "T w = 0" unfolding T_def True by simp
      thus ?thesis using q0 by simp
    next
      case False
      obtain c where c: "c \<in> Basis \<rightarrow>\<^sub>E \<rat>"
        and weq: "w = (\<Sum>b\<in>Basis. c b *\<^sub>R b)"
        using w unfolding rat_dirs_def by blast
      have coord: "w \<bullet> b = c b" if "b \<in> Basis" for b
        unfolding weq by (rule inner_sum_scaleR_Basis[OF that])
      have ne: "(\<Sum>b\<in>Basis. c b *\<^sub>R b) \<noteq> 0" using False weq by simp
      have "ddir f w x = (\<Sum>b\<in>Basis. c b * ddir f b x)"
        using ddir_rat_dir_sum[OF gd gadd gsc c finite_Basis subset_refl] ne weq
        by simp
      also have "\<dots> = T w"
        unfolding T_def by (rule sum.cong[OF refl]) (simp add: coord)
      finally have Teq: "ddir f w x = T w" .
      have "x \<in> dlim_set f w" using gd w False by blast
      from ddir_tendsto[OF this] show ?thesis unfolding Teq .
    qed
    have "(f has_derivative T) (at x)"
      by (rule differentiable_of_dense_linear_ddir[OF lipA _ Tlin _ der])
        (use rat_dirs_dense in auto)
    thus "f differentiable (at x)" unfolding differentiable_def by blast
  qed
qed

subsection \<open>Rademacher for vector-valued maps\<close>

text \<open>E3d begins here. Alexandrov's theorem will be obtained by
  differentiating the RESOLVENT, which is a map \<open>\<real>\<^sup>n \<rightarrow> \<real>\<^sup>n\<close>, so Rademacher is
  first lifted from real-valued functions to vector-valued ones: each
  component is Lipschitz with the same constant, and finitely many
  a.e. statements combine.\<close>

lemma lipschitz_component:
  fixes F :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes lip: "\<And>y z. norm (F y - F z) \<le> B * norm (y - z)" and b: "b \<in> Basis"
  shows "norm ((F y \<bullet> b) - (F z \<bullet> b)) \<le> B * norm (y - z)"
proof -
  have "\<bar>(F y \<bullet> b) - (F z \<bullet> b)\<bar> = \<bar>(F y - F z) \<bullet> b\<bar>"
    by (simp add: inner_diff_left)
  also have "\<dots> \<le> norm (F y - F z) * norm b"
    by (rule Cauchy_Schwarz_ineq2)
  also have "\<dots> = norm (F y - F z)" using norm_Basis[OF b] by simp
  finally show ?thesis using lip[of y z] by simp
qed

theorem rademacher_vec_AE:
  fixes F :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes lip: "\<And>y z. norm (F y - F z) \<le> B * norm (y - z)"
  shows "AE x in lborel. F differentiable (at x)"
proof -
  have comp: "AE x in lborel. \<forall>b \<in> (Basis :: 'b set).
      (\<lambda>y. F y \<bullet> b) differentiable (at x)"
  proof -
    have C: "countable (Basis :: 'b set)"
      using finite_Basis by (rule countable_finite)
    have "\<forall>b \<in> (Basis :: 'b set).
        AE x in lborel. (\<lambda>y. F y \<bullet> b) differentiable (at x)"
    proof
      fix b :: 'b assume b: "b \<in> Basis"
      show "AE x in lborel. (\<lambda>y. F y \<bullet> b) differentiable (at x)"
        by (rule rademacher_AE[where B = B]) (rule lipschitz_component[OF lip b])
    qed
    thus ?thesis unfolding AE_ball_countable[OF C] .
  qed
  show ?thesis
  proof (rule eventually_mono[OF comp])
    fix x :: 'a
    assume all: "\<forall>b \<in> (Basis :: 'b set). (\<lambda>y. F y \<bullet> b) differentiable (at x)"
    have "(\<lambda>y. \<Sum>b\<in>(Basis :: 'b set). (F y \<bullet> b) *\<^sub>R b) differentiable (at x)"
      using all by (intro differentiable_sum differentiable_scaleR) auto
    moreover have "(\<lambda>y. \<Sum>b\<in>(Basis :: 'b set). (F y \<bullet> b) *\<^sub>R b) = F"
      by (rule ext) (simp add: euclidean_representation)
    ultimately show "F differentiable (at x)" by simp
  qed
qed

subsection \<open>The resolvent is differentiable almost everywhere\<close>

text \<open>The first genuinely Alexandrov-directed consequence: since the proximal
  map of a finite convex function is 1-Lipschitz on ALL of the space
  (`prox_nonexpansive`), Rademacher applies to it verbatim. Differentiability
  of the resolvent is the substitute for second-order differentiability of the
  convex function itself \<comment> \<open>Minty's device\<close>, and \<open>prox_subdiff\<close> is the bridge
  back: \<open>x - prox f x\<close> is a subgradient at \<open>prox f x\<close>.\<close>

lemma prox_lipschitz:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "norm (prox f y - prox f z) \<le> 1 * norm (y - z)"
proof -
  have "dist (prox f y) (prox f z) \<le> dist y z"
    by (rule prox_nonexpansive[OF cvx])
  thus ?thesis by (simp add: dist_norm)
qed

theorem prox_differentiable_AE:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "AE x in lborel. (prox f) differentiable (at x)"
  by (rule rademacher_vec_AE[where B = 1]) (rule prox_lipschitz[OF cvx])

text \<open>Together with `minty_surjective` this says: the resolvent of the
  subdifferential is a globally defined, surjective, 1-Lipschitz map that is
  differentiable almost everywhere. Alexandrov's theorem follows by
  transporting that derivative back through \<open>prox_subdiff\<close>; the remaining work
  is the symmetry and positivity of the transported derivative and the
  second-order expansion it produces.\<close>

subsection \<open>Firm nonexpansiveness and the derivative of the resolvent\<close>

text \<open>Monotonicity of the subdifferential says more about the resolvent than
  1-Lipschitzness: it is FIRMLY nonexpansive,
  \<open>|R x - R y|\<^sup>2 \<le> (x - y) \<cdot> (R x - R y)\<close>. Differentiating this inequality along
  a line is what makes the derivative of the resolvent positive semidefinite
  with norm at most one \<comment> \<open>the matrix structure Alexandrov's theorem needs\<close>.\<close>

lemma prox_firm_nonexpansive:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "(norm (prox f x - prox f y))\<^sup>2 \<le> (x - y) \<bullet> (prox f x - prox f y)"
proof -
  have s1: "x - prox f x \<in> subdiff f (prox f x)" by (rule prox_subdiff[OF cvx])
  have s2: "y - prox f y \<in> subdiff f (prox f y)" by (rule prox_subdiff[OF cvx])
  have mono: "0 \<le> ((x - prox f x) - (y - prox f y)) \<bullet> (prox f x - prox f y)"
    by (rule subdiff_monotone[OF s1 s2])
  show ?thesis
    using mono by (simp add: power2_norm_eq_inner inner_commute algebra_simps)
qed

lemma has_derivative_dir_limit:
  fixes F :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes D: "(F has_derivative D) (at x)"
  shows "((\<lambda>t. (F (x + t *\<^sub>R h) - F x) /\<^sub>R t) \<longlongrightarrow> D h) (at (0::real))"
proof (cases "h = 0")
  case True
  have lin: "bounded_linear D" by (rule has_derivative_bounded_linear[OF D])
  have "D 0 = 0" using lin by (simp add: linear_simps(3))
  thus ?thesis unfolding True by simp
next
  case False
  have lin: "bounded_linear D" by (rule has_derivative_bounded_linear[OF D])
  have Dlin: "linear D" using lin unfolding bounded_linear_def by simp
  have Dsc: "D (t *\<^sub>R h) = t *\<^sub>R D h" for t
    using Dlin unfolding linear_iff by simp
  have lim0: "((\<lambda>u. norm (F (x + u) - F x - D u) / norm u) \<longlongrightarrow> 0) (at 0)"
    using D unfolding has_derivative_at by blast
  have flim: "filterlim (\<lambda>t::real. t *\<^sub>R h) (at 0) (at 0)"
    unfolding filterlim_at
  proof (intro conjI)
    have "((\<lambda>t::real. t *\<^sub>R h) \<longlongrightarrow> 0 *\<^sub>R h) (at 0)" by (intro tendsto_intros)
    thus "((\<lambda>t::real. t *\<^sub>R h) \<longlongrightarrow> 0) (at 0)" by simp
    have "eventually (\<lambda>t::real. t \<noteq> 0) (at 0)"
      unfolding eventually_at by (intro exI[of _ 1]) auto
    thus "eventually (\<lambda>t::real. t *\<^sub>R h \<in> UNIV \<and> t *\<^sub>R h \<noteq> 0) (at 0)"
      by (rule eventually_mono) (use False in simp)
  qed
  have comp: "((\<lambda>t. norm (F (x + t *\<^sub>R h) - F x - D (t *\<^sub>R h))
      / norm (t *\<^sub>R h)) \<longlongrightarrow> 0) (at (0::real))"
    by (rule filterlim_compose[OF lim0 flim])
  have scaled: "((\<lambda>t. (norm (F (x + t *\<^sub>R h) - F x - D (t *\<^sub>R h))
      / norm (t *\<^sub>R h)) * norm h) \<longlongrightarrow> 0 * norm h) (at (0::real))"
    by (intro tendsto_mult comp tendsto_const)
  have ev: "eventually (\<lambda>t. norm ((F (x + t *\<^sub>R h) - F x) /\<^sub>R t - D h)
      = (norm (F (x + t *\<^sub>R h) - F x - D (t *\<^sub>R h)) / norm (t *\<^sub>R h)) * norm h)
      (at (0::real))"
  proof -
    have "eventually (\<lambda>t::real. t \<noteq> 0) (at 0)"
      unfolding eventually_at by (intro exI[of _ 1]) auto
    thus ?thesis
    proof (eventually_elim)
      case (elim t)
      hence t: "t \<noteq> 0" .
      have "(F (x + t *\<^sub>R h) - F x) /\<^sub>R t - D h
          = (F (x + t *\<^sub>R h) - F x - D (t *\<^sub>R h)) /\<^sub>R t"
        using t by (simp add: Dsc scaleR_diff_right)
      hence "norm ((F (x + t *\<^sub>R h) - F x) /\<^sub>R t - D h)
          = norm (F (x + t *\<^sub>R h) - F x - D (t *\<^sub>R h)) / \<bar>t\<bar>"
        by (simp add: divide_inverse mult.commute)
      also have "\<dots> = (norm (F (x + t *\<^sub>R h) - F x - D (t *\<^sub>R h))
          / norm (t *\<^sub>R h)) * norm h"
        using t False by (simp add: field_simps)
      finally show ?case .
    qed
  qed
  have ev': "eventually (\<lambda>t. (norm (F (x + t *\<^sub>R h) - F x - D (t *\<^sub>R h))
      / norm (t *\<^sub>R h)) * norm h
      = norm ((F (x + t *\<^sub>R h) - F x) /\<^sub>R t - D h)) (at (0::real))"
    using ev by (rule eventually_mono) simp
  have "((\<lambda>t. norm ((F (x + t *\<^sub>R h) - F x) /\<^sub>R t - D h))
      \<longlongrightarrow> 0) (at (0::real))"
    using scaled ev' by (simp add: Lim_transform_eventually)
  hence "((\<lambda>t. (F (x + t *\<^sub>R h) - F x) /\<^sub>R t - D h) \<longlongrightarrow> 0) (at 0)"
    by (simp add: tendsto_norm_zero_iff)
  thus ?thesis by (simp add: Lim_null[symmetric])
qed

text \<open>Differentiating firm nonexpansiveness along a line: wherever the
  resolvent is differentiable, its derivative \<open>DR\<close> satisfies
  \<open>|DR h|\<^sup>2 \<le> h \<cdot> DR h\<close>. In particular \<open>DR\<close> is positive semidefinite and
  \<open>\<parallel>DR\<parallel> \<le> 1\<close> \<comment> \<open>equivalently \<open>I - DR\<close> is positive semidefinite as well\<close>.
  This is the matrix inequality that carries Alexandrov's theorem.\<close>

theorem prox_deriv_psd:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
    and D: "(prox f has_derivative D) (at x)"
  shows "(norm (D h))\<^sup>2 \<le> h \<bullet> D h"
proof -
  define q where "q = (\<lambda>t. (prox f (x + t *\<^sub>R h) - prox f x) /\<^sub>R t)"
  have qlim: "(q \<longlongrightarrow> D h) (at (0::real))"
    unfolding q_def by (rule has_derivative_dir_limit[OF D])
  have est: "(norm (q t))\<^sup>2 \<le> h \<bullet> q t" if t: "0 < t" for t
  proof -
    have firm: "(norm (prox f (x + t *\<^sub>R h) - prox f x))\<^sup>2
        \<le> ((x + t *\<^sub>R h) - x) \<bullet> (prox f (x + t *\<^sub>R h) - prox f x)"
      by (rule prox_firm_nonexpansive[OF cvx])
    have qeq: "q t = (1/t) *\<^sub>R (prox f (x + t *\<^sub>R h) - prox f x)"
      unfolding q_def by (simp add: divide_inverse)
    have lhs: "(norm (q t))\<^sup>2
        = (norm (prox f (x + t *\<^sub>R h) - prox f x))\<^sup>2 / t\<^sup>2"
      unfolding qeq using t
      by (simp add: power_divide power_mult_distrib power_inverse divide_inverse)
    have rhs: "h \<bullet> q t
        = (((x + t *\<^sub>R h) - x) \<bullet> (prox f (x + t *\<^sub>R h) - prox f x)) / t\<^sup>2"
    proof -
      have "h \<bullet> q t = (1/t) * (h \<bullet> (prox f (x + t *\<^sub>R h) - prox f x))"
        unfolding qeq by simp
      moreover have "((x + t *\<^sub>R h) - x) \<bullet> (prox f (x + t *\<^sub>R h) - prox f x)
          = t * (h \<bullet> (prox f (x + t *\<^sub>R h) - prox f x))" by simp
      ultimately show ?thesis using t by (simp add: power2_eq_square)
    qed
    show ?thesis unfolding lhs rhs
      using firm t by (intro divide_right_mono) auto
  qed
  have ev: "eventually (\<lambda>t. (norm (q t))\<^sup>2 \<le> h \<bullet> q t) (at_right (0::real))"
    unfolding eventually_at_right_field
    by (intro exI[of _ 1]) (use est in auto)
  have l1: "((\<lambda>t. (norm (q t))\<^sup>2) \<longlongrightarrow> (norm (D h))\<^sup>2)
      (at_right (0::real))"
    by (intro tendsto_intros tendsto_norm filterlim_mono[OF qlim])
      (auto simp: at_le)
  have l2: "((\<lambda>t. h \<bullet> q t) \<longlongrightarrow> h \<bullet> D h) (at_right (0::real))"
    by (intro tendsto_inner tendsto_const filterlim_mono[OF qlim])
      (auto simp: at_le)
  show ?thesis
    by (rule tendsto_le[OF _ l2 l1]) (use ev in auto)
qed

subsection \<open>The Moreau envelope and its gradient\<close>

text \<open>The envelope \<open>e f x = min\<^sub>y (f y + |x - y|\<^sup>2/2)\<close> is differentiable
  everywhere with gradient \<open>x - prox f x\<close>, and the error in that expansion is
  QUADRATIC, so the envelope is \<open>C\<^sup>1\<close> with a 1-Lipschitz gradient. Both
  inequalities come from testing the minimum against the other point's
  minimiser. This identifies the resolvent as \<open>id\<close> minus a gradient field,
  which is what will make its derivative symmetric.\<close>

definition moreau :: "('a::euclidean_space \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> real"
  where "moreau f x = f (prox f x) + (dist x (prox f x))\<^sup>2 / 2"

lemma moreau_le:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "moreau f x \<le> f z + (dist x z)\<^sup>2 / 2"
  unfolding moreau_def by (rule prox_min[OF cvx])

lemma moreau_upper:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "moreau f (x + h) \<le> moreau f x + h \<bullet> (x - prox f x) + (norm h)\<^sup>2 / 2"
proof -
  have "moreau f (x + h) \<le> f (prox f x) + (dist (x + h) (prox f x))\<^sup>2 / 2"
    by (rule moreau_le[OF cvx])
  moreover have "(dist (x + h) (prox f x))\<^sup>2
      = (dist x (prox f x))\<^sup>2 + 2 * (h \<bullet> (x - prox f x)) + (norm h)\<^sup>2"
    unfolding dist_norm power2_norm_eq_inner
    by (simp add: algebra_simps inner_commute)
  ultimately show ?thesis unfolding moreau_def by linarith
qed

lemma moreau_lower:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "moreau f x \<le> moreau f (x + h) - h \<bullet> (x + h - prox f (x + h))
      + (norm h)\<^sup>2 / 2"
proof -
  have "moreau f x \<le> f (prox f (x + h)) + (dist x (prox f (x + h)))\<^sup>2 / 2"
    by (rule moreau_le[OF cvx])
  moreover have "(dist x (prox f (x + h)))\<^sup>2
      = (dist (x + h) (prox f (x + h)))\<^sup>2
        - 2 * (h \<bullet> (x + h - prox f (x + h))) + (norm h)\<^sup>2"
    unfolding dist_norm power2_norm_eq_inner
    by (simp add: algebra_simps inner_commute)
  ultimately show ?thesis unfolding moreau_def by linarith
qed

theorem moreau_has_derivative:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "(moreau f has_derivative (\<lambda>h. h \<bullet> (x - prox f x))) (at x)"
  unfolding has_derivative_at
proof (intro conjI)
  show "bounded_linear (\<lambda>h. h \<bullet> (x - prox f x))"
    by (rule bounded_linear_inner_left)
  have quad: "norm (moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x))
      \<le> (5/2) * (norm h)\<^sup>2" for h
  proof -
    have up: "moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x)
        \<le> (norm h)\<^sup>2 / 2"
      using moreau_upper[OF cvx, of x h] by simp
    have "moreau f x \<le> moreau f (x + h) - h \<bullet> (x + h - prox f (x + h))
        + (norm h)\<^sup>2 / 2"
      by (rule moreau_lower[OF cvx])
    hence lo0: "moreau f (x + h) - moreau f x
        \<ge> h \<bullet> (x + h - prox f (x + h)) - (norm h)\<^sup>2 / 2" by simp
    have split: "h \<bullet> (x + h - prox f (x + h))
        = h \<bullet> (x - prox f x) + h \<bullet> (h + prox f x - prox f (x + h))"
      by (simp add: algebra_simps)
    have bnd: "\<bar>h \<bullet> (h + prox f x - prox f (x + h))\<bar>
        \<le> 2 * (norm h)\<^sup>2"
    proof -
      have assoc: "h + prox f x - prox f (x + h)
          = h + (prox f x - prox f (x + h))" by simp
      have "norm (h + prox f x - prox f (x + h))
          \<le> norm h + norm (prox f x - prox f (x + h))"
        unfolding assoc by (rule norm_triangle_ineq)
      moreover have "norm (prox f x - prox f (x + h)) \<le> norm h"
        using prox_lipschitz[OF cvx, of x "x + h"] by simp
      ultimately have "norm (h + prox f x - prox f (x + h)) \<le> 2 * norm h"
        by linarith
      hence "\<bar>h \<bullet> (h + prox f x - prox f (x + h))\<bar>
          \<le> norm h * (2 * norm h)"
        using Cauchy_Schwarz_ineq2[of h "h + prox f x - prox f (x + h)"]
        by (smt (verit) mult_left_mono norm_ge_zero)
      thus ?thesis by (simp add: power2_eq_square)
    qed
    have lo: "moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x)
        \<ge> - (5/2) * (norm h)\<^sup>2" using lo0 split bnd by (simp add: abs_le_iff)
    have nn: "0 \<le> (norm h)\<^sup>2" by simp
    show ?thesis unfolding real_norm_def using up lo nn by linarith
  qed
  have "((\<lambda>h. norm (moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x))
      / norm h) \<longlongrightarrow> 0) (at 0)"
  proof (rule Lim_transform_bound[where g = "\<lambda>h :: 'a. (5/2) * norm h"])
    show "((\<lambda>h :: 'a. (5/2) * norm h) \<longlongrightarrow> 0) (at 0)"
    proof -
      have "((\<lambda>h :: 'a. (5/2) * norm h) \<longlongrightarrow> (5/2) * norm (0 :: 'a)) (at 0)"
        by (intro tendsto_intros)
      thus ?thesis by simp
    qed
    show "eventually (\<lambda>h :: 'a. norm (norm (moreau f (x + h) - moreau f x
        - h \<bullet> (x - prox f x)) / norm h) \<le> norm ((5/2) * norm h)) (at 0)"
    proof (rule always_eventually, rule allI)
      fix h :: 'a
      show "norm (norm (moreau f (x + h) - moreau f x
          - h \<bullet> (x - prox f x)) / norm h) \<le> norm ((5/2) * norm h)"
      proof (cases "h = 0")
        case True thus ?thesis by simp
      next
        case False
        have "norm (moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x))
            / norm h \<le> ((5/2) * (norm h)\<^sup>2) / norm h"
          using quad[of h] False by (intro divide_right_mono) auto
        also have "\<dots> = (5/2) * norm h"
          using False by (simp add: power2_eq_square)
        finally show ?thesis using False by simp
      qed
    qed
  qed
  thus "((\<lambda>h. norm (moreau f (x + h) - moreau f x
      - h \<bullet> (x - prox f x)) / norm h) \<longlongrightarrow> 0) (at 0)" .
qed

subsection \<open>Second-order differentiability of the Moreau envelope\<close>

text \<open>The first second-order statement of the development, and an
  Alexandrov-type theorem in its own right: the Moreau envelope of a finite
  convex function is twice differentiable almost everywhere, with positive
  semidefinite Hessian \<open>I - DR\<close>. It follows by combining the everywhere-valid
  gradient formula with a.e. differentiability of the resolvent; positivity
  comes from the firm-nonexpansiveness inequality.\<close>

lemma prox_deriv_norm_le:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
    and D: "(prox f has_derivative D) (at x)"
  shows "norm (D h) \<le> norm h"
proof -
  have psd: "(norm (D h))\<^sup>2 \<le> h \<bullet> D h" by (rule prox_deriv_psd[OF cvx D])
  have cs: "h \<bullet> D h \<le> norm h * norm (D h)"
    using Cauchy_Schwarz_ineq2[of h "D h"] by linarith
  have "(norm (D h))\<^sup>2 \<le> norm h * norm (D h)" using psd cs by linarith
  thus ?thesis
    by (cases "D h = 0") (auto simp: power2_eq_square mult_le_cancel_right)
qed

lemma moreau_hessian_psd:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
    and D: "(prox f has_derivative D) (at x)"
  shows "0 \<le> h \<bullet> (h - D h)"
proof -
  have "h \<bullet> D h \<le> norm h * norm (D h)"
    using Cauchy_Schwarz_ineq2[of h "D h"] by linarith
  also have "\<dots> \<le> norm h * norm h"
    using prox_deriv_norm_le[OF cvx D] by (intro mult_left_mono) auto
  also have "\<dots> = h \<bullet> h"
    by (simp add: power2_eq_square[symmetric] power2_norm_eq_inner)
  finally show ?thesis by (simp add: inner_diff_right)
qed

lemma moreau_grad_has_derivative:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes D: "(prox f has_derivative D) (at x)"
  shows "((\<lambda>y. y - prox f y) has_derivative (\<lambda>h. h - D h)) (at x)"
  by (intro has_derivative_diff has_derivative_ident D)

theorem moreau_twice_differentiable_AE:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "AE x in lborel. \<exists>A. bounded_linear A
      \<and> (\<forall>y. (moreau f has_derivative (\<lambda>h. h \<bullet> (y - prox f y))) (at y))
      \<and> ((\<lambda>y. y - prox f y) has_derivative A) (at x)
      \<and> (\<forall>h. 0 \<le> h \<bullet> A h)"
proof -
  have grad: "\<forall>y. (moreau f has_derivative (\<lambda>h. h \<bullet> (y - prox f y))) (at y)"
    using moreau_has_derivative[OF cvx] by blast
  show ?thesis
  proof (rule eventually_mono[OF prox_differentiable_AE[OF cvx]])
    fix x :: 'a assume "(prox f) differentiable (at x)"
    then obtain D where D: "(prox f has_derivative D) (at x)"
      unfolding differentiable_def by blast
    have blD: "bounded_linear D" by (rule has_derivative_bounded_linear[OF D])
    have blA: "bounded_linear (\<lambda>h. h - D h)"
      using blD by (intro bounded_linear_sub bounded_linear_ident)
    have hess: "((\<lambda>y. y - prox f y) has_derivative (\<lambda>h. h - D h)) (at x)"
      by (rule moreau_grad_has_derivative[OF D])
    have psd: "0 \<le> h \<bullet> (h - D h)" for h
      by (rule moreau_hessian_psd[OF cvx D])
    show "\<exists>A. bounded_linear A
        \<and> (\<forall>y. (moreau f has_derivative (\<lambda>h. h \<bullet> (y - prox f y))) (at y))
        \<and> ((\<lambda>y. y - prox f y) has_derivative A) (at x)
        \<and> (\<forall>h. 0 \<le> h \<bullet> A h)"
      using blA grad hess psd by blast
  qed
qed

subsection \<open>Integral representation of the envelope's increments\<close>

text \<open>The bridge from "the gradient is differentiable at a point" to a genuine
  second-order Taylor expansion: since the envelope's gradient is known
  EVERYWHERE, the increment along a segment is the integral of the gradient,
  by the ordinary fundamental theorem of calculus. Feeding the first-order
  expansion of the gradient into this integral produces the quadratic term.\<close>

lemma moreau_line_vector_derivative:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "((\<lambda>s. moreau f (x + s *\<^sub>R h)) has_vector_derivative
      (h \<bullet> ((x + s *\<^sub>R h) - prox f (x + s *\<^sub>R h)))) (at s within T)"
proof -
  have inner': "((\<lambda>t. x + t *\<^sub>R h) has_derivative (\<lambda>t. t *\<^sub>R h)) (at s within T)"
    by (auto intro!: derivative_eq_intros)
  have outer: "(moreau f has_derivative
      (\<lambda>k. k \<bullet> ((x + s *\<^sub>R h) - prox f (x + s *\<^sub>R h))))
      (at (x + s *\<^sub>R h) within (\<lambda>t. x + t *\<^sub>R h) ` T)"
    using moreau_has_derivative[OF cvx] by (rule has_derivative_at_withinI)
  have "((\<lambda>s. moreau f (x + s *\<^sub>R h)) has_derivative
      (\<lambda>t. (t *\<^sub>R h) \<bullet> ((x + s *\<^sub>R h) - prox f (x + s *\<^sub>R h))))
      (at s within T)"
    by (rule diff_chain_within[OF inner' outer, unfolded comp_def])
  moreover have "(\<lambda>t. (t *\<^sub>R h) \<bullet> ((x + s *\<^sub>R h) - prox f (x + s *\<^sub>R h)))
      = (\<lambda>t. t *\<^sub>R (h \<bullet> ((x + s *\<^sub>R h) - prox f (x + s *\<^sub>R h))))"
    by (rule ext) simp
  ultimately show ?thesis unfolding has_vector_derivative_def by simp
qed

theorem moreau_ftc:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "((\<lambda>s. h \<bullet> ((x + s *\<^sub>R h) - prox f (x + s *\<^sub>R h)))
      has_integral (moreau f (x + h) - moreau f x)) {0..1}"
proof -
  have "((\<lambda>s. h \<bullet> ((x + s *\<^sub>R h) - prox f (x + s *\<^sub>R h)))
      has_integral (moreau f (x + 1 *\<^sub>R h) - moreau f (x + 0 *\<^sub>R h))) {0..1}"
    by (rule fundamental_theorem_of_calculus)
      (auto intro!: moreau_line_vector_derivative[OF cvx])
  thus ?thesis by simp
qed

text \<open>The quadratic term itself: integrating the FIRST-order expansion of the
  gradient over the segment produces \<open>h \<cdot> G x + (h \<cdot> A h)/2\<close>. The factor
  \<open>1/2\<close> is exactly \<open>\<integral>\<^sub>0\<^sup>1 s ds\<close>.\<close>

lemma has_integral_affine_unit:
  fixes c d :: real
  shows "((\<lambda>s. c + s * d) has_integral (c + d/2)) {0..1}"
proof -
  have "((\<lambda>s. c + s * d) has_integral
      ((c * 1 + d * 1\<^sup>2 / 2) - (c * 0 + d * 0\<^sup>2 / 2))) {0..1}"
  proof (rule fundamental_theorem_of_calculus)
    show "(0::real) \<le> 1" by simp
    fix s :: real assume "s \<in> {0..1}"
    show "((\<lambda>s. c * s + d * s\<^sup>2 / 2) has_vector_derivative (c + s * d))
        (at s within {0..1})"
      unfolding has_vector_derivative_def
      by (auto intro!: derivative_eq_intros simp: algebra_simps)
  qed
  thus ?thesis by simp
qed

lemma has_integral_gradient_model:
  fixes h :: "'a::euclidean_space"
  assumes A: "bounded_linear A"
  shows "((\<lambda>s. h \<bullet> (g + A (s *\<^sub>R h)))
      has_integral (h \<bullet> g + (h \<bullet> A h) / 2)) {0..1}"
proof -
  have lin: "linear A" using A unfolding bounded_linear_def by simp
  have pt: "h \<bullet> (g + A (s *\<^sub>R h)) = (h \<bullet> g) + s * (h \<bullet> A h)" for s
  proof -
    have "A (s *\<^sub>R h) = s *\<^sub>R A h" using lin unfolding linear_iff by simp
    thus ?thesis by (simp add: inner_add_right)
  qed
  have "((\<lambda>s. (h \<bullet> g) + s * (h \<bullet> A h))
      has_integral ((h \<bullet> g) + (h \<bullet> A h)/2)) {0..1}"
    by (rule has_integral_affine_unit)
  thus ?thesis by (simp add: pt)
qed

subsection \<open>Second-order Taylor expansion of the envelope\<close>

text \<open>The error estimate, and with it the expansion itself: the increment of
  the envelope equals the integral of its gradient, the model quadratic equals
  the integral of the gradient's first-order expansion, and the difference of
  the two integrands is \<open>\<le> \<epsilon>\<parallel>h\<parallel>\<close> once \<open>\<parallel>h\<parallel>\<close> is small \<comment> \<open>uniformly in the
  segment parameter, since \<open>\<parallel>s h\<parallel> \<le> \<parallel>h\<parallel>\<close>\<close>. Integrating over a unit interval
  keeps the bound.\<close>

theorem moreau_second_order_taylor:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
    and D: "(prox f has_derivative D) (at x)"
  shows "((\<lambda>h. (moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x)
      - (h \<bullet> (h - D h)) / 2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
proof (rule tendstoI)
  fix \<epsilon> :: real assume \<epsilon>: "0 < \<epsilon>"
  define e2 where "e2 = \<epsilon>/2"
  have e2: "0 < e2" using \<epsilon> by (simp add: e2_def)
  define G where "G = (\<lambda>y :: 'a. y - prox f y)"
  define A where "A = (\<lambda>k :: 'a. k - D k)"
  have Gx: "G x = x - prox f x" by (simp add: G_def)
  have Ah: "A h = h - D h" for h by (simp add: A_def)
  have GA: "(G has_derivative A) (at x)"
    unfolding G_def A_def by (rule moreau_grad_has_derivative[OF D])
  have blA: "bounded_linear A"
    by (rule has_derivative_bounded_linear[OF GA])
  have "((\<lambda>u. norm (G (x + u) - G x - A u) / norm u) \<longlongrightarrow> 0) (at 0)"
    using GA unfolding has_derivative_at by blast
  from tendstoD[OF this e2] obtain \<delta> where \<delta>: "0 < \<delta>"
    and db: "\<And>u. u \<noteq> 0 \<Longrightarrow> dist u 0 < \<delta>
      \<Longrightarrow> dist (norm (G (x + u) - G x - A u) / norm u) 0 < e2"
    unfolding eventually_at by blast
  have small: "norm (G (x + u) - G x - A u) \<le> e2 * norm u"
    if u: "norm u < \<delta>" for u
  proof (cases "u = 0")
    case True
    have "A 0 = 0" using blA by (simp add: linear_simps(3))
    thus ?thesis unfolding True by simp
  next
    case False
    have "norm (G (x + u) - G x - A u) / norm u < e2"
      using db[OF False] u by (simp add: dist_norm)
    thus ?thesis using False by (simp add: divide_less_eq)
  qed
  have main: "\<bar>(moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x)
      - (h \<bullet> (h - D h)) / 2) / (norm h)\<^sup>2\<bar> \<le> e2"
    if h: "h \<noteq> 0" "norm h < \<delta>" for h
  proof -
    have i1: "((\<lambda>s. h \<bullet> G (x + s *\<^sub>R h))
        has_integral (moreau f (x + h) - moreau f x)) (cbox 0 1)"
      using moreau_ftc[OF cvx, of h x] unfolding G_def by simp
    have i2: "((\<lambda>s. h \<bullet> (G x + A (s *\<^sub>R h)))
        has_integral (h \<bullet> G x + (h \<bullet> A h) / 2)) (cbox 0 1)"
      using has_integral_gradient_model[OF blA, of h "G x"] by simp
    have i3: "((\<lambda>s. h \<bullet> G (x + s *\<^sub>R h) - h \<bullet> (G x + A (s *\<^sub>R h)))
        has_integral ((moreau f (x + h) - moreau f x)
          - (h \<bullet> G x + (h \<bullet> A h) / 2))) (cbox 0 1)"
      by (rule has_integral_diff[OF i1 i2])
    have bnd: "norm (h \<bullet> G (x + s *\<^sub>R h) - h \<bullet> (G x + A (s *\<^sub>R h)))
        \<le> e2 * (norm h)\<^sup>2" if s: "s \<in> cbox (0::real) 1" for s
    proof -
      have s01: "0 \<le> s" "s \<le> 1" using s by auto
      have nsh: "norm (s *\<^sub>R h) \<le> norm h"
      proof -
        have "norm (s *\<^sub>R h) = s * norm h" using s01 by simp
        also have "\<dots> \<le> 1 * norm h" using s01 by (intro mult_right_mono) auto
        finally show ?thesis by simp
      qed
      have "h \<bullet> G (x + s *\<^sub>R h) - h \<bullet> (G x + A (s *\<^sub>R h))
          = h \<bullet> (G (x + s *\<^sub>R h) - G x - A (s *\<^sub>R h))"
        by (simp add: inner_diff_right inner_add_right)
      hence "norm (h \<bullet> G (x + s *\<^sub>R h) - h \<bullet> (G x + A (s *\<^sub>R h)))
          \<le> norm h * norm (G (x + s *\<^sub>R h) - G x - A (s *\<^sub>R h))"
        using Cauchy_Schwarz_ineq2[of h "G (x + s *\<^sub>R h) - G x - A (s *\<^sub>R h)"]
        by simp
      also have "\<dots> \<le> norm h * (e2 * norm (s *\<^sub>R h))"
        using small[of "s *\<^sub>R h"] nsh h(2) by (intro mult_left_mono) auto
      also have "\<dots> \<le> norm h * (e2 * norm h)"
        using nsh e2 by (intro mult_left_mono mult_left_mono) auto
      finally show ?thesis by (simp add: power2_eq_square algebra_simps)
    qed
    have "norm ((moreau f (x + h) - moreau f x)
        - (h \<bullet> G x + (h \<bullet> A h) / 2))
        \<le> e2 * (norm h)\<^sup>2 * content (cbox (0::real) 1)"
      using e2 by (intro has_integral_bound[OF _ i3 bnd]) auto
    hence err: "\<bar>moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x)
        - (h \<bullet> (h - D h)) / 2\<bar> \<le> e2 * (norm h)\<^sup>2"
      unfolding Gx[symmetric] Ah[symmetric] by simp
    have hpos: "0 < (norm h)\<^sup>2" using h(1) by simp
    show ?thesis using err hpos by (simp add: divide_le_eq)
  qed
  show "eventually (\<lambda>h. dist ((moreau f (x + h) - moreau f x
      - h \<bullet> (x - prox f x) - (h \<bullet> (h - D h)) / 2) / (norm h)\<^sup>2) 0 < \<epsilon>)
      (at 0)"
    unfolding eventually_at
  proof (intro exI[of _ \<delta>] conjI)
    show "0 < \<delta>" by (rule \<delta>)
    show "\<forall>h\<in>UNIV. h \<noteq> 0 \<and> dist h 0 < \<delta>
        \<longrightarrow> dist ((moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x)
            - (h \<bullet> (h - D h)) / 2) / (norm h)\<^sup>2) 0 < \<epsilon>"
    proof (intro ballI impI)
      fix h :: 'a assume "h \<noteq> 0 \<and> dist h 0 < \<delta>"
      hence h: "h \<noteq> 0" "norm h < \<delta>" by (auto simp: dist_norm)
      have le: "\<bar>(moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x)
          - (h \<bullet> (h - D h)) / 2) / (norm h)\<^sup>2\<bar> \<le> e2"
        by (rule main[OF h])
      have "dist ((moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x)
          - (h \<bullet> (h - D h)) / 2) / (norm h)\<^sup>2) 0
          = \<bar>(moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x)
            - (h \<bullet> (h - D h)) / 2) / (norm h)\<^sup>2\<bar>"
        by (simp add: dist_real_def)
      also have "\<dots> \<le> e2" by (rule le)
      also have "e2 < \<epsilon>" using \<epsilon> by (simp add: e2_def)
      finally show "dist ((moreau f (x + h) - moreau f x
          - h \<bullet> (x - prox f x) - (h \<bullet> (h - D h)) / 2) / (norm h)\<^sup>2) 0
          < \<epsilon>" .
    qed
  qed
qed

subsection \<open>Alexandrov's theorem for the Moreau envelope\<close>

text \<open>The headline form: at almost every point the envelope has a genuine
  second-order Taylor expansion whose quadratic form is positive
  semidefinite. This is Alexandrov's theorem for the \<open>C\<^sup>1\<^sup>,\<^sup>1\<close> envelope; the
  remaining step towards Alexandrov for \<open>f\<close> itself is to transport the
  expansion along the resolvent, whose derivative supplies the quadratic
  form.\<close>

theorem moreau_alexandrov_AE:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "AE x in lborel. \<exists>A. bounded_linear A \<and> (\<forall>h. 0 \<le> h \<bullet> A h)
      \<and> ((\<lambda>h. (moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x)
          - (h \<bullet> A h) / 2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
proof (rule eventually_mono[OF prox_differentiable_AE[OF cvx]])
  fix x :: 'a assume "(prox f) differentiable (at x)"
  then obtain D where D: "(prox f has_derivative D) (at x)"
    unfolding differentiable_def by blast
  have blD: "bounded_linear D" by (rule has_derivative_bounded_linear[OF D])
  have blA: "bounded_linear (\<lambda>h. h - D h)"
    using blD by (intro bounded_linear_sub bounded_linear_ident)
  have psd: "0 \<le> h \<bullet> (h - D h)" for h
    by (rule moreau_hessian_psd[OF cvx D])
  have tay: "((\<lambda>h. (moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x)
      - (h \<bullet> (h - D h)) / 2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    by (rule moreau_second_order_taylor[OF cvx D])
  show "\<exists>A. bounded_linear A \<and> (\<forall>h. 0 \<le> h \<bullet> A h)
      \<and> ((\<lambda>h. (moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x)
          - (h \<bullet> A h) / 2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    using blA psd tay by blast
qed

subsection \<open>Second differences\<close>

text \<open>Towards symmetry of the resolvent's derivative. The SECOND DIFFERENCE
  \<open>\<Delta>(u,v) = e(x+u+v) - e(x+u) - e(x+v) + e(x)\<close> is symmetric in \<open>u\<close> and \<open>v\<close> for
  trivial reasons, while the fundamental theorem of calculus expresses it as a
  difference of two integrals of the gradient along parallel segments.
  Comparing the two, after inserting the first-order expansion of the
  gradient, forces \<open>u \<cdot> A v = v \<cdot> A u\<close> \<comment> \<open>the symmetry of the Hessian\<close>.\<close>

lemma second_difference_symmetric:
  fixes g :: "'a::ab_group_add \<Rightarrow> real"
  shows "g (x + u + v) - g (x + u) - g (x + v) + g x
       = g (x + v + u) - g (x + v) - g (x + u) + g x"
  by (simp add: add.commute add.left_commute)

theorem moreau_second_difference_integral:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "moreau f (x + v + u) - moreau f (x + v)
       - (moreau f (x + u) - moreau f x)
       = integral {0..1} (\<lambda>s. u \<bullet> ((x + v + s *\<^sub>R u)
           - prox f (x + v + s *\<^sub>R u)))
       - integral {0..1} (\<lambda>s. u \<bullet> ((x + s *\<^sub>R u) - prox f (x + s *\<^sub>R u)))"
proof -
  have i1: "((\<lambda>s. u \<bullet> ((x + v + s *\<^sub>R u) - prox f (x + v + s *\<^sub>R u)))
      has_integral (moreau f (x + v + u) - moreau f (x + v))) {0..1}"
    by (rule moreau_ftc[OF cvx])
  have i2: "((\<lambda>s. u \<bullet> ((x + s *\<^sub>R u) - prox f (x + s *\<^sub>R u)))
      has_integral (moreau f (x + u) - moreau f x)) {0..1}"
    by (rule moreau_ftc[OF cvx])
  have e1: "integral {0..1} (\<lambda>s. u \<bullet> ((x + v + s *\<^sub>R u)
      - prox f (x + v + s *\<^sub>R u))) = moreau f (x + v + u) - moreau f (x + v)"
    by (rule integral_unique[OF i1])
  have e2: "integral {0..1} (\<lambda>s. u \<bullet> ((x + s *\<^sub>R u) - prox f (x + s *\<^sub>R u)))
      = moreau f (x + u) - moreau f x"
    by (rule integral_unique[OF i2])
  show ?thesis unfolding e1 e2 by simp
qed

text \<open>Skeleton of the symmetry estimate. Along the two parallel segments the
  linear part of the gradient's increment is exactly \<open>t \<cdot> A v\<close> \<comment> \<open>independent
  of the segment parameter \<open>s\<close>, which is why the second difference sees the
  UNSYMMETRISED \<open>u \<cdot> A v\<close> rather than its symmetrisation\<close>, and what is left
  over is a difference of two first-order remainders.\<close>

lemma linear_parallel_increment:
  fixes A :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes lin: "linear A"
  shows "A (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u)) - A (s *\<^sub>R (t *\<^sub>R u)) = t *\<^sub>R A v"
proof -
  have "A (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u)) = A (t *\<^sub>R v) + A (s *\<^sub>R (t *\<^sub>R u))"
    using lin unfolding linear_iff by simp
  moreover have "A (t *\<^sub>R v) = t *\<^sub>R A v"
    using lin unfolding linear_iff by simp
  ultimately show ?thesis by simp
qed

lemma gradient_increment_decomp:
  fixes G :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes lin: "linear A"
  shows "G (x + (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u))) - G (x + s *\<^sub>R (t *\<^sub>R u))
       = t *\<^sub>R A v
         + ((G (x + (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u))) - G x
             - A (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u)))
           - (G (x + s *\<^sub>R (t *\<^sub>R u)) - G x - A (s *\<^sub>R (t *\<^sub>R u))))"
proof -
  have "t *\<^sub>R A v = A (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u)) - A (s *\<^sub>R (t *\<^sub>R u))"
    by (rule linear_parallel_increment[OF lin, symmetric])
  thus ?thesis by simp
qed

text \<open>With this decomposition the symmetry proof is a pure estimate: the
  remainder terms are \<open>\<le> \<epsilon>\<parallel>t\<parallel>(\<parallel>v\<parallel> + 2\<parallel>u\<parallel>)\<close> by differentiability of the
  gradient at \<open>x\<close>, so `moreau_second_difference_integral` divided by \<open>t\<^sup>2\<close>
  converges to \<open>u \<cdot> A v\<close>; `second_difference_symmetric` then forces
  \<open>u \<cdot> A v = v \<cdot> A u\<close>.\<close>

text \<open>The analytic core of the symmetry estimate: pointwise on the segment,
  the integrand of the second difference differs from \<open>t\<^sup>2 (u \<cdot> A v)\<close> by at
  most \<open>\<epsilon> t\<^sup>2 \<parallel>u\<parallel>(\<parallel>v\<parallel> + 2\<parallel>u\<parallel>)\<close>. Integrating over the unit interval preserves
  the bound, so the second difference divided by \<open>t\<^sup>2\<close> converges to \<open>u \<cdot> A v\<close>.\<close>

lemma second_difference_integrand_bound:
  fixes G :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes lin: "linear A"
    and rem: "\<And>w. norm w < \<delta> \<Longrightarrow> norm (G (x + w) - G x - A w) \<le> e2 * norm w"
    and e2: "0 \<le> e2"
    and w1: "norm (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u)) < \<delta>"
    and w2: "norm (s *\<^sub>R (t *\<^sub>R u)) < \<delta>"
    and s: "0 \<le> s" "s \<le> 1"
  shows "\<bar>(t *\<^sub>R u) \<bullet> (G (x + (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u)))
        - G (x + s *\<^sub>R (t *\<^sub>R u))) - t\<^sup>2 * (u \<bullet> A v)\<bar>
      \<le> e2 * t\<^sup>2 * (norm u * (norm v + 2 * norm u))"
proof -
  define R1 where "R1 = G (x + (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u))) - G x
      - A (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u))"
  define R2 where "R2 = G (x + s *\<^sub>R (t *\<^sub>R u)) - G x - A (s *\<^sub>R (t *\<^sub>R u))"
  have decomp: "G (x + (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u))) - G (x + s *\<^sub>R (t *\<^sub>R u))
      = t *\<^sub>R A v + (R1 - R2)"
    unfolding R1_def R2_def by (rule gradient_increment_decomp[OF lin])
  have main: "(t *\<^sub>R u) \<bullet> (G (x + (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u)))
      - G (x + s *\<^sub>R (t *\<^sub>R u))) - t\<^sup>2 * (u \<bullet> A v) = t * (u \<bullet> (R1 - R2))"
    unfolding decomp by (simp add: power2_eq_square algebra_simps)
  have n1: "norm R1 \<le> e2 * norm (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u))"
    unfolding R1_def by (rule rem[OF w1])
  have n2: "norm R2 \<le> e2 * norm (s *\<^sub>R (t *\<^sub>R u))"
    unfolding R2_def by (rule rem[OF w2])
  have b2: "norm (s *\<^sub>R (t *\<^sub>R u)) \<le> \<bar>t\<bar> * norm u"
  proof -
    have "norm (s *\<^sub>R (t *\<^sub>R u)) = s * (\<bar>t\<bar> * norm u)"
      using s by (simp add: abs_mult)
    also have "\<dots> \<le> 1 * (\<bar>t\<bar> * norm u)"
      using s by (intro mult_right_mono) auto
    finally show ?thesis by simp
  qed
  have b1: "norm (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u)) \<le> \<bar>t\<bar> * (norm v + norm u)"
  proof -
    have "norm (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u))
        \<le> norm (t *\<^sub>R v) + norm (s *\<^sub>R (t *\<^sub>R u))"
      by (rule norm_triangle_ineq)
    thus ?thesis using b2 by (simp add: algebra_simps)
  qed
  have r1: "norm R1 \<le> e2 * (\<bar>t\<bar> * (norm v + norm u))"
  proof -
    have "e2 * norm (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u))
        \<le> e2 * (\<bar>t\<bar> * (norm v + norm u))"
      by (rule mult_left_mono[OF b1 e2])
    thus ?thesis using n1 by linarith
  qed
  have r2: "norm R2 \<le> e2 * (\<bar>t\<bar> * norm u)"
  proof -
    have "e2 * norm (s *\<^sub>R (t *\<^sub>R u)) \<le> e2 * (\<bar>t\<bar> * norm u)"
      by (rule mult_left_mono[OF b2 e2])
    thus ?thesis using n2 by linarith
  qed
  have nRR: "norm (R1 - R2) \<le> e2 * (\<bar>t\<bar> * (norm v + 2 * norm u))"
  proof -
    have "norm (R1 - R2) \<le> norm R1 + norm R2" by (rule norm_triangle_ineq4)
    thus ?thesis using r1 r2 by (simp add: algebra_simps)
  qed
  have inner_b: "\<bar>u \<bullet> (R1 - R2)\<bar>
      \<le> norm u * (e2 * (\<bar>t\<bar> * (norm v + 2 * norm u)))"
  proof -
    have "\<bar>u \<bullet> (R1 - R2)\<bar> \<le> norm u * norm (R1 - R2)"
      using Cauchy_Schwarz_ineq2[of u "R1 - R2"] by simp
    also have "\<dots> \<le> norm u * (e2 * (\<bar>t\<bar> * (norm v + 2 * norm u)))"
      by (rule mult_left_mono[OF nRR]) simp
    finally show ?thesis .
  qed
  have "\<bar>t * (u \<bullet> (R1 - R2))\<bar>
      \<le> \<bar>t\<bar> * (norm u * (e2 * (\<bar>t\<bar> * (norm v + 2 * norm u))))"
    unfolding abs_mult by (rule mult_left_mono[OF inner_b]) simp
  also have "\<dots> = e2 * t\<^sup>2 * (norm u * (norm v + 2 * norm u))"
    by (simp add: power2_eq_square abs_mult[symmetric] algebra_simps)
  finally show ?thesis unfolding main .
qed

subsection \<open>Symmetry of the Hessian\<close>

text \<open>Integrating the pointwise bound over the unit interval gives the limit
  \<open>\<Delta>(t)/t\<^sup>2 \<rightarrow> u \<cdot> A v\<close>, and the trivial symmetry of the second difference then
  forces \<open>u \<cdot> A v = v \<cdot> A u\<close>.\<close>
text \<open>The same bound in the LEFT-associated form that `moreau_ftc` actually
  produces. Stating it separately avoids letting simp near the integrand,
  where it would distribute the inner product and lose the shape.\<close>

lemma second_difference_integrand_bound_left:
  fixes G :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes lin: "linear A"
    and rem: "\<And>w. norm w < \<delta> \<Longrightarrow> norm (G (x + w) - G x - A w) \<le> e2 * norm w"
    and e2: "0 \<le> e2"
    and w1: "norm (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u)) < \<delta>"
    and w2: "norm (s *\<^sub>R (t *\<^sub>R u)) < \<delta>"
    and s: "0 \<le> s" "s \<le> 1"
  shows "\<bar>(t *\<^sub>R u) \<bullet> (G (x + t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u))
        - G (x + s *\<^sub>R (t *\<^sub>R u))) - t\<^sup>2 * (u \<bullet> A v)\<bar>
      \<le> e2 * t\<^sup>2 * (norm u * (norm v + 2 * norm u))"
proof -
  have assoc: "x + t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u)
      = x + (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u))" by (simp add: add.assoc)
  show ?thesis
    unfolding assoc
    by (rule second_difference_integrand_bound[OF lin rem e2 w1 w2 s])
qed
text \<open>The second difference as a single integral, in exactly the shape the
  pointwise bound expects. This is the last piece of glue before the limit.\<close>

lemma moreau_second_difference_has_integral:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "((\<lambda>s. (t *\<^sub>R u) \<bullet> (((x + t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u))
        - prox f (x + t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u)))
        - ((x + s *\<^sub>R (t *\<^sub>R u)) - prox f (x + s *\<^sub>R (t *\<^sub>R u)))))
      has_integral (moreau f (x + t *\<^sub>R v + t *\<^sub>R u)
        - moreau f (x + t *\<^sub>R v)
        - (moreau f (x + t *\<^sub>R u) - moreau f x))) {0..1}"
proof -
  have i1: "((\<lambda>s. (t *\<^sub>R u) \<bullet> ((x + t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u))
      - prox f (x + t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u))))
      has_integral (moreau f (x + t *\<^sub>R v + t *\<^sub>R u)
        - moreau f (x + t *\<^sub>R v))) {0..1}"
    by (rule moreau_ftc[OF cvx])
  have i2: "((\<lambda>s. (t *\<^sub>R u) \<bullet> ((x + s *\<^sub>R (t *\<^sub>R u))
      - prox f (x + s *\<^sub>R (t *\<^sub>R u))))
      has_integral (moreau f (x + t *\<^sub>R u) - moreau f x)) {0..1}"
    by (rule moreau_ftc[OF cvx])
  have eq: "(\<lambda>s. (t *\<^sub>R u) \<bullet> ((x + t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u))
        - prox f (x + t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u)))
      - (t *\<^sub>R u) \<bullet> ((x + s *\<^sub>R (t *\<^sub>R u))
        - prox f (x + s *\<^sub>R (t *\<^sub>R u))))
      = (\<lambda>s. (t *\<^sub>R u) \<bullet> (((x + t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u))
          - prox f (x + t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u)))
          - ((x + s *\<^sub>R (t *\<^sub>R u)) - prox f (x + s *\<^sub>R (t *\<^sub>R u)))))"
    by (rule ext) (simp only: inner_diff_right)
  show ?thesis
    using has_integral_diff[OF i1 i2] unfolding eq by simp
qed
theorem moreau_second_difference_limit:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
    and D: "(prox f has_derivative D) (at x)"
  shows "((\<lambda>t. (moreau f (x + t *\<^sub>R v + t *\<^sub>R u) - moreau f (x + t *\<^sub>R v)
      - (moreau f (x + t *\<^sub>R u) - moreau f x)) / t\<^sup>2)
      \<longlongrightarrow> u \<bullet> (v - D v)) (at 0)"
proof (rule tendstoI)
  fix \<epsilon> :: real assume \<epsilon>: "0 < \<epsilon>"
  define A where "A = (\<lambda>k :: 'a. k - D k)"
  have GA: "((\<lambda>z :: 'a. z - prox f z) has_derivative A) (at x)"
    unfolding A_def by (rule moreau_grad_has_derivative[OF D])
  have blA: "bounded_linear A" by (rule has_derivative_bounded_linear[OF GA])
  have linA: "linear A" using blA unfolding bounded_linear_def by simp
  define C where "C = norm u * (norm v + 2 * norm u) + 1"
  have C: "0 < C" by (simp add: C_def add_nonneg_pos)
  define e2 where "e2 = (\<epsilon>/2) / C"
  have e2: "0 < e2" using \<epsilon> C by (simp add: e2_def)
  have "((\<lambda>w. norm ((x + w - prox f (x + w)) - (x - prox f x) - A w)
      / norm w) \<longlongrightarrow> 0) (at 0)"
    using GA unfolding has_derivative_at by simp
  from tendstoD[OF this e2] obtain \<delta> where \<delta>: "0 < \<delta>"
    and db: "\<And>w. w \<noteq> 0 \<Longrightarrow> dist w 0 < \<delta>
      \<Longrightarrow> dist (norm ((x + w - prox f (x + w)) - (x - prox f x) - A w)
          / norm w) 0 < e2"
    unfolding eventually_at by blast
  have rem: "norm ((x + w - prox f (x + w)) - (x - prox f x) - A w)
      \<le> e2 * norm w" if w: "norm w < \<delta>" for w
  proof (cases "w = 0")
    case True
    have "A 0 = 0" using blA by (simp add: linear_simps(3))
    thus ?thesis unfolding True by simp
  next
    case False
    have "norm ((x + w - prox f (x + w)) - (x - prox f x) - A w) / norm w < e2"
      using db[OF False] w by (simp add: dist_norm)
    thus ?thesis using False by (simp add: divide_less_eq)
  qed
  define M where "M = norm v + 2 * norm u + 1"
  have M: "0 < M" by (simp add: M_def add_nonneg_pos)
  define \<delta>' where "\<delta>' = \<delta> / M"
  have \<delta>': "0 < \<delta>'" using \<delta> M by (simp add: \<delta>'_def)
  have main: "\<bar>(moreau f (x + t *\<^sub>R v + t *\<^sub>R u) - moreau f (x + t *\<^sub>R v)
      - (moreau f (x + t *\<^sub>R u) - moreau f x)) / t\<^sup>2 - u \<bullet> A v\<bar> \<le> \<epsilon>/2"
    if t: "t \<noteq> 0" "\<bar>t\<bar> < \<delta>'" for t
  proof -
    have tM: "\<bar>t\<bar> * M < \<delta>" using t(2) M by (simp add: \<delta>'_def field_simps)
    have iD: "((\<lambda>s. (t *\<^sub>R u) \<bullet> (((x + t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u))
          - prox f (x + t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u)))
          - ((x + s *\<^sub>R (t *\<^sub>R u)) - prox f (x + s *\<^sub>R (t *\<^sub>R u)))))
        has_integral (moreau f (x + t *\<^sub>R v + t *\<^sub>R u)
          - moreau f (x + t *\<^sub>R v)
          - (moreau f (x + t *\<^sub>R u) - moreau f x))) {0..1}"
      by (rule moreau_second_difference_has_integral[OF cvx])
    have iC: "((\<lambda>s :: real. t\<^sup>2 * (u \<bullet> A v))
        has_integral (t\<^sup>2 * (u \<bullet> A v))) {0..1}"
      using has_integral_const_real[of "t\<^sup>2 * (u \<bullet> A v)" 0 1] by simp
    have i5: "((\<lambda>s. (t *\<^sub>R u) \<bullet> (((x + t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u))
          - prox f (x + t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u)))
          - ((x + s *\<^sub>R (t *\<^sub>R u)) - prox f (x + s *\<^sub>R (t *\<^sub>R u))))
        - t\<^sup>2 * (u \<bullet> A v))
        has_integral ((moreau f (x + t *\<^sub>R v + t *\<^sub>R u)
          - moreau f (x + t *\<^sub>R v)
          - (moreau f (x + t *\<^sub>R u) - moreau f x)) - t\<^sup>2 * (u \<bullet> A v))) {0..1}"
      by (rule has_integral_diff[OF iD iC])
    have pb: "norm ((t *\<^sub>R u) \<bullet> (((x + t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u))
          - prox f (x + t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u)))
          - ((x + s *\<^sub>R (t *\<^sub>R u)) - prox f (x + s *\<^sub>R (t *\<^sub>R u))))
        - t\<^sup>2 * (u \<bullet> A v))
        \<le> e2 * t\<^sup>2 * (norm u * (norm v + 2 * norm u))"
      if s: "s \<in> cbox (0::real) 1" for s
    proof -
      have s01: "0 \<le> s" "s \<le> 1" using s by auto
      have nb2: "norm (s *\<^sub>R (t *\<^sub>R u)) \<le> \<bar>t\<bar> * norm u"
      proof -
        have "norm (s *\<^sub>R (t *\<^sub>R u)) = s * (\<bar>t\<bar> * norm u)"
          using s01 by (simp add: abs_mult)
        also have "\<dots> \<le> 1 * (\<bar>t\<bar> * norm u)"
          using s01 by (intro mult_right_mono) auto
        finally show ?thesis by simp
      qed
      have nb1: "norm (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u)) \<le> \<bar>t\<bar> * (norm v + norm u)"
      proof -
        have "norm (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u))
            \<le> norm (t *\<^sub>R v) + norm (s *\<^sub>R (t *\<^sub>R u))"
          by (rule norm_triangle_ineq)
        thus ?thesis using nb2 by (simp add: algebra_simps)
      qed
      have lt1: "norm (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u)) < \<delta>"
      proof -
        have "\<bar>t\<bar> * (norm v + norm u) \<le> \<bar>t\<bar> * M"
          using t(1) by (intro mult_left_mono) (auto simp: M_def)
        thus ?thesis using nb1 tM by linarith
      qed
      have lt2: "norm (s *\<^sub>R (t *\<^sub>R u)) < \<delta>"
      proof -
        have "\<bar>t\<bar> * norm u \<le> \<bar>t\<bar> * M"
          using t(1) by (intro mult_left_mono) (auto simp: M_def)
        thus ?thesis using nb2 tM by linarith
      qed
      show ?thesis
        using second_difference_integrand_bound_left
          [OF linA rem less_imp_le[OF e2] lt1 lt2 s01] by simp
    qed
    have bound: "norm ((moreau f (x + t *\<^sub>R v + t *\<^sub>R u)
        - moreau f (x + t *\<^sub>R v) - (moreau f (x + t *\<^sub>R u) - moreau f x))
        - t\<^sup>2 * (u \<bullet> A v))
        \<le> e2 * t\<^sup>2 * (norm u * (norm v + 2 * norm u))
          * content (cbox (0::real) 1)"
      using e2 by (intro has_integral_bound[OF _ i5[folded box_real(2)] pb])
        auto
    have tsq: "0 < t\<^sup>2" using t(1) by simp
    have "e2 * t\<^sup>2 * (norm u * (norm v + 2 * norm u)) \<le> e2 * t\<^sup>2 * C"
      using e2 tsq by (intro mult_left_mono) (auto simp: C_def)
    also have "\<dots> = (\<epsilon>/2) * t\<^sup>2" using C by (simp add: e2_def)
    finally have b2: "\<bar>(moreau f (x + t *\<^sub>R v + t *\<^sub>R u)
        - moreau f (x + t *\<^sub>R v) - (moreau f (x + t *\<^sub>R u) - moreau f x))
        - t\<^sup>2 * (u \<bullet> A v)\<bar> \<le> (\<epsilon>/2) * t\<^sup>2" using bound by simp
    show ?thesis using b2 tsq by (simp add: field_simps)
  qed
  show "eventually (\<lambda>t. dist ((moreau f (x + t *\<^sub>R v + t *\<^sub>R u)
      - moreau f (x + t *\<^sub>R v) - (moreau f (x + t *\<^sub>R u) - moreau f x)) / t\<^sup>2)
      (u \<bullet> (v - D v)) < \<epsilon>) (at 0)"
    unfolding eventually_at
  proof (intro exI[of _ \<delta>'] conjI)
    show "0 < \<delta>'" by (rule \<delta>')
    show "\<forall>t\<in>UNIV. t \<noteq> 0 \<and> dist t 0 < \<delta>'
        \<longrightarrow> dist ((moreau f (x + t *\<^sub>R v + t *\<^sub>R u) - moreau f (x + t *\<^sub>R v)
            - (moreau f (x + t *\<^sub>R u) - moreau f x)) / t\<^sup>2)
            (u \<bullet> (v - D v)) < \<epsilon>"
    proof (intro ballI impI)
      fix t :: real assume "t \<noteq> 0 \<and> dist t 0 < \<delta>'"
      hence t: "t \<noteq> 0" "\<bar>t\<bar> < \<delta>'" by (auto simp: dist_real_def)
      have "dist ((moreau f (x + t *\<^sub>R v + t *\<^sub>R u) - moreau f (x + t *\<^sub>R v)
          - (moreau f (x + t *\<^sub>R u) - moreau f x)) / t\<^sup>2) (u \<bullet> (v - D v))
          = \<bar>(moreau f (x + t *\<^sub>R v + t *\<^sub>R u) - moreau f (x + t *\<^sub>R v)
            - (moreau f (x + t *\<^sub>R u) - moreau f x)) / t\<^sup>2 - u \<bullet> A v\<bar>"
        by (simp add: dist_real_def A_def)
      also have "\<dots> \<le> \<epsilon>/2" by (rule main[OF t])
      also have "\<epsilon>/2 < \<epsilon>" using \<epsilon> by simp
      finally show "dist ((moreau f (x + t *\<^sub>R v + t *\<^sub>R u)
          - moreau f (x + t *\<^sub>R v) - (moreau f (x + t *\<^sub>R u) - moreau f x))
          / t\<^sup>2) (u \<bullet> (v - D v)) < \<epsilon>" .
    qed
  qed
qed

text \<open>Symmetry of the Hessian, at last: the second difference is symmetric in
  \<open>u\<close> and \<open>v\<close> for trivial reasons, so the two limits computed from it must
  agree.\<close>

theorem moreau_hessian_symmetric:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
    and D: "(prox f has_derivative D) (at x)"
  shows "u \<bullet> (v - D v) = v \<bullet> (u - D u)"
proof -
  have l1: "((\<lambda>t. (moreau f (x + t *\<^sub>R v + t *\<^sub>R u) - moreau f (x + t *\<^sub>R v)
      - (moreau f (x + t *\<^sub>R u) - moreau f x)) / t\<^sup>2)
      \<longlongrightarrow> u \<bullet> (v - D v)) (at 0)"
    by (rule moreau_second_difference_limit[OF cvx D])
  have l2: "((\<lambda>t. (moreau f (x + t *\<^sub>R u + t *\<^sub>R v) - moreau f (x + t *\<^sub>R u)
      - (moreau f (x + t *\<^sub>R v) - moreau f x)) / t\<^sup>2)
      \<longlongrightarrow> v \<bullet> (u - D u)) (at 0)"
    by (rule moreau_second_difference_limit[OF cvx D])
  have same: "(\<lambda>t. (moreau f (x + t *\<^sub>R v + t *\<^sub>R u) - moreau f (x + t *\<^sub>R v)
      - (moreau f (x + t *\<^sub>R u) - moreau f x)) / t\<^sup>2)
      = (\<lambda>t. (moreau f (x + t *\<^sub>R u + t *\<^sub>R v) - moreau f (x + t *\<^sub>R u)
      - (moreau f (x + t *\<^sub>R v) - moreau f x)) / t\<^sup>2)"
  proof (rule ext)
    fix t :: real
    have eq: "x + t *\<^sub>R v + t *\<^sub>R u = x + t *\<^sub>R u + t *\<^sub>R v"
      by (simp add: add.commute add.left_commute)
    show "(moreau f (x + t *\<^sub>R v + t *\<^sub>R u) - moreau f (x + t *\<^sub>R v)
        - (moreau f (x + t *\<^sub>R u) - moreau f x)) / t\<^sup>2
        = (moreau f (x + t *\<^sub>R u + t *\<^sub>R v) - moreau f (x + t *\<^sub>R u)
        - (moreau f (x + t *\<^sub>R v) - moreau f x)) / t\<^sup>2"
      unfolding eq by (rule arg_cong[where f = "\<lambda>y::real. y / t\<^sup>2"]) simp
  qed
  from l1 have l1': "((\<lambda>t. (moreau f (x + t *\<^sub>R u + t *\<^sub>R v)
      - moreau f (x + t *\<^sub>R u) - (moreau f (x + t *\<^sub>R v) - moreau f x)) / t\<^sup>2)
      \<longlongrightarrow> u \<bullet> (v - D v)) (at 0)"
    unfolding same .
  show ?thesis by (rule tendsto_unique[OF at_neq_bot l1' l2])
qed

text \<open>ALEXANDROV'S THEOREM for the Moreau envelope, in its final form: almost
  every point admits a second-order Taylor expansion whose quadratic form is
  bounded, symmetric and positive semidefinite \<comment> \<open>a genuine Hessian\<close>.\<close>

theorem moreau_alexandrov_sym_AE:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "AE x in lborel. \<exists>A. bounded_linear A \<and> (\<forall>h. 0 \<le> h \<bullet> A h)
      \<and> (\<forall>u v. u \<bullet> A v = v \<bullet> A u)
      \<and> ((\<lambda>h. (moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x)
          - (h \<bullet> A h) / 2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
proof (rule eventually_mono[OF prox_differentiable_AE[OF cvx]])
  fix x :: 'a assume "(prox f) differentiable (at x)"
  then obtain D where D: "(prox f has_derivative D) (at x)"
    unfolding differentiable_def by blast
  have blD: "bounded_linear D" by (rule has_derivative_bounded_linear[OF D])
  have blA: "bounded_linear (\<lambda>h. h - D h)"
    using blD by (intro bounded_linear_sub bounded_linear_ident)
  have psd: "0 \<le> h \<bullet> (h - D h)" for h
    by (rule moreau_hessian_psd[OF cvx D])
  have sym: "u \<bullet> (v - D v) = v \<bullet> (u - D u)" for u v
    by (rule moreau_hessian_symmetric[OF cvx D])
  have tay: "((\<lambda>h. (moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x)
      - (h \<bullet> (h - D h)) / 2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    by (rule moreau_second_order_taylor[OF cvx D])
  show "\<exists>A. bounded_linear A \<and> (\<forall>h. 0 \<le> h \<bullet> A h)
      \<and> (\<forall>u v. u \<bullet> A v = v \<bullet> A u)
      \<and> ((\<lambda>h. (moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x)
          - (h \<bullet> A h) / 2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    using blA psd sym tay by blast
qed

subsection \<open>Transporting Alexandrov from the envelope to the function\<close>

text \<open>The envelope is a smoothed copy of \<open>f\<close>, reached through the resolvent
  \<open>R = prox f\<close>. To move the second-order expansion back onto \<open>f\<close> we need the
  resolvent's defining property in the reverse direction: \<open>R\<close> undoes
  \<open>id + subdiff f\<close>.\<close>

lemma subdiff_prox:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f" and p: "p \<in> subdiff f y"
  shows "prox f (y + p) = y"
proof (rule prox_unique[OF cvx, of "prox f (y + p)" "y + p" y])
  show "f (prox f (y + p)) + (dist (y + p) (prox f (y + p)))\<^sup>2/2
      \<le> f z + (dist (y + p) z)\<^sup>2/2" for z
    by (rule prox_min[OF cvx])
next
  fix z :: 'a
  have sd: "f y + p \<bullet> (z - y) \<le> f z" by (rule subdiffD[OF p])
  have rw: "y + p - z = p - (z - y)" by simp
  have exp: "(dist (y + p) z)\<^sup>2
      = (norm p)\<^sup>2 - 2 * (p \<bullet> (z - y)) + (norm (z - y))\<^sup>2"
    unfolding dist_norm rw
    by (simp add: power2_norm_eq_inner inner_diff_left inner_diff_right
        inner_commute)
  have d1: "(dist (y + p) y)\<^sup>2 = (norm p)\<^sup>2" by (simp add: dist_norm)
  have nn: "0 \<le> (norm (z - y))\<^sup>2" by simp
  show "f y + (dist (y + p) y)\<^sup>2/2 \<le> f z + (dist (y + p) z)\<^sup>2/2"
    unfolding d1 exp using sd nn by argo
qed

text \<open>Subgradients are bounded by difference quotients: pushing a distance
  \<open>r\<close> in the direction of a subgradient must increase \<open>f\<close> by at least
  \<open>r * norm p\<close>.\<close>

lemma subdiff_norm_le:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes r: "0 < r" and p: "p \<in> subdiff f u"
    and M: "\<And>v. v \<in> cball u r \<Longrightarrow> f v \<le> M"
  shows "norm p \<le> (M - f u) / r"
proof (cases "p = 0")
  case True
  have "f u \<le> M" using M[of u] r by simp
  thus ?thesis unfolding True using r by simp
next
  case False
  hence np: "0 < norm p" by simp
  define v where "v = u + (r / norm p) *\<^sub>R p"
  have "dist v u = \<bar>r / norm p\<bar> * norm p"
    unfolding v_def dist_norm by simp
  also have "\<dots> = r" using np r by simp
  finally have vm: "v \<in> cball u r" by (simp add: dist_commute)
  have "p \<bullet> (v - u) = (r / norm p) * (p \<bullet> p)"
    unfolding v_def by simp
  also have "\<dots> = r * norm p"
    using np by (simp add: power2_norm_eq_inner[symmetric] power2_eq_square)
  finally have pv: "p \<bullet> (v - u) = r * norm p" .
  have "f u + p \<bullet> (v - u) \<le> f v" by (rule subdiffD[OF p])
  hence "f u + r * norm p \<le> M" using M[OF vm] unfolding pv by linarith
  thus ?thesis using r by (simp add: field_simps)
qed

lemma convex_bdd_above_cball:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "\<exists>M. \<forall>v \<in> cball u r. f v \<le> M"
proof -
  have cf: "continuous_on UNIV f"
    by (rule convex_on_continuous[OF open_UNIV cvx])
  have "compact (f ` cball u r)"
    by (rule compact_continuous_image[OF continuous_on_subset[OF cf subset_UNIV]
        compact_cball])
  hence "bdd_above (f ` cball u r)"
    by (simp add: compact_imp_bounded bounded_imp_bdd_above)
  hence "f v \<le> Sup (f ` cball u r)" if "v \<in> cball u r" for v
    using that by (intro cSup_upper) auto
  thus ?thesis by blast
qed

lemma convex_bdd_below_cball:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "\<exists>m. \<forall>v \<in> cball u r. m \<le> f v"
proof -
  have cf: "continuous_on UNIV f"
    by (rule convex_on_continuous[OF open_UNIV cvx])
  have "compact (f ` cball u r)"
    by (rule compact_continuous_image[OF continuous_on_subset[OF cf subset_UNIV]
        compact_cball])
  hence "bdd_below (f ` cball u r)"
    by (simp add: compact_imp_bounded bounded_imp_bdd_below)
  hence "Inf (f ` cball u r) \<le> f v" if "v \<in> cball u r" for v
    using that by (intro cInf_lower) auto
  thus ?thesis by blast
qed

text \<open>The subdifferential is convex, being cut out by linear inequalities.\<close>

lemma convex_subdiff:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes p: "p \<in> subdiff f x" and q: "q \<in> subdiff f x"
    and t: "0 \<le> t" "t \<le> 1"
  shows "(1 - t) *\<^sub>R p + t *\<^sub>R q \<in> subdiff f x"
proof (rule subdiffI)
  fix y
  have 1: "f x + p \<bullet> (y - x) \<le> f y" by (rule subdiffD[OF p])
  have 2: "f x + q \<bullet> (y - x) \<le> f y" by (rule subdiffD[OF q])
  have e: "((1 - t) *\<^sub>R p + t *\<^sub>R q) \<bullet> (y - x)
      = (1 - t) * (p \<bullet> (y - x)) + t * (q \<bullet> (y - x))"
    by (simp add: inner_add_left)
  have "(1 - t) * (f x + p \<bullet> (y - x)) + t * (f x + q \<bullet> (y - x))
      \<le> (1 - t) * f y + t * f y"
    using t 1 2 by (intro add_mono mult_left_mono) auto
  thus "f x + ((1 - t) *\<^sub>R p + t *\<^sub>R q) \<bullet> (y - x) \<le> f y"
    unfolding e by (simp add: algebra_simps)
qed

text \<open>At a point where the resolvent's derivative is injective the
  subdifferential downstream is a SINGLETON: two distinct subgradients at
  \<open>prox f x\<close> would make the resolvent constant along a whole segment
  through \<open>x\<close>, so its derivative would kill that segment's direction.\<close>

lemma prox_deriv_inj_subdiff_singleton:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
    and D: "(prox f has_derivative D) (at x)"
    and injD: "inj D"
    and q: "q \<in> subdiff f (prox f x)"
  shows "q = x - prox f x"
proof -
  define y where "y = prox f x"
  define p where "p = x - y"
  define d where "d = q - p"
  have p_sub: "p \<in> subdiff f y" unfolding p_def y_def by (rule prox_subdiff[OF cvx])
  have q_sub: "q \<in> subdiff f y" using q unfolding y_def .
  have const: "prox f (x + t *\<^sub>R d) = y" if t: "0 \<le> t" "t \<le> 1" for t
  proof -
    have "(1 - t) *\<^sub>R p + t *\<^sub>R q \<in> subdiff f y"
      by (rule convex_subdiff[OF p_sub q_sub t])
    hence "prox f (y + ((1 - t) *\<^sub>R p + t *\<^sub>R q)) = y"
      by (rule subdiff_prox[OF cvx])
    moreover have "y + ((1 - t) *\<^sub>R p + t *\<^sub>R q) = x + t *\<^sub>R d"
      unfolding d_def p_def
      by (simp add: algebra_simps)
    ultimately show ?thesis by simp
  qed
  have lim0: "((\<lambda>t. (prox f (x + t *\<^sub>R d) - prox f x) /\<^sub>R t) \<longlongrightarrow> D d) (at (0::real))"
    by (rule has_derivative_dir_limit[OF D])
  have lim1: "((\<lambda>t. (prox f (x + t *\<^sub>R d) - prox f x) /\<^sub>R t) \<longlongrightarrow> D d)
      (at_right (0::real))"
    by (rule tendsto_mono[OF at_le[OF subset_UNIV] lim0])
  have ev: "\<forall>\<^sub>F t in at_right (0::real).
      (prox f (x + t *\<^sub>R d) - prox f x) /\<^sub>R t = 0"
  proof (rule eventually_mono[OF eventually_at_right_real[OF zero_less_one]])
    fix t :: real assume "t \<in> {0<..<1}"
    hence t: "0 \<le> t" "t \<le> 1" by auto
    show "(prox f (x + t *\<^sub>R d) - prox f x) /\<^sub>R t = 0"
      unfolding const[OF t] y_def[symmetric] by simp
  qed
  have lim2: "((\<lambda>t. (prox f (x + t *\<^sub>R d) - prox f x) /\<^sub>R t) \<longlongrightarrow> 0)
      (at_right (0::real))"
    by (rule tendsto_eventually[OF ev])
  have nb: "at_right (0::real) \<noteq> bot"
    using trivial_limit_at_right_real unfolding trivial_limit_def by blast
  have Dd: "D d = 0" by (rule tendsto_unique[OF nb lim1 lim2])
  have "D 0 = 0"
    using has_derivative_bounded_linear[OF D] by (simp add: linear_simps(3))
  with Dd have "D d = D 0" by simp
  hence "d = 0" using injD by (simp add: inj_eq)
  thus ?thesis unfolding d_def p_def y_def by simp
qed


text \<open>The resolvent is continuous; and its fibres over a bounded set are
  bounded, because the displacement \<open>z - prox f z\<close> is a subgradient at
  \<open>prox f z\<close> and subgradients are locally bounded.\<close>

lemma prox_lipschitz_on:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "lipschitz_on 1 UNIV (prox f)"
  by (intro lipschitz_onI) (auto simp: prox_nonexpansive[OF cvx])

lemma continuous_on_prox:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "continuous_on S (prox f)"
  by (rule continuous_on_subset[OF
      lipschitz_on_continuous_on[OF prox_lipschitz_on[OF cvx]] subset_UNIV])

lemma prox_fibre_bounded:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "\<exists>C. \<forall>z. dist (prox f z) y \<le> 1 \<longrightarrow> norm (z - prox f z) \<le> C"
proof -
  obtain M where M: "\<And>v. v \<in> cball y 2 \<Longrightarrow> f v \<le> M"
    using convex_bdd_above_cball[OF cvx, of y 2] by blast
  obtain m where m: "\<And>v. v \<in> cball y 1 \<Longrightarrow> m \<le> f v"
    using convex_bdd_below_cball[OF cvx, of y 1] by blast
  have "norm (z - prox f z) \<le> M - m" if zz: "dist (prox f z) y \<le> 1" for z
  proof -
    have sd: "z - prox f z \<in> subdiff f (prox f z)" by (rule prox_subdiff[OF cvx])
    have sub: "f v \<le> M" if "v \<in> cball (prox f z) 1" for v
    proof -
      have "dist v y \<le> dist v (prox f z) + dist (prox f z) y"
        by (rule dist_triangle)
      also have "\<dots> \<le> 2" using that zz by (simp add: dist_commute)
      finally show ?thesis by (intro M) (simp add: dist_commute)
    qed
    have "norm (z - prox f z) \<le> (M - f (prox f z)) / 1"
      by (rule subdiff_norm_le[OF zero_less_one sd sub])
    moreover have "m \<le> f (prox f z)"
      using zz by (intro m) (simp add: dist_commute)
    ultimately show ?thesis by simp
  qed
  thus ?thesis by blast
qed

lemma prox_fibre_compact:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "compact {z. dist (prox f z) y \<le> 1}"
proof (rule compact_eq_bounded_closed[THEN iffD2], intro conjI)
  obtain C where C: "\<And>z. dist (prox f z) y \<le> 1 \<Longrightarrow> norm (z - prox f z) \<le> C"
    using prox_fibre_bounded[OF cvx, of y] by blast
  have "norm z \<le> C + (1 + norm y)" if zz: "dist (prox f z) y \<le> 1" for z
  proof -
    have t1: "norm z \<le> norm (prox f z) + norm (z - prox f z)"
      by (rule norm_triangle_sub)
    have t2: "norm (prox f z) \<le> norm y + norm (prox f z - y)"
      by (rule norm_triangle_sub)
    have t3: "norm (prox f z - y) \<le> 1" using zz by (simp add: dist_norm)
    show ?thesis using t1 t2 t3 C[OF zz] by simp
  qed
  thus "bounded {z. dist (prox f z) y \<le> 1}" by (intro boundedI) auto
next
  have c1: "continuous_on UNIV (\<lambda>z. dist (prox f z) y)"
    by (rule continuous_on_dist[OF continuous_on_prox[OF cvx] continuous_on_const])
  show "closed {z. dist (prox f z) y \<le> 1}"
    by (rule closed_Collect_le[OF c1 continuous_on_const])
qed

text \<open>Local invertibility of the resolvent, by compactness rather than by an
  inverse function theorem: on the compact fibre over a unit ball the map
  \<open>z \<mapsto> dist (prox f z) y\<close> vanishes only at \<open>x\<close>, so outside any ball around
  \<open>x\<close> it is bounded below by a positive constant.\<close>

lemma prox_local_inverse_continuous:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
    and sing: "\<And>q. q \<in> subdiff f (prox f x) \<Longrightarrow> q = x - prox f x"
    and e: "0 < \<epsilon>"
  shows "\<exists>\<delta>>0. \<forall>z. dist (prox f z) (prox f x) < \<delta> \<longrightarrow> dist z x < \<epsilon>"
proof -
  define y where "y = prox f x"
  define K where "K = {z. dist (prox f z) y \<le> 1}"
  have Kc: "compact K" unfolding K_def by (rule prox_fibre_compact[OF cvx])
  define L where "L = K \<inter> (- ball x \<epsilon>)"
  have Lc: "compact L"
    unfolding L_def by (intro compact_Int_closed Kc closed_Compl open_ball)
  show ?thesis
  proof (cases "L = {}")
    case True
    have "dist z x < \<epsilon>" if "dist (prox f z) y < 1" for z
    proof -
      have "z \<in> K" using that unfolding K_def by simp
      hence "z \<in> ball x \<epsilon>" using True unfolding L_def by auto
      thus ?thesis by (simp add: dist_commute)
    qed
    thus ?thesis unfolding y_def by (intro exI[of _ 1]) simp
  next
    case False
    have cg: "continuous_on L (\<lambda>z. dist (prox f z) y)"
      by (rule continuous_on_dist[OF continuous_on_prox[OF cvx]
          continuous_on_const])
    obtain z0 where z0: "z0 \<in> L"
      and mn: "\<And>z. z \<in> L \<Longrightarrow> dist (prox f z0) y \<le> dist (prox f z) y"
      using continuous_attains_inf[OF Lc False cg] by blast
    have pos: "0 < dist (prox f z0) y"
    proof (rule ccontr)
      assume "\<not> 0 < dist (prox f z0) y"
      hence pz: "prox f z0 = y" by simp
      have "z0 - prox f z0 \<in> subdiff f (prox f z0)" by (rule prox_subdiff[OF cvx])
      hence "z0 - y \<in> subdiff f (prox f x)" unfolding pz y_def .
      hence "z0 - y = x - prox f x" by (rule sing)
      hence "z0 = x" unfolding y_def by simp
      moreover have "x \<in> ball x \<epsilon>" using e by simp
      ultimately show False using z0 unfolding L_def by simp
    qed
    define \<delta> where "\<delta> = min (dist (prox f z0) y) 1"
    have dpos: "0 < \<delta>" unfolding \<delta>_def using pos by simp
    have "dist z x < \<epsilon>" if dz: "dist (prox f z) y < \<delta>" for z
    proof (rule ccontr)
      assume "\<not> dist z x < \<epsilon>"
      hence "z \<notin> ball x \<epsilon>" by (simp add: dist_commute)
      moreover have "z \<in> K" using dz unfolding K_def \<delta>_def by simp
      ultimately have "z \<in> L" unfolding L_def by simp
      hence "dist (prox f z0) y \<le> dist (prox f z) y" by (rule mn)
      thus False using dz unfolding \<delta>_def by simp
    qed
    thus ?thesis unfolding y_def using dpos by blast
  qed
qed

text \<open>The exact bookkeeping identity behind the transport. Writing
  \<open>G z = z - prox f z\<close> for the displacement, the increment of \<open>f\<close> between two
  proximal points, measured against the subgradient \<open>G x\<close>, equals the
  increment of the envelope measured against the same vector, minus half the
  squared increment of \<open>G\<close>. The first-order terms in \<open>G\<close> cancel exactly \<comment>
  \<open>this is what makes a second-order expansion survive the transport\<close>.\<close>

lemma f_increment_exact:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "f (prox f (x + h)) - f (prox f x)
       - (x - prox f x) \<bullet> (prox f (x + h) - prox f x)
       = moreau f (x + h) - moreau f x - (x - prox f x) \<bullet> h
       - (norm ((x + h - prox f (x + h)) - (x - prox f x)))\<^sup>2 / 2"
proof -
  define y where "y = prox f x"
  define w where "w = prox f (x + h)"
  have e1: "moreau f x = f y + (norm (x - y))\<^sup>2/2"
    unfolding moreau_def y_def by (simp add: dist_norm)
  have e2: "moreau f (x + h) = f w + (norm (x + h - w))\<^sup>2/2"
    unfolding moreau_def w_def by (simp add: dist_norm)
  have s1: "(norm (x + h - w))\<^sup>2 = (x + h - w) \<bullet> (x + h - w)"
    by (rule power2_norm_eq_inner)
  have s2: "(norm (x - y))\<^sup>2 = (x - y) \<bullet> (x - y)"
    by (rule power2_norm_eq_inner)
  have s3: "(norm ((x + h - w) - (x - y)))\<^sup>2
      = ((x + h - w) - (x - y)) \<bullet> ((x + h - w) - (x - y))"
    by (rule power2_norm_eq_inner)
  show ?thesis
    unfolding y_def[symmetric] w_def[symmetric] e1 e2 s1 s2 s3
    by (simp add: inner_commute algebra_simps) argo
qed

text \<open>Three quantitative ingredients: the displacement's first-order
  remainder, the envelope's second-order remainder, and a lower bound for an
  injective linear map.\<close>

lemma prox_remainder_small:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes D: "(prox f has_derivative D) (at x)" and \<eta>: "0 < \<eta>"
  shows "\<exists>\<delta>>0. \<forall>h. norm h < \<delta> \<longrightarrow>
      norm ((x + h - prox f (x + h)) - (x - prox f x) - (h - D h)) \<le> \<eta> * norm h"
proof -
  define G where "G = (\<lambda>z :: 'a. z - prox f z)"
  define A where "A = (\<lambda>k :: 'a. k - D k)"
  have GA: "(G has_derivative A) (at x)"
    unfolding G_def A_def by (rule moreau_grad_has_derivative[OF D])
  have blA: "bounded_linear A" by (rule has_derivative_bounded_linear[OF GA])
  have "((\<lambda>u. norm (G (x + u) - G x - A u) / norm u) \<longlongrightarrow> 0) (at 0)"
    using GA unfolding has_derivative_at by blast
  from tendstoD[OF this \<eta>] obtain \<delta> where d: "0 < \<delta>"
    and db: "\<And>u. u \<noteq> 0 \<Longrightarrow> dist u 0 < \<delta>
      \<Longrightarrow> dist (norm (G (x + u) - G x - A u) / norm u) 0 < \<eta>"
    unfolding eventually_at by blast
  have "norm (G (x + h) - G x - A h) \<le> \<eta> * norm h" if hh: "norm h < \<delta>" for h
  proof (cases "h = 0")
    case True
    have "A 0 = 0" using blA by (simp add: linear_simps(3))
    thus ?thesis unfolding True by simp
  next
    case False
    hence nh: "0 < norm h" by simp
    have "norm (G (x + h) - G x - A h) / norm h < \<eta>"
      using db[OF False] hh by (simp add: dist_norm)
    thus ?thesis using nh by (simp add: field_simps)
  qed
  thus ?thesis unfolding G_def A_def using d by blast
qed

lemma moreau_taylor_bound:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
    and D: "(prox f has_derivative D) (at x)" and \<eta>: "0 < \<eta>"
  shows "\<exists>\<delta>>0. \<forall>h. norm h < \<delta> \<longrightarrow>
      \<bar>moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x)
        - (h \<bullet> (h - D h))/2\<bar> \<le> \<eta> * (norm h)\<^sup>2"
proof -
  define T where "T = (\<lambda>h. moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x)
      - (h \<bullet> (h - D h))/2)"
  have "((\<lambda>h. T h / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    unfolding T_def by (rule moreau_second_order_taylor[OF cvx D])
  from tendstoD[OF this \<eta>] obtain \<delta> where d: "0 < \<delta>"
    and db: "\<And>u. u \<noteq> 0 \<Longrightarrow> dist u 0 < \<delta> \<Longrightarrow> dist (T u / (norm u)\<^sup>2) 0 < \<eta>"
    unfolding eventually_at by blast
  have "\<bar>T h\<bar> \<le> \<eta> * (norm h)\<^sup>2" if hh: "norm h < \<delta>" for h
  proof (cases "h = 0")
    case True
    show ?thesis unfolding True T_def by simp
  next
    case False
    hence nh: "0 < (norm h)\<^sup>2" by simp
    have "\<bar>T h / (norm h)\<^sup>2\<bar> < \<eta>"
      using db[OF False] hh by (simp add: dist_norm)
    hence "\<bar>T h\<bar> / (norm h)\<^sup>2 < \<eta>" by simp
    thus ?thesis using nh by (simp add: field_simps)
  qed
  thus ?thesis unfolding T_def using d by blast
qed

lemma inj_linear_bounded_below:
  fixes D :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes bl: "bounded_linear D" and injD: "inj D"
  shows "\<exists>K>0. \<forall>u. norm u \<le> K * norm (D u)"
proof -
  have lin: "linear D" using bl by (rule bounded_linear.linear)
  obtain D' where lin': "linear D'" and inv: "D' \<circ> D = id"
    using linear_injective_left_inverse[OF lin injD] by blast
  obtain K where K: "\<And>v. norm (D' v) \<le> K * norm v"
    using lin' linear_bounded by blast
  have K1: "\<And>v. norm (D' v) \<le> (max K 1) * norm v"
    using K by (meson max.cobounded1 mult_right_mono norm_ge_zero order_trans)
  have "norm u \<le> (max K 1) * norm (D u)" for u
  proof -
    have "u = D' (D u)" using inv by (simp add: pointfree_idE)
    thus ?thesis using K1[of "D u"] by simp
  qed
  thus ?thesis by (intro exI[of _ "max K 1"]) auto
qed

text \<open>The algebraic heart of the transport. With \<open>A u = u - D u\<close> and
  \<open>B u = D' u - u\<close>, the quadratic form seen by the envelope at \<open>h\<close> and the
  one seen by \<open>f\<close> at \<open>k = D h - \<rho>\<close> differ only by terms carrying a factor
  \<open>\<rho>\<close> \<comment> \<open>the whole point being that the leading terms\<close> \<open>D h \<cdot> A h\<close>
  \<open>cancel identically\<close>.\<close>

lemma taylor_remainder_identity:
  fixes D D' :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes lin': "linear D'" and inv: "D' (D h) = h"
  shows "h \<bullet> (h - D h) - (norm ((h - D h) + \<rho>))\<^sup>2
       - (D h - \<rho>) \<bullet> (D' (D h - \<rho>) - (D h - \<rho>))
       = - ((h - D h) \<bullet> \<rho>) - (norm \<rho>)\<^sup>2
       + D h \<bullet> (D' \<rho> - \<rho>) - \<rho> \<bullet> (D' \<rho> - \<rho>)"
proof -
  have e1: "D' (D h - \<rho>) = h - D' \<rho>"
    using linear_diff[OF lin'] inv by simp
  show ?thesis
    unfolding e1 power2_norm_eq_inner
    by (simp add: inner_diff_left inner_diff_right inner_add_left
        inner_add_right inner_commute)
qed

text \<open>THE TRANSPORT. At a point where the resolvent is differentiable with
  injective derivative, the convex function itself has a second-order
  expansion at the corresponding proximal point, with quadratic form
  \<open>B = D' - id\<close>. Every step of the passage from \<open>h\<close> to \<open>k = D h - \<rho>\<close> is
  controlled by the single remainder \<open>\<rho>\<close>, and the compactness lemma
  guarantees that \<open>h\<close> is small whenever \<open>k\<close> is.\<close>

theorem f_taylor_limit:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
    and D: "(prox f has_derivative D) (at x)"
    and injD: "inj D"
    and lin': "linear D'" and inv: "\<And>u. D' (D u) = u"
  shows "((\<lambda>k. (f (prox f x + k) - f (prox f x) - (x - prox f x) \<bullet> k
      - (k \<bullet> (D' k - k))/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
proof (rule tendstoI)
  fix \<epsilon> :: real assume \<epsilon>: "0 < \<epsilon>"
  have blD: "bounded_linear D" by (rule has_derivative_bounded_linear[OF D])
  have blA: "bounded_linear (\<lambda>u. u - D u)"
    by (intro bounded_linear_sub bounded_linear_ident blD)
  have blD': "bounded_linear D'" using lin' by (simp add: linear_conv_bounded_linear)
  have blB: "bounded_linear (\<lambda>u. D' u - u)"
    by (intro bounded_linear_sub bounded_linear_ident blD')
  obtain NA where NA0: "0 < NA" and NAb: "\<And>u. norm (u - D u) \<le> norm u * NA"
    using bounded_linear.pos_bounded[OF blA] by blast
  obtain NB where NB0: "0 < NB" and NBb: "\<And>u. norm (D' u - u) \<le> norm u * NB"
    using bounded_linear.pos_bounded[OF blB] by blast
  obtain K where K0: "0 < K" and Kb: "\<And>u. norm u \<le> K * norm (D u)"
    using inj_linear_bounded_below[OF blD injD] by blast
  define C where "C = 2 + NA + 2*NB"
  have C0: "0 < C" unfolding C_def using NA0 NB0 by simp
  define \<eta> where "\<eta> = min (min 1 (1/(2*K))) (\<epsilon>/(C * 8 * K\<^sup>2))"
  have \<eta>1: "\<eta> \<le> 1" and \<eta>K: "\<eta> \<le> 1/(2*K)" and \<eta>e: "\<eta> \<le> \<epsilon>/(C * 8 * K\<^sup>2)"
    unfolding \<eta>_def by auto
  have \<eta>0: "0 < \<eta>" unfolding \<eta>_def using K0 \<epsilon> C0 by simp
  obtain \<delta>1 where \<delta>1: "0 < \<delta>1"
    and B1: "\<And>h. norm h < \<delta>1 \<Longrightarrow>
      norm ((x + h - prox f (x + h)) - (x - prox f x) - (h - D h)) \<le> \<eta> * norm h"
    using prox_remainder_small[OF D \<eta>0] by blast
  obtain \<delta>2 where \<delta>2: "0 < \<delta>2"
    and B2: "\<And>h. norm h < \<delta>2 \<Longrightarrow>
      \<bar>moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x)
        - (h \<bullet> (h - D h))/2\<bar> \<le> \<eta> * (norm h)\<^sup>2"
    using moreau_taylor_bound[OF cvx D \<eta>0] by blast
  define \<delta>0 where "\<delta>0 = min \<delta>1 \<delta>2"
  have \<delta>00: "0 < \<delta>0" unfolding \<delta>0_def using \<delta>1 \<delta>2 by simp
  have sing: "\<And>q. q \<in> subdiff f (prox f x) \<Longrightarrow> q = x - prox f x"
    by (rule prox_deriv_inj_subdiff_singleton[OF cvx D injD])
  obtain \<delta>3 where \<delta>3: "0 < \<delta>3"
    and B3: "\<And>z. dist (prox f z) (prox f x) < \<delta>3 \<Longrightarrow> dist z x < \<delta>0"
    using prox_local_inverse_continuous[OF cvx sing \<delta>00] by blast
  have main: "dist ((f (prox f x + k) - f (prox f x) - (x - prox f x) \<bullet> k
      - (k \<bullet> (D' k - k))/2) / (norm k)\<^sup>2) 0 < \<epsilon>"
    if k0: "k \<noteq> 0" and kd: "dist k 0 < \<delta>3" for k
  proof -
    define Nm where "Nm = f (prox f x + k) - f (prox f x) - (x - prox f x) \<bullet> k
        - (k \<bullet> (D' k - k))/2"
    have nk: "0 < norm k" using k0 by simp
    obtain q where q: "q \<in> subdiff f (prox f x + k)"
      using subdiff_nonempty[OF cvx] by blast
    define h where "h = (prox f x + k) + q - x"
    have xh: "x + h = (prox f x + k) + q" unfolding h_def by simp
    have ph: "prox f (x + h) = prox f x + k"
      unfolding xh by (rule subdiff_prox[OF cvx q])
    have "dist (prox f (x + h)) (prox f x) < \<delta>3"
      unfolding ph using kd by (simp add: dist_norm)
    hence "dist (x + h) x < \<delta>0" by (rule B3)
    hence nh: "norm h < \<delta>0" by (simp add: dist_norm)
    have nh1: "norm h < \<delta>1" using nh unfolding \<delta>0_def by simp
    have nh2: "norm h < \<delta>2" using nh unfolding \<delta>0_def by simp
    define g where "g = (x + h - prox f (x + h)) - (x - prox f x)"
    define \<rho> where "\<rho> = g - (h - D h)"
    have n\<rho>: "norm \<rho> \<le> \<eta> * norm h"
      unfolding \<rho>_def g_def by (rule B1[OF nh1])
    have gh: "g = h - k" unfolding g_def ph by simp
    have kD: "k = D h - \<rho>" unfolding \<rho>_def gh by simp
    have g\<rho>: "g = (h - D h) + \<rho>" unfolding \<rho>_def by simp
    have inc: "f (prox f x + k) - f (prox f x) - (x - prox f x) \<bullet> k
        = moreau f (x + h) - moreau f x - (x - prox f x) \<bullet> h - (norm g)\<^sup>2/2"
      using f_increment_exact[OF cvx, of x h] unfolding ph gh by simp
    define T where "T = moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x)
        - (h \<bullet> (h - D h))/2"
    have nT: "\<bar>T\<bar> \<le> \<eta> * (norm h)\<^sup>2" unfolding T_def by (rule B2[OF nh2])
    define Rm where "Rm = h \<bullet> (h - D h) - (norm g)\<^sup>2 - k \<bullet> (D' k - k)"
    have N: "Nm = T + Rm/2"
      unfolding Nm_def T_def Rm_def using inc by (simp add: inner_commute) argo
    have rid: "Rm = - ((h - D h) \<bullet> \<rho>) - (norm \<rho>)\<^sup>2
        + D h \<bullet> (D' \<rho> - \<rho>) - \<rho> \<bullet> (D' \<rho> - \<rho>)"
      unfolding Rm_def g\<rho> kD by (rule taylor_remainder_identity[OF lin' inv])
    have nh0: "0 \<le> norm h" by simp
    have n\<rho>0: "0 \<le> norm \<rho>" by simp
    have n1: "\<bar>(h - D h) \<bullet> \<rho>\<bar> \<le> NA * (\<eta> * (norm h)\<^sup>2)"
    proof -
      have "\<bar>(h - D h) \<bullet> \<rho>\<bar> \<le> norm (h - D h) * norm \<rho>"
        by (rule Cauchy_Schwarz_ineq2)
      also have "\<dots> \<le> (norm h * NA) * (\<eta> * norm h)"
        using NAb[of h] n\<rho> n\<rho>0 NA0 nh0 by (intro mult_mono) auto
      finally show ?thesis by (simp add: power2_eq_square field_simps)
    qed
    have n2: "(norm \<rho>)\<^sup>2 \<le> \<eta> * (norm h)\<^sup>2"
    proof -
      have "(norm \<rho>)\<^sup>2 \<le> (\<eta> * norm h)\<^sup>2"
        using n\<rho> n\<rho>0 by (intro power_mono) auto
      also have "\<dots> = \<eta> * (\<eta> * (norm h)\<^sup>2)" by (simp add: power2_eq_square field_simps)
      also have "\<dots> \<le> 1 * (\<eta> * (norm h)\<^sup>2)"
        using \<eta>1 \<eta>0 by (intro mult_right_mono) auto
      finally show ?thesis by simp
    qed
    have nDh: "norm (D h) \<le> norm h" by (rule prox_deriv_norm_le[OF cvx D])
    have n3: "\<bar>D h \<bullet> (D' \<rho> - \<rho>)\<bar> \<le> NB * (\<eta> * (norm h)\<^sup>2)"
    proof -
      have "\<bar>D h \<bullet> (D' \<rho> - \<rho>)\<bar> \<le> norm (D h) * norm (D' \<rho> - \<rho>)"
        by (rule Cauchy_Schwarz_ineq2)
      also have "\<dots> \<le> norm h * (\<eta> * norm h * NB)"
        using nDh NBb[of \<rho>] n\<rho> NB0 nh0 n\<rho>0
        by (intro mult_mono order_trans[OF NBb[of \<rho>]] mult_right_mono) auto
      finally show ?thesis by (simp add: power2_eq_square field_simps)
    qed
    have n4: "\<bar>\<rho> \<bullet> (D' \<rho> - \<rho>)\<bar> \<le> NB * (\<eta> * (norm h)\<^sup>2)"
    proof -
      have "\<bar>\<rho> \<bullet> (D' \<rho> - \<rho>)\<bar> \<le> norm \<rho> * norm (D' \<rho> - \<rho>)"
        by (rule Cauchy_Schwarz_ineq2)
      also have "\<dots> \<le> norm \<rho> * (norm \<rho> * NB)"
        using NBb[of \<rho>] n\<rho>0 by (intro mult_left_mono) auto
      also have "\<dots> = NB * (norm \<rho>)\<^sup>2" by (simp add: power2_eq_square field_simps)
      also have "\<dots> \<le> NB * (\<eta> * (norm h)\<^sup>2)"
        using n2 NB0 by (intro mult_left_mono) auto
      finally show ?thesis .
    qed
    have nRm: "\<bar>Rm\<bar> \<le> (NA + 1 + 2*NB) * (\<eta> * (norm h)\<^sup>2)"
    proof -
      have a1: "(h - D h) \<bullet> \<rho> \<le> NA * (\<eta> * (norm h)\<^sup>2)"
        and a1': "- ((h - D h) \<bullet> \<rho>) \<le> NA * (\<eta> * (norm h)\<^sup>2)"
        using n1 by (simp_all add: abs_le_iff)
      have a3: "D h \<bullet> (D' \<rho> - \<rho>) \<le> NB * (\<eta> * (norm h)\<^sup>2)"
        and a3': "- (D h \<bullet> (D' \<rho> - \<rho>)) \<le> NB * (\<eta> * (norm h)\<^sup>2)"
        using n3 by (simp_all add: abs_le_iff)
      have a4: "\<rho> \<bullet> (D' \<rho> - \<rho>) \<le> NB * (\<eta> * (norm h)\<^sup>2)"
        and a4': "- (\<rho> \<bullet> (D' \<rho> - \<rho>)) \<le> NB * (\<eta> * (norm h)\<^sup>2)"
        using n4 by (simp_all add: abs_le_iff)
      have a2: "0 \<le> (norm \<rho>)\<^sup>2" by simp
      have dexp: "(NA + 1 + 2*NB) * (\<eta> * (norm h)\<^sup>2)
          = NA * (\<eta> * (norm h)\<^sup>2) + (\<eta> * (norm h)\<^sup>2)
            + 2 * (NB * (\<eta> * (norm h)\<^sup>2))"
        by (simp add: algebra_simps)
      show ?thesis unfolding rid dexp
        using a1 a1' a2 a3 a3' a4 a4' n2 by (intro abs_leI; linarith)
    qed
    have nN: "\<bar>Nm\<bar> \<le> C * (\<eta> * (norm h)\<^sup>2)"
      unfolding N C_def using nT nRm NA0 NB0 \<eta>0 nh0 by (simp add: field_simps)
    have hk: "norm h \<le> 2 * K * norm k"
    proof -
      have Dh: "D h = k + \<rho>" using kD by simp
      have "norm h \<le> K * norm (D h)" by (rule Kb)
      also have "\<dots> = K * norm (k + \<rho>)" unfolding Dh ..
      also have "\<dots> \<le> K * (norm k + norm \<rho>)"
        using K0 by (intro mult_left_mono norm_triangle_ineq) auto
      also have "\<dots> \<le> K * (norm k + \<eta> * norm h)"
        using n\<rho> K0 by (intro mult_left_mono add_left_mono) auto
      finally have step: "norm h \<le> K * norm k + (K * \<eta>) * norm h"
        by (simp add: field_simps)
      have "K * \<eta> \<le> 1/2" using \<eta>K K0 by (simp add: field_simps)
      hence "(K * \<eta>) * norm h \<le> (1/2) * norm h"
        using nh0 by (intro mult_right_mono) auto
      with step show ?thesis by argo
    qed
    have hk2: "(norm h)\<^sup>2 \<le> 4 * K\<^sup>2 * (norm k)\<^sup>2"
    proof -
      have "(norm h)\<^sup>2 \<le> (2 * K * norm k)\<^sup>2"
        using hk nh0 by (intro power_mono) auto
      thus ?thesis by (simp add: power2_eq_square field_simps)
    qed
    have "C * (\<eta> * (norm h)\<^sup>2) \<le> C * (\<eta> * (4 * K\<^sup>2 * (norm k)\<^sup>2))"
      using hk2 C0 \<eta>0 by (intro mult_left_mono) auto
    also have "\<dots> = (C * 8 * K\<^sup>2) * \<eta> * ((norm k)\<^sup>2 / 2)"
      by (simp add: power2_eq_square field_simps)
    also have "\<dots> \<le> \<epsilon> * ((norm k)\<^sup>2 / 2)"
      using \<eta>e C0 K0 nk by (intro mult_right_mono) (auto simp: field_simps)
    finally have fin: "\<bar>Nm\<bar> \<le> \<epsilon> * ((norm k)\<^sup>2 / 2)"
      using nN by linarith
    have nk2: "0 < (norm k)\<^sup>2" using nk by simp
    have "\<bar>Nm\<bar> / (norm k)\<^sup>2 \<le> (\<epsilon> * ((norm k)\<^sup>2 / 2)) / (norm k)\<^sup>2"
      using fin by (intro divide_right_mono) auto
    also have "\<dots> = \<epsilon>/2" using nk2 by (simp add: field_simps)
    also have "\<dots> < \<epsilon>" using \<epsilon> by simp
    finally have "\<bar>Nm\<bar> / (norm k)\<^sup>2 < \<epsilon>" .
    hence "dist (Nm / (norm k)\<^sup>2) 0 < \<epsilon>" by (simp add: dist_real_def)
    thus ?thesis unfolding Nm_def .
  qed
  show "\<forall>\<^sub>F k in at (0::'a). dist ((f (prox f x + k) - f (prox f x)
      - (x - prox f x) \<bullet> k - (k \<bullet> (D' k - k))/2) / (norm k)\<^sup>2) 0 < \<epsilon>"
    unfolding eventually_at using \<delta>3 main by blast
qed

text \<open>The transported form \<open>B = D' - id\<close> inherits symmetry and positive
  semidefiniteness from the resolvent's derivative, so it really is a
  Hessian.\<close>

lemma linear_inj_two_sided_inverse:
  fixes D :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes lD: "linear D" and injD: "inj D"
  shows "\<exists>D'. linear D' \<and> (\<forall>u. D' (D u) = u) \<and> (\<forall>u. D (D' u) = u)"
proof -
  obtain D' where lin': "linear D'" and inv: "D' \<circ> D = id"
    using linear_injective_left_inverse[OF lD injD] by blast
  have left: "D' (D u) = u" for u using inv by (simp add: pointfree_idE)
  have surjD: "surj D"
    by (rule linear_injective_imp_surjective[OF lD injD]) simp
  have right: "D (D' u) = u" for u
  proof -
    obtain b where ub: "u = D b" using surjD unfolding surj_def by blast
    show ?thesis unfolding ub left ..
  qed
  show ?thesis using lin' left right by blast
qed

lemma prox_deriv_symmetric:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f" and D: "(prox f has_derivative D) (at x)"
  shows "u \<bullet> D v = v \<bullet> D u"
proof -
  have "u \<bullet> (v - D v) = v \<bullet> (u - D u)"
    by (rule moreau_hessian_symmetric[OF cvx D])
  thus ?thesis by (simp add: inner_diff_right inner_commute)
qed

lemma transported_form_symmetric:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f" and D: "(prox f has_derivative D) (at x)"
    and right: "\<And>w. D (D' w) = w"
  shows "u \<bullet> (D' v - v) = v \<bullet> (D' u - u)"
proof -
  have "u \<bullet> D' v = D (D' u) \<bullet> D' v" unfolding right ..
  also have "\<dots> = D' v \<bullet> D (D' u)" by (rule inner_commute)
  also have "\<dots> = D' u \<bullet> D (D' v)" by (rule prox_deriv_symmetric[OF cvx D])
  also have "\<dots> = D' u \<bullet> v" unfolding right ..
  also have "\<dots> = v \<bullet> D' u" by (rule inner_commute)
  finally have "u \<bullet> D' v = v \<bullet> D' u" .
  thus ?thesis by (simp add: inner_diff_right inner_commute)
qed

lemma transported_form_psd:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f" and D: "(prox f has_derivative D) (at x)"
    and right: "\<And>w. D (D' w) = w"
  shows "0 \<le> k \<bullet> (D' k - k)"
proof -
  define h where "h = D' k"
  have Dh: "D h = k" unfolding h_def by (rule right)
  have "k \<bullet> (D' k - k) = D h \<bullet> (h - D h)"
    unfolding h_def[symmetric] Dh ..
  also have "\<dots> = h \<bullet> D h - (norm (D h))\<^sup>2"
    by (simp add: inner_diff_right power2_norm_eq_inner inner_commute)
  also have "0 \<le> \<dots>" using prox_deriv_psd[OF cvx D, of h] by simp
  finally show ?thesis by simp
qed

text \<open>Packaging the local statement: at a point where the resolvent is
  differentiable with injective derivative, \<open>f\<close> has a genuine second-order
  expansion at the corresponding proximal point.\<close>

theorem f_alexandrov_at:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
    and D: "(prox f has_derivative D) (at x)"
    and injD: "inj D"
  shows "\<exists>B. bounded_linear B \<and> (\<forall>k. 0 \<le> k \<bullet> B k)
      \<and> (\<forall>u v. u \<bullet> B v = v \<bullet> B u)
      \<and> ((\<lambda>k. (f (prox f x + k) - f (prox f x) - (x - prox f x) \<bullet> k
          - (k \<bullet> B k)/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
proof -
  have lD: "linear D"
    using has_derivative_bounded_linear[OF D] by (rule bounded_linear.linear)
  obtain D' where lin': "linear D'" and left: "\<And>u. D' (D u) = u"
    and right: "\<And>u. D (D' u) = u"
    using linear_inj_two_sided_inverse[OF lD injD] by blast
  have blD': "bounded_linear D'" using lin' by (simp add: linear_conv_bounded_linear)
  have blB: "bounded_linear (\<lambda>u. D' u - u)"
    by (intro bounded_linear_sub bounded_linear_ident blD')
  have psd: "0 \<le> k \<bullet> (D' k - k)" for k
    by (rule transported_form_psd[OF cvx D right])
  have sym: "u \<bullet> (D' v - v) = v \<bullet> (D' u - u)" for u v
    by (rule transported_form_symmetric[OF cvx D right])
  have lim: "((\<lambda>k. (f (prox f x + k) - f (prox f x) - (x - prox f x) \<bullet> k
      - (k \<bullet> (D' k - k))/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    by (rule f_taylor_limit[OF cvx D injD lin' left])
  show ?thesis using blB psd sym lim by blast
qed

text \<open>Two auxiliaries for the measure-theoretic assembly: a non-injective
  linear endomorphism has range of deficient dimension, and an
  almost-everywhere statement for the Borel measure yields a negligible
  exceptional set.\<close>

lemma dim_range_lt_of_not_inj:
  fixes D :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes lD: "linear D" and ninj: "\<not> inj D"
  shows "dim (D ` UNIV) < DIM('a)"
proof -
  have nsurj: "\<not> surj D"
  proof
    assume s: "surj D"
    have "inj D" using lD s by (rule linear_surjective_imp_injective) simp
    with ninj show False ..
  qed
  have sub: "subspace (D ` UNIV)"
    using lD subspace_UNIV by (rule linear_subspace_image)
  have le: "dim (D ` UNIV) \<le> DIM('a)" by (rule dim_subset_UNIV)
  have "dim (D ` UNIV) \<noteq> DIM('a)"
  proof
    assume "dim (D ` UNIV) = DIM('a)"
    hence "span (D ` UNIV) = UNIV" by (simp add: dim_eq_full)
    moreover have "span (D ` UNIV) = D ` UNIV" using sub by simp
    ultimately have "D ` UNIV = UNIV" by simp
    thus False using nsurj by simp
  qed
  with le show ?thesis by simp
qed

lemma AE_lborel_negligible:
  fixes P :: "'a::euclidean_space \<Rightarrow> bool"
  assumes ae: "AE x in lborel. P x"
  shows "negligible {x. \<not> P x}"
proof -
  obtain N where N: "N \<in> null_sets lborel"
    and sub: "{x \<in> space lborel. \<not> P x} \<subseteq> N"
    using ae unfolding eventually_ae_filter by blast
  have "N \<in> null_sets lebesgue" using N by (rule null_sets_completionI)
  hence "negligible N" by (simp add: negligible_iff_null_sets)
  moreover have "{x. \<not> P x} \<subseteq> N" using sub by simp
  ultimately show ?thesis by (rule negligible_subset)
qed

subsection \<open>Alexandrov's theorem\<close>

text \<open>ALEXANDROV'S THEOREM. A finite convex function on a Euclidean space is
  twice differentiable almost everywhere: outside a negligible set every point
  admits a second-order Taylor expansion with a bounded, symmetric, positive
  semidefinite quadratic form.

  The proof runs entirely through the Minty resolvent. Every point \<open>y\<close> is
  \<open>prox f z\<close> for some \<open>z\<close> (surjectivity of \<open>id + subdiff f\<close>), and at every
  \<open>z\<close> where the resolvent is differentiable with injective derivative the
  expansion is available. The exceptional points form two sets: those where
  the resolvent fails to be differentiable, negligible by Rademacher and with
  negligible Lipschitz image; and those where its derivative is singular,
  whose image is negligible by Sard's lemma for the degenerate part.\<close>

theorem convex_alexandrov:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "negligible {y. \<not> (\<exists>p B. bounded_linear B \<and> (\<forall>k. 0 \<le> k \<bullet> B k)
      \<and> (\<forall>u v. u \<bullet> B v = v \<bullet> B u)
      \<and> ((\<lambda>k. (f (y + k) - f y - p \<bullet> k - (k \<bullet> B k)/2) / (norm k)\<^sup>2)
          \<longlongrightarrow> 0) (at 0))}"
proof -
  define Bad where "Bad = {z. \<not> (\<exists>D. (prox f has_derivative D) (at z) \<and> inj D)}"
  define Nd where "Nd = {z :: 'a. \<not> (prox f) differentiable (at z)}"
  define Sg where "Sg = {z :: 'a. (prox f) differentiable (at z)
      \<and> \<not> inj (frechet_derivative (prox f) (at z))}"
  have BadSub: "Bad \<subseteq> Nd \<union> Sg"
  proof
    fix z assume z: "z \<in> Bad"
    show "z \<in> Nd \<union> Sg"
    proof (cases "(prox f) differentiable (at z)")
      case False
      thus ?thesis unfolding Nd_def by simp
    next
      case True
      hence "(prox f has_derivative frechet_derivative (prox f) (at z)) (at z)"
        by (simp add: frechet_derivative_works)
      hence "\<not> inj (frechet_derivative (prox f) (at z))"
        using z unfolding Bad_def by blast
      thus ?thesis unfolding Sg_def using True by simp
    qed
  qed
  have negNd: "negligible Nd"
    unfolding Nd_def by (rule AE_lborel_negligible[OF prox_differentiable_AE[OF cvx]])
  have negNdIm: "negligible (prox f ` Nd)"
  proof (rule negligible_locally_Lipschitz_image[OF order_refl negNd])
    fix z :: 'a assume "z \<in> Nd"
    have "\<forall>w \<in> Nd \<inter> UNIV. norm (prox f w - prox f z) \<le> 1 * norm (w - z)"
      using prox_lipschitz[OF cvx] by blast
    thus "\<exists>T B. open T \<and> z \<in> T
        \<and> (\<forall>w \<in> Nd \<inter> T. norm (prox f w - prox f z) \<le> B * norm (w - z))"
      by blast
  qed
  have negSgIm: "negligible (prox f ` Sg)"
  proof (rule baby_Sard[OF order_refl])
    fix z :: 'a assume z: "z \<in> Sg"
    hence dz: "(prox f has_derivative frechet_derivative (prox f) (at z)) (at z)"
      unfolding Sg_def by (simp add: frechet_derivative_works)
    show "(prox f has_derivative frechet_derivative (prox f) (at z)) (at z within Sg)"
      by (rule has_derivative_at_withinI[OF dz])
    have lz: "linear (frechet_derivative (prox f) (at z))"
      using has_derivative_bounded_linear[OF dz] by (rule bounded_linear.linear)
    have nz: "\<not> inj (frechet_derivative (prox f) (at z))"
      using z unfolding Sg_def by simp
    show "dim (frechet_derivative (prox f) (at z) ` UNIV) < DIM('a)"
      by (rule dim_range_lt_of_not_inj[OF lz nz])
  qed
  have negBadIm: "negligible (prox f ` Bad)"
  proof (rule negligible_subset[of "prox f ` Nd \<union> prox f ` Sg"])
    show "negligible (prox f ` Nd \<union> prox f ` Sg)"
      using negNdIm negSgIm by (rule negligible_Un)
    show "prox f ` Bad \<subseteq> prox f ` Nd \<union> prox f ` Sg"
      using BadSub by (auto simp: image_Un[symmetric])
  qed
  show ?thesis
  proof (rule negligible_subset[OF negBadIm])
    show "{y. \<not> (\<exists>p B. bounded_linear B \<and> (\<forall>k. 0 \<le> k \<bullet> B k)
        \<and> (\<forall>u v. u \<bullet> B v = v \<bullet> B u)
        \<and> ((\<lambda>k. (f (y + k) - f y - p \<bullet> k - (k \<bullet> B k)/2) / (norm k)\<^sup>2)
            \<longlongrightarrow> 0) (at 0))} \<subseteq> prox f ` Bad"
    proof
      fix y :: 'a
      assume "y \<in> {y. \<not> (\<exists>p B. bounded_linear B \<and> (\<forall>k. 0 \<le> k \<bullet> B k)
          \<and> (\<forall>u v. u \<bullet> B v = v \<bullet> B u)
          \<and> ((\<lambda>k. (f (y + k) - f y - p \<bullet> k - (k \<bullet> B k)/2) / (norm k)\<^sup>2)
              \<longlongrightarrow> 0) (at 0))}"
      hence nP: "\<not> (\<exists>p B. bounded_linear B \<and> (\<forall>k. 0 \<le> k \<bullet> B k)
          \<and> (\<forall>u v. u \<bullet> B v = v \<bullet> B u)
          \<and> ((\<lambda>k. (f (y + k) - f y - p \<bullet> k - (k \<bullet> B k)/2) / (norm k)\<^sup>2)
              \<longlongrightarrow> 0) (at 0))" by simp
      obtain q where q: "q \<in> subdiff f y" using subdiff_nonempty[OF cvx] by blast
      have pz: "prox f (y + q) = y" by (rule subdiff_prox[OF cvx q])
      have "y + q \<in> Bad"
      proof (rule ccontr)
        assume "y + q \<notin> Bad"
        then obtain D where D: "(prox f has_derivative D) (at (y + q))" and iD: "inj D"
          unfolding Bad_def by blast
        obtain B where B: "bounded_linear B" "\<forall>k. 0 \<le> k \<bullet> B k"
          "\<forall>u v. u \<bullet> B v = v \<bullet> B u"
          and lim: "((\<lambda>k. (f (prox f (y + q) + k) - f (prox f (y + q))
              - ((y + q) - prox f (y + q)) \<bullet> k - (k \<bullet> B k)/2) / (norm k)\<^sup>2)
              \<longlongrightarrow> 0) (at 0)"
          using f_alexandrov_at[OF cvx D iD] by blast
        have lim': "((\<lambda>k. (f (y + k) - f y - q \<bullet> k - (k \<bullet> B k)/2) / (norm k)\<^sup>2)
            \<longlongrightarrow> 0) (at 0)"
          using lim unfolding pz by simp
        show False using nP B lim' by blast
      qed
      thus "y \<in> prox f ` Bad" using pz by (metis image_eqI)
    qed
  qed
qed

text \<open>The form actually consumed by Crandall-Ishii: a SEMICONVEX function is
  twice differentiable almost everywhere. Subtracting the quadratic shifts the
  gradient by \<open>c *\<^sub>R y\<close> and the Hessian by \<open>c\<close> times the identity, leaving the
  remainder untouched; positive semidefiniteness is of course lost.\<close>

corollary semiconvex_alexandrov:
  fixes u :: "'a::euclidean_space \<Rightarrow> real" and c :: real
  assumes cvx: "convex_on UNIV (\<lambda>x. u x + (c/2) * (norm x)\<^sup>2)"
  shows "negligible {y. \<not> (\<exists>p B. bounded_linear B \<and> (\<forall>v w. v \<bullet> B w = w \<bullet> B v)
      \<and> ((\<lambda>k. (u (y + k) - u y - p \<bullet> k - (k \<bullet> B k)/2) / (norm k)\<^sup>2)
          \<longlongrightarrow> 0) (at 0))}"
proof (rule negligible_subset[OF convex_alexandrov[OF cvx]])
  show "{y. \<not> (\<exists>p B. bounded_linear B \<and> (\<forall>v w. v \<bullet> B w = w \<bullet> B v)
      \<and> ((\<lambda>k. (u (y + k) - u y - p \<bullet> k - (k \<bullet> B k)/2) / (norm k)\<^sup>2)
          \<longlongrightarrow> 0) (at 0))}
    \<subseteq> {y. \<not> (\<exists>p B. bounded_linear B \<and> (\<forall>k. 0 \<le> k \<bullet> B k)
      \<and> (\<forall>v w. v \<bullet> B w = w \<bullet> B v)
      \<and> ((\<lambda>k. (u (y + k) + (c/2) * (norm (y + k))\<^sup>2
          - (u y + (c/2) * (norm y)\<^sup>2) - p \<bullet> k - (k \<bullet> B k)/2) / (norm k)\<^sup>2)
          \<longlongrightarrow> 0) (at 0))}"
  proof (rule subsetI, rule CollectI, rule notI, erule CollectE, erule notE)
    fix y :: 'a
    assume "\<exists>p B. bounded_linear B \<and> (\<forall>k. 0 \<le> k \<bullet> B k)
      \<and> (\<forall>v w. v \<bullet> B w = w \<bullet> B v)
      \<and> ((\<lambda>k. (u (y + k) + (c/2) * (norm (y + k))\<^sup>2
          - (u y + (c/2) * (norm y)\<^sup>2) - p \<bullet> k - (k \<bullet> B k)/2) / (norm k)\<^sup>2)
          \<longlongrightarrow> 0) (at 0)"
    then obtain p B where blB: "bounded_linear B"
      and symB: "\<And>v w. v \<bullet> B w = w \<bullet> B v"
      and lim: "((\<lambda>k. (u (y + k) + (c/2) * (norm (y + k))\<^sup>2
          - (u y + (c/2) * (norm y)\<^sup>2) - p \<bullet> k - (k \<bullet> B k)/2) / (norm k)\<^sup>2)
          \<longlongrightarrow> 0) (at 0)" by blast
    have blB': "bounded_linear (\<lambda>w. B w - c *\<^sub>R w)"
      by (intro bounded_linear_sub blB bounded_linear_scaleR_right)
    have symB': "v \<bullet> (B w - c *\<^sub>R w) = w \<bullet> (B v - c *\<^sub>R v)" for v w
      using symB[of v w] by (simp add: inner_diff_right inner_commute)
    have eq: "(\<lambda>k. (u (y + k) - u y - (p - c *\<^sub>R y) \<bullet> k
            - (k \<bullet> (B k - c *\<^sub>R k))/2) / (norm k)\<^sup>2)
        = (\<lambda>k. (u (y + k) + (c/2) * (norm (y + k))\<^sup>2
            - (u y + (c/2) * (norm y)\<^sup>2) - p \<bullet> k - (k \<bullet> B k)/2) / (norm k)\<^sup>2)"
    proof (rule ext)
      fix k :: 'a
      have sq: "(norm (y + k))\<^sup>2 = (norm y)\<^sup>2 + 2*(y \<bullet> k) + (norm k)\<^sup>2"
        by (simp add: power2_norm_eq_inner inner_add_left inner_add_right
            inner_commute)
      have i1: "(p - c *\<^sub>R y) \<bullet> k = p \<bullet> k - c * (y \<bullet> k)"
        by (simp add: inner_diff_left)
      have i2: "k \<bullet> (B k - c *\<^sub>R k) = k \<bullet> B k - c * (norm k)\<^sup>2"
        by (simp add: inner_diff_right power2_norm_eq_inner)
      have num: "u (y + k) - u y - (p - c *\<^sub>R y) \<bullet> k
            - (k \<bullet> (B k - c *\<^sub>R k))/2
          = u (y + k) + (c/2) * (norm (y + k))\<^sup>2
            - (u y + (c/2) * (norm y)\<^sup>2) - p \<bullet> k - (k \<bullet> B k)/2"
        unfolding sq i1 i2 by argo
      show "(u (y + k) - u y - (p - c *\<^sub>R y) \<bullet> k
            - (k \<bullet> (B k - c *\<^sub>R k))/2) / (norm k)\<^sup>2
          = (u (y + k) + (c/2) * (norm (y + k))\<^sup>2
            - (u y + (c/2) * (norm y)\<^sup>2) - p \<bullet> k - (k \<bullet> B k)/2) / (norm k)\<^sup>2"
        unfolding num ..
    qed
    have "((\<lambda>k. (u (y + k) - u y - (p - c *\<^sub>R y) \<bullet> k
        - (k \<bullet> (B k - c *\<^sub>R k))/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
      unfolding eq by (rule lim)
    thus "\<exists>p B. bounded_linear B \<and> (\<forall>v w. v \<bullet> B w = w \<bullet> B v)
        \<and> ((\<lambda>k. (u (y + k) - u y - p \<bullet> k - (k \<bullet> B k)/2) / (norm k)\<^sup>2)
            \<longlongrightarrow> 0) (at 0)"
      using blB' symB' by blast
  qed
qed

subsection \<open>Towards Jensen's lemma\<close>

text \<open>The first ingredient: if the maximum at the centre beats the boundary by
  more than the linear perturbation can recover, then every maximiser of the
  perturbed function is INTERIOR, so a first-order condition is available
  there.\<close>

lemma perturbed_maximiser_interior:
  fixes \<phi> :: "'a::euclidean_space \<Rightarrow> real"
  assumes r: "0 < r"
    and bnd: "\<And>y. y \<in> sphere \<xi> r \<Longrightarrow> \<phi> y \<le> m"
    and d0: "0 \<le> d" and small: "2 * d * r < \<phi> \<xi> - m"
    and p: "norm p \<le> d"
    and xin: "x \<in> cball \<xi> r"
    and xmax: "\<And>y. y \<in> cball \<xi> r \<Longrightarrow> \<phi> y + p \<bullet> y \<le> \<phi> x + p \<bullet> x"
  shows "x \<in> ball \<xi> r"
proof (rule ccontr)
  assume "x \<notin> ball \<xi> r"
  hence "r \<le> dist x \<xi>" by (simp add: dist_commute)
  moreover have "dist x \<xi> \<le> r" using xin by (simp add: dist_commute)
  ultimately have dxr: "dist x \<xi> = r" by simp
  hence "x \<in> sphere \<xi> r" by (simp add: dist_commute)
  hence phix: "\<phi> x \<le> m" by (rule bnd)
  have "\<xi> \<in> cball \<xi> r" using r by simp
  hence "\<phi> \<xi> + p \<bullet> \<xi> \<le> \<phi> x + p \<bullet> x" by (rule xmax)
  hence step: "\<phi> \<xi> - \<phi> x \<le> p \<bullet> (x - \<xi>)" by (simp add: inner_diff_right)
  have "p \<bullet> (x - \<xi>) \<le> norm p * norm (x - \<xi>)"
    using Cauchy_Schwarz_ineq2[of p "x - \<xi>"] by linarith
  also have "\<dots> = norm p * r" using dxr by (simp add: dist_norm)
  also have "\<dots> \<le> d * r" using p r by (intro mult_right_mono) auto
  finally have "\<phi> \<xi> - \<phi> x \<le> d * r" using step by linarith
  moreover have "\<phi> \<xi> - m \<le> \<phi> \<xi> - \<phi> x" using phix by simp
  ultimately have "\<phi> \<xi> - m \<le> d * r" by linarith
  hence "2 * d * r < d * r" using small by linarith
  hence "d * r < 0" by linarith
  moreover have "0 \<le> d * r" using d0 r by simp
  ultimately show False by linarith
qed

lemma le_of_le_plus_small:
  fixes a b e t0 :: real
  assumes t0: "0 < t0" and h: "\<And>t. 0 < t \<Longrightarrow> t < t0 \<Longrightarrow> a \<le> b + e * t"
  shows "a \<le> b"
proof -
  have "((\<lambda>t. b + e * t) \<longlongrightarrow> b + e * 0) (at_right (0::real))"
    by (intro tendsto_intros)
  hence lim: "((\<lambda>t. b + e * t) \<longlongrightarrow> b) (at_right (0::real))" by simp
  have ev: "\<forall>\<^sub>F t in at_right (0::real). a \<le> b + e * t"
  proof (rule eventually_mono[OF eventually_at_right_real[OF t0]])
    fix t :: real assume "t \<in> {0<..<t0}"
    thus "a \<le> b + e * t" using h by simp
  qed
  show ?thesis
    by (rule tendsto_lowerbound[OF lim ev]) (simp add: trivial_limit_at_right_real)
qed

text \<open>The second ingredient, and the reason the Minty resolvent keeps paying
  off: at an INTERIOR maximiser of \<open>\<phi> + p \<cdot> (-)\<close> the convexified function
  \<open>\<psi> = \<phi> + (c/2) * (norm -)\<^sup>2\<close> has the EXPLICIT subgradient \<open>c *\<^sub>R x - p\<close>. No
  differentiability of \<open>\<phi>\<close> is needed: the subdifferential of \<open>\<psi>\<close> is nonempty
  by convexity, and the maximality forces its (unique) element.\<close>

lemma interior_max_subdiff_unique:
  fixes \<phi> :: "'a::euclidean_space \<Rightarrow> real"
  assumes x: "x \<in> ball \<xi> r"
    and xmax: "\<And>y. y \<in> cball \<xi> r \<Longrightarrow> \<phi> y + p \<bullet> y \<le> \<phi> x + p \<bullet> x"
    and q: "q \<in> subdiff (\<lambda>z. \<phi> z + (c/2) * (norm z)\<^sup>2) x"
  shows "q = c *\<^sub>R x - p"
proof -
  have key: "q \<bullet> v \<le> (c *\<^sub>R x - p) \<bullet> v" for v
  proof -
    define t0 where "t0 = (r - dist x \<xi>) / (norm v + 1)"
    have nvpos: "0 < norm v + 1"
      by (rule add_nonneg_pos[OF norm_ge_zero zero_less_one])
    have rx: "0 < r - dist x \<xi>" using x by (simp add: dist_commute)
    have t0pos: "0 < t0"
      unfolding t0_def by (rule divide_pos_pos[OF rx nvpos])
    have inball: "x + t *\<^sub>R v \<in> cball \<xi> r" if t: "0 < t" "t < t0" for t
    proof -
      have "dist (x + t *\<^sub>R v) \<xi> = norm ((x - \<xi>) + t *\<^sub>R v)"
        by (simp add: dist_norm algebra_simps)
      also have "\<dots> \<le> norm (x - \<xi>) + norm (t *\<^sub>R v)" by (rule norm_triangle_ineq)
      also have "\<dots> = dist x \<xi> + t * norm v" using t by (simp add: dist_norm)
      also have "\<dots> \<le> r"
      proof -
        have "t * norm v \<le> t * (norm v + 1)" using t by simp
        also have "\<dots> < t0 * (norm v + 1)"
          by (rule mult_strict_right_mono[OF t(2) nvpos])
        also have "\<dots> = r - dist x \<xi>" unfolding t0_def using nvpos by simp
        finally show ?thesis by simp
      qed
      finally show ?thesis by (simp add: dist_commute)
    qed
    have ineq: "q \<bullet> v \<le> (c *\<^sub>R x - p) \<bullet> v + ((c/2) * (norm v)\<^sup>2) * t"
      if t: "0 < t" "t < t0" for t
    proof -
      have "(\<phi> x + (c/2) * (norm x)\<^sup>2) + q \<bullet> ((x + t *\<^sub>R v) - x)
          \<le> \<phi> (x + t *\<^sub>R v) + (c/2) * (norm (x + t *\<^sub>R v))\<^sup>2"
        by (rule subdiffD[OF q])
      hence sd: "t * (q \<bullet> v)
          \<le> (\<phi> (x + t *\<^sub>R v) - \<phi> x)
            + (c/2) * ((norm (x + t *\<^sub>R v))\<^sup>2 - (norm x)\<^sup>2)"
        by (simp add: algebra_simps)
      have "\<phi> (x + t *\<^sub>R v) + p \<bullet> (x + t *\<^sub>R v) \<le> \<phi> x + p \<bullet> x"
        by (rule xmax[OF inball[OF t]])
      hence mx: "\<phi> (x + t *\<^sub>R v) - \<phi> x \<le> - (t * (p \<bullet> v))"
        by (simp add: inner_add_right algebra_simps)
      have sq: "(norm (x + t *\<^sub>R v))\<^sup>2 - (norm x)\<^sup>2
          = 2*t*(x \<bullet> v) + t\<^sup>2 * (norm v)\<^sup>2"
      proof -
        have e1: "(norm (x + t *\<^sub>R v))\<^sup>2 = (x + t *\<^sub>R v) \<bullet> (x + t *\<^sub>R v)"
          by (rule power2_norm_eq_inner)
        have e2: "(norm x)\<^sup>2 = x \<bullet> x" by (rule power2_norm_eq_inner)
        have e3: "(norm v)\<^sup>2 = v \<bullet> v" by (rule power2_norm_eq_inner)
        have e4: "(x + t *\<^sub>R v) \<bullet> (x + t *\<^sub>R v)
            = x \<bullet> x + 2*t*(x \<bullet> v) + (t*t)*(v \<bullet> v)"
          by (simp add: inner_add_left inner_add_right inner_commute
              algebra_simps)
        show ?thesis unfolding e1 e4 e2 e3 by (simp add: power2_eq_square)
      qed
      have "t * (q \<bullet> v)
          \<le> - (t * (p \<bullet> v)) + (c/2) * (2*t*(x \<bullet> v) + t\<^sup>2 * (norm v)\<^sup>2)"
        using sd mx unfolding sq by linarith
      also have "\<dots> = t * ((c *\<^sub>R x - p) \<bullet> v + ((c/2) * (norm v)\<^sup>2) * t)"
        by (simp add: inner_diff_left power2_eq_square algebra_simps)
      finally show ?thesis using t by simp
    qed
    show ?thesis by (rule le_of_le_plus_small[OF t0pos ineq])
  qed
  have eq: "q \<bullet> v = (c *\<^sub>R x - p) \<bullet> v" for v
  proof -
    have "q \<bullet> v \<le> (c *\<^sub>R x - p) \<bullet> v" by (rule key)
    moreover have "q \<bullet> (- v) \<le> (c *\<^sub>R x - p) \<bullet> (- v)" by (rule key)
    ultimately show ?thesis by simp
  qed
  have "(q - (c *\<^sub>R x - p)) \<bullet> (q - (c *\<^sub>R x - p)) = 0"
    using eq[of "q - (c *\<^sub>R x - p)"] by (simp add: inner_diff_left)
  thus ?thesis by simp
qed

lemma interior_max_subdiff:
  fixes \<phi> :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV (\<lambda>z. \<phi> z + (c/2) * (norm z)\<^sup>2)"
    and x: "x \<in> ball \<xi> r"
    and xmax: "\<And>y. y \<in> cball \<xi> r \<Longrightarrow> \<phi> y + p \<bullet> y \<le> \<phi> x + p \<bullet> x"
  shows "c *\<^sub>R x - p \<in> subdiff (\<lambda>z. \<phi> z + (c/2) * (norm z)\<^sup>2) x"
proof -
  obtain q where q: "q \<in> subdiff (\<lambda>z. \<phi> z + (c/2) * (norm z)\<^sup>2) x"
    using subdiff_nonempty[OF cvx] by blast
  have "q = c *\<^sub>R x - p" by (rule interior_max_subdiff_unique[OF x xmax q])
  with q show ?thesis by simp
qed

text \<open>The third ingredient. At a maximiser of \<open>\<phi> + p \<cdot> (-)\<close> the convexified
  \<open>\<psi>\<close> also satisfies the REVERSE (semiconcavity) inequality with the very same
  vector \<open>c *\<^sub>R x - p\<close>. Together with convexity this pins the Bregman
  divergence of \<open>\<psi>\<close> at \<open>x\<close> between \<open>0\<close> and \<open>(c/2) * (norm (z - x))\<^sup>2\<close>, which is
  exactly the two-sided bound that forces the resolvent's derivative into
  \<open>[1/(1+c), 1]\<close>.\<close>

lemma max_semiconcave_bound:
  fixes \<phi> :: "'a::euclidean_space \<Rightarrow> real"
  assumes xmax: "\<And>y. y \<in> cball \<xi> r \<Longrightarrow> \<phi> y + p \<bullet> y \<le> \<phi> x + p \<bullet> x"
    and z: "z \<in> cball \<xi> r"
  shows "(\<phi> z + (c/2) * (norm z)\<^sup>2) - (\<phi> x + (c/2) * (norm x)\<^sup>2)
       \<le> (c *\<^sub>R x - p) \<bullet> (z - x) + (c/2) * (norm (z - x))\<^sup>2"
proof -
  have mx: "\<phi> z - \<phi> x \<le> - (p \<bullet> (z - x))"
    using xmax[OF z] by (simp add: inner_diff_right)
  have sq: "(norm z)\<^sup>2 - (norm x)\<^sup>2 = 2 * (x \<bullet> (z - x)) + (norm (z - x))\<^sup>2"
  proof -
    have e0: "z = x + (z - x)" by simp
    have e1: "(norm z)\<^sup>2 = z \<bullet> z" by (rule power2_norm_eq_inner)
    have e2: "(norm x)\<^sup>2 = x \<bullet> x" by (rule power2_norm_eq_inner)
    have e3: "(norm (z - x))\<^sup>2 = (z - x) \<bullet> (z - x)" by (rule power2_norm_eq_inner)
    have e4: "z \<bullet> z = x \<bullet> x + 2 * (x \<bullet> (z - x)) + (z - x) \<bullet> (z - x)"
      by (simp add: inner_diff_left inner_diff_right inner_commute algebra_simps)
    show ?thesis unfolding e1 e2 e3 e4 by simp
  qed
  have lin: "(c *\<^sub>R x - p) \<bullet> (z - x) = c * (x \<bullet> (z - x)) - p \<bullet> (z - x)"
    by (simp add: inner_diff_left)
  have half: "(c/2) * (norm z)\<^sup>2 - (c/2) * (norm x)\<^sup>2
      = c * (x \<bullet> (z - x)) + (c/2) * (norm (z - x))\<^sup>2"
  proof -
    have "(c/2) * (norm z)\<^sup>2 - (c/2) * (norm x)\<^sup>2
        = (c/2) * ((norm z)\<^sup>2 - (norm x)\<^sup>2)" by (simp add: algebra_simps)
    also have "\<dots> = (c/2) * (2 * (x \<bullet> (z - x)) + (norm (z - x))\<^sup>2)"
      unfolding sq ..
    also have "\<dots> = c * (x \<bullet> (z - x)) + (c/2) * (norm (z - x))\<^sup>2"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  show ?thesis unfolding lin using mx half by argo
qed

text \<open>A UNIFORM interiority margin. Bounding \<open>\<phi>\<close> on the whole annulus
  \<open>\<rho> \<le> dist y \<xi> \<le> r\<close> rather than only on the sphere puts every maximiser
  strictly inside \<open>ball \<xi> \<rho>\<close>, so all maximisers keep a common distance
  \<open>r - \<rho>\<close> from the boundary. That margin is what makes the co-coercivity
  argument below localisable.\<close>

lemma perturbed_maximiser_deep_interior:
  fixes \<phi> :: "'a::euclidean_space \<Rightarrow> real"
  assumes bnd: "\<And>y. y \<in> cball \<xi> r \<Longrightarrow> \<rho> \<le> dist y \<xi> \<Longrightarrow> \<phi> y \<le> m"
    and r: "0 < r" and d0: "0 \<le> d" and small: "2 * d * r < \<phi> \<xi> - m"
    and p: "norm p \<le> d"
    and xin: "x \<in> cball \<xi> r"
    and xmax: "\<And>y. y \<in> cball \<xi> r \<Longrightarrow> \<phi> y + p \<bullet> y \<le> \<phi> x + p \<bullet> x"
  shows "dist x \<xi> < \<rho>"
proof (rule ccontr)
  assume "\<not> dist x \<xi> < \<rho>"
  hence phix: "\<phi> x \<le> m" using bnd[OF xin] by simp
  have "\<xi> \<in> cball \<xi> r" using r by simp
  hence "\<phi> \<xi> + p \<bullet> \<xi> \<le> \<phi> x + p \<bullet> x" by (rule xmax)
  hence step: "\<phi> \<xi> - \<phi> x \<le> p \<bullet> (x - \<xi>)" by (simp add: inner_diff_right)
  have "p \<bullet> (x - \<xi>) \<le> norm p * norm (x - \<xi>)"
    using Cauchy_Schwarz_ineq2[of p "x - \<xi>"] by linarith
  also have "\<dots> \<le> d * r"
  proof (rule mult_mono)
    show "norm p \<le> d" by (rule p)
    show "norm (x - \<xi>) \<le> r" using xin by (simp add: dist_norm norm_minus_commute)
  qed (use d0 in auto)
  finally have "\<phi> \<xi> - \<phi> x \<le> d * r" using step by linarith
  moreover have "\<phi> \<xi> - m \<le> \<phi> \<xi> - \<phi> x" using phix by simp
  ultimately have "\<phi> \<xi> - m \<le> d * r" by linarith
  hence "d * r < 0" using small by linarith
  moreover have "0 \<le> d * r" using d0 r by simp
  ultimately show False by linarith
qed

text \<open>CO-COERCIVITY, in the localised form. If \<open>\<psi>\<close> is convex and admits at
  \<open>x\<close> the semiconcave upper bound with vector \<open>q\<close> on \<open>cball \<xi> r\<close>, then for
  ANY step \<open>s\<close> with \<open>s * c \<le> 1\<close> whose test point stays in the ball,
  \<open>(s/2) * norm (q - q')\<^sup>2\<close> is dominated by the Bregman divergence. The
  textbook takes the optimal \<open>s = 1/c\<close>; allowing a smaller \<open>s\<close> is exactly what
  lets the test point be kept inside \<open>cball \<xi> r\<close>.\<close>

lemma bregman_cocoercive_step:
  fixes \<psi> :: "'a::euclidean_space \<Rightarrow> real"
  assumes q': "q' \<in> subdiff \<psi> x'"
    and ub: "\<And>y. y \<in> cball \<xi> r
        \<Longrightarrow> \<psi> y \<le> \<psi> x + q \<bullet> (y - x) + (c/2) * (norm (y - x))\<^sup>2"
    and s: "0 < s" "s * c \<le> 1"
    and mem: "x - s *\<^sub>R (q - q') \<in> cball \<xi> r"
  shows "(s/2) * (norm (q - q'))\<^sup>2 \<le> \<psi> x - \<psi> x' - q' \<bullet> (x - x')"
proof -
  define w where "w = q - q'"
  define y where "y = x - s *\<^sub>R w"
  have ymem: "y \<in> cball \<xi> r" unfolding y_def w_def by (rule mem)
  have yx: "y - x = - (s *\<^sub>R w)" unfolding y_def by simp
  have nyx: "(norm (y - x))\<^sup>2 = s\<^sup>2 * (norm w)\<^sup>2"
    unfolding yx using s by (simp add: power_mult_distrib)
  have qy: "q \<bullet> (y - x) = - (s * (q \<bullet> w))"
    unfolding yx by simp
  have up: "\<psi> y \<le> \<psi> x - s * (q \<bullet> w) + (c/2) * (s\<^sup>2 * (norm w)\<^sup>2)"
    using ub[OF ymem] unfolding qy nyx by simp
  have low: "\<psi> x' + q' \<bullet> (y - x') \<le> \<psi> y" by (rule subdiffD[OF q'])
  have split: "q' \<bullet> (y - x') = q' \<bullet> (x - x') - s * (q' \<bullet> w)"
    unfolding y_def by (simp add: inner_diff_right algebra_simps)
  have qq: "q \<bullet> w - q' \<bullet> w = (norm w)\<^sup>2"
    unfolding w_def[symmetric]
    by (simp add: w_def inner_diff_left[symmetric] power2_norm_eq_inner)
  have main: "s * (norm w)\<^sup>2
      \<le> (\<psi> x - \<psi> x' - q' \<bullet> (x - x')) + (c/2) * (s\<^sup>2 * (norm w)\<^sup>2)"
    using up low unfolding split by (simp add: algebra_simps qq[symmetric])
  have Wnn: "0 \<le> (norm w)\<^sup>2" by simp
  have shrink: "(c/2) * (s\<^sup>2 * (norm w)\<^sup>2) \<le> (s * (norm w)\<^sup>2)/2"
  proof -
    have "(c/2) * (s\<^sup>2 * (norm w)\<^sup>2) = ((s * (norm w)\<^sup>2)/2) * (s * c)"
      by (simp add: power2_eq_square algebra_simps)
    also have "\<dots> \<le> ((s * (norm w)\<^sup>2)/2) * 1"
    proof (rule mult_left_mono[OF s(2)])
      show "0 \<le> (s * (norm w)\<^sup>2)/2" using s(1) Wnn by simp
    qed
    finally show ?thesis by simp
  qed
  have half: "(s/2) * (norm w)\<^sup>2 = (s * (norm w)\<^sup>2)/2" by simp
  show ?thesis unfolding w_def[symmetric] half using main shrink by linarith
qed

text \<open>The REVERSE BAILLON-HADDAD implication, localised: adding the two
  co-coercivity estimates makes the Bregman divergences collapse into
  \<open>(q - q') \<cdot> (x - x')\<close>, and Cauchy-Schwarz then bounds \<open>norm (q - q')\<close> by
  \<open>norm (x - x') / s\<close>. So a convex function that is also \<open>c\<close>-semiconcave on a
  ball has a LIPSCHITZ selection of subgradients there.\<close>

lemma subdiff_lipschitz_of_semiconcave:
  fixes \<psi> :: "'a::euclidean_space \<Rightarrow> real"
  assumes q: "q \<in> subdiff \<psi> x" and q': "q' \<in> subdiff \<psi> x'"
    and ubx: "\<And>y. y \<in> cball \<xi> r
        \<Longrightarrow> \<psi> y \<le> \<psi> x + q \<bullet> (y - x) + (c/2) * (norm (y - x))\<^sup>2"
    and ubx': "\<And>y. y \<in> cball \<xi> r
        \<Longrightarrow> \<psi> y \<le> \<psi> x' + q' \<bullet> (y - x') + (c/2) * (norm (y - x'))\<^sup>2"
    and s: "0 < s" "s * c \<le> 1"
    and mem1: "x - s *\<^sub>R (q - q') \<in> cball \<xi> r"
    and mem2: "x' - s *\<^sub>R (q' - q) \<in> cball \<xi> r"
  shows "s * norm (q - q') \<le> norm (x - x')"
proof -
  have A: "(s/2) * (norm (q - q'))\<^sup>2 \<le> \<psi> x - \<psi> x' - q' \<bullet> (x - x')"
    by (rule bregman_cocoercive_step[OF q' ubx s(1) s(2) mem1])
  have B: "(s/2) * (norm (q' - q))\<^sup>2 \<le> \<psi> x' - \<psi> x - q \<bullet> (x' - x)"
    by (rule bregman_cocoercive_step[OF q ubx' s(1) s(2) mem2])
  have nq: "norm (q' - q) = norm (q - q')" by (rule norm_minus_commute)
  have coll: "- (q' \<bullet> (x - x')) - q \<bullet> (x' - x) = (q - q') \<bullet> (x - x')"
    by (simp add: inner_diff_left inner_diff_right)
  have sum: "s * (norm (q - q'))\<^sup>2 \<le> (q - q') \<bullet> (x - x')"
    using A B unfolding nq coll[symmetric] by argo
  have cs: "(q - q') \<bullet> (x - x') \<le> norm (q - q') * norm (x - x')"
    using Cauchy_Schwarz_ineq2[of "q - q'" "x - x'"] by linarith
  have key: "s * (norm (q - q'))\<^sup>2 \<le> norm (q - q') * norm (x - x')"
    using sum cs by linarith
  show ?thesis
  proof (cases "q = q'")
    case True
    thus ?thesis by simp
  next
    case False
    hence pos: "0 < norm (q - q')" by simp
    have "(s * norm (q - q')) * norm (q - q')
        \<le> norm (x - x') * norm (q - q')"
      using key by (simp add: power2_eq_square algebra_simps)
    thus ?thesis using pos by (simp add: mult_le_cancel_right)
  qed
qed

text \<open>Routine set-up for Jensen's lemma: a semiconvex function is continuous
  (subtract the quadratic from the continuous convex \<open>\<psi>\<close>), hence the perturbed
  function attains its maximum on the compact ball; and a ball of positive
  radius is not negligible, which is the contradiction the argument runs
  into.\<close>

lemma semiconvex_continuous:
  fixes \<phi> :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV (\<lambda>z. \<phi> z + (c/2) * (norm z)\<^sup>2)"
  shows "continuous_on S \<phi>"
proof -
  have c1: "continuous_on UNIV (\<lambda>z. \<phi> z + (c/2) * (norm z)\<^sup>2)"
    by (rule convex_on_continuous[OF open_UNIV cvx])
  have c2: "continuous_on UNIV (\<lambda>z::'a. (c/2) * (norm z)\<^sup>2)"
    by (intro continuous_intros)
  have "continuous_on UNIV (\<lambda>z. (\<phi> z + (c/2) * (norm z)\<^sup>2) - (c/2) * (norm z)\<^sup>2)"
    by (rule continuous_on_diff[OF c1 c2])
  hence "continuous_on UNIV \<phi>" by simp
  thus ?thesis by (rule continuous_on_subset) simp
qed

lemma semiconvex_max_exists:
  fixes \<phi> :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV (\<lambda>z. \<phi> z + (c/2) * (norm z)\<^sup>2)"
    and r: "0 \<le> r"
  shows "\<exists>x \<in> cball \<xi> r. \<forall>y \<in> cball \<xi> r. \<phi> y + p \<bullet> y \<le> \<phi> x + p \<bullet> x"
proof (rule continuous_attains_sup)
  show "compact (cball \<xi> r)" by (rule compact_cball)
  show "cball \<xi> r \<noteq> {}" using r by auto
  show "continuous_on (cball \<xi> r) (\<lambda>y. \<phi> y + p \<bullet> y)"
    by (intro continuous_intros semiconvex_continuous[OF cvx])
qed

lemma not_negligible_cball:
  fixes d :: real
  assumes d: "0 < d"
  shows "\<not> negligible (cball (0::'a::euclidean_space) d)"
proof -
  have "\<not> negligible (ball (0::'a) d)"
    using d by (intro open_not_negligible) auto
  moreover have "ball (0::'a) d \<subseteq> cball 0 d" by (rule ball_subset_cball)
  ultimately show ?thesis using negligible_subset by blast
qed

text \<open>JENSEN'S LEMMA. For a semiconvex \<open>\<phi>\<close> whose maximum over \<open>cball \<xi> r\<close> at
  the centre beats the surrounding annulus by more than the perturbation can
  recover, the set of points that maximise SOME small linear perturbation of
  \<open>\<phi>\<close> is NOT negligible.

  The usual proof estimates the measure from below by a Jacobian determinant,
  which would need Hadamard's inequality or a spectral theorem, neither of
  which is available in this HOL-Analysis. Only positivity is ever used
  downstream, and positivity needs no determinants at all: the map
  \<open>P x = c *\<^sub>R x - grad \<psi> x\<close> is a genuine function on \<open>K\<close> (its subdifferential
  is a singleton there, by \<open>interior_max_subdiff_unique\<close>), it is LIPSCHITZ
  there (by \<open>subdiff_lipschitz_of_semiconcave\<close>, localised using the uniform
  interiority margin), and it maps \<open>K\<close> ONTO \<open>cball 0 d\<close>. A negligible \<open>K\<close>
  would therefore have negligible image, yet that image contains a ball.\<close>

theorem jensen_lemma:
  fixes \<phi> :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV (\<lambda>z. \<phi> z + (c/2) * (norm z)\<^sup>2)"
    and c: "0 < c"
    and rho: "0 < \<rho>" "\<rho> < r"
    and bnd: "\<And>y. y \<in> cball \<xi> r \<Longrightarrow> \<rho> \<le> dist y \<xi> \<Longrightarrow> \<phi> y \<le> m"
    and d: "0 < d" and small: "2 * d * r < \<phi> \<xi> - m"
  shows "\<not> negligible {x \<in> cball \<xi> r. \<exists>p. norm p \<le> d
      \<and> (\<forall>y \<in> cball \<xi> r. \<phi> y + p \<bullet> y \<le> \<phi> x + p \<bullet> x)}"
proof -
  have r: "0 < r" using rho by simp
  define \<psi> where "\<psi> = (\<lambda>z::'a. \<phi> z + (c/2) * (norm z)\<^sup>2)"
  have cvx': "convex_on UNIV \<psi>" unfolding \<psi>_def by (rule cvx)
  define K where "K = {x \<in> cball \<xi> r. \<exists>p. norm p \<le> d
      \<and> (\<forall>y \<in> cball \<xi> r. \<phi> y + p \<bullet> y \<le> \<phi> x + p \<bullet> x)}"
  define Q where "Q = (\<lambda>x. SOME q. q \<in> subdiff \<psi> x)"
  define P where "P = (\<lambda>x. c *\<^sub>R x - Q x)"
  have Qsub: "Q x \<in> subdiff \<psi> x" for x
  proof -
    have "\<exists>q. q \<in> subdiff \<psi> x" using subdiff_nonempty[OF cvx'] by blast
    thus ?thesis unfolding Q_def by (rule someI_ex)
  qed
  have deepK: "dist x \<xi> < \<rho>"
    if xin: "x \<in> cball \<xi> r" and np: "norm p \<le> d"
      and xmax: "\<And>y. y \<in> cball \<xi> r \<Longrightarrow> \<phi> y + p \<bullet> y \<le> \<phi> x + p \<bullet> x"
    for x p
    by (rule perturbed_maximiser_deep_interior[OF bnd r less_imp_le[OF d]
        small np xin xmax])
  have QK: "Q x = c *\<^sub>R x - p"
    if xin: "x \<in> cball \<xi> r" and np: "norm p \<le> d"
      and xmax: "\<And>y. y \<in> cball \<xi> r \<Longrightarrow> \<phi> y + p \<bullet> y \<le> \<phi> x + p \<bullet> x"
    for x p
  proof -
    have "dist x \<xi> < \<rho>" by (rule deepK[OF xin np xmax])
    hence xball: "x \<in> ball \<xi> r" using rho by (simp add: dist_commute)
    show ?thesis
      by (rule interior_max_subdiff_unique[OF xball xmax
          Qsub[of x, unfolded \<psi>_def]])
  qed
  have PK: "P x = p"
    if xin: "x \<in> cball \<xi> r" and np: "norm p \<le> d"
      and xmax: "\<And>y. y \<in> cball \<xi> r \<Longrightarrow> \<phi> y + p \<bullet> y \<le> \<phi> x + p \<bullet> x"
    for x p
  proof -
    have Qx: "Q x = c *\<^sub>R x - p" by (rule QK[OF xin np xmax])
    have "P x = c *\<^sub>R x - Q x" by (simp add: P_def)
    thus ?thesis using Qx by simp
  qed
  have ub: "\<psi> y \<le> \<psi> x + Q x \<bullet> (y - x) + (c/2) * (norm (y - x))\<^sup>2"
    if ymem: "y \<in> cball \<xi> r" and xin: "x \<in> cball \<xi> r" and np: "norm p \<le> d"
      and xmax: "\<And>z. z \<in> cball \<xi> r \<Longrightarrow> \<phi> z + p \<bullet> z \<le> \<phi> x + p \<bullet> x"
    for x y p
  proof -
    have Qx: "Q x = c *\<^sub>R x - p" by (rule QK[OF xin np xmax])
    have "\<psi> y - \<psi> x \<le> (c *\<^sub>R x - p) \<bullet> (y - x) + (c/2) * (norm (y - x))\<^sup>2"
      unfolding \<psi>_def by (rule max_semiconcave_bound[OF xmax ymem])
    thus ?thesis using Qx by simp
  qed
  define Qb where "Qb = c * (norm \<xi> + r) + d"
  have Qbnn: "0 \<le> Qb"
  proof -
    have n1: "0 \<le> norm \<xi> + r"
      by (rule add_nonneg_nonneg[OF norm_ge_zero less_imp_le[OF r]])
    have "0 \<le> c * (norm \<xi> + r)"
      by (rule mult_nonneg_nonneg[OF less_imp_le[OF c] n1])
    thus ?thesis unfolding Qb_def using d by linarith
  qed
  have Qbound: "norm (Q x) \<le> Qb" if xK: "x \<in> K" for x
  proof -
    from xK obtain p where np: "norm p \<le> d" and xin: "x \<in> cball \<xi> r"
      and xmax: "\<And>y. y \<in> cball \<xi> r \<Longrightarrow> \<phi> y + p \<bullet> y \<le> \<phi> x + p \<bullet> x"
      unfolding K_def by blast
    have nx: "norm x \<le> norm \<xi> + r"
    proof -
      have "norm x \<le> norm \<xi> + norm (x - \<xi>)" by (rule norm_triangle_sub)
      moreover have "norm (x - \<xi>) \<le> r"
        using xin by (simp add: dist_norm norm_minus_commute)
      ultimately show ?thesis by simp
    qed
    have Qx: "Q x = c *\<^sub>R x - p" by (rule QK[OF xin np xmax])
    have b1: "norm (c *\<^sub>R x) \<le> c * (norm \<xi> + r)" using nx c by simp
    have b2: "norm (c *\<^sub>R x - p) \<le> norm (c *\<^sub>R x) + norm p"
      by (rule norm_triangle_ineq4)
    show ?thesis unfolding Qb_def using b1 b2 np Qx by simp
  qed
  define s where "s = min (1/c) ((r - \<rho>)/(2*Qb + 1))"
  have pos1: "0 < 2*Qb + 1" using Qbnn by simp
  have s0: "0 < s" unfolding s_def using c rho pos1 by simp
  have sc: "s * c \<le> 1"
  proof -
    have "s \<le> 1/c" unfolding s_def by simp
    thus ?thesis using c by (simp add: field_simps)
  qed
  have sQ: "s * (2*Qb) < r - \<rho>"
  proof -
    have le: "s \<le> (r - \<rho>)/(2*Qb + 1)" unfolding s_def by simp
    have "s * (2*Qb) \<le> ((r - \<rho>)/(2*Qb + 1)) * (2*Qb)"
      using le Qbnn by (intro mult_right_mono) auto
    also have "\<dots> < ((r - \<rho>)/(2*Qb + 1)) * (2*Qb + 1)"
      using rho pos1 by (intro mult_strict_left_mono) auto
    also have "\<dots> = r - \<rho>" using pos1 by simp
    finally show ?thesis .
  qed
  have mem: "z - s *\<^sub>R w \<in> cball \<xi> r"
    if dz: "dist z \<xi> < \<rho>" and nw: "norm w \<le> 2*Qb" for z w
  proof -
    have "dist (z - s *\<^sub>R w) \<xi> = norm ((z - \<xi>) - s *\<^sub>R w)"
      by (simp add: dist_norm algebra_simps)
    also have "\<dots> \<le> norm (z - \<xi>) + norm (s *\<^sub>R w)" by (rule norm_triangle_ineq4)
    also have "\<dots> = dist z \<xi> + s * norm w"
      using s0 by (simp add: dist_norm)
    also have "\<dots> \<le> dist z \<xi> + s * (2*Qb)"
      using nw s0 by (intro add_left_mono mult_left_mono) auto
    also have "\<dots> < \<rho> + (r - \<rho>)" using dz sQ by linarith
    finally show ?thesis by (simp add: dist_commute)
  qed
  have lip: "norm (P x - P x') \<le> (c + 1/s) * norm (x - x')"
    if kx: "x \<in> K" and kx': "x' \<in> K" for x x'
  proof -
    from kx obtain p where np: "norm p \<le> d" and xin: "x \<in> cball \<xi> r"
      and xmax: "\<And>y. y \<in> cball \<xi> r \<Longrightarrow> \<phi> y + p \<bullet> y \<le> \<phi> x + p \<bullet> x"
      unfolding K_def by blast
    from kx' obtain p' where np': "norm p' \<le> d" and xin': "x' \<in> cball \<xi> r"
      and xmax': "\<And>y. y \<in> cball \<xi> r \<Longrightarrow> \<phi> y + p' \<bullet> y \<le> \<phi> x' + p' \<bullet> x'"
      unfolding K_def by blast
    have dx: "dist x \<xi> < \<rho>" by (rule deepK[OF xin np xmax])
    have dx': "dist x' \<xi> < \<rho>" by (rule deepK[OF xin' np' xmax'])
    have nQQ: "norm (Q x - Q x') \<le> 2*Qb"
      using Qbound[OF kx] Qbound[OF kx'] norm_triangle_ineq4[of "Q x" "Q x'"]
      by simp
    have nQQ': "norm (Q x' - Q x) \<le> 2*Qb"
      using nQQ by (simp add: norm_minus_commute)
    have L1: "s * norm (Q x - Q x') \<le> norm (x - x')"
    proof (rule subdiff_lipschitz_of_semiconcave[OF Qsub Qsub _ _ s0 sc])
      show "\<psi> y \<le> \<psi> x + Q x \<bullet> (y - x) + (c/2) * (norm (y - x))\<^sup>2"
        if "y \<in> cball \<xi> r" for y by (rule ub[OF that xin np xmax])
      show "\<psi> y \<le> \<psi> x' + Q x' \<bullet> (y - x') + (c/2) * (norm (y - x'))\<^sup>2"
        if "y \<in> cball \<xi> r" for y by (rule ub[OF that xin' np' xmax'])
      show "x - s *\<^sub>R (Q x - Q x') \<in> cball \<xi> r" by (rule mem[OF dx nQQ])
      show "x' - s *\<^sub>R (Q x' - Q x) \<in> cball \<xi> r" by (rule mem[OF dx' nQQ'])
    qed
    have L2: "norm (Q x - Q x') \<le> (1/s) * norm (x - x')"
      using L1 s0 by (simp add: field_simps)
    have "norm (P x - P x') = norm (c *\<^sub>R (x - x') - (Q x - Q x'))"
      unfolding P_def by (simp add: algebra_simps scaleR_diff_right)
    also have "\<dots> \<le> norm (c *\<^sub>R (x - x')) + norm (Q x - Q x')"
      by (rule norm_triangle_ineq4)
    also have "\<dots> = c * norm (x - x') + norm (Q x - Q x')" using c by simp
    also have "\<dots> \<le> c * norm (x - x') + (1/s) * norm (x - x')" using L2 by simp
    finally show ?thesis by (simp add: algebra_simps)
  qed
  have surjP: "cball (0::'a) d \<subseteq> P ` K"
  proof
    fix p :: 'a assume "p \<in> cball 0 d"
    hence np: "norm p \<le> d" by (simp add: dist_norm)
    obtain x where xin: "x \<in> cball \<xi> r"
      and xmax: "\<And>y. y \<in> cball \<xi> r \<Longrightarrow> \<phi> y + p \<bullet> y \<le> \<phi> x + p \<bullet> x"
      using semiconvex_max_exists[OF cvx less_imp_le[OF r], of \<xi> p] by blast
    have xK: "x \<in> K" unfolding K_def using xin np xmax by blast
    have "P x = p" by (rule PK[OF xin np xmax])
    thus "p \<in> P ` K" using xK by (metis image_eqI)
  qed
  have main: "\<not> negligible K"
  proof
    assume neg: "negligible K"
    have negP: "negligible (P ` K)"
    proof (rule negligible_locally_Lipschitz_image[OF order_refl neg])
      fix x :: 'a assume xK: "x \<in> K"
      have "\<forall>y \<in> K \<inter> UNIV. norm (P y - P x) \<le> (c + 1/s) * norm (y - x)"
        using lip xK by blast
      thus "\<exists>T B. open T \<and> x \<in> T
          \<and> (\<forall>y \<in> K \<inter> T. norm (P y - P x) \<le> B * norm (y - x))"
        by blast
    qed
    have "negligible (cball (0::'a) d)"
      by (rule negligible_subset[OF negP surjP])
    thus False using not_negligible_cball[OF d] by blast
  qed
  thus ?thesis unfolding K_def .
qed

subsection \<open>Towards the theorem on sums: doubling of variables\<close>

text \<open>The quantitative core of Crandall-Ishii-Lions Lemma 3.1, in purely
  algebraic form: no semicontinuity, no compactness, only the two maximality
  statements. Writing \<open>\<Phi>\<^sub>\<alpha>(x,y) = u x - w y - (\<alpha>/2) * norm (x - y)\<^sup>2\<close> and
  \<open>M\<^sub>\<alpha> = max \<Phi>\<^sub>\<alpha>\<close>, testing \<open>\<Phi>\<^sub>\<beta>\<close> at the maximiser OF \<open>\<Phi>\<^sub>\<alpha>\<close> gives at once
  that \<open>M\<^sub>\<alpha>\<close> is nonincreasing in \<open>\<alpha>\<close> AND that the penalty term is squeezed
  between consecutive values. That squeeze is what forces
  \<open>\<alpha> * norm (x\<^sub>\<alpha> - y\<^sub>\<alpha>)\<^sup>2 \<longrightarrow> 0\<close> once \<open>M\<^sub>\<alpha>\<close> is known to converge, and hence
  drives the two maximisers together.\<close>

lemma doubling_ge_diagonal:
  fixes u w :: "'a::euclidean_space \<Rightarrow> real"
  assumes x: "x \<in> K"
    and maxa: "\<And>z y. z \<in> K \<Longrightarrow> y \<in> K
        \<Longrightarrow> u z - w y - (\<alpha>/2) * (norm (z - y))\<^sup>2 \<le> Ma"
  shows "u x - w x \<le> Ma"
  using maxa[OF x x] by simp

lemma doubling_ring_identity:
  fixes A N \<alpha> \<beta> :: real
  shows "A - (\<beta>/2) * N = (A - (\<alpha>/2) * N) + ((\<alpha> - \<beta>)/2) * N"
  by (simp add: field_simps)

lemma doubling_penalty_squeeze:
  fixes u w :: "'a::euclidean_space \<Rightarrow> real"
  assumes ab: "\<beta> \<le> \<alpha>"
    and xa: "xa \<in> K" and ya: "ya \<in> K"
    and atta: "u xa - w ya - (\<alpha>/2) * (norm (xa - ya))\<^sup>2 = Ma"
    and maxb: "\<And>z y. z \<in> K \<Longrightarrow> y \<in> K
        \<Longrightarrow> u z - w y - (\<beta>/2) * (norm (z - y))\<^sup>2 \<le> Mb"
  shows "((\<alpha> - \<beta>)/2) * (norm (xa - ya))\<^sup>2 \<le> Mb - Ma"
proof -
  have step: "u xa - w ya - (\<beta>/2) * (norm (xa - ya))\<^sup>2 \<le> Mb"
    by (rule maxb[OF xa ya])
  have ring: "u xa - w ya - (\<beta>/2) * (norm (xa - ya))\<^sup>2
      = (u xa - w ya - (\<alpha>/2) * (norm (xa - ya))\<^sup>2)
        + ((\<alpha> - \<beta>)/2) * (norm (xa - ya))\<^sup>2"
    by (rule doubling_ring_identity)
  show ?thesis using step ring atta by linarith
qed

lemma doubling_antitone:
  fixes u w :: "'a::euclidean_space \<Rightarrow> real"
  assumes ab: "\<beta> \<le> \<alpha>"
    and xa: "xa \<in> K" and ya: "ya \<in> K"
    and atta: "u xa - w ya - (\<alpha>/2) * (norm (xa - ya))\<^sup>2 = Ma"
    and maxb: "\<And>z y. z \<in> K \<Longrightarrow> y \<in> K
        \<Longrightarrow> u z - w y - (\<beta>/2) * (norm (z - y))\<^sup>2 \<le> Mb"
  shows "Ma \<le> Mb"
proof -
  have sq: "((\<alpha> - \<beta>)/2) * (norm (xa - ya))\<^sup>2 \<le> Mb - Ma"
    by (rule doubling_penalty_squeeze[OF ab xa ya atta maxb])
  have "0 \<le> ((\<alpha> - \<beta>)/2) * (norm (xa - ya))\<^sup>2"
    using ab by (intro mult_nonneg_nonneg) auto
  with sq show ?thesis by linarith
qed

text \<open>The limit half of Lemma 3.1. Once \<open>M\<^sub>\<alpha>\<close> is known to converge, applying
  the squeeze with \<open>\<beta> = \<alpha>/2\<close> traps \<open>(\<alpha>/4) * pen \<alpha>\<close> between \<open>0\<close> and
  \<open>M\<^bsub>\<alpha>/2\<^esub> - M\<^sub>\<alpha>\<close>, and both ends go to \<open>0\<close>. So the PENALTY term vanishes, not
  merely the distance: this is what makes the two maximisers usable as a
  single point in the limit.\<close>

lemma doubling_penalty_tendsto_zero:
  fixes M pen :: "real \<Rightarrow> real"
  assumes conv: "(M \<longlongrightarrow> L) at_top"
    and sq: "\<And>\<alpha>. 1 \<le> \<alpha> \<Longrightarrow> (\<alpha>/4) * pen \<alpha> \<le> M (\<alpha>/2) - M \<alpha>"
    and nn: "\<And>\<alpha>. 0 \<le> pen \<alpha>"
  shows "((\<lambda>\<alpha>. \<alpha> * pen \<alpha>) \<longlongrightarrow> 0) at_top"
proof -
  have half: "filterlim (\<lambda>\<alpha>::real. \<alpha>/2) at_top at_top"
  proof (rule filterlim_at_top[THEN iffD2], rule allI)
    fix Z :: real
    show "\<forall>\<^sub>F \<alpha> in at_top. Z \<le> \<alpha>/2"
      using eventually_ge_at_top[of "2*Z"] by (rule eventually_mono) simp
  qed
  have c2: "((\<lambda>\<alpha>. M (\<alpha>/2)) \<longlongrightarrow> L) at_top"
    by (rule filterlim_compose[OF conv half])
  have diff: "((\<lambda>\<alpha>. M (\<alpha>/2) - M \<alpha>) \<longlongrightarrow> 0) at_top"
    using tendsto_diff[OF c2 conv] by simp
  have lo: "\<forall>\<^sub>F \<alpha> in at_top. (0::real) \<le> (\<alpha>/4) * pen \<alpha>"
  proof (rule eventually_mono[OF eventually_ge_at_top[of "0::real"]])
    fix \<alpha> :: real assume "0 \<le> \<alpha>"
    thus "0 \<le> (\<alpha>/4) * pen \<alpha>"
      by (intro mult_nonneg_nonneg nn) simp
  qed
  have hi: "\<forall>\<^sub>F \<alpha> in at_top. (\<alpha>/4) * pen \<alpha> \<le> M (\<alpha>/2) - M \<alpha>"
  proof (rule eventually_mono[OF eventually_ge_at_top[of "1::real"]])
    fix \<alpha> :: real assume "1 \<le> \<alpha>"
    thus "(\<alpha>/4) * pen \<alpha> \<le> M (\<alpha>/2) - M \<alpha>" by (rule sq)
  qed
  have "((\<lambda>\<alpha>. (\<alpha>/4) * pen \<alpha>) \<longlongrightarrow> 0) at_top"
    by (rule tendsto_sandwich[OF lo hi tendsto_const diff])
  hence "((\<lambda>\<alpha>. 4 * ((\<alpha>/4) * pen \<alpha>)) \<longlongrightarrow> 4 * 0) at_top"
    by (rule tendsto_mult_left)
  thus ?thesis by simp
qed

text \<open>And the hypothesis of the previous lemma is exactly what \<open>doubling_antitone\<close>
  plus \<open>doubling_ge_diagonal\<close> supply: \<open>M\<^sub>\<alpha>\<close> is antitone and bounded below by any
  diagonal value, hence convergent along \<open>at_top\<close>.\<close>

lemma antitone_bdd_below_convergent_at_top:
  fixes M :: "real \<Rightarrow> real"
  assumes anti: "\<And>\<beta> \<alpha>. 1 \<le> \<beta> \<Longrightarrow> \<beta> \<le> \<alpha> \<Longrightarrow> M \<alpha> \<le> M \<beta>"
    and bdd: "\<And>\<alpha>. 1 \<le> \<alpha> \<Longrightarrow> B \<le> M \<alpha>"
  shows "\<exists>L. (M \<longlongrightarrow> L) at_top"
proof -
  define S where "S = M ` {1..}"
  have Sne: "S \<noteq> {}" unfolding S_def by auto
  have Sbdd: "bdd_below S"
    unfolding S_def by (rule bdd_belowI[of _ B]) (auto intro: bdd)
  define L where "L = Inf S"
  have Llow: "L \<le> M \<alpha>" if a: "1 \<le> \<alpha>" for \<alpha>
    unfolding L_def by (rule cInf_lower[OF _ Sbdd]) (use a in \<open>auto simp: S_def\<close>)
  have "(M \<longlongrightarrow> L) at_top"
  proof (subst tendsto_iff, rule allI, rule impI)
    fix e :: real assume e: "0 < e"
    have "L < L + e" using e by simp
    hence "\<exists>x \<in> S. x < L + e"
      unfolding L_def using Sne Sbdd by (subst (asm) cInf_less_iff) auto
    then obtain a where a1: "1 \<le> a" and aM: "M a < L + e"
      unfolding S_def by auto
    show "\<forall>\<^sub>F \<alpha> in at_top. dist (M \<alpha>) L < e"
    proof (rule eventually_mono[OF eventually_ge_at_top[of a]])
      fix \<alpha> :: real assume aa: "a \<le> \<alpha>"
      hence a1': "1 \<le> \<alpha>" using a1 by simp
      have "M \<alpha> \<le> M a" by (rule anti[OF a1 aa])
      moreover have "L \<le> M \<alpha>" by (rule Llow[OF a1'])
      ultimately show "dist (M \<alpha>) L < e" using aM by (simp add: dist_real_def)
    qed
  qed
  thus ?thesis by blast
qed

subsection \<open>Composing the three big theorems on the sup-convolution\<close>

text \<open>\<open>supconv_semiconvex\<close> delivers semiconvexity in the form
  \<open>(norm x)\<^sup>2 / (2*\<epsilon>)\<close>, while \<open>jensen_lemma\<close> and \<open>semiconvex_alexandrov\<close>
  consume it in the form \<open>(c/2) * (norm x)\<^sup>2\<close>. The two agree with \<open>c = 1/\<epsilon>\<close>;
  restating it once here is what lets the three theorems be composed without
  re-deriving anything, and gives Crandall-Ishii its two working facts about
  the sup-convolution.\<close>

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

text \<open>The sup-convolution of ANY bounded-above function is twice differentiable
  almost everywhere. This is the fact Crandall-Ishii uses to put genuine second
  derivatives at the perturbed maximiser produced by Jensen's lemma.\<close>

corollary supconv_alexandrov:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> B" and e: "0 < \<epsilon>"
  shows "negligible {y. \<not> (\<exists>p X. bounded_linear X \<and> (\<forall>v w. v \<bullet> X w = w \<bullet> X v)
      \<and> ((\<lambda>k. (supconv u \<epsilon> (y + k) - supconv u \<epsilon> y - p \<bullet> k - (k \<bullet> X k)/2)
          / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0))}"
  by (rule semiconvex_alexandrov[OF supconv_semiconvex'[OF B e]])

text \<open>And Jensen's lemma applies to it verbatim: the set of points maximising
  some small linear perturbation of the sup-convolution is not negligible, so
  it MEETS the full-measure set of the previous corollary. That intersection is
  exactly the point at which the theorem on sums reads off its matrices.\<close>

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

text \<open>THE ENGINE OF CRANDALL-ISHII. Jensen's lemma says the perturbed
  maximisers form a set of positive measure; Alexandrov's says the twice
  differentiable points form a set of full measure. A non-negligible set cannot
  sit inside a negligible one, so the two MEET: there is a single point that is
  simultaneously a maximiser of a small linear perturbation and a point of
  genuine second-order expansion. Reading the second-order expansion off at
  such a point is exactly how the theorem on sums produces its matrices.\<close>

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

text \<open>SECOND-ORDER CONDITIONS at an interior maximum. If a function has a
  second-order expansion with data \<open>(q, X)\<close> at an interior maximiser, then
  \<open>q = 0\<close> and the quadratic form is negative semidefinite. Both follow from the
  SAME limit, \<open>R (t *\<^sub>R v) / t\<^sup>2 \<longrightarrow> 0\<close> along \<open>at_right 0\<close>: dividing the
  maximality inequality by \<open>t\<close> gives the first, and by \<open>t\<^sup>2\<close> the second. This is
  what upgrades the Alexandrov expansion at the Jensen point into a genuine
  second-order jet.\<close>

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
      by (rule tendsto_mult[OF lim3]) (simp add: tendsto_ident_at)
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
      by (intro tendsto_intros lim5) (simp add: tendsto_ident_at)
    have qle: "q \<bullet> w \<le> 0"
      by (rule tendsto_upperbound[OF _ g1])
        (use c1 in \<open>simp_all add: trivial_limit_at_right_real\<close>)
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
          (use c2 in \<open>simp_all add: trivial_limit_at_right_real\<close>)
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

subsection \<open>Block structure on the product space\<close>

text \<open>The doubled function lives on \<open>'a \<times> 'b\<close>, which is itself a Euclidean
  space, so every result above applies to it verbatim. Two things are needed to
  come back down to the factors. First, the negative semidefiniteness delivered
  on the product is TESTED on the diagonal: with \<open>w = v\<close> the penalty term
  vanishes and only \<open>v \<cdot> X v \<le> v \<cdot> Y v\<close> survives \<open>this is the matrix
  inequality of the theorem on sums\<close>. Second, a second-order expansion on the
  product RESTRICTS to each slice, which is what lets the single product
  Hessian be read as two separate matrices.\<close>

lemma block_diagonal_test:
  fixes X Y :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes neg: "\<And>v w. v \<bullet> X v - w \<bullet> Y w - \<alpha> * (norm (v - w))\<^sup>2 \<le> 0"
  shows "v \<bullet> X v \<le> v \<bullet> Y v"
  using neg[of v v] by simp

lemma norm_Pair_right_zero:
  fixes h :: "'a::euclidean_space"
  shows "norm ((h, 0) :: 'a \<times> 'b::euclidean_space) = norm h"
  by (simp add: norm_prod_def)

lemma norm_Pair_left_zero:
  fixes h :: "'b::euclidean_space"
  shows "norm ((0, h) :: 'a::euclidean_space \<times> 'b) = norm h"
  by (simp add: norm_prod_def)

lemma expansion_restrict_fst:
  fixes \<Psi> :: "'a::euclidean_space \<times> 'b::euclidean_space \<Rightarrow> real"
  assumes exp: "((\<lambda>k. (\<Psi> (z + k) - \<Psi> z - q \<bullet> k - (k \<bullet> Z k)/2) / (norm k)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
  shows "((\<lambda>h. (\<Psi> (fst z + h, snd z) - \<Psi> z - (fst q) \<bullet> h
      - (h \<bullet> fst (Z (h, 0)))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
proof -
  have emb: "filterlim (\<lambda>h::'a. (h, 0::'b)) (at 0) (at 0)"
  proof (rule filterlim_atI)
    have "((\<lambda>h::'a. (h, 0::'b)) \<longlongrightarrow> (0, 0)) (at 0)"
      by (intro tendsto_intros)
    thus "((\<lambda>h::'a. (h, 0::'b)) \<longlongrightarrow> 0) (at 0)" by (simp add: zero_prod_def)
    show "\<forall>\<^sub>F h in at (0::'a). (h, 0::'b) \<noteq> 0"
      by (simp add: eventually_at_filter zero_prod_def)
  qed
  have c: "((\<lambda>h. (\<Psi> (z + (h, 0::'b)) - \<Psi> z - q \<bullet> (h, 0::'b)
      - ((h, 0::'b) \<bullet> Z (h, 0::'b))/2)
      / (norm ((h, 0::'b) :: 'a \<times> 'b))\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    by (rule filterlim_compose[OF exp emb])
  have eq: "(\<Psi> (z + (h, 0::'b)) - \<Psi> z - q \<bullet> (h, 0::'b)
      - ((h, 0::'b) \<bullet> Z (h, 0::'b))/2) / (norm ((h, 0::'b) :: 'a \<times> 'b))\<^sup>2
      = (\<Psi> (fst z + h, snd z) - \<Psi> z - (fst q) \<bullet> h
        - (h \<bullet> fst (Z (h, 0::'b)))/2) / (norm h)\<^sup>2" for h :: 'a
  proof -
    have zsum: "z + (h, 0::'b) = (fst z + h, snd z)"
      by (cases z) simp
    have inn1: "q \<bullet> (h, 0::'b) = (fst q) \<bullet> h"
      by (cases q) (simp add: inner_commute)
    have inn2: "(h, 0::'b) \<bullet> Z (h, 0::'b) = h \<bullet> fst (Z (h, 0::'b))"
      by (cases "Z (h, 0::'b)") simp
    show ?thesis
      unfolding zsum inn1 inn2 norm_Pair_right_zero ..
  qed
  show ?thesis using c unfolding eq .
qed

lemma expansion_restrict_snd:
  fixes \<Psi> :: "'a::euclidean_space \<times> 'b::euclidean_space \<Rightarrow> real"
  assumes exp: "((\<lambda>k. (\<Psi> (z + k) - \<Psi> z - q \<bullet> k - (k \<bullet> Z k)/2) / (norm k)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
  shows "((\<lambda>h. (\<Psi> (fst z, snd z + h) - \<Psi> z - (snd q) \<bullet> h
      - (h \<bullet> snd (Z (0, h)))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
proof -
  have emb: "filterlim (\<lambda>h::'b. (0::'a, h)) (at 0) (at 0)"
  proof (rule filterlim_atI)
    have "((\<lambda>h::'b. (0::'a, h)) \<longlongrightarrow> (0, 0)) (at 0)"
      by (intro tendsto_intros)
    thus "((\<lambda>h::'b. (0::'a, h)) \<longlongrightarrow> 0) (at 0)" by (simp add: zero_prod_def)
    show "\<forall>\<^sub>F h in at (0::'b). (0::'a, h) \<noteq> 0"
      by (simp add: eventually_at_filter zero_prod_def)
  qed
  have c: "((\<lambda>h. (\<Psi> (z + (0::'a, h)) - \<Psi> z - q \<bullet> (0::'a, h)
      - ((0::'a, h) \<bullet> Z (0::'a, h))/2)
      / (norm ((0::'a, h) :: 'a \<times> 'b))\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    by (rule filterlim_compose[OF exp emb])
  have eq: "(\<Psi> (z + (0::'a, h)) - \<Psi> z - q \<bullet> (0::'a, h)
      - ((0::'a, h) \<bullet> Z (0::'a, h))/2) / (norm ((0::'a, h) :: 'a \<times> 'b))\<^sup>2
      = (\<Psi> (fst z, snd z + h) - \<Psi> z - (snd q) \<bullet> h
        - (h \<bullet> snd (Z (0::'a, h)))/2) / (norm h)\<^sup>2" for h :: 'b
  proof -
    have zsum: "z + (0::'a, h) = (fst z, snd z + h)"
      by (cases z) simp
    have inn1: "q \<bullet> (0::'a, h) = (snd q) \<bullet> h"
      by (cases q) (simp add: inner_commute)
    have inn2: "(0::'a, h) \<bullet> Z (0::'a, h) = h \<bullet> snd (Z (0::'a, h))"
      by (cases "Z (0::'a, h)") simp
    show ?thesis
      unfolding zsum inn1 inn2 norm_Pair_left_zero ..
  qed
  show ?thesis using c unfolding eq .
qed

subsection \<open>Semiconvexity calculus for the doubled functional\<close>

text \<open>Before any of the machinery can be pointed at the doubled functional
  \<open>(x,y) \<mapsto> u x - w y - (\<alpha>/2) * norm (x - y)\<^sup>2\<close>, that functional has to be known
  SEMICONVEX on the product. Three closure properties suffice: semiconvexity
  adds (with the constants), it survives composition with \<open>fst\<close> and \<open>snd\<close>, and
  the concave penalty is itself semiconvex with constant \<open>2*\<alpha>\<close>, the last by the
  identity \<open>-(\<alpha>/2) * norm (x-y)\<^sup>2 + \<alpha> * (norm x\<^sup>2 + norm y\<^sup>2) = (\<alpha>/2) * norm (x+y)\<^sup>2\<close>,
  which turns it into a convex function outright.\<close>

lemma convex_on_norm_sq:
  fixes S :: "'a::real_inner set"
  assumes S: "convex S"
  shows "convex_on S (\<lambda>x. (norm x)\<^sup>2)"
proof (rule convex_onI[OF _ S])
  fix t :: real and x y :: 'a
  assume t: "0 < t" "t < 1"
  have eA: "(norm x)\<^sup>2 = x \<bullet> x" by (rule power2_norm_eq_inner)
  have eB: "(norm y)\<^sup>2 = y \<bullet> y" by (rule power2_norm_eq_inner)
  have eC: "(norm ((1 - t) *\<^sub>R x + t *\<^sub>R y))\<^sup>2
      = ((1 - t) *\<^sub>R x + t *\<^sub>R y) \<bullet> ((1 - t) *\<^sub>R x + t *\<^sub>R y)"
    by (rule power2_norm_eq_inner)
  have expand: "((1 - t) *\<^sub>R x + t *\<^sub>R y) \<bullet> ((1 - t) *\<^sub>R x + t *\<^sub>R y)
      = (1-t)*(1-t)*(x \<bullet> x) + 2*(1-t)*t*(x \<bullet> y) + t*t*(y \<bullet> y)"
    by (simp add: inner_add_left inner_add_right inner_commute algebra_simps)
  have expand2: "(x - y) \<bullet> (x - y) = (x \<bullet> x) - 2*(x \<bullet> y) + (y \<bullet> y)"
    by (simp add: inner_diff_left inner_diff_right inner_commute)
  have ident: "(1 - t) * (x \<bullet> x) + t * (y \<bullet> y)
      - ((1-t)*(1-t)*(x \<bullet> x) + 2*(1-t)*t*(x \<bullet> y) + t*t*(y \<bullet> y))
      = (t*(1-t)) * ((x \<bullet> x) - 2*(x \<bullet> y) + (y \<bullet> y))"
    by (simp add: algebra_simps)
  have nn: "0 \<le> (t*(1-t)) * ((x \<bullet> x) - 2*(x \<bullet> y) + (y \<bullet> y))"
  proof -
    have p1: "0 \<le> t*(1-t)" using t by (intro mult_nonneg_nonneg) auto
    have p2: "0 \<le> (x \<bullet> x) - 2*(x \<bullet> y) + (y \<bullet> y)"
      unfolding expand2[symmetric] by simp
    show ?thesis by (rule mult_nonneg_nonneg[OF p1 p2])
  qed
  show "(norm ((1 - t) *\<^sub>R x + t *\<^sub>R y))\<^sup>2
      \<le> (1 - t) * (norm x)\<^sup>2 + t * (norm y)\<^sup>2"
    unfolding eA eB eC expand using ident nn by linarith
qed

lemma semiconvex_add:
  fixes f g :: "'a::euclidean_space \<Rightarrow> real"
  assumes f: "convex_on UNIV (\<lambda>x. f x + (c/2) * (norm x)\<^sup>2)"
    and g: "convex_on UNIV (\<lambda>x. g x + (c'/2) * (norm x)\<^sup>2)"
  shows "convex_on UNIV (\<lambda>x. (f x + g x) + ((c + c')/2) * (norm x)\<^sup>2)"
proof -
  have "convex_on UNIV (\<lambda>x::'a. (f x + (c/2) * (norm x)\<^sup>2)
      + (g x + (c'/2) * (norm x)\<^sup>2))"
    by (rule convex_on_add[OF f g])
  moreover have "(\<lambda>x::'a. (f x + (c/2) * (norm x)\<^sup>2) + (g x + (c'/2) * (norm x)\<^sup>2))
      = (\<lambda>x. (f x + g x) + ((c + c')/2) * (norm x)\<^sup>2)"
    by (rule ext) (simp add: algebra_simps)
  ultimately show ?thesis by simp
qed

lemma convex_on_fst:
  fixes h :: "'a::euclidean_space \<Rightarrow> real"
  assumes h: "convex_on UNIV h"
  shows "convex_on UNIV (\<lambda>z::'a \<times> 'b::euclidean_space. h (fst z))"
proof (rule convex_onI)
  fix t :: real and z1 z2 :: "'a \<times> 'b"
  assume t: "0 < t" "t < 1"
  have "fst ((1 - t) *\<^sub>R z1 + t *\<^sub>R z2) = (1 - t) *\<^sub>R fst z1 + t *\<^sub>R fst z2"
    by simp
  moreover have "h ((1 - t) *\<^sub>R fst z1 + t *\<^sub>R fst z2)
      \<le> (1 - t) * h (fst z1) + t * h (fst z2)"
    using t by (intro convex_onD[OF h]) auto
  ultimately show "h (fst ((1 - t) *\<^sub>R z1 + t *\<^sub>R z2))
      \<le> (1 - t) * h (fst z1) + t * h (fst z2)" by simp
qed simp

lemma convex_on_snd:
  fixes h :: "'b::euclidean_space \<Rightarrow> real"
  assumes h: "convex_on UNIV h"
  shows "convex_on UNIV (\<lambda>z::'a::euclidean_space \<times> 'b. h (snd z))"
proof (rule convex_onI)
  fix t :: real and z1 z2 :: "'a \<times> 'b"
  assume t: "0 < t" "t < 1"
  have "snd ((1 - t) *\<^sub>R z1 + t *\<^sub>R z2) = (1 - t) *\<^sub>R snd z1 + t *\<^sub>R snd z2"
    by simp
  moreover have "h ((1 - t) *\<^sub>R snd z1 + t *\<^sub>R snd z2)
      \<le> (1 - t) * h (snd z1) + t * h (snd z2)"
    using t by (intro convex_onD[OF h]) auto
  ultimately show "h (snd ((1 - t) *\<^sub>R z1 + t *\<^sub>R z2))
      \<le> (1 - t) * h (snd z1) + t * h (snd z2)" by simp
qed simp

lemma convex_on_scaleR_nonneg:
  fixes h :: "'a::real_vector \<Rightarrow> real"
  assumes h: "convex_on UNIV h" and c: "0 \<le> c"
  shows "convex_on UNIV (\<lambda>x. c * h x)"
proof (rule convex_onI)
  fix t :: real and x y :: 'a
  assume t: "0 < t" "t < 1"
  have "h ((1 - t) *\<^sub>R x + t *\<^sub>R y) \<le> (1 - t) * h x + t * h y"
    using t by (intro convex_onD[OF h]) auto
  hence "c * h ((1 - t) *\<^sub>R x + t *\<^sub>R y) \<le> c * ((1 - t) * h x + t * h y)"
    using c by (rule mult_left_mono)
  thus "c * h ((1 - t) *\<^sub>R x + t *\<^sub>R y) \<le> (1 - t) * (c * h x) + t * (c * h y)"
    by (simp add: algebra_simps)
qed simp

lemma convex_on_proj_sum:
  fixes h :: "'a::euclidean_space \<Rightarrow> real"
  assumes h: "convex_on UNIV h"
  shows "convex_on UNIV (\<lambda>z::'a \<times> 'a. h (fst z + snd z))"
proof (rule convex_onI)
  fix t :: real and z1 z2 :: "'a \<times> 'a"
  assume t: "0 < t" "t < 1"
  have e: "fst ((1 - t) *\<^sub>R z1 + t *\<^sub>R z2) + snd ((1 - t) *\<^sub>R z1 + t *\<^sub>R z2)
      = (1 - t) *\<^sub>R (fst z1 + snd z1) + t *\<^sub>R (fst z2 + snd z2)"
    by (simp add: algebra_simps)
  have "h ((1 - t) *\<^sub>R (fst z1 + snd z1) + t *\<^sub>R (fst z2 + snd z2))
      \<le> (1 - t) * h (fst z1 + snd z1) + t * h (fst z2 + snd z2)"
    using t by (intro convex_onD[OF h]) auto
  thus "h (fst ((1 - t) *\<^sub>R z1 + t *\<^sub>R z2)
        + snd ((1 - t) *\<^sub>R z1 + t *\<^sub>R z2))
      \<le> (1 - t) * h (fst z1 + snd z1) + t * h (fst z2 + snd z2)"
    unfolding e .
qed simp

lemma norm_prod_sq:
  fixes z :: "'a::euclidean_space \<times> 'b::euclidean_space"
  shows "(norm z)\<^sup>2 = (norm (fst z))\<^sup>2 + (norm (snd z))\<^sup>2"
  by (simp add: norm_prod_def)

text \<open>The concave penalty is semiconvex with constant \<open>2*\<alpha>\<close>. Adding
  \<open>\<alpha> * (norm x\<^sup>2 + norm y\<^sup>2)\<close> to \<open>-(\<alpha>/2) * norm (x-y)\<^sup>2\<close> gives exactly
  \<open>(\<alpha>/2) * norm (x+y)\<^sup>2\<close>, a convex function outright.\<close>

lemma semiconvex_penalty:
  fixes \<alpha> :: real
  assumes a: "0 \<le> \<alpha>"
  shows "convex_on UNIV (\<lambda>z::'a::euclidean_space \<times> 'a.
      - ((\<alpha>/2) * (norm (fst z - snd z))\<^sup>2) + ((2*\<alpha>)/2) * (norm z)\<^sup>2)"
proof -
  have eq: "(\<lambda>z::'a \<times> 'a. - ((\<alpha>/2) * (norm (fst z - snd z))\<^sup>2)
        + ((2*\<alpha>)/2) * (norm z)\<^sup>2)
      = (\<lambda>z::'a \<times> 'a. (\<alpha>/2) * (norm (fst z + snd z))\<^sup>2)"
  proof (rule ext)
    fix z :: "'a \<times> 'a"
    have d: "(norm (fst z - snd z))\<^sup>2
        = (norm (fst z))\<^sup>2 - 2*(fst z \<bullet> snd z) + (norm (snd z))\<^sup>2"
      by (simp add: power2_norm_eq_inner inner_diff_left inner_diff_right
          inner_commute)
    have s: "(norm (fst z + snd z))\<^sup>2
        = (norm (fst z))\<^sup>2 + 2*(fst z \<bullet> snd z) + (norm (snd z))\<^sup>2"
      by (simp add: power2_norm_eq_inner inner_add_left inner_add_right
          inner_commute)
    show "- ((\<alpha>/2) * (norm (fst z - snd z))\<^sup>2) + ((2*\<alpha>)/2) * (norm z)\<^sup>2
        = (\<alpha>/2) * (norm (fst z + snd z))\<^sup>2"
      unfolding norm_prod_sq d s by (simp add: algebra_simps)
  qed
  have cn: "convex_on UNIV (\<lambda>x::'a. (norm x)\<^sup>2)"
    by (rule convex_on_norm_sq[OF convex_UNIV])
  have "convex_on UNIV (\<lambda>z::'a \<times> 'a. (\<alpha>/2) * (norm (fst z + snd z))\<^sup>2)"
    using a by (intro convex_on_scaleR_nonneg convex_on_proj_sum[OF cn]) simp
  thus ?thesis unfolding eq .
qed

lemma semiconvex_of_fst:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes f: "convex_on UNIV (\<lambda>x. f x + (c/2) * (norm x)\<^sup>2)" and c: "0 \<le> c"
  shows "convex_on UNIV
      (\<lambda>z::'a \<times> 'b::euclidean_space. f (fst z) + (c/2) * (norm z)\<^sup>2)"
proof -
  have p1: "convex_on UNIV
      (\<lambda>z::'a \<times> 'b. f (fst z) + (c/2) * (norm (fst z))\<^sup>2)"
    by (rule convex_on_fst[OF f])
  have cn: "convex_on UNIV (\<lambda>x::'b. (norm x)\<^sup>2)"
    by (rule convex_on_norm_sq[OF convex_UNIV])
  have p2: "convex_on UNIV (\<lambda>z::'a \<times> 'b. (c/2) * (norm (snd z))\<^sup>2)"
    using c by (intro convex_on_scaleR_nonneg convex_on_snd[OF cn]) simp
  have "convex_on UNIV (\<lambda>z::'a \<times> 'b.
      (f (fst z) + (c/2) * (norm (fst z))\<^sup>2) + (c/2) * (norm (snd z))\<^sup>2)"
    by (rule convex_on_add[OF p1 p2])
  moreover have "(\<lambda>z::'a \<times> 'b.
        (f (fst z) + (c/2) * (norm (fst z))\<^sup>2) + (c/2) * (norm (snd z))\<^sup>2)
      = (\<lambda>z::'a \<times> 'b. f (fst z) + (c/2) * (norm z)\<^sup>2)"
    by (rule ext) (simp add: norm_prod_sq algebra_simps)
  ultimately show ?thesis by simp
qed

lemma semiconvex_of_snd:
  fixes f :: "'b::euclidean_space \<Rightarrow> real"
  assumes f: "convex_on UNIV (\<lambda>x. f x + (c/2) * (norm x)\<^sup>2)" and c: "0 \<le> c"
  shows "convex_on UNIV
      (\<lambda>z::'a::euclidean_space \<times> 'b. f (snd z) + (c/2) * (norm z)\<^sup>2)"
proof -
  have p1: "convex_on UNIV
      (\<lambda>z::'a \<times> 'b. f (snd z) + (c/2) * (norm (snd z))\<^sup>2)"
    by (rule convex_on_snd[OF f])
  have cn: "convex_on UNIV (\<lambda>x::'a. (norm x)\<^sup>2)"
    by (rule convex_on_norm_sq[OF convex_UNIV])
  have p2: "convex_on UNIV (\<lambda>z::'a \<times> 'b. (c/2) * (norm (fst z))\<^sup>2)"
    using c by (intro convex_on_scaleR_nonneg convex_on_fst[OF cn]) simp
  have "convex_on UNIV (\<lambda>z::'a \<times> 'b.
      (f (snd z) + (c/2) * (norm (snd z))\<^sup>2) + (c/2) * (norm (fst z))\<^sup>2)"
    by (rule convex_on_add[OF p1 p2])
  moreover have "(\<lambda>z::'a \<times> 'b.
        (f (snd z) + (c/2) * (norm (snd z))\<^sup>2) + (c/2) * (norm (fst z))\<^sup>2)
      = (\<lambda>z::'a \<times> 'b. f (snd z) + (c/2) * (norm z)\<^sup>2)"
    by (rule ext) (simp add: norm_prod_sq algebra_simps)
  ultimately show ?thesis by simp
qed

text \<open>THE DOUBLED FUNCTIONAL IS SEMICONVEX, with constant
  \<open>1/\<epsilon> + 1/\<epsilon> + 2*\<alpha>\<close>. This is the hypothesis every one of Rademacher,
  Alexandrov, Jensen and \<open>supconv_jensen_alexandrov_point\<close> needs before it can
  be pointed at the doubling of variables, and it is what opens the theorem on
  sums.\<close>

theorem doubled_functional_semiconvex:
  fixes u v :: "'a::euclidean_space \<Rightarrow> real"
  assumes Bu: "\<And>y. u y \<le> Bu" and Bv: "\<And>y. v y \<le> Bv"
    and e: "0 < \<epsilon>" and a: "0 \<le> \<alpha>"
  shows "convex_on UNIV (\<lambda>z::'a \<times> 'a.
      (supconv u \<epsilon> (fst z) + supconv v \<epsilon> (snd z)
        - (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2)
      + ((1/\<epsilon> + 1/\<epsilon> + 2*\<alpha>)/2) * (norm z)\<^sup>2)"
proof -
  have ce: "0 \<le> 1/\<epsilon>" using e by simp
  have A: "convex_on UNIV
      (\<lambda>z::'a \<times> 'a. supconv u \<epsilon> (fst z) + ((1/\<epsilon>)/2) * (norm z)\<^sup>2)"
    by (rule semiconvex_of_fst[OF supconv_semiconvex'[OF Bu e] ce])
  have B: "convex_on UNIV
      (\<lambda>z::'a \<times> 'a. supconv v \<epsilon> (snd z) + ((1/\<epsilon>)/2) * (norm z)\<^sup>2)"
    by (rule semiconvex_of_snd[OF supconv_semiconvex'[OF Bv e] ce])
  have AB: "convex_on UNIV (\<lambda>z::'a \<times> 'a.
      (supconv u \<epsilon> (fst z) + supconv v \<epsilon> (snd z))
      + ((1/\<epsilon> + 1/\<epsilon>)/2) * (norm z)\<^sup>2)"
    by (rule semiconvex_add[OF A B])
  have C: "convex_on UNIV (\<lambda>z::'a \<times> 'a.
      - ((\<alpha>/2) * (norm (fst z - snd z))\<^sup>2) + ((2*\<alpha>)/2) * (norm z)\<^sup>2)"
    by (rule semiconvex_penalty[OF a])
  have ABC: "convex_on UNIV (\<lambda>z::'a \<times> 'a.
      ((supconv u \<epsilon> (fst z) + supconv v \<epsilon> (snd z))
        + - ((\<alpha>/2) * (norm (fst z - snd z))\<^sup>2))
      + (((1/\<epsilon> + 1/\<epsilon>) + 2*\<alpha>)/2) * (norm z)\<^sup>2)"
    by (rule semiconvex_add[OF AB C])
  have eq: "(\<lambda>z::'a \<times> 'a.
        ((supconv u \<epsilon> (fst z) + supconv v \<epsilon> (snd z))
          + - ((\<alpha>/2) * (norm (fst z - snd z))\<^sup>2))
        + (((1/\<epsilon> + 1/\<epsilon>) + 2*\<alpha>)/2) * (norm z)\<^sup>2)
      = (\<lambda>z::'a \<times> 'a.
        (supconv u \<epsilon> (fst z) + supconv v \<epsilon> (snd z)
          - (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2)
        + ((1/\<epsilon> + 1/\<epsilon> + 2*\<alpha>)/2) * (norm z)\<^sup>2)"
    by (rule ext) simp
  show ?thesis using ABC unfolding eq .
qed

subsection \<open>The engine in general form\<close>

text \<open>\<open>supconv_jensen_alexandrov_point\<close> was stated for a sup-convolution, but
  the only property it used was semiconvexity, and the doubled functional is
  semiconvex without being a sup-convolution. So the engine is restated for an
  arbitrary semiconvex \<open>\<phi>\<close>, and strengthened with the INTERIORITY
  \<open>dist x \<xi> < \<rho>\<close> that the maximum conditions need in order to apply
  \<open>second_order_interior_max\<close>.\<close>

theorem semiconvex_jensen_alexandrov_point:
  fixes \<phi> :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV (\<lambda>z. \<phi> z + (c/2) * (norm z)\<^sup>2)"
    and c: "0 < c"
    and rho: "0 < \<rho>" "\<rho> < r"
    and bnd: "\<And>y. y \<in> cball \<xi> r \<Longrightarrow> \<rho> \<le> dist y \<xi> \<Longrightarrow> \<phi> y \<le> m"
    and d: "0 < d" and small: "2 * d * r < \<phi> \<xi> - m"
  shows "\<exists>x p q X. dist x \<xi> < \<rho> \<and> norm p \<le> d
      \<and> (\<forall>y \<in> cball \<xi> r. \<phi> y + p \<bullet> y \<le> \<phi> x + p \<bullet> x)
      \<and> bounded_linear X \<and> (\<forall>v w. v \<bullet> X w = w \<bullet> X v)
      \<and> ((\<lambda>k. (\<phi> (x + k) - \<phi> x - q \<bullet> k - (k \<bullet> X k)/2) / (norm k)\<^sup>2)
          \<longlongrightarrow> 0) (at 0)"
proof -
  have r: "0 < r" using rho by simp
  define J where "J = {x \<in> cball \<xi> r. \<exists>p. norm p \<le> d
      \<and> (\<forall>y \<in> cball \<xi> r. \<phi> y + p \<bullet> y \<le> \<phi> x + p \<bullet> x)}"
  define N where "N = {y. \<not> (\<exists>q X. bounded_linear X \<and> (\<forall>v w. v \<bullet> X w = w \<bullet> X v)
      \<and> ((\<lambda>k. (\<phi> (y + k) - \<phi> y - q \<bullet> k - (k \<bullet> X k)/2) / (norm k)\<^sup>2)
          \<longlongrightarrow> 0) (at 0))}"
  have nJ: "\<not> negligible J"
    unfolding J_def by (rule jensen_lemma[OF cvx c rho(1) rho(2) bnd d small])
  have nN: "negligible N"
    unfolding N_def by (rule semiconvex_alexandrov[OF cvx])
  have "\<not> (J \<subseteq> N)"
  proof
    assume sub: "J \<subseteq> N"
    have "negligible J" by (rule negligible_subset[OF nN sub])
    with nJ show False ..
  qed
  then obtain x where xJ: "x \<in> J" and xN: "x \<notin> N" by blast
  from xJ obtain p where np: "norm p \<le> d" and xin: "x \<in> cball \<xi> r"
    and xmax: "\<forall>y \<in> cball \<xi> r. \<phi> y + p \<bullet> y \<le> \<phi> x + p \<bullet> x"
    unfolding J_def by blast
  have xmax': "\<And>y. y \<in> cball \<xi> r \<Longrightarrow> \<phi> y + p \<bullet> y \<le> \<phi> x + p \<bullet> x"
    using xmax by blast
  have deep: "dist x \<xi> < \<rho>"
    by (rule perturbed_maximiser_deep_interior[OF bnd r less_imp_le[OF d]
        small np xin xmax'])
  from xN obtain q X where blX: "bounded_linear X"
    and symX: "\<forall>v w. v \<bullet> X w = w \<bullet> X v"
    and lim: "((\<lambda>k. (\<phi> (x + k) - \<phi> x - q \<bullet> k - (k \<bullet> X k)/2) / (norm k)\<^sup>2)
        \<longlongrightarrow> 0) (at 0)"
    unfolding N_def by blast
  show ?thesis
    using deep np xmax blX symX lim by blast
qed

subsection \<open>Uniqueness of the second-order form, and block diagonality\<close>

text \<open>The quadratic form in a second-order expansion is UNIQUE. Restricting to
  a ray \<open>t \<mapsto> t *\<^sub>R v\<close> makes the difference quotient CONSTANT in \<open>t\<close>, and a
  constant that tends to \<open>0\<close> is \<open>0\<close>.

  This is what makes the theorem on sums reachable here without the
  \<open>A + \<epsilon> A\<^sup>2\<close> matrix argument of the textbook proof: for a function of the form
  \<open>a (fst z) + b (snd z)\<close> the two slice expansions reassemble into a
  block-diagonal quadratic form, and by uniqueness the product form must EQUAL
  it, so the off-diagonal blocks vanish EXACTLY rather than only after an
  \<open>\<epsilon>\<close>-perturbation.\<close>

lemma second_order_form_unique:
  fixes g :: "'a::euclidean_space \<Rightarrow> real"
  assumes l1: "((\<lambda>k. (g k - (k \<bullet> Q1 k)/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and l2: "((\<lambda>k. (g k - (k \<bullet> Q2 k)/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and b1: "bounded_linear Q1" and b2: "bounded_linear Q2"
  shows "v \<bullet> Q1 v = v \<bullet> Q2 v"
proof (cases "v = 0")
  case True
  have "Q1 0 = 0" using b1 by (simp add: linear_simps)
  moreover have "Q2 0 = 0" using b2 by (simp add: linear_simps)
  ultimately show ?thesis unfolding True by simp
next
  case False
  have nv: "0 < (norm v)\<^sup>2" using False by simp
  have q1: "(t *\<^sub>R v) \<bullet> Q1 (t *\<^sub>R v) = t\<^sup>2 * (v \<bullet> Q1 v)" for t :: real
    using b1 by (simp add: linear_simps power2_eq_square)
  have q2: "(t *\<^sub>R v) \<bullet> Q2 (t *\<^sub>R v) = t\<^sup>2 * (v \<bullet> Q2 v)" for t :: real
    using b2 by (simp add: linear_simps power2_eq_square)
  have flt: "filterlim (\<lambda>t::real. t *\<^sub>R v) (at 0) (at_right 0)"
  proof (rule filterlim_atI)
    have "((\<lambda>t::real. t *\<^sub>R v) \<longlongrightarrow> 0 *\<^sub>R v) (at_right 0)"
      by (intro tendsto_intros)
    thus "((\<lambda>t::real. t *\<^sub>R v) \<longlongrightarrow> 0) (at_right 0)" by simp
    show "\<forall>\<^sub>F t in at_right (0::real). t *\<^sub>R v \<noteq> 0"
      using eventually_at_right_less by (rule eventually_mono) (use False in simp)
  qed
  have dd: "(g k - (k \<bullet> Q1 k)/2)/(norm k)\<^sup>2 - (g k - (k \<bullet> Q2 k)/2)/(norm k)\<^sup>2
      = ((k \<bullet> Q2 k)/2 - (k \<bullet> Q1 k)/2) / (norm k)\<^sup>2" for k
    by (simp add: diff_divide_distrib[symmetric])
  have d0: "((\<lambda>k. ((k \<bullet> Q2 k)/2 - (k \<bullet> Q1 k)/2) / (norm k)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    using tendsto_diff[OF l1 l2] unfolding dd by simp
  have dr: "((\<lambda>t. (((t *\<^sub>R v) \<bullet> Q2 (t *\<^sub>R v))/2 - ((t *\<^sub>R v) \<bullet> Q1 (t *\<^sub>R v))/2)
      / (norm (t *\<^sub>R v))\<^sup>2) \<longlongrightarrow> 0) (at_right 0)"
    by (rule filterlim_compose[OF d0 flt])
  have const: "(((t *\<^sub>R v) \<bullet> Q2 (t *\<^sub>R v))/2 - ((t *\<^sub>R v) \<bullet> Q1 (t *\<^sub>R v))/2)
      / (norm (t *\<^sub>R v))\<^sup>2
      = ((v \<bullet> Q2 v)/2 - (v \<bullet> Q1 v)/2) / (norm v)\<^sup>2" if t: "t \<noteq> 0" for t :: real
  proof -
    have nn: "(norm (t *\<^sub>R v))\<^sup>2 = t\<^sup>2 * (norm v)\<^sup>2"
      by (simp add: power_mult_distrib)
    have tt: "t\<^sup>2 \<noteq> 0" using t by simp
    show ?thesis unfolding q1 q2 nn using tt nv by (simp add: field_simps)
  qed
  have ev: "\<forall>\<^sub>F t in at_right (0::real).
      (((t *\<^sub>R v) \<bullet> Q2 (t *\<^sub>R v))/2 - ((t *\<^sub>R v) \<bullet> Q1 (t *\<^sub>R v))/2)
        / (norm (t *\<^sub>R v))\<^sup>2
      = ((v \<bullet> Q2 v)/2 - (v \<bullet> Q1 v)/2) / (norm v)\<^sup>2"
  proof (rule eventually_mono[OF eventually_at_right_less])
    fix t :: real assume "0 < t"
    hence "t \<noteq> 0" by simp
    thus "(((t *\<^sub>R v) \<bullet> Q2 (t *\<^sub>R v))/2 - ((t *\<^sub>R v) \<bullet> Q1 (t *\<^sub>R v))/2)
        / (norm (t *\<^sub>R v))\<^sup>2
        = ((v \<bullet> Q2 v)/2 - (v \<bullet> Q1 v)/2) / (norm v)\<^sup>2"
      by (rule const)
  qed
  have "((\<lambda>t::real. ((v \<bullet> Q2 v)/2 - (v \<bullet> Q1 v)/2) / (norm v)\<^sup>2)
      \<longlongrightarrow> 0) (at_right 0)"
    using dr unfolding tendsto_cong[OF ev] .
  moreover have "((\<lambda>t::real. ((v \<bullet> Q2 v)/2 - (v \<bullet> Q1 v)/2) / (norm v)\<^sup>2)
      \<longlongrightarrow> ((v \<bullet> Q2 v)/2 - (v \<bullet> Q1 v)/2) / (norm v)\<^sup>2) (at_right 0)"
    by (rule tendsto_const)
  moreover have "at_right (0::real) \<noteq> bot"
    using trivial_limit_at_right_real unfolding trivial_limit_def by blast
  ultimately have "((v \<bullet> Q2 v)/2 - (v \<bullet> Q1 v)/2) / (norm v)\<^sup>2 = 0"
    by (blast dest: tendsto_unique)
  thus ?thesis using nv by (simp add: field_simps)
qed

text \<open>The reusable ray step: along a fixed direction the second-order
  expansion says exactly that \<open>F (t *\<^sub>R w) / t\<^sup>2\<close> converges to half the
  quadratic form at \<open>w\<close>. Applying this to the product expansion and to the two
  slice expansions, and adding the latter two, identifies the product form with
  the block-diagonal one.\<close>

lemma expansion_ray_limit:
  fixes F :: "'a::euclidean_space \<Rightarrow> real"
  assumes exp: "((\<lambda>k. (F k - (k \<bullet> Q k)/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and scal: "\<And>s u. Q (s *\<^sub>R u) = s *\<^sub>R Q u" and w: "w \<noteq> 0"
  shows "((\<lambda>t. F (t *\<^sub>R w) / t\<^sup>2) \<longlongrightarrow> (w \<bullet> Q w)/2) (at_right 0)"
proof -
  have nw: "0 < (norm w)\<^sup>2" using w by simp
  have quad: "(t *\<^sub>R w) \<bullet> Q (t *\<^sub>R w) = t\<^sup>2 * (w \<bullet> Q w)" for t :: real
    by (simp add: scal power2_eq_square)
  have flt: "filterlim (\<lambda>t::real. t *\<^sub>R w) (at 0) (at_right 0)"
  proof (rule filterlim_atI)
    have "((\<lambda>t::real. t *\<^sub>R w) \<longlongrightarrow> 0 *\<^sub>R w) (at_right 0)"
      by (intro tendsto_intros)
    thus "((\<lambda>t::real. t *\<^sub>R w) \<longlongrightarrow> 0) (at_right 0)" by simp
    show "\<forall>\<^sub>F t in at_right (0::real). t *\<^sub>R w \<noteq> 0"
      using eventually_at_right_less by (rule eventually_mono) (use w in simp)
  qed
  have c: "((\<lambda>t. (F (t *\<^sub>R w) - ((t *\<^sub>R w) \<bullet> Q (t *\<^sub>R w))/2)
      / (norm (t *\<^sub>R w))\<^sup>2) \<longlongrightarrow> 0) (at_right 0)"
    by (rule filterlim_compose[OF exp flt])
  have rw: "(F (t *\<^sub>R w) - ((t *\<^sub>R w) \<bullet> Q (t *\<^sub>R w))/2) / (norm (t *\<^sub>R w))\<^sup>2
      = (F (t *\<^sub>R w) / t\<^sup>2 - (w \<bullet> Q w)/2) / (norm w)\<^sup>2" if t: "t \<noteq> 0" for t :: real
  proof -
    have nn: "(norm (t *\<^sub>R w))\<^sup>2 = t\<^sup>2 * (norm w)\<^sup>2"
      by (simp add: power_mult_distrib)
    have tt: "t\<^sup>2 \<noteq> 0" using t by simp
    show ?thesis unfolding quad nn using tt nw by (simp add: field_simps)
  qed
  have ev: "\<forall>\<^sub>F t in at_right (0::real).
      (F (t *\<^sub>R w) - ((t *\<^sub>R w) \<bullet> Q (t *\<^sub>R w))/2) / (norm (t *\<^sub>R w))\<^sup>2
      = (F (t *\<^sub>R w) / t\<^sup>2 - (w \<bullet> Q w)/2) / (norm w)\<^sup>2"
  proof (rule eventually_mono[OF eventually_at_right_less])
    fix t :: real assume "0 < t"
    hence "t \<noteq> 0" by simp
    thus "(F (t *\<^sub>R w) - ((t *\<^sub>R w) \<bullet> Q (t *\<^sub>R w))/2) / (norm (t *\<^sub>R w))\<^sup>2
        = (F (t *\<^sub>R w) / t\<^sup>2 - (w \<bullet> Q w)/2) / (norm w)\<^sup>2" by (rule rw)
  qed
  have c2: "((\<lambda>t. (F (t *\<^sub>R w) / t\<^sup>2 - (w \<bullet> Q w)/2) / (norm w)\<^sup>2)
      \<longlongrightarrow> 0) (at_right 0)"
    using c unfolding tendsto_cong[OF ev] .
  have c3: "((\<lambda>t. ((F (t *\<^sub>R w) / t\<^sup>2 - (w \<bullet> Q w)/2) / (norm w)\<^sup>2) * (norm w)\<^sup>2)
      \<longlongrightarrow> 0 * (norm w)\<^sup>2) (at_right 0)"
    by (rule tendsto_mult[OF c2 tendsto_const])
  have rw2: "((F (t *\<^sub>R w) / t\<^sup>2 - (w \<bullet> Q w)/2) / (norm w)\<^sup>2) * (norm w)\<^sup>2
      = F (t *\<^sub>R w) / t\<^sup>2 - (w \<bullet> Q w)/2" for t :: real
    using nw by simp
  have c4: "((\<lambda>t. F (t *\<^sub>R w) / t\<^sup>2 - (w \<bullet> Q w)/2) \<longlongrightarrow> 0) (at_right 0)"
    using c3 unfolding rw2 by simp
  have "((\<lambda>t. (F (t *\<^sub>R w) / t\<^sup>2 - (w \<bullet> Q w)/2) + (w \<bullet> Q w)/2)
      \<longlongrightarrow> 0 + (w \<bullet> Q w)/2) (at_right 0)"
    by (rule tendsto_add[OF c4 tendsto_const])
  thus ?thesis by simp
qed

text \<open>BLOCK DIAGONALITY. For a function of the form \<open>a (fst z) + b (snd z)\<close>
  the product quadratic form is exactly the sum of the two slice forms: the
  off-diagonal blocks vanish IDENTICALLY. Along the ray \<open>t *\<^sub>R (h,g)\<close> the
  difference quotient of the product splits as a sum of the two slice
  quotients, and the three ray limits then force the identity. No
  \<open>\<epsilon>\<close>-perturbation and no spectral theory are involved.\<close>

theorem product_form_block_diagonal:
  fixes a :: "'a::euclidean_space \<Rightarrow> real" and b :: "'b::euclidean_space \<Rightarrow> real"
  assumes exp: "((\<lambda>k. ((a (fst (z + k)) + b (snd (z + k)))
        - (a (fst z) + b (snd z)) - q \<bullet> k - (k \<bullet> W k)/2) / (norm k)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    and scW: "\<And>s u. W (s *\<^sub>R u) = s *\<^sub>R W u"
    and h: "h \<noteq> 0" and g: "g \<noteq> 0"
  shows "(h, g) \<bullet> W (h, g) = h \<bullet> fst (W (h, 0)) + g \<bullet> snd (W (0, g))"
proof -
  define \<Psi> where "\<Psi> = (\<lambda>z'::'a \<times> 'b. a (fst z') + b (snd z'))"
  have expP: "((\<lambda>k. (\<Psi> (z + k) - \<Psi> z - q \<bullet> k - (k \<bullet> W k)/2) / (norm k)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    unfolding \<Psi>_def by (rule exp)
  have hg: "((h, g) :: 'a \<times> 'b) \<noteq> 0" using h by (simp add: zero_prod_def)
  have L0: "((\<lambda>t. (\<Psi> (z + t *\<^sub>R (h, g)) - \<Psi> z - q \<bullet> (t *\<^sub>R (h, g))) / t\<^sup>2)
      \<longlongrightarrow> ((h, g) \<bullet> W (h, g))/2) (at_right 0)"
    by (rule expansion_ray_limit[OF expP scW hg])
  have expF: "((\<lambda>k. (\<Psi> (fst z + k, snd z) - \<Psi> z - (fst q) \<bullet> k
      - (k \<bullet> fst (W (k, 0)))/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    by (rule expansion_restrict_fst[OF expP])
  have scX: "fst (W (s *\<^sub>R u, 0)) = s *\<^sub>R fst (W (u, 0))" for s :: real and u
  proof -
    have e: "((s *\<^sub>R u, (0::'b))) = s *\<^sub>R ((u, (0::'b)))" by simp
    show ?thesis unfolding e scW by simp
  qed
  have L1: "((\<lambda>t. (\<Psi> (fst z + t *\<^sub>R h, snd z) - \<Psi> z - (fst q) \<bullet> (t *\<^sub>R h)) / t\<^sup>2)
      \<longlongrightarrow> (h \<bullet> fst (W (h, 0)))/2) (at_right 0)"
    by (rule expansion_ray_limit[OF expF scX h])
  have expS: "((\<lambda>k. (\<Psi> (fst z, snd z + k) - \<Psi> z - (snd q) \<bullet> k
      - (k \<bullet> snd (W (0, k)))/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    by (rule expansion_restrict_snd[OF expP])
  have scY: "snd (W (0, s *\<^sub>R u)) = s *\<^sub>R snd (W (0, u))" for s :: real and u
  proof -
    have e: "((0::'a), s *\<^sub>R u) = s *\<^sub>R ((0::'a), u)" by simp
    show ?thesis unfolding e scW by simp
  qed
  have L2: "((\<lambda>t. (\<Psi> (fst z, snd z + t *\<^sub>R g) - \<Psi> z - (snd q) \<bullet> (t *\<^sub>R g)) / t\<^sup>2)
      \<longlongrightarrow> (g \<bullet> snd (W (0, g)))/2) (at_right 0)"
    by (rule expansion_ray_limit[OF expS scY g])
  have Lsum: "((\<lambda>t. (\<Psi> (fst z + t *\<^sub>R h, snd z) - \<Psi> z - (fst q) \<bullet> (t *\<^sub>R h)) / t\<^sup>2
      + (\<Psi> (fst z, snd z + t *\<^sub>R g) - \<Psi> z - (snd q) \<bullet> (t *\<^sub>R g)) / t\<^sup>2)
      \<longlongrightarrow> (h \<bullet> fst (W (h, 0)))/2 + (g \<bullet> snd (W (0, g)))/2) (at_right 0)"
    by (rule tendsto_add[OF L1 L2])
  have split: "(\<Psi> (z + t *\<^sub>R (h, g)) - \<Psi> z - q \<bullet> (t *\<^sub>R (h, g))) / t\<^sup>2
      = (\<Psi> (fst z + t *\<^sub>R h, snd z) - \<Psi> z - (fst q) \<bullet> (t *\<^sub>R h)) / t\<^sup>2
      + (\<Psi> (fst z, snd z + t *\<^sub>R g) - \<Psi> z - (snd q) \<bullet> (t *\<^sub>R g)) / t\<^sup>2"
    for t :: real
  proof -
    have zk: "z + t *\<^sub>R ((h, g) :: 'a \<times> 'b) = (fst z + t *\<^sub>R h, snd z + t *\<^sub>R g)"
      by (cases z) simp
    have qk: "q \<bullet> (t *\<^sub>R ((h, g) :: 'a \<times> 'b))
        = (fst q) \<bullet> (t *\<^sub>R h) + (snd q) \<bullet> (t *\<^sub>R g)"
      by (cases q) simp
    have num: "\<Psi> (z + t *\<^sub>R (h, g)) - \<Psi> z - q \<bullet> (t *\<^sub>R (h, g))
        = (\<Psi> (fst z + t *\<^sub>R h, snd z) - \<Psi> z - (fst q) \<bullet> (t *\<^sub>R h))
        + (\<Psi> (fst z, snd z + t *\<^sub>R g) - \<Psi> z - (snd q) \<bullet> (t *\<^sub>R g))"
      unfolding zk qk \<Psi>_def by simp
    show ?thesis unfolding num by (rule add_divide_distrib)
  qed
  have L0': "((\<lambda>t. (\<Psi> (fst z + t *\<^sub>R h, snd z) - \<Psi> z - (fst q) \<bullet> (t *\<^sub>R h)) / t\<^sup>2
      + (\<Psi> (fst z, snd z + t *\<^sub>R g) - \<Psi> z - (snd q) \<bullet> (t *\<^sub>R g)) / t\<^sup>2)
      \<longlongrightarrow> ((h, g) \<bullet> W (h, g))/2) (at_right 0)"
    using L0 unfolding split .
  have nb: "at_right (0::real) \<noteq> bot"
    using trivial_limit_at_right_real unfolding trivial_limit_def by blast
  have "((h, g) \<bullet> W (h, g))/2
      = (h \<bullet> fst (W (h, 0)))/2 + (g \<bullet> snd (W (0, g)))/2"
    by (rule tendsto_unique[OF nb L0' Lsum])
  thus ?thesis by simp
qed

text \<open>The penalty is a quadratic, so its second-order expansion is EXACT: no
  remainder at all. Its gradient at \<open>zh\<close> is \<open>\<alpha> *\<^sub>R (Dz, -Dz)\<close> and its quadratic
  form is \<open>k \<mapsto> \<alpha> * norm (fst k - snd k)\<^sup>2\<close>, both written here as honest vectors
  and linear maps on the product so that they can be ADDED to the expansion of
  \<open>\<Psi>\<close> to recover the expansion of \<open>\<Psi> + pen\<close>, which is the separated form
  \<open>a (fst z) + b (snd z)\<close> that \<open>product_form_block_diagonal\<close> needs.

  Note the quadratic form VANISHES on the diagonal \<open>(v,v)\<close> \<^emph>\<open>and that is exactly
  why testing there kills the penalty and leaves only\<close> \<open>X \<preceq> Y\<close>.\<close>

lemma penalty_exact:
  fixes \<alpha> :: real and zh k :: "'a::euclidean_space \<times> 'a"
  shows "(\<alpha>/2) * (norm (fst (zh + k) - snd (zh + k)))\<^sup>2
       = (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2
       + (\<alpha> *\<^sub>R (fst zh - snd zh, - (fst zh - snd zh))) \<bullet> k
       + (k \<bullet> (\<alpha> *\<^sub>R (fst k - snd k, snd k - fst k)))/2"
proof -
  have d1: "fst (zh + k) - snd (zh + k)
      = (fst zh - snd zh) + (fst k - snd k)"
    by (cases zh; cases k) simp
  have e1: "(norm ((fst zh - snd zh) + (fst k - snd k)))\<^sup>2
      = (norm (fst zh - snd zh))\<^sup>2
        + 2*((fst zh - snd zh) \<bullet> (fst k - snd k))
        + (norm (fst k - snd k))\<^sup>2"
    by (simp add: power2_norm_eq_inner inner_add_left inner_add_right
        inner_commute)
  have e2: "(\<alpha> *\<^sub>R (fst zh - snd zh, - (fst zh - snd zh))) \<bullet> k
      = \<alpha> * ((fst zh - snd zh) \<bullet> (fst k - snd k))"
    by (cases k) (simp add: inner_diff_right algebra_simps)
  have e3: "k \<bullet> (\<alpha> *\<^sub>R (fst k - snd k, snd k - fst k))
      = \<alpha> * (norm (fst k - snd k))\<^sup>2"
    by (cases k) (simp add: power2_norm_eq_inner inner_diff_left
        inner_diff_right inner_commute algebra_simps)
  show ?thesis unfolding d1 e1 e2 e3 by (simp add: algebra_simps)
qed

text \<open>And the penalty's quadratic form is linear in \<open>k\<close> and vanishes on the
  diagonal.\<close>

lemma penalty_form_scaleR:
  fixes \<alpha> s :: real and k :: "'a::euclidean_space \<times> 'a"
  shows "(\<alpha> *\<^sub>R (fst (s *\<^sub>R k) - snd (s *\<^sub>R k), snd (s *\<^sub>R k) - fst (s *\<^sub>R k)))
      = s *\<^sub>R (\<alpha> *\<^sub>R (fst k - snd k, snd k - fst k))"
  by (cases k) (simp add: scaleR_diff_right mult.commute)

lemma penalty_form_diagonal:
  fixes \<alpha> :: real and v :: "'a::euclidean_space"
  shows "((v, v) :: 'a \<times> 'a)
      \<bullet> (\<alpha> *\<^sub>R (fst (v, v) - snd (v, v), snd (v, v) - fst (v, v))) = 0"
  by simp

subsection \<open>The theorem on sums: matrix inequality\<close>

text \<open>THE THEOREM ON SUMS, algebraic core. Suppose the doubled functional
  \<open>a (fst z) + b (snd z) - (\<alpha>/2) * norm (fst z - snd z)\<^sup>2\<close> has a second-order
  expansion at \<open>zh\<close> with a NEGATIVE SEMIDEFINITE form \<open>W\<close> \<^emph>\<open>which is what an
  interior maximum supplies\<close>. Adding the penalty's exact expansion turns the
  form into \<open>WP\<close> and the functional into the SEPARATED form
  \<open>a (fst z) + b (snd z)\<close>; block diagonality then splits \<open>WP\<close> into its two
  slice matrices, and testing on the diagonal \<open>(v,v)\<close> \<^emph>\<open>where the penalty
  contributes nothing\<close> leaves exactly the matrix inequality.

  With \<open>b = - w\<close> the second slice matrix is \<open>- Y\<close>, so the conclusion reads
  \<open>v \<cdot> X v \<le> v \<cdot> Y v\<close>, i.e. \<open>X \<preceq> Y\<close>: this is what the comparison principle
  feeds to degenerate ellipticity.\<close>

theorem sums_matrix_inequality:
  fixes a b :: "'a::euclidean_space \<Rightarrow> real"
    and W :: "'a \<times> 'a \<Rightarrow> 'a \<times> 'a"
  assumes expPsi: "((\<lambda>k. ((a (fst (zh + k)) + b (snd (zh + k))
          - (\<alpha>/2) * (norm (fst (zh + k) - snd (zh + k)))\<^sup>2)
        - (a (fst zh) + b (snd zh) - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
        - q \<bullet> k - (k \<bullet> W k)/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and scW: "\<And>s u. W (s *\<^sub>R u) = s *\<^sub>R W u"
    and neg: "\<And>k. k \<bullet> W k \<le> 0"
    and v: "v \<noteq> 0"
  shows "v \<bullet> fst (W (v, 0) + \<alpha> *\<^sub>R (v - 0, 0 - v))
       + v \<bullet> snd (W (0, v) + \<alpha> *\<^sub>R (0 - v, v - 0)) \<le> 0"
proof -
  define P where "P = (\<lambda>k::'a \<times> 'a. \<alpha> *\<^sub>R (fst k - snd k, snd k - fst k))"
  define WP where "WP = (\<lambda>k::'a \<times> 'a. W k + P k)"
  define g0 where "g0 = \<alpha> *\<^sub>R (fst zh - snd zh, - (fst zh - snd zh))"
  have scP: "P (s *\<^sub>R u) = s *\<^sub>R P u" for s :: real and u
    unfolding P_def by (rule penalty_form_scaleR)
  have scWP: "WP (s *\<^sub>R u) = s *\<^sub>R WP u" for s :: real and u
    unfolding WP_def scW scP by (simp add: scaleR_add_right)
  have pen: "(\<alpha>/2) * (norm (fst (zh + k) - snd (zh + k)))\<^sup>2
      = (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2 + g0 \<bullet> k + (k \<bullet> P k)/2" for k
    unfolding g0_def P_def by (rule penalty_exact)
  have rem: "(a (fst (zh + k)) + b (snd (zh + k)))
        - (a (fst zh) + b (snd zh)) - (q + g0) \<bullet> k - (k \<bullet> WP k)/2
      = ((a (fst (zh + k)) + b (snd (zh + k))
          - (\<alpha>/2) * (norm (fst (zh + k) - snd (zh + k)))\<^sup>2)
        - (a (fst zh) + b (snd zh) - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
        - q \<bullet> k - (k \<bullet> W k)/2)" for k
  proof -
    have iWP: "k \<bullet> WP k = k \<bullet> W k + k \<bullet> P k"
      unfolding WP_def by (simp add: inner_add_right)
    have iq: "(q + g0) \<bullet> k = q \<bullet> k + g0 \<bullet> k"
      by (simp add: inner_add_left)
    show ?thesis unfolding iWP iq pen by simp argo
  qed
  have expTheta: "((\<lambda>k. ((a (fst (zh + k)) + b (snd (zh + k)))
      - (a (fst zh) + b (snd zh)) - (q + g0) \<bullet> k - (k \<bullet> WP k)/2)
      / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    using expPsi unfolding rem .
  have blk: "(v, v) \<bullet> WP (v, v)
      = v \<bullet> fst (WP (v, 0)) + v \<bullet> snd (WP (0, v))"
    by (rule product_form_block_diagonal[OF expTheta scWP v v])
  have pdiag: "(v, v) \<bullet> P (v, v) = 0"
    unfolding P_def by (rule penalty_form_diagonal)
  have "(v, v) \<bullet> WP (v, v) = (v, v) \<bullet> W (v, v) + (v, v) \<bullet> P (v, v)"
    unfolding WP_def by (simp add: inner_add_right)
  hence "(v, v) \<bullet> WP (v, v) = (v, v) \<bullet> W (v, v)"
    unfolding pdiag by simp
  moreover have "(v, v) \<bullet> W (v, v) \<le> 0" by (rule neg)
  ultimately have "v \<bullet> fst (WP (v, 0)) + v \<bullet> snd (WP (0, v)) \<le> 0"
    unfolding blk[symmetric] by simp
  thus ?thesis unfolding WP_def P_def by simp
qed

end
