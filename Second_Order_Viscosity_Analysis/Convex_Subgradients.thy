section \<open>Subgradients of convex functions\<close>

(*<*)
theory Convex_Subgradients
  imports "HOL-Analysis.Analysis"
begin

(*>*)

text \<open>
  Convex-analytic foundations for the Crandall--Ishii development:
  subgradients, monotonicity of the subdifferential, and nonemptiness via
  a supporting hyperplane, feeding the proximal map and Minty resolvent
  below, which reduce Alexandrov's theorem to Rademacher's.
\<close>

definition subdiff :: "('a::euclidean_space \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "subdiff f x = {p. \<forall>y. f x + p \<bullet> (y - x) \<le> f y}"

lemma subdiffI: "(\<And>y. f x + p \<bullet> (y - x) \<le> f y) \<Longrightarrow> p \<in> subdiff f x"
  by (simp add: subdiff_def)

lemma subdiffD: "p \<in> subdiff f x \<Longrightarrow> f x + p \<bullet> (y - x) \<le> f y"
  by (simp add: subdiff_def)

text \<open>Monotonicity of the subdifferential: the defining inequalities at
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

text \<open>The epigraph of a finite convex function is closed and convex; the
  supporting hyperplane at its frontier point \<open>(x, f x)\<close> is non-vertical
  and normalizes to a subgradient.\<close>

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
  text \<open>Uses \<open>supporting_hyperplane_rel_boundary\<close> and
  \<open>epigraph_frontier_point\<close>, since the epigraph has nonempty interior.\<close>
  have mem: "(x, f x) \<in> epigraph UNIV f"
    by (simp add: mem_epigraph)
  have neI: "interior (epigraph UNIV f) \<noteq> {}"
  proof -
    have op: "open {z :: 'a \<times> real. f (fst z) - snd z < 0}"
      by (intro open_Collect_less continuous_on_diff continuous_on_snd
          continuous_on_compose2[OF cf continuous_on_fst]) auto
    have subep: "{z :: 'a \<times> real. f (fst z) - snd z < 0} \<subseteq> epigraph UNIV f"
      by (auto simp: epigraph_def)
    have "(x, f x + 1) \<in> {z :: 'a \<times> real. f (fst z) - snd z < 0}"
      by simp
    then have "(x, f x + 1) \<in> interior (epigraph UNIV f)"
      using interior_maximal[OF subep op] by blast
    then show ?thesis by blast
  qed
  have notint: "(x, f x) \<notin> interior (epigraph UNIV f)"
    using epigraph_frontier_point[OF cf, of x]
    by (auto simp: frontier_def)
  have notrel: "(x, f x) \<notin> rel_interior (epigraph UNIV f)"
    using rel_interior_nonempty_interior[OF neI] notint by simp
  obtain a where a0: "a \<noteq> 0"
    and supE0: "\<And>y. y \<in> epigraph UNIV f \<Longrightarrow> a \<bullet> (x, f x) \<le> a \<bullet> y"
    by (rule supporting_hyperplane_rel_boundary[OF cvxE mem notrel]) blast
  have sup: "a \<bullet> (x, f x) \<le> a \<bullet> z"
    if "z \<in> closure (epigraph UNIV f)" for z
    using supE0 that clE by simp
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

text \<open>For a finite convex function, \<open>y \<mapsto> f y + dist x y\<^sup>2/2\<close> attains a
  unique minimum, coercive by an affine subgradient bound.\<close>

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

text \<open>Uniqueness of the proximal point, by strict convexity of the
  quadratic penalty.\<close>

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

text \<open>The proximal characterization: \<open>x - prox f x\<close> is a subgradient at
  the proximal point.\<close>

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

text \<open>Minty: \<open>id + subdiff f\<close> is surjective (witnessed by the proximal
  point), and \<open>prox f\<close> is nonexpansive --- the route to Alexandrov's
  theorem via Rademacher's.\<close>

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


(*<*)
end
(*>*)
