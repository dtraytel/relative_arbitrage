section \<open>The Crandall--Ishii theorem on sums, assembled\<close>

(*<*)
theory Crandall_Ishii_Sums
  imports Theorem_On_Sums Doubling_Of_Variables
begin

(*>*)

text \<open>The machinery of @{theory Second_Order_Viscosity_Analysis.Theorem_On_Sums}
  and @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables} proves the
  Crandall--Ishii theorem on sums in the distributed form a comparison
  argument consumes.  This theory assembles it into standalone statements in
  the standard vocabulary of the literature: second-order semijets, their
  closures, and two named theorems for the quadratic coupling
  \<open>(\<alpha>/2)\<parallel>x - y\<parallel>\<^sup>2\<close> --- the instance every standard uniqueness proof,
  including the one in this development, actually uses.  The staged form
  (\<open>theorem_on_sums_quadratic\<close>) exhibits genuine jets with quantitative
  control; the closed-jet form (\<open>theorem_on_sums_quadratic_closed\<close>) is the
  classical statement, with the two-sided bound \<open>-(1/\<lambda>) I \<preceq> X \<preceq> Y \<preceq> (1/\<lambda>) I\<close>
  for every regularisation scale \<open>\<lambda>\<close> with \<open>2\<lambda>\<alpha> < 1\<close>.\<close>

section \<open>Second-order semijets\<close>

definition superjet :: "('a::euclidean_space \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> ('a \<times> ('a \<Rightarrow> 'a)) set"
  where
  "superjet u x = {(p, X). linear X \<and> (\<forall>a b. a \<bullet> X b = b \<bullet> X a) \<and>
     (\<forall>e>0. \<exists>d>0. \<forall>k. norm k < d \<longrightarrow>
        u (x + k) \<le> u x + p \<bullet> k + (k \<bullet> X k)/2 + e * (norm k)\<^sup>2)}"

definition subjet :: "('a::euclidean_space \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> ('a \<times> ('a \<Rightarrow> 'a)) set"
  where
  "subjet w x = {(p, X). linear X \<and> (\<forall>a b. a \<bullet> X b = b \<bullet> X a) \<and>
     (\<forall>e>0. \<exists>d>0. \<forall>k. norm k < d \<longrightarrow>
        w x + p \<bullet> k + (k \<bullet> X k)/2 - e * (norm k)\<^sup>2 \<le> w (x + k))}"

lemma linear_neg_iff: "linear (\<lambda>k. - f k) \<longleftrightarrow> linear f"
proof
  assume "linear (\<lambda>k. - f k)"
  then have "linear (\<lambda>k. - (- f k))" by (rule linear_compose_neg)
  then show "linear f" by simp
qed (rule linear_compose_neg)

lemma subjet_neg_superjet:
  "(p, X) \<in> subjet w x \<longleftrightarrow> (- p, \<lambda>k. - X k) \<in> superjet (\<lambda>z. - w z) x"
  unfolding subjet_def superjet_def
  by (auto simp: linear_neg_iff algebra_simps)

lemma superjet_mono:
  assumes j: "(p, X) \<in> superjet u x" and lin: "linear X'"
    and sym: "\<And>a b. a \<bullet> X' b = b \<bullet> X' a"
    and le: "\<And>v. v \<bullet> X v \<le> v \<bullet> X' v"
  shows "(p, X') \<in> superjet u x"
proof -
  have h: "\<exists>d>0. \<forall>k. norm k < d \<longrightarrow>
      u (x + k) \<le> u x + p \<bullet> k + (k \<bullet> X' k)/2 + e * (norm k)\<^sup>2"
    if e: "0 < e" for e
  proof -
    obtain d where d: "0 < d" and b: "\<And>k. norm k < d \<Longrightarrow>
        u (x + k) \<le> u x + p \<bullet> k + (k \<bullet> X k)/2 + e * (norm k)\<^sup>2"
      using j e unfolding superjet_def by blast
    have "u (x + k) \<le> u x + p \<bullet> k + (k \<bullet> X' k)/2 + e * (norm k)\<^sup>2"
      if kd: "norm k < d" for k
      using b[OF kd] le[of k] by linarith
    then show ?thesis using d by blast
  qed
  show ?thesis unfolding superjet_def using lin sym h by auto
qed


subsection \<open>Closed semijets\<close>

text \<open>The closure in the sense of Crandall--Ishii: limits of jets at nearby
  points along which the function values also converge.  Convergence of the
  forms is pointwise, which on a euclidean space agrees with every other
  reasonable topology on linear maps.  The \<open>linear\<close> and symmetry conjuncts
  are redundant --- both pass to pointwise limits --- but keep the set
  self-contained for a consumer.\<close>

definition superjet_cl :: "('a::euclidean_space \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> ('a \<times> ('a \<Rightarrow> 'a)) set"
  where
  "superjet_cl u x = {(p, X). linear X \<and> (\<forall>a b. a \<bullet> X b = b \<bullet> X a) \<and>
     (\<exists>xs ps Xs. (\<forall>i :: nat. (ps i, Xs i) \<in> superjet u (xs i)) \<and>
        xs \<longlonglongrightarrow> x \<and> (\<lambda>i. u (xs i)) \<longlonglongrightarrow> u x \<and>
        ps \<longlonglongrightarrow> p \<and> (\<forall>v. (\<lambda>i. Xs i v) \<longlonglongrightarrow> X v))}"

definition subjet_cl :: "('a::euclidean_space \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> ('a \<times> ('a \<Rightarrow> 'a)) set"
  where
  "subjet_cl w x = {(p, X). linear X \<and> (\<forall>a b. a \<bullet> X b = b \<bullet> X a) \<and>
     (\<exists>xs ps Xs. (\<forall>i :: nat. (ps i, Xs i) \<in> subjet w (xs i)) \<and>
        xs \<longlonglongrightarrow> x \<and> (\<lambda>i. w (xs i)) \<longlonglongrightarrow> w x \<and>
        ps \<longlonglongrightarrow> p \<and> (\<forall>v. (\<lambda>i. Xs i v) \<longlonglongrightarrow> X v))}"

lemma superjet_subset_cl: "superjet u x \<subseteq> superjet_cl u x"
  unfolding superjet_cl_def
  by (auto intro!: exI[of _ "\<lambda>_. x"] exI[of _ "\<lambda>_. _"]
      simp: superjet_def)

lemma subjet_subset_cl: "subjet w x \<subseteq> subjet_cl w x"
  unfolding subjet_cl_def
  by (auto intro!: exI[of _ "\<lambda>_. x"] exI[of _ "\<lambda>_. _"]
      simp: subjet_def)

section \<open>Upper semicontinuity toolbox\<close>

text \<open>The session sits on plain HOL-Analysis, so the two attainment facts
  below are proved here rather than imported from the
  \<open>Semicontinuous_Analysis\<close> session; they are deliberately minimal.\<close>

lemma usc_open_lt:
  fixes f :: "'a::metric_space \<Rightarrow> real"
  assumes usc: "\<And>c z. f z < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> f y < c"
  shows "open {y. f y < c}"
  unfolding open_dist
proof (intro ballI)
  fix z assume "z \<in> {y. f y < c}"
  then have "f z < c" by simp
  from usc[OF this] obtain e where e: "0 < e"
    and b: "\<And>y. dist z y < e \<Longrightarrow> f y < c" by blast
  show "\<exists>e>0. \<forall>y. dist y z < e \<longrightarrow> y \<in> {y. f y < c}"
    by (intro exI[of _ e] conjI e allI impI)
      (use b in \<open>simp add: dist_commute\<close>)
qed

lemma usc_attains_sup_compact:
  fixes f :: "'a::metric_space \<Rightarrow> real"
  assumes usc: "\<And>c z. f z < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> f y < c"
    and cS: "compact S" and neS: "S \<noteq> {}"
  shows "\<exists>z\<in>S. \<forall>y\<in>S. f y \<le> f z"
proof (rule ccontr)
  assume "\<not> (\<exists>z\<in>S. \<forall>y\<in>S. f y \<le> f z)"
  then have H: "\<And>z. z \<in> S \<Longrightarrow> \<exists>z'\<in>S. f z < f z'" by force
  have cov: "S \<subseteq> (\<Union>z'\<in>S. {y. f y < f z'})"
    using H by blast
  have opn: "\<And>z'. z' \<in> S \<Longrightarrow> open {y. f y < f z'}"
    by (rule usc_open_lt[OF usc])
  obtain T where TS: "T \<subseteq> S" and fT: "finite T"
    and covT: "S \<subseteq> (\<Union>z'\<in>T. {y. f y < f z'})"
    using compactE_image[OF cS opn cov] by blast
  obtain s where sS: "s \<in> S" using neS by blast
  have neT: "T \<noteq> {}" using covT sS by blast
  have "Max (f ` T) \<in> f ` T"
    by (rule Max_in) (use fT neT in auto)
  then obtain zm where zmT: "zm \<in> T" and zmM: "Max (f ` T) = f zm"
    by (rule imageE)
  have zmS: "zm \<in> S" using TS zmT by blast
  have "zm \<in> (\<Union>z'\<in>T. {y. f y < f z'})" by (rule subsetD[OF covT zmS])
  then obtain z'' where z'': "z'' \<in> T" and lt: "f zm < f z''" by auto
  have "f z'' \<le> Max (f ` T)" by (rule Max_ge) (use fT z'' in auto)
  then show False using lt zmM by linarith
qed

lemma supconv_attained_usc:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> B" and e: "0 < \<epsilon>"
    and usc: "\<And>c z. u z < c \<Longrightarrow> \<exists>d>0. \<forall>y. dist z y < d \<longrightarrow> u y < c"
  shows "\<exists>ys. supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
proof -
  define g where "g = (\<lambda>y. u y - (dist x y)\<^sup>2 / (2*\<epsilon>))"
  have ene: "2*\<epsilon> \<noteq> 0" using e by simp
  have gusc: "\<exists>d>0. \<forall>y. dist z y < d \<longrightarrow> g y < c" if lt: "g z < c" for c z
  proof -
    define \<eta> where "\<eta> = (c - g z)/2"
    have \<eta>: "0 < \<eta>" using lt by (simp add: \<eta>_def)
    obtain d1 where d1: "0 < d1"
      and h1: "\<And>y. dist z y < d1 \<Longrightarrow> u y < u z + \<eta>"
      using usc[of z "u z + \<eta>"] \<eta> by auto
    have pc: "isCont (\<lambda>y. (dist x y)\<^sup>2 / (2*\<epsilon>)) z"
      by (intro continuous_intros) (use ene in simp_all)
    have "((\<lambda>y. (dist x y)\<^sup>2 / (2*\<epsilon>)) \<longlongrightarrow> (dist x z)\<^sup>2 / (2*\<epsilon>)) (at z)"
      using pc by (simp add: isCont_def)
    from tendstoD[OF this \<eta>] obtain d2 where d2: "0 < d2"
      and h2: "\<And>y. y \<noteq> z \<Longrightarrow> dist y z < d2 \<Longrightarrow>
        \<bar>(dist x y)\<^sup>2 / (2*\<epsilon>) - (dist x z)\<^sup>2 / (2*\<epsilon>)\<bar> < \<eta>"
    unfolding eventually_at by (auto simp: dist_real_def)
    have main: "g y < c" if dy: "dist z y < min d1 d2" for y
    proof (cases "y = z")
      case True then show ?thesis using lt by simp
    next
      case False
      have "u y < u z + \<eta>" using h1 dy by simp
      moreover have "(dist x z)\<^sup>2 / (2*\<epsilon>) - \<eta> < (dist x y)\<^sup>2 / (2*\<epsilon>)"
        using h2[OF False] dy by (simp add: dist_commute abs_diff_less_iff)
      ultimately have "g y < g z + 2*\<eta>" unfolding g_def by linarith
      moreover have "g z + 2*\<eta> = c" unfolding \<eta>_def by argo
      ultimately show ?thesis by linarith
    qed
    show ?thesis
      by (intro exI[of _ "min d1 d2"] conjI allI impI)
        (use d1 d2 main in auto)
  qed
  define R where "R = sqrt (2*\<epsilon>*(B - u x)) + 1"
  have Bx: "0 \<le> B - u x" using B[of x] by simp
  have arg0: "0 \<le> 2*\<epsilon>*(B - u x)"
    using e Bx by (intro mult_nonneg_nonneg) auto
  have R1: "1 \<le> R" unfolding R_def
    using real_sqrt_ge_zero[OF arg0] by simp
  have R0: "0 < R" using R1 by linarith
  have Rsq: "2*\<epsilon>*(B - u x) < R\<^sup>2"
  proof -
    have s0: "0 \<le> sqrt (2*\<epsilon>*(B - u x))"
      by (rule real_sqrt_ge_zero[OF arg0])
    have "R\<^sup>2 = (sqrt (2*\<epsilon>*(B - u x)))\<^sup>2
        + 2 * sqrt (2*\<epsilon>*(B - u x)) + 1"
      unfolding R_def power2_sum by (simp add: power2_eq_square)
    also have "(sqrt (2*\<epsilon>*(B - u x)))\<^sup>2 = 2*\<epsilon>*(B - u x)"
      by (rule real_sqrt_pow2[OF arg0])
    finally show ?thesis using s0 by linarith
  qed
  have outside: "g y < g x" if dy: "\<not> dist x y \<le> R" for y
  proof -
    have "R\<^sup>2 < (dist x y)\<^sup>2"
      using dy R0 by (intro power2_strict_mono) auto
    then have "2*\<epsilon>*(B - u x) < (dist x y)\<^sup>2" using Rsq by linarith
    then have "B - u x < (dist x y)\<^sup>2 / (2*\<epsilon>)"
      using e by (simp add: field_simps)
    then have "u y - (dist x y)\<^sup>2 / (2*\<epsilon>) < u x" using B[of y] by linarith
    then show ?thesis unfolding g_def by simp
  qed
  obtain ys where ysc: "ys \<in> cball x R"
    and mxb: "\<And>y. y \<in> cball x R \<Longrightarrow> g y \<le> g ys"
    using usc_attains_sup_compact[OF gusc compact_cball, of x R]
      R0 by force
  have xc: "x \<in> cball x R" using R0 by simp
  have glob: "g y \<le> g ys" for y
  proof (cases "dist x y \<le> R")
    case True then show ?thesis by (intro mxb) simp
  next
    case False
    have "g y < g x" by (rule outside[OF False])
    also have "g x \<le> g ys" by (rule mxb[OF xc])
    finally show ?thesis by linarith
  qed
  have le: "supconv u \<epsilon> x \<le> g ys"
    unfolding supconv_def
    by (intro cSUP_least) (use glob in \<open>auto simp: g_def\<close>)
  have ge: "g ys \<le> supconv u \<epsilon> x"
    unfolding supconv_def g_def
    by (intro cSUP_upper supconv_bdd_above[OF B e]) auto
  have "supconv u \<epsilon> x = g ys" using le ge by linarith
  then show ?thesis unfolding g_def by blast
qed

section \<open>Quantitative estimates for the doubled sup-convolution\<close>

lemma quad_root_bound:
  fixes t b c :: real
  assumes b0: "0 \<le> b" and c0: "0 \<le> c" and h: "t\<^sup>2 \<le> b*t + c"
  shows "t \<le> b + sqrt c"
proof (rule ccontr)
  assume "\<not> t \<le> b + sqrt c"
  then have lt: "b + sqrt c < t" by linarith
  have sc: "0 \<le> sqrt c" by (rule real_sqrt_ge_zero[OF c0])
  have t0: "0 < t" using lt b0 sc by linarith
  have h1: "(b + sqrt c) * t < t * t"
    by (rule mult_strict_right_mono[OF lt t0])
  have sct: "sqrt c \<le> t" using lt b0 by linarith
  have h2: "sqrt c * sqrt c \<le> sqrt c * t"
    by (rule mult_left_mono[OF sct sc])
  have h3: "sqrt c * sqrt c = c"
    using real_sqrt_mult_self[of c] c0 by simp
  have "b*t + c \<le> (b + sqrt c) * t"
    using h2 h3 by (simp add: algebra_simps)
  then have "b*t + c < t * t" using h1 by linarith
  moreover have "t * t \<le> b*t + c" using h by (simp add: power2_eq_square)
  ultimately show False by linarith
qed

text \<open>On any region where the penalty gradient is bounded by \<open>\<alpha> A\<close>, the
  doubled sup-convolution functional exceeds the maximum \<open>M\<close> of the
  unconvolved functional by at most \<open>2\<alpha>\<^sup>2A\<^sup>2\<epsilon>\<close> --- the quantitative heart of
  the \<open>\<epsilon> \<rightarrow> 0\<close> limit.  Stated pointwise; the caller supplies the bound
  \<open>norm (x - y) \<le> A\<close>.\<close>

lemma doubled_supconv_pointwise_bound:
  fixes u b :: "'a::euclidean_space \<Rightarrow> real"
  assumes Bu: "\<And>y. u y \<le> Bu" and Bb: "\<And>y. b y \<le> Bb"
    and e: "0 < \<epsilon>" and a0: "0 < \<alpha>" and e4: "4*\<alpha>*\<epsilon> \<le> 1"
    and mx: "\<And>x' y'. u x' + b y' - (\<alpha>/2) * (norm (x' - y'))\<^sup>2 \<le> M"
    and A0: "norm (x - y) \<le> A"
  shows "supconv u \<epsilon> x + supconv b \<epsilon> y - (\<alpha>/2) * (norm (x - y))\<^sup>2
       \<le> M + 2*\<alpha>\<^sup>2*A\<^sup>2*\<epsilon>"
proof -
  define K where
    "K = M + (\<alpha>/2) * (norm (x - y))\<^sup>2 + 2 * \<alpha>\<^sup>2 * A\<^sup>2 * \<epsilon>"
  have Ann: "0 \<le> A" using A0 norm_ge_zero[of "x - y"] by linarith
  have core: "(u x' - (dist x x')\<^sup>2 / (2 * \<epsilon>))
      + (b y' - (dist y y')\<^sup>2 / (2 * \<epsilon>)) \<le> K" for x' y'
  proof -
    define sx where "sx = dist x x'"
    define sy where "sy = dist y y'"
    define tt where "tt = sx + sy"
    have sxn: "0 \<le> sx" unfolding sx_def by simp
    have syn: "0 \<le> sy" unfolding sy_def by simp
    have tn: "0 \<le> tt" unfolding tt_def using sxn syn by linarith
    have tri: "norm (x' - y') \<le> norm (x - y) + tt"
    proof -
      have a1: "dist x' y' \<le> dist x' x + dist x y'" by (rule dist_triangle)
      have a2: "dist x y' \<le> dist x y + dist y y'" by (rule dist_triangle)
      have "dist x' y' \<le> dist x y + (dist x x' + dist y y')"
        using a1 a2 dist_commute[of x' x] by linarith
      then show ?thesis unfolding tt_def sx_def sy_def
        by (simp add: dist_norm[symmetric])
    qed
    have sqm: "(norm (x' - y'))\<^sup>2 \<le> (norm (x - y) + tt)\<^sup>2"
      by (rule power_mono[OF tri]) simp
    have exp1: "(norm (x - y) + tt)\<^sup>2
        = (norm (x - y))\<^sup>2 + 2 * norm (x - y) * tt + tt\<^sup>2"
      by (simp add: power2_sum)
    have lin: "2 * norm (x - y) * tt \<le> 2 * A * tt"
      using A0 tn by (intro mult_right_mono) auto
    have twoprod: "2 * sx * sy \<le> sx\<^sup>2 + sy\<^sup>2"
    proof -
      have "0 \<le> (sx - sy)\<^sup>2" by simp
      moreover have "(sx - sy)\<^sup>2 = sx\<^sup>2 - 2 * sx * sy + sy\<^sup>2"
        by (simp add: power2_diff)
      ultimately show ?thesis by linarith
    qed
    have pen1: "tt\<^sup>2 \<le> 2 * (sx\<^sup>2 + sy\<^sup>2)"
    proof -
      have "tt\<^sup>2 = sx\<^sup>2 + 2 * sx * sy + sy\<^sup>2"
        unfolding tt_def by (simp add: power2_sum)
      then show ?thesis using twoprod by argo
    qed
    have half: "(\<alpha>/2) * tt\<^sup>2 \<le> tt\<^sup>2 / (8 * \<epsilon>)"
    proof -
      have "\<alpha>/2 \<le> 1/(8 * \<epsilon>)" using e4 e by (simp add: field_simps)
      then show ?thesis
        using mult_right_mono[of "\<alpha>/2" "1/(8 * \<epsilon>)" "tt\<^sup>2"]
        by (simp add: field_simps)
    qed
    have sos: "\<alpha> * A * tt - tt\<^sup>2 / (8 * \<epsilon>) \<le> 2 * \<epsilon> * \<alpha>\<^sup>2 * A\<^sup>2"
    proof -
      have nn: "0 \<le> (tt - 4 * \<epsilon> * \<alpha> * A)\<^sup>2 / (8 * \<epsilon>)"
        using e by (intro divide_nonneg_pos) auto
      have ex: "(tt - 4 * \<epsilon> * \<alpha> * A)\<^sup>2 / (8 * \<epsilon>)
          = tt\<^sup>2 / (8 * \<epsilon>) - \<alpha> * A * tt + 2 * \<epsilon> * \<alpha>\<^sup>2 * A\<^sup>2"
        using e by (simp add: power2_diff power2_eq_square field_simps)
      show ?thesis using nn unfolding ex by linarith
    qed
    have peneq: "(dist x x')\<^sup>2 / (2 * \<epsilon>) + (dist y y')\<^sup>2 / (2 * \<epsilon>)
        = (sx\<^sup>2 + sy\<^sup>2) / (2 * \<epsilon>)"
      unfolding sx_def sy_def by (simp add: add_divide_distrib)
    have pen2: "tt\<^sup>2 / (4 * \<epsilon>) \<le> (sx\<^sup>2 + sy\<^sup>2) / (2 * \<epsilon>)"
      using pen1 e by (simp add: field_simps)
    have "u x' + b y' \<le> M + (\<alpha>/2) * (norm (x' - y'))\<^sup>2"
      using mx[of x' y'] by linarith
    also have "\<dots> \<le> M + (\<alpha>/2) * (norm (x - y))\<^sup>2
        + \<alpha> * A * tt + (\<alpha>/2) * tt\<^sup>2"
    proof -
      have "(\<alpha>/2) * (norm (x' - y'))\<^sup>2
          \<le> (\<alpha>/2) * ((norm (x - y))\<^sup>2 + 2 * A * tt + tt\<^sup>2)"
        using sqm exp1 lin a0 by (intro mult_left_mono) auto
      then show ?thesis by (simp add: field_simps)
    qed
    finally have main: "u x' + b y' \<le> M + (\<alpha>/2) * (norm (x - y))\<^sup>2
        + \<alpha> * A * tt + (\<alpha>/2) * tt\<^sup>2" .
    have "(u x' - (dist x x')\<^sup>2 / (2 * \<epsilon>)) + (b y' - (dist y y')\<^sup>2 / (2 * \<epsilon>))
        = u x' + b y' - (sx\<^sup>2 + sy\<^sup>2) / (2 * \<epsilon>)"
      using peneq by linarith
    also have "\<dots> \<le> M + (\<alpha>/2) * (norm (x - y))\<^sup>2 + \<alpha> * A * tt
        + (\<alpha>/2) * tt\<^sup>2 - tt\<^sup>2 / (4 * \<epsilon>)"
      using main pen2 by linarith
    also have "\<dots> \<le> M + (\<alpha>/2) * (norm (x - y))\<^sup>2 + \<alpha> * A * tt - tt\<^sup>2 / (8 * \<epsilon>)"
    proof -
      have "(\<alpha>/2) * tt\<^sup>2 - tt\<^sup>2 / (4 * \<epsilon>) \<le> - (tt\<^sup>2 / (8 * \<epsilon>))"
        using half e by (simp add: field_simps)
      then show ?thesis by linarith
    qed
    also have "\<dots> \<le> M + (\<alpha>/2) * (norm (x - y))\<^sup>2 + 2 * \<epsilon> * \<alpha>\<^sup>2 * A\<^sup>2"
      using sos by linarith
    finally show ?thesis unfolding K_def by (simp add: algebra_simps)
  qed
  have step1: "supconv b \<epsilon> y \<le> K - (u x' - (dist x x')\<^sup>2 / (2 * \<epsilon>))" for x'
    unfolding supconv_def
    by (intro cSUP_least) (use core[of x'] in \<open>auto simp: algebra_simps\<close>)
  have step2: "supconv u \<epsilon> x \<le> K - supconv b \<epsilon> y"
  proof -
    have h: "u x' - (dist x x')\<^sup>2 / (2 * \<epsilon>) \<le> K - supconv b \<epsilon> y" for x'
      using step1[of x'] by linarith
    show ?thesis unfolding supconv_def[of u]
      by (intro cSUP_least) (use h in auto)
  qed
  then show ?thesis unfolding K_def by (simp add: algebra_simps)
qed

section \<open>Squeeze helpers\<close>

lemma usc_eventually_lt:
  fixes f :: "'a::metric_space \<Rightarrow> real"
  assumes usc: "\<And>c z. f z < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> f y < c"
    and xs: "xs \<longlonglongrightarrow> x0" and c: "f x0 < c"
  shows "\<forall>\<^sub>F n in sequentially. f (xs n) < c"
proof -
  from usc[OF c] obtain e where e0: "0 < e"
    and b: "\<And>y. dist x0 y < e \<Longrightarrow> f y < c" by blast
  have "\<forall>\<^sub>F n in sequentially. dist (xs n) x0 < e"
    by (rule tendstoD[OF xs e0])
  then show ?thesis
    by (rule eventually_mono) (use b in \<open>simp add: dist_commute\<close>)
qed

lemma sum_squeeze_pair_fst:
  fixes an bn :: "nat \<Rightarrow> real"
  assumes ua: "\<And>c. A < c \<Longrightarrow> \<forall>\<^sub>F n in sequentially. an n < c"
    and ub: "\<And>c. B < c \<Longrightarrow> \<forall>\<^sub>F n in sequentially. bn n < c"
    and s: "(\<lambda>n. an n + bn n) \<longlonglongrightarrow> (A + B)"
  shows "an \<longlonglongrightarrow> A"
proof (rule tendstoI)
  fix \<eta> :: real assume \<eta>: "0 < \<eta>"
  have \<eta>2: "0 < \<eta>/2" using \<eta> by simp
  have up: "\<forall>\<^sub>F n in sequentially. an n < A + \<eta>/2"
    by (rule ua) (use \<eta>2 in simp)
  have upb: "\<forall>\<^sub>F n in sequentially. bn n < B + \<eta>/2"
    by (rule ub) (use \<eta>2 in simp)
  have sm: "\<forall>\<^sub>F n in sequentially. dist (an n + bn n) (A + B) < \<eta>/2"
    by (rule tendstoD[OF s \<eta>2])
  show "\<forall>\<^sub>F n in sequentially. dist (an n) A < \<eta>"
    using up upb sm
  proof eventually_elim
    case (elim n)
    have lo: "A - \<eta> < an n"
    proof -
      have "\<bar>(an n + bn n) - (A + B)\<bar> < \<eta>/2"
        using elim(3) by (simp add: dist_real_def)
      then have "A + B - \<eta>/2 < an n + bn n"
        unfolding abs_diff_less_iff by linarith
      moreover have "bn n < B + \<eta>/2" using elim(2) .
      ultimately show ?thesis by linarith
    qed
    have hi: "an n < A + \<eta>" using elim(1) \<eta> by linarith
    show ?case using lo hi by (simp add: dist_real_def abs_diff_less_iff)
  qed
qed

section \<open>From exact expansions to semijets\<close>

lemma norm_sq_add_expand:
  fixes a k :: "'a::euclidean_space"
  shows "(norm (a + k))\<^sup>2 = (norm a)\<^sup>2 + 2 * (a \<bullet> k) + (norm k)\<^sup>2"
  by (simp add: power2_norm_eq_inner inner_add_left inner_add_right
      inner_commute)

text \<open>Adding an exactly expanded quadratic to an exact second-order
  expansion shifts the gradient and the form and changes nothing else:
  the remainders are literally equal.\<close>

lemma expansion_add_centered_sq:
  fixes f :: "'a::euclidean_space \<Rightarrow> real" and x c :: 'a and \<delta> :: real
  assumes exp: "((\<lambda>k. (f (x + k) - f x - p \<bullet> k - (k \<bullet> F k)/2)
      / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows "((\<lambda>k. ((f (x + k) + \<delta> * (norm (x + k - c))\<^sup>2)
      - (f x + \<delta> * (norm (x - c))\<^sup>2)
      - (p + (2 * \<delta>) *\<^sub>R (x - c)) \<bullet> k
      - (k \<bullet> (F k + (2 * \<delta>) *\<^sub>R k))/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
proof -
  have ident: "(f (x + k) + \<delta> * (norm (x + k - c))\<^sup>2)
      - (f x + \<delta> * (norm (x - c))\<^sup>2)
      - (p + (2 * \<delta>) *\<^sub>R (x - c)) \<bullet> k
      - (k \<bullet> (F k + (2 * \<delta>) *\<^sub>R k))/2
      = f (x + k) - f x - p \<bullet> k - (k \<bullet> F k)/2" for k
  proof -
    have e1: "(norm (x + k - c))\<^sup>2
        = (norm (x - c))\<^sup>2 + 2 * ((x - c) \<bullet> k) + (norm k)\<^sup>2"
      using norm_sq_add_expand[of "x - c" k]
      by (simp add: algebra_simps)
    have e2: "(p + (2 * \<delta>) *\<^sub>R (x - c)) \<bullet> k
        = p \<bullet> k + 2 * \<delta> * ((x - c) \<bullet> k)"
      by (simp add: inner_add_left)
    have e3: "k \<bullet> (F k + (2 * \<delta>) *\<^sub>R k) = k \<bullet> F k + 2 * \<delta> * (norm k)\<^sup>2"
      by (simp add: inner_add_right power2_norm_eq_inner)
    show ?thesis unfolding e1 e2 e3 by (simp add: algebra_simps)
  qed
  have "(\<lambda>k. ((f (x + k) + \<delta> * (norm (x + k - c))\<^sup>2)
      - (f x + \<delta> * (norm (x - c))\<^sup>2)
      - (p + (2 * \<delta>) *\<^sub>R (x - c)) \<bullet> k
      - (k \<bullet> (F k + (2 * \<delta>) *\<^sub>R k))/2) / (norm k)\<^sup>2)
      = (\<lambda>k. (f (x + k) - f x - p \<bullet> k - (k \<bullet> F k)/2) / (norm k)\<^sup>2)"
    by (rule ext) (simp only: ident)
  then show ?thesis using exp by simp
qed

text \<open>A one-sided remainder comparison against an exactly expanded majorant
  is exactly membership in the superjet.\<close>

lemma superjet_of_transfer:
  fixes u g :: "'a::euclidean_space \<Rightarrow> real"
  assumes trans: "\<And>k. (u (ys + k) - u ys - p \<bullet> k - (k \<bullet> F k)/2) / (norm k)\<^sup>2
      \<le> (g (xx + k) - g xx - p \<bullet> k - (k \<bullet> F k)/2) / (norm k)\<^sup>2"
    and exp: "((\<lambda>k. (g (xx + k) - g xx - p \<bullet> k - (k \<bullet> F k)/2)
      / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and lin: "linear F" and sym: "\<And>a b. a \<bullet> F b = b \<bullet> F a"
  shows "(p, F) \<in> superjet u ys"
proof -
  have h: "\<exists>d>0. \<forall>k. norm k < d \<longrightarrow>
      u (ys + k) \<le> u ys + p \<bullet> k + (k \<bullet> F k)/2 + e * (norm k)\<^sup>2"
    if e: "0 < e" for e
  proof -
    from tendstoD[OF exp e] obtain d where d: "0 < d"
      and b: "\<And>k. k \<noteq> 0 \<Longrightarrow> dist k 0 < d \<Longrightarrow>
        \<bar>(g (xx + k) - g xx - p \<bullet> k - (k \<bullet> F k)/2) / (norm k)\<^sup>2\<bar> < e"
      unfolding eventually_at by (auto simp: dist_real_def)
    have main: "u (ys + k) \<le> u ys + p \<bullet> k + (k \<bullet> F k)/2 + e * (norm k)\<^sup>2"
      if kd: "norm k < d" for k
    proof (cases "k = 0")
      case True
      then show ?thesis by simp
    next
      case False
      have nk: "0 < (norm k)\<^sup>2" using False by simp
      have b': "\<bar>(g (xx + k) - g xx - p \<bullet> k - (k \<bullet> F k)/2) / (norm k)\<^sup>2\<bar> < e"
        using b[OF False] kd by (simp add: dist_norm)
      have "(u (ys + k) - u ys - p \<bullet> k - (k \<bullet> F k)/2) / (norm k)\<^sup>2
          \<le> (g (xx + k) - g xx - p \<bullet> k - (k \<bullet> F k)/2) / (norm k)\<^sup>2"
        by (rule trans)
      also have "\<dots> \<le> \<bar>(g (xx + k) - g xx - p \<bullet> k - (k \<bullet> F k)/2) / (norm k)\<^sup>2\<bar>"
        by (rule abs_ge_self)
      also have "\<dots> < e" by (rule b')
      finally have "(u (ys + k) - u ys - p \<bullet> k - (k \<bullet> F k)/2) / (norm k)\<^sup>2 < e" .
      then have "u (ys + k) - u ys - p \<bullet> k - (k \<bullet> F k)/2 < e * (norm k)\<^sup>2"
        using nk by (simp add: pos_divide_less_eq)
      then show ?thesis by linarith
    qed
    show ?thesis using d main by blast
  qed
  show ?thesis unfolding superjet_def using lin sym h by auto
qed

lemma supconv_superjet_at_optimizer:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> B" and e: "0 < \<epsilon>"
    and opt: "supconv u \<epsilon> xx = u ys - (dist xx ys)\<^sup>2 / (2*\<epsilon>)"
    and exp: "((\<lambda>k. (supconv u \<epsilon> (xx + k) - supconv u \<epsilon> xx
        - p \<bullet> k - (k \<bullet> F k)/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and lin: "linear F" and sym: "\<And>a b. a \<bullet> F b = b \<bullet> F a"
  shows "(p, F) \<in> superjet u ys"
proof -
  have tr: "\<And>k. (u (ys + k) - u ys - p \<bullet> k - (k \<bullet> F k)/2) / (norm k)\<^sup>2
      \<le> (supconv u \<epsilon> (xx + k) - supconv u \<epsilon> xx
          - p \<bullet> k - (k \<bullet> F k)/2) / (norm k)\<^sup>2"
    by (rule supconv_jet_transfer[OF B e opt])
  show ?thesis by (rule superjet_of_transfer[OF tr exp lin sym])
qed

section \<open>Sequential limit utilities\<close>

lemma tendsto_of_dist_bound:
  fixes zf :: "nat \<Rightarrow> 'a::metric_space"
  assumes b: "\<And>n. dist (zf n) z \<le> \<rho> n" and r: "\<rho> \<longlonglongrightarrow> 0"
  shows "zf \<longlonglongrightarrow> z"
proof (rule tendstoI)
  fix e :: real assume e: "0 < e"
  have ev: "\<forall>\<^sub>F n in sequentially. dist (\<rho> n) 0 < e"
    by (rule tendstoD[OF r e])
  show "\<forall>\<^sub>F n in sequentially. dist (zf n) z < e"
    using ev
  proof (rule eventually_mono)
    fix n assume h: "dist (\<rho> n) 0 < e"
    have "dist (zf n) z \<le> \<rho> n" by (rule b)
    also have "\<rho> n \<le> \<bar>\<rho> n\<bar>" by (rule abs_ge_self)
    also have "\<bar>\<rho> n\<bar> < e" using h by (simp add: dist_real_def)
    finally show "dist (zf n) z < e" .
  qed
qed

section \<open>Small algebraic helpers\<close>

lemma linear_add_scaleR:
  fixes F :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes lF: "linear F"
  shows "linear (\<lambda>k. F k + c *\<^sub>R k)"
proof (rule linearI)
  fix x y :: 'a
  have "F (x + y) = F x + F y"
    using lF unfolding linear_iff by blast
  then show "F (x + y) + c *\<^sub>R (x + y) = (F x + c *\<^sub>R x) + (F y + c *\<^sub>R y)"
    by (simp add: algebra_simps)
next
  fix r :: real and x :: 'a
  have "F (r *\<^sub>R x) = r *\<^sub>R F x"
    using lF unfolding linear_iff by blast
  then show "F (r *\<^sub>R x) + c *\<^sub>R (r *\<^sub>R x) = r *\<^sub>R (F x + c *\<^sub>R x)"
    by (simp add: algebra_simps)
qed

lemma sym_add_scaleR:
  fixes F :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes sF: "\<And>a b. a \<bullet> F b = b \<bullet> F a"
  shows "a \<bullet> (F b + c *\<^sub>R b) = b \<bullet> (F a + c *\<^sub>R a)"
  using sF[of a b] by (simp add: inner_add_right inner_commute)

lemma add_sq_le_double:
  fixes x y :: real
  shows "(x + y)\<^sup>2 \<le> 2 * (x\<^sup>2 + y\<^sup>2)"
proof -
  have "0 \<le> (x - y)\<^sup>2" by simp
  moreover have "(x - y)\<^sup>2 = x\<^sup>2 - 2 * x * y + y\<^sup>2"
    by (simp add: power2_diff)
  moreover have "(x + y)\<^sup>2 = x\<^sup>2 + 2 * x * y + y\<^sup>2"
    by (simp add: power2_sum)
  ultimately show ?thesis by argo
qed

section \<open>The theorem on sums at one regularisation stage\<close>

text \<open>One pass of the sup-convolution/Jensen machinery at fixed
  regularisation \<open>\<epsilon>\<close>, strictness \<open>\<delta>\<close>, localisation \<open>\<rho>\<close> and tilt budget
  \<open>dd\<close>: it produces one genuine superjet of \<open>u\<close> and one of \<open>b\<close>, ordered up
  to \<open>4\<delta>\<close>, at points quantitatively close to the maximum \<open>(xh, yh)\<close> of the
  doubled functional, with value and gradient control.  The limit theorem
  strings a sequence of these stages together.\<close>

lemma theorem_on_sums_stage:
  fixes u b :: "real^'n::finite \<Rightarrow> real" and \<alpha> \<epsilon> \<delta> \<rho> dd A M :: real
    and xh yh :: "real^'n"
  assumes Bu: "\<And>y. u y \<le> Bu" and Bb: "\<And>y. b y \<le> Bb"
    and uscu: "\<And>c z. u z < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> u y < c"
    and uscb: "\<And>c z. b z < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> b y < c"
    and a0: "0 < \<alpha>"
    and mxb: "\<And>x y. u x + b y - (\<alpha>/2) * (norm (x - y))\<^sup>2 \<le> M"
    and Mval: "M = u xh + b yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
    and Aval: "A = norm (xh - yh) + 2"
    and e0: "0 < \<epsilon>" and e4: "4 * \<alpha> * \<epsilon> \<le> 1"
    and d0: "0 < \<delta>"
    and rho0: "0 < \<rho>" and rho1: "\<rho> < 1"
    and gap: "2 * \<alpha>\<^sup>2 * A\<^sup>2 * \<epsilon> \<le> \<delta> * \<rho>\<^sup>2 / 2"
    and dd0: "0 < dd" and ddsmall: "2 * dd < \<delta> * \<rho>\<^sup>2 / 2"
  shows "\<exists>(xy :: (real^'n) \<times> (real^'n)) (pq :: (real^'n) \<times> (real^'n))
      (XU :: real^'n \<Rightarrow> real^'n) (YU :: real^'n \<Rightarrow> real^'n).
    (fst pq, XU) \<in> superjet u (fst xy) \<and>
    (snd pq, YU) \<in> superjet b (snd xy) \<and>
    (\<forall>v. v \<bullet> XU v + v \<bullet> YU v \<le> 4 * \<delta> * (norm v)\<^sup>2) \<and>
    dist (fst xy) xh \<le> \<rho> + 8 * \<epsilon> * \<alpha> * A + sqrt (8 * \<epsilon> * dd) \<and>
    dist (snd xy) yh \<le> \<rho> + 8 * \<epsilon> * \<alpha> * A + sqrt (8 * \<epsilon> * dd) \<and>
    norm (fst pq - \<alpha> *\<^sub>R (xh - yh)) \<le> dd + 2 * \<alpha> * \<rho> + 2 * \<delta> * \<rho> \<and>
    norm (snd pq + \<alpha> *\<^sub>R (xh - yh)) \<le> dd + 2 * \<alpha> * \<rho> + 2 * \<delta> * \<rho> \<and>
    M - dd - 2 * \<alpha> * A * \<rho> + (\<alpha>/2) * (norm (xh - yh))\<^sup>2
      \<le> u (fst xy) + b (snd xy)"
proof -
  have Ann: "0 \<le> A" unfolding Aval
    using norm_ge_zero[of "xh - yh"] by linarith
  have nhA: "norm (xh - yh) \<le> A" unfolding Aval by simp
  define C where "C = 2 * \<alpha>\<^sup>2 * A\<^sup>2"
  have C0: "0 \<le> C" unfolding C_def
    by (intro mult_nonneg_nonneg) auto
  have normbnd: "norm (fst z - snd z) \<le> A"
    if zball: "dist z ((xh, yh) :: (real^'n) \<times> (real^'n)) \<le> 1" for z
  proof -
    have f1: "dist (fst z) xh \<le> 1"
      using dist_fst_le[of z "(xh, yh)"] zball by simp
    have s1: "dist (snd z) yh \<le> 1"
      using dist_snd_le[of z "(xh, yh)"] zball by simp
    have t1: "dist (fst z) (snd z) \<le> dist (fst z) xh + dist xh (snd z)"
      by (rule dist_triangle)
    have t2: "dist xh (snd z) \<le> dist xh yh + dist yh (snd z)"
      by (rule dist_triangle)
    have c1: "dist (fst z) (snd z) = norm (fst z - snd z)"
      by (simp add: dist_norm)
    have c2: "dist xh yh = norm (xh - yh)" by (simp add: dist_norm)
    have c3: "dist yh (snd z) = dist (snd z) yh" by (rule dist_commute)
    show ?thesis using t1 t2 f1 s1
      unfolding c1 c2 c3 Aval by linarith
  qed
  define m where "m = M + C * \<epsilon> - \<delta> * \<rho>\<^sup>2"
  have bndH: "(supconv u \<epsilon> (fst y)
        - \<delta> * (norm (fst y - fst ((xh, yh) :: (real^'n) \<times> (real^'n))))\<^sup>2)
      + (supconv b \<epsilon> (snd y) - \<delta> * (norm (snd y - snd ((xh, yh))))\<^sup>2)
      - (\<alpha>/2) * (norm (fst y - snd y))\<^sup>2 \<le> m"
    if yb: "y \<in> cball ((xh, yh) :: (real^'n) \<times> (real^'n)) 1"
      and yr: "\<rho> \<le> dist y (xh, yh)" for y
  proof -
    have db1: "dist y ((xh, yh) :: (real^'n) \<times> (real^'n)) \<le> 1"
      using yb by (simp add: dist_commute)
    have nb: "norm (fst y - snd y) \<le> A" by (rule normbnd[OF db1])
    have pb: "supconv u \<epsilon> (fst y) + supconv b \<epsilon> (snd y)
        - (\<alpha>/2) * (norm (fst y - snd y))\<^sup>2 \<le> M + 2 * \<alpha>\<^sup>2 * A\<^sup>2 * \<epsilon>"
      by (rule doubled_supconv_pointwise_bound[OF Bu Bb e0 a0 e4 mxb nb])
    have pen1: "\<delta> * (norm (fst y - fst ((xh, yh) :: (real^'n) \<times> (real^'n))))\<^sup>2
        + \<delta> * (norm (snd y - snd ((xh, yh))))\<^sup>2
        = \<delta> * (norm (y - ((xh, yh) :: (real^'n) \<times> (real^'n))))\<^sup>2"
      unfolding norm_sq_prod_split[of y "(xh, yh)"]
      by (simp add: algebra_simps)
    have pen2: "\<rho>\<^sup>2 \<le> (norm (y - ((xh, yh) :: (real^'n) \<times> (real^'n))))\<^sup>2"
    proof -
      have "\<rho> \<le> norm (y - (xh, yh))" using yr by (simp add: dist_norm)
      then show ?thesis using rho0 by (intro power_mono) auto
    qed
    have pen3: "\<delta> * \<rho>\<^sup>2 \<le> \<delta> * (norm (y - ((xh, yh) :: (real^'n) \<times> (real^'n))))\<^sup>2"
      using pen2 d0 by (intro mult_left_mono) auto
    show ?thesis using pb pen1 pen3 unfolding m_def C_def by linarith
  qed
  have shiftxi: "(supconv u \<epsilon> (fst ((xh, yh) :: (real^'n) \<times> (real^'n)))
        - \<delta> * (norm (fst ((xh, yh) :: (real^'n) \<times> (real^'n))
            - fst ((xh, yh))))\<^sup>2)
      + (supconv b \<epsilon> (snd ((xh, yh))) - \<delta> * (norm (snd ((xh, yh))
            - snd ((xh, yh))))\<^sup>2)
      - (\<alpha>/2) * (norm (fst ((xh, yh)) - snd ((xh, yh))))\<^sup>2
      = supconv u \<epsilon> xh + supconv b \<epsilon> yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
    by simp
  have smallH: "2 * dd * 1
      < ((supconv u \<epsilon> (fst ((xh, yh) :: (real^'n) \<times> (real^'n)))
          - \<delta> * (norm (fst ((xh, yh)) - fst ((xh, yh))))\<^sup>2)
        + (supconv b \<epsilon> (snd ((xh, yh)))
          - \<delta> * (norm (snd ((xh, yh)) - snd ((xh, yh))))\<^sup>2)
        - (\<alpha>/2) * (norm (fst ((xh, yh)) - snd ((xh, yh))))\<^sup>2) - m"
  proof -
    have g1: "u xh \<le> supconv u \<epsilon> xh" by (rule supconv_ge[OF Bu e0])
    have g2: "b yh \<le> supconv b \<epsilon> yh" by (rule supconv_ge[OF Bb e0])
    have "M \<le> supconv u \<epsilon> xh + supconv b \<epsilon> yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
      unfolding Mval using g1 g2 by linarith
    moreover have "C * \<epsilon> \<le> \<delta> * \<rho>\<^sup>2 / 2"
      unfolding C_def using gap by simp
    ultimately show ?thesis
      unfolding shiftxi m_def using ddsmall by linarith
  qed
  have anneg: "0 \<le> \<alpha>" using a0 by linarith
  have dnn: "0 \<le> \<delta>" using d0 by linarith
  obtain zh pt qq WW where
    dzr: "dist zh ((xh, yh) :: (real^'n) \<times> (real^'n)) < \<rho>"
    and npt: "norm pt \<le> dd"
    and mxraw: "\<forall>y \<in> cball ((xh, yh) :: (real^'n) \<times> (real^'n)) 1.
        ((supconv u \<epsilon> (fst y) - \<delta> * (norm (fst y - fst ((xh, yh))))\<^sup>2)
          + (supconv b \<epsilon> (snd y) - \<delta> * (norm (snd y - snd ((xh, yh))))\<^sup>2)
          - (\<alpha>/2) * (norm (fst y - snd y))\<^sup>2) + pt \<bullet> y
        \<le> ((supconv u \<epsilon> (fst zh) - \<delta> * (norm (fst zh - fst ((xh, yh))))\<^sup>2)
          + (supconv b \<epsilon> (snd zh) - \<delta> * (norm (snd zh - snd ((xh, yh))))\<^sup>2)
          - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2) + pt \<bullet> zh"
    and blW: "bounded_linear WW"
    and symW: "\<forall>v z. v \<bullet> WW z = z \<bullet> WW v"
    and expraw: "((\<lambda>k. (((supconv u \<epsilon> (fst (zh + k))
            - \<delta> * (norm (fst (zh + k) - fst ((xh, yh))))\<^sup>2)
          + (supconv b \<epsilon> (snd (zh + k))
            - \<delta> * (norm (snd (zh + k) - snd ((xh, yh))))\<^sup>2)
          - (\<alpha>/2) * (norm (fst (zh + k) - snd (zh + k)))\<^sup>2)
        - ((supconv u \<epsilon> (fst zh) - \<delta> * (norm (fst zh - fst ((xh, yh))))\<^sup>2)
          + (supconv b \<epsilon> (snd zh) - \<delta> * (norm (snd zh - snd ((xh, yh))))\<^sup>2)
          - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
        - qq \<bullet> k - (k \<bullet> WW k)/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    using doubled_supconv_jet_exists_shifted[where u = u and w = b
        and Bu = Bu and Bw = Bb and \<epsilon> = \<epsilon> and \<alpha> = \<alpha> and \<delta> = \<delta>
        and \<rho> = \<rho> and r = 1 and \<xi> = "(xh, yh)" and \<xi>\<^sub>0 = "(xh, yh)"
        and m = m and dd = dd,
        OF Bu Bb e0 anneg dnn rho0 rho1 bndH dd0 smallH]
    by blast
  define af where "af = (\<lambda>x. supconv u \<epsilon> x - \<delta> * (norm (x - xh))\<^sup>2)"
  define bf where "bf = (\<lambda>y. supconv b \<epsilon> y - \<delta> * (norm (y - yh))\<^sup>2)"
  have mxA: "(af (fst y) + bf (snd y)
        - (\<alpha>/2) * (norm (fst y - snd y))\<^sup>2) + pt \<bullet> y
      \<le> (af (fst zh) + bf (snd zh)
        - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2) + pt \<bullet> zh"
    if "y \<in> cball ((xh, yh) :: (real^'n) \<times> (real^'n)) 1" for y
    using mxraw that unfolding af_def bf_def by simp
  have expA: "((\<lambda>k. ((af (fst (zh + k)) + bf (snd (zh + k))
        - (\<alpha>/2) * (norm (fst (zh + k) - snd (zh + k)))\<^sup>2)
      - (af (fst zh) + bf (snd zh)
        - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
      - qq \<bullet> k - (k \<bullet> WW k)/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    using expraw unfolding af_def bf_def by simp
  have dz1: "dist zh ((xh, yh) :: (real^'n) \<times> (real^'n)) < 1"
    using dzr rho1 by linarith
  note slices = tilted_doubled_jet_slices[where a = af and b = bf
      and \<alpha> = \<alpha> and W = WW and zh = zh and \<xi> = "(xh, yh)" and r = 1
      and pt = pt and q = qq, OF blW dz1 mxA expA]
  have hiW: "\<And>v. v \<bullet> WW v \<le> 0"
    by (rule tilted_doubled_hessian_nonpositive[where a = af and b = bf
        and \<alpha> = \<alpha> and W = WW and zh = zh and \<xi> = "(xh, yh)" and r = 1
        and pt = pt and q = qq, OF blW dz1 mxA expA])
  have scW: "\<And>s uu. WW (s *\<^sub>R uu) = s *\<^sub>R WW uu"
    using blW by (simp add: linear_simps)
  have symW': "\<And>v z. v \<bullet> WW z = z \<bullet> WW v" using symW by blast
  have ord: "\<And>v. v \<bullet> (fst (WW (v, 0)) + \<alpha> *\<^sub>R v)
      \<le> v \<bullet> (- (snd (WW (0, v)) + \<alpha> *\<^sub>R v))"
    by (rule sums_gives_ordering[OF expA scW hiW])
  obtain ysu where optu: "supconv u \<epsilon> (fst zh)
      = u ysu - (dist (fst zh) ysu)\<^sup>2 / (2*\<epsilon>)"
    using supconv_attained_usc[OF Bu e0 uscu] by blast
  obtain ysw where optb: "supconv b \<epsilon> (snd zh)
      = b ysw - (dist (snd zh) ysw)\<^sup>2 / (2*\<epsilon>)"
    using supconv_attained_usc[OF Bb e0 uscb] by blast
  define pu where "pu = (- fst pt + \<alpha> *\<^sub>R (fst zh - snd zh))
      + (2 * \<delta>) *\<^sub>R (fst zh - xh)"
  define XU where "XU = (\<lambda>k :: real^'n. (fst (WW (k, 0)) + \<alpha> *\<^sub>R k)
      + (2 * \<delta>) *\<^sub>R k)"
  define pw where "pw = (- (snd pt + \<alpha> *\<^sub>R (fst zh - snd zh)))
      + (2 * \<delta>) *\<^sub>R (snd zh - yh)"
  define YU where "YU = (\<lambda>k :: real^'n. (snd (WW (0, k)) + \<alpha> *\<^sub>R k)
      + (2 * \<delta>) *\<^sub>R k)"
  have collu: "\<And>x. af x + \<delta> * (norm (x - xh))\<^sup>2 = supconv u \<epsilon> x"
    unfolding af_def by simp
  have collb: "\<And>y. bf y + \<delta> * (norm (y - yh))\<^sup>2 = supconv b \<epsilon> y"
    unfolding bf_def by simp
  have expu: "((\<lambda>k. (supconv u \<epsilon> (fst zh + k) - supconv u \<epsilon> (fst zh)
      - pu \<bullet> k - (k \<bullet> XU k)/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    using expansion_add_centered_sq[where \<delta> = \<delta> and c = xh, OF slices(2)]
    unfolding collu pu_def XU_def .
  have expb: "((\<lambda>k. (supconv b \<epsilon> (snd zh + k) - supconv b \<epsilon> (snd zh)
      - pw \<bullet> k - (k \<bullet> YU k)/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    using expansion_add_centered_sq[where \<delta> = \<delta> and c = yh, OF slices(3)]
    unfolding collb pw_def YU_def .
  have linXU: "linear XU"
    unfolding XU_def
    by (rule linear_add_scaleR[OF linear_block_fst[OF blW]])
  have symXU: "\<And>a b. a \<bullet> XU b = b \<bullet> XU a"
    unfolding XU_def
    by (rule sym_add_scaleR[OF sym_block_fst[OF symW']])
  have linYU: "linear YU"
  proof -
    have "linear (\<lambda>v. - (snd (WW (0, v)) + \<alpha> *\<^sub>R v))"
      by (rule linear_block_snd[OF blW])
    then have "linear (\<lambda>v. snd (WW (0, v)) + \<alpha> *\<^sub>R v)"
      using linear_neg_iff by fastforce
    then show ?thesis unfolding YU_def by (rule linear_add_scaleR)
  qed
  have symYU: "\<And>a b. a \<bullet> YU b = b \<bullet> YU a"
  proof -
    have s: "\<And>a b. a \<bullet> (snd (WW (0, b)) + \<alpha> *\<^sub>R b)
        = b \<bullet> (snd (WW (0, a)) + \<alpha> *\<^sub>R a)"
    proof -
      fix a b :: "real^'n"
      have n1: "a \<bullet> (- (snd (WW (0, b)) + \<alpha> *\<^sub>R b))
          = b \<bullet> (- (snd (WW (0, a)) + \<alpha> *\<^sub>R a))"
        by (rule sym_block_snd[OF symW'])
      have l: "a \<bullet> (- (snd (WW (0, b)) + \<alpha> *\<^sub>R b))
          = - (a \<bullet> (snd (WW (0, b)) + \<alpha> *\<^sub>R b))"
        by (rule inner_minus_right)
      have r: "b \<bullet> (- (snd (WW (0, a)) + \<alpha> *\<^sub>R a))
          = - (b \<bullet> (snd (WW (0, a)) + \<alpha> *\<^sub>R a))"
        by (rule inner_minus_right)
      show "a \<bullet> (snd (WW (0, b)) + \<alpha> *\<^sub>R b)
          = b \<bullet> (snd (WW (0, a)) + \<alpha> *\<^sub>R a)"
        using n1 unfolding l r by linarith
    qed
    show "\<And>a b. a \<bullet> YU b = b \<bullet> YU a"
      unfolding YU_def by (rule sym_add_scaleR[OF s])
  qed
  have jetu: "(pu, XU) \<in> superjet u ysu"
    by (rule supconv_superjet_at_optimizer[OF Bu e0 optu expu linXU symXU])
  have jetb: "(pw, YU) \<in> superjet b ysw"
    by (rule supconv_superjet_at_optimizer[OF Bb e0 optb expb linYU symYU])
  have o3: "v \<bullet> XU v + v \<bullet> YU v \<le> 4 * \<delta> * (norm v)\<^sup>2" for v
  proof -
    have neg: "v \<bullet> (- (snd (WW (0, v)) + \<alpha> *\<^sub>R v))
        = - (v \<bullet> (snd (WW (0, v)) + \<alpha> *\<^sub>R v))"
      by (rule inner_minus_right)
    have base: "v \<bullet> (fst (WW (v, 0)) + \<alpha> *\<^sub>R v)
        + v \<bullet> (snd (WW (0, v)) + \<alpha> *\<^sub>R v) \<le> 0"
      using ord[of v] unfolding neg by linarith
    have x1: "v \<bullet> XU v = v \<bullet> (fst (WW (v, 0)) + \<alpha> *\<^sub>R v)
        + 2 * \<delta> * (norm v)\<^sup>2"
      unfolding XU_def
      by (simp add: inner_add_right power2_norm_eq_inner)
    have y1: "v \<bullet> YU v = v \<bullet> (snd (WW (0, v)) + \<alpha> *\<^sub>R v)
        + 2 * \<delta> * (norm v)\<^sup>2"
      unfolding YU_def
      by (simp add: inner_add_right power2_norm_eq_inner)
    show ?thesis unfolding x1 y1 using base by linarith
  qed
  have dfz: "dist (fst zh) xh \<le> \<rho>"
    using dist_fst_le[of zh "(xh, yh)"] dzr by simp
  have dsz: "dist (snd zh) yh \<le> \<rho>"
    using dist_snd_le[of zh "(xh, yh)"] dzr by simp
  define du where "du = dist (fst zh) ysu"
  define db where "db = dist (snd zh) ysw"
  define tt where "tt = du + db"
  have du0: "0 \<le> du" unfolding du_def by simp
  have db0: "0 \<le> db" unfolding db_def by simp
  have tt0: "0 \<le> tt" unfolding tt_def using du0 db0 by linarith
  have Tlow: "M - dd + (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2
      \<le> supconv u \<epsilon> (fst zh) + supconv b \<epsilon> (snd zh)"
  proof -
    have ximem: "((xh, yh) :: (real^'n) \<times> (real^'n)) \<in> cball ((xh, yh)) 1"
      by simp
    have step: "(af xh + bf yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2)
        + pt \<bullet> ((xh, yh) :: (real^'n) \<times> (real^'n))
        \<le> (af (fst zh) + bf (snd zh)
          - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2) + pt \<bullet> zh"
      using mxA[OF ximem] by simp
    have afxh: "af xh = supconv u \<epsilon> xh" unfolding af_def by simp
    have bfyh: "bf yh = supconv b \<epsilon> yh" unfolding bf_def by simp
    have gM: "M \<le> af xh + bf yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
      unfolding afxh bfyh Mval
      using supconv_ge[where u = u and B = Bu and \<epsilon> = \<epsilon> and x = xh, OF Bu e0]
        supconv_ge[where u = b and B = Bb and \<epsilon> = \<epsilon> and x = yh, OF Bb e0]
      by linarith
    have tilt: "pt \<bullet> zh - pt \<bullet> ((xh, yh) :: (real^'n) \<times> (real^'n)) \<le> dd"
    proof -
      have "pt \<bullet> zh - pt \<bullet> ((xh, yh) :: (real^'n) \<times> (real^'n))
          = pt \<bullet> (zh - (xh, yh))" by (simp add: inner_diff_right)
      also have "\<dots> \<le> \<bar>pt \<bullet> (zh - (xh, yh))\<bar>" by simp
      also have "\<dots> \<le> norm pt * norm (zh - ((xh, yh) :: (real^'n) \<times> (real^'n)))"
        by (rule Cauchy_Schwarz_ineq2)
      also have "\<dots> \<le> dd * 1"
      proof (rule mult_mono)
        show "norm pt \<le> dd" by (rule npt)
        show "norm (zh - ((xh, yh) :: (real^'n) \<times> (real^'n))) \<le> 1"
          using dz1 by (simp add: dist_norm)
      qed (use dd0 in auto)
      finally show ?thesis by simp
    qed
    have thz: "M - dd
        \<le> af (fst zh) + bf (snd zh) - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2"
      using step gM tilt by linarith
    have pen0: "0 \<le> \<delta> * (norm (fst zh - xh))\<^sup>2"
      using d0 by (intro mult_nonneg_nonneg) auto
    have pen0': "0 \<le> \<delta> * (norm (snd zh - yh))\<^sup>2"
      using d0 by (intro mult_nonneg_nonneg) auto
    show ?thesis using thz pen0 pen0' unfolding af_def bf_def by linarith
  qed
  have sumid: "u ysu + b ysw
      = (supconv u \<epsilon> (fst zh) + supconv b \<epsilon> (snd zh))
        + (du\<^sup>2 / (2*\<epsilon>) + db\<^sup>2 / (2*\<epsilon>))"
    unfolding du_def db_def using optu optb by simp
  have sumup: "u ysu + b ysw \<le> M + (\<alpha>/2) * (norm (ysu - ysw))\<^sup>2"
    using mxb[of ysu ysw] by linarith
  have anb: "norm (fst zh - snd zh) \<le> A"
    by (rule normbnd) (use dz1 in simp)
  have sigma: "du\<^sup>2 / (2*\<epsilon>) + db\<^sup>2 / (2*\<epsilon>)
        + (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2
      \<le> dd + (\<alpha>/2) * (norm (ysu - ysw))\<^sup>2"
    using Tlow sumid sumup by linarith
  have trib: "norm (ysu - ysw) \<le> norm (fst zh - snd zh) + tt"
  proof -
    have a1: "dist ysu ysw \<le> dist ysu (fst zh) + dist (fst zh) ysw"
      by (rule dist_triangle)
    have a2: "dist (fst zh) ysw \<le> dist (fst zh) (snd zh) + dist (snd zh) ysw"
      by (rule dist_triangle)
    have "dist ysu ysw \<le> dist (fst zh) (snd zh)
        + (dist (fst zh) ysu + dist (snd zh) ysw)"
      using a1 a2 dist_commute[of ysu "fst zh"] by linarith
    then show ?thesis unfolding tt_def du_def db_def
      by (simp add: dist_norm[symmetric])
  qed
  have ttb: "tt \<le> 8 * \<epsilon> * \<alpha> * A + sqrt (8 * \<epsilon> * dd)"
  proof -
    have sq: "(norm (ysu - ysw))\<^sup>2
        \<le> (norm (fst zh - snd zh))\<^sup>2 + 2 * A * tt + tt\<^sup>2"
    proof -
      have "(norm (ysu - ysw))\<^sup>2 \<le> (norm (fst zh - snd zh) + tt)\<^sup>2"
        by (rule power_mono[OF trib]) simp
      also have "\<dots> = (norm (fst zh - snd zh))\<^sup>2
          + 2 * norm (fst zh - snd zh) * tt + tt\<^sup>2"
        by (simp add: power2_sum)
      also have "2 * norm (fst zh - snd zh) * tt \<le> 2 * A * tt"
        using anb tt0 by (intro mult_right_mono) auto
      finally show ?thesis by linarith
    qed
    have pen: "tt\<^sup>2 / (4*\<epsilon>) \<le> du\<^sup>2 / (2*\<epsilon>) + db\<^sup>2 / (2*\<epsilon>)"
    proof -
      have "tt\<^sup>2 \<le> 2 * (du\<^sup>2 + db\<^sup>2)" unfolding tt_def
        by (rule add_sq_le_double)
      then show ?thesis using e0 by (simp add: field_simps)
    qed
    have half: "(\<alpha>/2) * tt\<^sup>2 \<le> tt\<^sup>2 / (8*\<epsilon>)"
    proof -
      have "\<alpha>/2 \<le> 1/(8*\<epsilon>)" using e4 e0 by (simp add: field_simps)
      then show ?thesis
        using mult_right_mono[of "\<alpha>/2" "1/(8*\<epsilon>)" "tt\<^sup>2"]
        by (simp add: field_simps)
    qed
    have h8: "tt\<^sup>2 / (4*\<epsilon>) - tt\<^sup>2 / (8*\<epsilon>) = tt\<^sup>2 / (8*\<epsilon>)"
      using e0 by (simp add: field_simps)
    have key: "tt\<^sup>2 / (8*\<epsilon>) \<le> dd + \<alpha> * A * tt"
    proof -
      have expand: "(\<alpha>/2) * ((norm (fst zh - snd zh))\<^sup>2 + 2 * A * tt + tt\<^sup>2)
          = (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2 + \<alpha> * A * tt + (\<alpha>/2) * tt\<^sup>2"
        by (simp add: field_simps)
      have mono: "(\<alpha>/2) * (norm (ysu - ysw))\<^sup>2
          \<le> (\<alpha>/2) * ((norm (fst zh - snd zh))\<^sup>2 + 2 * A * tt + tt\<^sup>2)"
        using sq a0 by (intro mult_left_mono) auto
      have mono': "(\<alpha>/2) * (norm (ysu - ysw))\<^sup>2
          \<le> (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2 + \<alpha> * A * tt + (\<alpha>/2) * tt\<^sup>2"
        using mono unfolding expand .
      show ?thesis using sigma pen half h8 mono' by linarith
    qed
    have quad: "tt\<^sup>2 \<le> (8 * \<epsilon> * \<alpha> * A) * tt + 8 * \<epsilon> * dd"
    proof -
      have "tt\<^sup>2 \<le> (dd + \<alpha> * A * tt) * (8*\<epsilon>)"
        using key e0 by (simp add: pos_divide_le_eq)
      then show ?thesis by (simp add: algebra_simps)
    qed
    show ?thesis
      by (rule quad_root_bound[OF _ _ quad])
        (use e0 a0 Ann dd0 in auto)
  qed
  have o4: "dist ysu xh \<le> \<rho> + 8 * \<epsilon> * \<alpha> * A + sqrt (8 * \<epsilon> * dd)"
  proof -
    have "dist ysu xh \<le> dist ysu (fst zh) + dist (fst zh) xh"
      by (rule dist_triangle)
    also have "dist ysu (fst zh) = du"
      unfolding du_def by (rule dist_commute)
    finally have "dist ysu xh \<le> du + \<rho>" using dfz by linarith
    moreover have "du \<le> tt" unfolding tt_def using db0 by linarith
    ultimately show ?thesis using ttb by linarith
  qed
  have o5: "dist ysw yh \<le> \<rho> + 8 * \<epsilon> * \<alpha> * A + sqrt (8 * \<epsilon> * dd)"
  proof -
    have "dist ysw yh \<le> dist ysw (snd zh) + dist (snd zh) yh"
      by (rule dist_triangle)
    also have "dist ysw (snd zh) = db"
      unfolding db_def by (rule dist_commute)
    finally have "dist ysw yh \<le> db + \<rho>" using dsz by linarith
    moreover have "db \<le> tt" unfolding tt_def using du0 by linarith
    ultimately show ?thesis using ttb by linarith
  qed
  have rearr: "(fst zh - snd zh) - (xh - yh)
      = (fst zh - xh) - (snd zh - yh)" by simp
  have ndiff: "norm ((fst zh - snd zh) - (xh - yh)) \<le> 2 * \<rho>"
  proof -
    have "norm ((fst zh - xh) - (snd zh - yh))
        \<le> norm (fst zh - xh) + norm (snd zh - yh)"
      by (rule norm_triangle_ineq4)
    also have "norm (fst zh - xh) \<le> \<rho>"
      using dfz by (simp add: dist_norm)
    also have "norm (snd zh - yh) \<le> \<rho>"
      using dsz by (simp add: dist_norm)
    finally show ?thesis unfolding rearr by linarith
  qed
  have o6: "norm (pu - \<alpha> *\<^sub>R (xh - yh)) \<le> dd + 2 * \<alpha> * \<rho> + 2 * \<delta> * \<rho>"
  proof -
    have split: "pu - \<alpha> *\<^sub>R (xh - yh)
        = - fst pt + \<alpha> *\<^sub>R ((fst zh - snd zh) - (xh - yh))
          + (2 * \<delta>) *\<^sub>R (fst zh - xh)"
      unfolding pu_def by (simp add: algebra_simps)
    have "norm (pu - \<alpha> *\<^sub>R (xh - yh))
        \<le> norm (- fst pt) + norm (\<alpha> *\<^sub>R ((fst zh - snd zh) - (xh - yh)))
          + norm ((2 * \<delta>) *\<^sub>R (fst zh - xh))"
      unfolding split by (meson norm_triangle_ineq norm_triangle_mono
          order_refl order_trans)
    moreover have "norm (- fst pt) \<le> dd"
      using norm_fst_le[of "fst pt" "snd pt"] npt by simp
    moreover have "norm (\<alpha> *\<^sub>R ((fst zh - snd zh) - (xh - yh)))
        \<le> \<alpha> * (2 * \<rho>)"
      using ndiff a0 by (simp add: mult_left_mono)
    moreover have "norm ((2 * \<delta>) *\<^sub>R (fst zh - xh)) \<le> 2 * \<delta> * \<rho>"
      using dfz d0 by (simp add: dist_norm mult_left_mono)
    ultimately show ?thesis by linarith
  qed
  have o7: "norm (pw + \<alpha> *\<^sub>R (xh - yh)) \<le> dd + 2 * \<alpha> * \<rho> + 2 * \<delta> * \<rho>"
  proof -
    have split: "pw + \<alpha> *\<^sub>R (xh - yh)
        = - snd pt - \<alpha> *\<^sub>R ((fst zh - snd zh) - (xh - yh))
          + (2 * \<delta>) *\<^sub>R (snd zh - yh)"
      unfolding pw_def by (simp add: algebra_simps)
    have "norm (pw + \<alpha> *\<^sub>R (xh - yh))
        \<le> norm (- snd pt) + norm (\<alpha> *\<^sub>R ((fst zh - snd zh) - (xh - yh)))
          + norm ((2 * \<delta>) *\<^sub>R (snd zh - yh))"
      unfolding split by (meson norm_triangle_ineq norm_triangle_mono
          norm_minus_cancel order_refl order_trans norm_diff_ineq
          norm_triangle_ineq4 add_mono)
    moreover have "norm (- snd pt) \<le> dd"
      using norm_snd_le[of "snd pt" "fst pt"] npt by simp
    moreover have "norm (\<alpha> *\<^sub>R ((fst zh - snd zh) - (xh - yh)))
        \<le> \<alpha> * (2 * \<rho>)"
      using ndiff a0 by (simp add: mult_left_mono)
    moreover have "norm ((2 * \<delta>) *\<^sub>R (snd zh - yh)) \<le> 2 * \<delta> * \<rho>"
      using dsz d0 by (simp add: dist_norm mult_left_mono)
    ultimately show ?thesis by linarith
  qed
  have o8: "M - dd - 2 * \<alpha> * A * \<rho> + (\<alpha>/2) * (norm (xh - yh))\<^sup>2
      \<le> u ysu + b ysw"
  proof -
    define aa where "aa = norm (fst zh - snd zh)"
    define bb where "bb = norm (xh - yh)"
    have aa0: "0 \<le> aa" unfolding aa_def by simp
    have bb0: "0 \<le> bb" unfolding bb_def by simp
    have bbA: "bb \<le> A" unfolding bb_def by (rule nhA)
    have close: "\<bar>aa - bb\<bar> \<le> 2 * \<rho>"
    proof -
      have "\<bar>norm (fst zh - snd zh) - norm (xh - yh)\<bar>
          \<le> norm ((fst zh - snd zh) - (xh - yh))"
        by (rule norm_triangle_ineq3)
      then show ?thesis unfolding aa_def bb_def using ndiff by linarith
    qed
    have sqlow: "bb\<^sup>2 - 4 * \<rho> * bb \<le> aa\<^sup>2"
    proof (cases "2 * \<rho> \<le> bb")
      case True
      have "bb - 2 * \<rho> \<le> aa" using close by linarith
      moreover have "0 \<le> bb - 2 * \<rho>" using True by linarith
      ultimately have "(bb - 2 * \<rho>)\<^sup>2 \<le> aa\<^sup>2" by (intro power_mono) auto
      moreover have "(bb - 2 * \<rho>)\<^sup>2 = bb\<^sup>2 - 4 * \<rho> * bb + 4 * \<rho>\<^sup>2"
        by (simp add: power2_diff power2_eq_square algebra_simps)
      ultimately show ?thesis
        using zero_le_power2[of \<rho>] by linarith
    next
      case False
      have "bb\<^sup>2 - 4 * \<rho> * bb = bb * (bb - 4 * \<rho>)"
        by (simp add: power2_eq_square algebra_simps)
      also have "\<dots> \<le> 0"
        using False bb0 rho0 by (intro mult_nonneg_nonpos) auto
      finally show ?thesis using zero_le_power2[of aa] by linarith
    qed
    have alow: "(\<alpha>/2) * bb\<^sup>2 - 2 * \<alpha> * \<rho> * bb \<le> (\<alpha>/2) * aa\<^sup>2"
    proof -
      have "(\<alpha>/2) * (bb\<^sup>2 - 4 * \<rho> * bb) \<le> (\<alpha>/2) * aa\<^sup>2"
        using sqlow a0 by (intro mult_left_mono) auto
      then show ?thesis by (simp add: field_simps)
    qed
    have rb: "2 * \<alpha> * \<rho> * bb \<le> 2 * \<alpha> * \<rho> * A"
      using bbA a0 rho0 by (intro mult_left_mono) auto
    have low: "M - dd + (\<alpha>/2) * aa\<^sup>2 \<le> u ysu + b ysw"
    proof -
      have pn: "0 \<le> du\<^sup>2 / (2*\<epsilon>) + db\<^sup>2 / (2*\<epsilon>)"
        using e0 by (intro add_nonneg_nonneg divide_nonneg_pos) auto
      show ?thesis using Tlow sumid pn unfolding aa_def by linarith
    qed
    show ?thesis using low alow rb unfolding bb_def
      by (simp add: algebra_simps)
  qed
  show ?thesis
    apply (rule exI[of _ "(ysu, ysw)"])
    apply (rule exI[of _ "(pu, pw)"])
    apply (rule exI[of _ XU])
    apply (rule exI[of _ YU])
    using jetu jetb o3 o4 o5 o6 o7 o8 by simp
qed


text \<open>The theorem on sums for the quadratic coupling, in the staged form the
  regularisation actually proves.  At a global maximum \<open>(xh, yh)\<close> of
  \<open>u x - w y - (\<alpha>/2)\<parallel>x - y\<parallel>\<^sup>2\<close> with \<open>u\<close> usc bounded above and \<open>w\<close> lsc
  bounded below, it produces a sequence of \<^emph>\<open>genuine\<close> semijets --- one
  superjet of \<open>u\<close>, one subjet of \<open>w\<close> --- ordered up to a vanishing slack,
  whose points, values and gradients converge to the data at \<open>(xh, yh)\<close>:
  every conjunct of the closed-semijet membership
  \<open>(\<alpha>(xh - yh), X) \<in> superjet_cl u xh\<close> except pointwise convergence of the
  form sequences \<open>Xs\<close>, \<open>Ys\<close> themselves.

  Along the \<open>\<epsilon> \<rightarrow> 0\<close> limit run here the form sequences are ordered and
  bounded on one side each, which does not yield convergent subsequences;
  the closed-jet statement of the classical theorem therefore does not
  follow from this one.  It is proved separately below
  (\<open>theorem_on_sums_quadratic_closed\<close>) by running the machinery at a
  FIXED regularisation against a deconvolved penalty.  The staged form
  remains the sharper quantitative statement: each of its jets is genuine,
  not a closure element.\<close>

section \<open>The theorem on sums, quadratic-penalty form\<close>

theorem theorem_on_sums_quadratic:
  fixes u w :: "real^'n::finite \<Rightarrow> real" and \<alpha> :: real and xh yh :: "real^'n"
  assumes usc: "\<And>c z. u z < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> u y < c"
    and lsc: "\<And>c z. c < w z \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> c < w y"
    and Bu: "\<And>y. u y \<le> Bu" and Bw: "\<And>y. Bw' \<le> w y"
    and a0: "0 < \<alpha>"
    and mx: "\<And>x y. u x - w y - (\<alpha>/2) * (norm (x - y))\<^sup>2
        \<le> u xh - w yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
  shows "\<exists>xs ys ps qs Xs Ys.
    (\<forall>n::nat. (ps n, Xs n) \<in> superjet u (xs n)) \<and>
    (\<forall>n. (qs n, Ys n) \<in> subjet w (ys n)) \<and>
    (\<forall>n v. v \<bullet> Xs n v \<le> v \<bullet> Ys n v + 4 / (real n + 2) * (norm v)\<^sup>2) \<and>
    xs \<longlonglongrightarrow> xh \<and> (\<lambda>n. u (xs n)) \<longlonglongrightarrow> u xh \<and>
    ys \<longlonglongrightarrow> yh \<and> (\<lambda>n. w (ys n)) \<longlonglongrightarrow> w yh \<and>
    ps \<longlonglongrightarrow> \<alpha> *\<^sub>R (xh - yh) \<and> qs \<longlonglongrightarrow> \<alpha> *\<^sub>R (xh - yh)"
proof -
  define b where "b = (\<lambda>y. - w y)"
  have Bb: "\<And>y. b y \<le> - Bw'" unfolding b_def using Bw by simp
  have uscb: "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> b y < c" if lt: "b z < c" for c z
  proof -
    have "- c < w z" using lt unfolding b_def by simp
    from lsc[OF this] obtain e where e: "0 < e"
      and h: "\<forall>y. dist z y < e \<longrightarrow> - c < w y" by blast
    show ?thesis
    proof (intro exI[of _ e] conjI e allI impI)
      fix y assume "dist z y < e"
      then have "- c < w y" using h by blast
      then show "b y < c" unfolding b_def by linarith
    qed
  qed
  define M where "M = u xh + b yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
  have mxb: "\<And>x y. u x + b y - (\<alpha>/2) * (norm (x - y))\<^sup>2 \<le> M"
    unfolding M_def b_def using mx by simp
  have Mval: "M = u xh + b yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
    unfolding M_def by (rule refl)
  define A where "A = norm (xh - yh) + 2"
  have Aval: "A = norm (xh - yh) + 2" unfolding A_def by (rule refl)
  have Ann: "0 \<le> A" unfolding A_def
    using norm_ge_zero[of "xh - yh"] by linarith
  define C where "C = 2 * \<alpha>\<^sup>2 * A\<^sup>2"
  have C0: "0 \<le> C" unfolding C_def
    by (intro mult_nonneg_nonneg) auto
  define dl where "dl = (\<lambda>n :: nat. 1 / (real n + 2))"
  define q3 where "q3 = (\<lambda>n. dl n * (dl n)\<^sup>2)"
  define ee where "ee = (\<lambda>n. min (1 / (4 * \<alpha> + 4)) (q3 n / (2 * C + 2)))"
  define ddn where "ddn = (\<lambda>n. q3 n / 8)"
  have dl0: "0 < dl n" for n unfolding dl_def by simp
  have dl1: "dl n < 1" for n unfolding dl_def by simp
  have q30: "0 < q3 n" for n unfolding q3_def
    using dl0[of n] by (intro mult_pos_pos) auto
  have ee0: "0 < ee n" for n
  proof -
    have "0 < 1 / (4 * \<alpha> + 4)" using a0 by simp
    moreover have "0 < q3 n / (2 * C + 2)"
      using q30[of n] C0 by (intro divide_pos_pos) auto
    ultimately show ?thesis unfolding ee_def by simp
  qed
  have ee4: "4 * \<alpha> * ee n \<le> 1" for n
  proof -
    have h1: "ee n \<le> 1 / (4 * \<alpha> + 4)"
      unfolding ee_def by (rule min.cobounded1)
    have "4 * \<alpha> * ee n \<le> 4 * \<alpha> * (1 / (4 * \<alpha> + 4))"
      using h1 a0 by (intro mult_left_mono) auto
    also have "\<dots> \<le> 1" using a0 by (simp add: field_simps)
    finally show ?thesis .
  qed
  have dd0n: "0 < ddn n" for n
    unfolding ddn_def using q30[of n] by simp
  have gapn: "2 * \<alpha>\<^sup>2 * A\<^sup>2 * ee n \<le> dl n * (dl n)\<^sup>2 / 2" for n
  proof -
    have le1: "ee n \<le> q3 n / (2 * C + 2)"
      unfolding ee_def by (rule min.cobounded2)
    have le2: "C * ee n \<le> C * (q3 n / (2 * C + 2))"
      by (rule mult_left_mono[OF le1 C0])
    have le3: "C * (q3 n / (2 * C + 2)) \<le> q3 n / 2"
    proof -
      have e1: "C * (q3 n / (2 * C + 2)) = (C / (2 * C + 2)) * q3 n"
        by simp
      have e2: "C / (2 * C + 2) \<le> 1 / 2"
        using C0 by (simp add: field_simps)
      have "(C / (2 * C + 2)) * q3 n \<le> (1 / 2) * q3 n"
        using e2 q30[of n] by (intro mult_right_mono) auto
      then show ?thesis unfolding e1 by simp
    qed
    have "C * ee n \<le> q3 n / 2" using le2 le3 by linarith
    then show ?thesis unfolding C_def q3_def by linarith
  qed
  have ddsmalln: "2 * ddn n < dl n * (dl n)\<^sup>2 / 2" for n
  proof -
    have "2 * ddn n = q3 n / 4" unfolding ddn_def by simp
    also have "q3 n / 4 < q3 n / 2" using q30[of n] by argo
    finally show ?thesis unfolding q3_def by simp
  qed
  define SP where "SP = (\<lambda>n (xy :: (real^'n) \<times> (real^'n))
      (pq :: (real^'n) \<times> (real^'n)) (XU :: real^'n \<Rightarrow> real^'n)
      (YU :: real^'n \<Rightarrow> real^'n).
    (fst pq, XU) \<in> superjet u (fst xy) \<and>
    (snd pq, YU) \<in> superjet b (snd xy) \<and>
    (\<forall>v. v \<bullet> XU v + v \<bullet> YU v \<le> 4 * dl n * (norm v)\<^sup>2) \<and>
    dist (fst xy) xh \<le> dl n + 8 * ee n * \<alpha> * A + sqrt (8 * ee n * ddn n) \<and>
    dist (snd xy) yh \<le> dl n + 8 * ee n * \<alpha> * A + sqrt (8 * ee n * ddn n) \<and>
    norm (fst pq - \<alpha> *\<^sub>R (xh - yh))
      \<le> ddn n + 2 * \<alpha> * dl n + 2 * dl n * dl n \<and>
    norm (snd pq + \<alpha> *\<^sub>R (xh - yh))
      \<le> ddn n + 2 * \<alpha> * dl n + 2 * dl n * dl n \<and>
    M - ddn n - 2 * \<alpha> * A * dl n + (\<alpha>/2) * (norm (xh - yh))\<^sup>2
      \<le> u (fst xy) + b (snd xy))"
  have EX: "\<exists>xy pq XU YU. SP n xy pq XU YU" for n
    unfolding SP_def
    by (rule theorem_on_sums_stage[OF Bu Bb usc uscb a0 mxb Mval Aval
        ee0 ee4 dl0 dl0 dl1 gapn dd0n ddsmalln])
  obtain FF GG HH II where ALL: "\<forall>n. SP n (FF n) (GG n) (HH n) (II n)"
    using choice4[of SP, OF EX] by blast
  define xs where "xs = (\<lambda>n. fst (FF n))"
  define ys where "ys = (\<lambda>n. snd (FF n))"
  define ps where "ps = (\<lambda>n. fst (GG n))"
  define qs where "qs = (\<lambda>n. - snd (GG n))"
  define Xs where "Xs = HH"
  define Ys where "Ys = (\<lambda>n h. - II n h)"
  have sp: "SP n (FF n) (GG n) (HH n) (II n)" for n using ALL by blast
  have jetu: "(ps n, Xs n) \<in> superjet u (xs n)" for n
    using sp[of n] unfolding SP_def xs_def ps_def Xs_def by blast
  have jetbb: "(snd (GG n), II n) \<in> superjet b (ys n)" for n
    using sp[of n] unfolding SP_def ys_def by blast
  have ordn: "v \<bullet> HH n v + v \<bullet> II n v \<le> 4 * dl n * (norm v)\<^sup>2" for n v
    using sp[of n] unfolding SP_def by blast
  have o4n: "dist (xs n) xh
      \<le> dl n + 8 * ee n * \<alpha> * A + sqrt (8 * ee n * ddn n)" for n
    using sp[of n] unfolding SP_def xs_def by blast
  have o5n: "dist (ys n) yh
      \<le> dl n + 8 * ee n * \<alpha> * A + sqrt (8 * ee n * ddn n)" for n
    using sp[of n] unfolding SP_def ys_def by blast
  have o6n: "norm (ps n - \<alpha> *\<^sub>R (xh - yh))
      \<le> ddn n + 2 * \<alpha> * dl n + 2 * dl n * dl n" for n
    using sp[of n] unfolding SP_def ps_def by blast
  have o7n: "norm (snd (GG n) + \<alpha> *\<^sub>R (xh - yh))
      \<le> ddn n + 2 * \<alpha> * dl n + 2 * dl n * dl n" for n
    using sp[of n] unfolding SP_def by blast
  have o8n: "M - ddn n - 2 * \<alpha> * A * dl n + (\<alpha>/2) * (norm (xh - yh))\<^sup>2
      \<le> u (xs n) + b (ys n)" for n
    using sp[of n] unfolding SP_def xs_def ys_def by blast
  have jetw: "(qs n, Ys n) \<in> subjet w (ys n)" for n
  proof -
    have h: "(snd (GG n), II n) \<in> superjet (\<lambda>z. - w z) (ys n)"
      using jetbb[of n] unfolding b_def .
    show ?thesis unfolding qs_def Ys_def
      by (subst subjet_neg_superjet) (use h in simp)
  qed
  have ordfin: "v \<bullet> Xs n v \<le> v \<bullet> Ys n v + 4 / (real n + 2) * (norm v)\<^sup>2"
    for n v
  proof -
    have m: "v \<bullet> Ys n v = - (v \<bullet> II n v)"
      unfolding Ys_def by (rule inner_minus_right)
    have d: "4 * dl n = 4 / (real n + 2)" unfolding dl_def by simp
    show ?thesis using ordn[of v n] unfolding Xs_def m d[symmetric]
      by linarith
  qed
  have dlt: "dl \<longlonglongrightarrow> 0"
  proof (rule tendsto_sandwich[of "\<lambda>_. 0" _ _ "\<lambda>n. inverse (real (Suc n))"])
    show "\<forall>\<^sub>F n in sequentially. 0 \<le> dl n"
      using dl0 by (intro always_eventually allI) (simp add: less_imp_le)
    show "\<forall>\<^sub>F n in sequentially. dl n \<le> inverse (real (Suc n))"
      unfolding dl_def
      by (intro always_eventually allI) (simp add: field_simps)
    show "(\<lambda>_ :: nat. (0::real)) \<longlonglongrightarrow> 0" by (rule tendsto_const)
    show "(\<lambda>n. inverse (real (Suc n))) \<longlonglongrightarrow> 0"
      by (rule LIMSEQ_inverse_real_of_nat)
  qed
  have q3t: "q3 \<longlonglongrightarrow> 0"
  proof -
    have "(\<lambda>n. dl n * (dl n)\<^sup>2) \<longlonglongrightarrow> 0 * (0::real)\<^sup>2"
      by (intro tendsto_mult tendsto_power dlt)
    then show ?thesis unfolding q3_def by simp
  qed
  have eet: "ee \<longlonglongrightarrow> 0"
  proof (rule tendsto_sandwich[of "\<lambda>_. 0" _ _ "\<lambda>n. q3 n / (2 * C + 2)"])
    show "\<forall>\<^sub>F n in sequentially. 0 \<le> ee n"
      using ee0 by (intro always_eventually allI) (simp add: less_imp_le)
    show "\<forall>\<^sub>F n in sequentially. ee n \<le> q3 n / (2 * C + 2)"
      unfolding ee_def by (intro always_eventually allI min.cobounded2)
    have "(\<lambda>n. q3 n / (2 * C + 2)) \<longlonglongrightarrow> 0 / (2 * C + 2)"
      using C0 by (intro tendsto_divide q3t tendsto_const) auto
    then show "(\<lambda>n. q3 n / (2 * C + 2)) \<longlonglongrightarrow> 0" by simp
  qed simp
  have ddt: "ddn \<longlonglongrightarrow> 0"
  proof -
    have "(\<lambda>n. q3 n / 8) \<longlonglongrightarrow> 0 / 8"
      by (intro tendsto_divide q3t tendsto_const) auto
    then show ?thesis unfolding ddn_def by simp
  qed
  have bndt: "(\<lambda>n. dl n + 8 * ee n * \<alpha> * A + sqrt (8 * ee n * ddn n))
      \<longlonglongrightarrow> 0"
  proof -
    have t2: "(\<lambda>n. 8 * ee n * ddn n) \<longlonglongrightarrow> 8 * 0 * 0"
      by (intro tendsto_mult tendsto_const eet ddt)
    have t3: "(\<lambda>n. sqrt (8 * ee n * ddn n)) \<longlonglongrightarrow> sqrt (8 * 0 * 0)"
      by (rule tendsto_real_sqrt[OF t2])
    have "(\<lambda>n. dl n + 8 * ee n * \<alpha> * A + sqrt (8 * ee n * ddn n))
        \<longlonglongrightarrow> 0 + 8 * 0 * \<alpha> * A + sqrt (8 * 0 * 0)"
      by (intro tendsto_add tendsto_mult tendsto_const dlt eet t3)
    then show ?thesis by simp
  qed
  have xst: "xs \<longlonglongrightarrow> xh"
    by (rule tendsto_of_dist_bound[OF o4n bndt])
  have yst: "ys \<longlonglongrightarrow> yh"
    by (rule tendsto_of_dist_bound[OF o5n bndt])
  have gbt: "(\<lambda>n. ddn n + 2 * \<alpha> * dl n + 2 * dl n * dl n) \<longlonglongrightarrow> 0"
  proof -
    have "(\<lambda>n. ddn n + 2 * \<alpha> * dl n + 2 * dl n * dl n)
        \<longlonglongrightarrow> 0 + 2 * \<alpha> * 0 + 2 * 0 * 0"
      by (intro tendsto_add tendsto_mult tendsto_const ddt dlt)
    then show ?thesis by simp
  qed
  have pst: "ps \<longlonglongrightarrow> \<alpha> *\<^sub>R (xh - yh)"
  proof (rule tendsto_of_dist_bound[OF _ gbt])
    fix n
    show "dist (ps n) (\<alpha> *\<^sub>R (xh - yh))
        \<le> ddn n + 2 * \<alpha> * dl n + 2 * dl n * dl n"
      using o6n[of n] by (simp add: dist_norm)
  qed
  have qst: "qs \<longlonglongrightarrow> \<alpha> *\<^sub>R (xh - yh)"
  proof (rule tendsto_of_dist_bound[OF _ gbt])
    fix n
    have e1: "qs n - \<alpha> *\<^sub>R (xh - yh) = - (snd (GG n) + \<alpha> *\<^sub>R (xh - yh))"
      unfolding qs_def by (simp add: algebra_simps)
    have "dist (qs n) (\<alpha> *\<^sub>R (xh - yh))
        = norm (snd (GG n) + \<alpha> *\<^sub>R (xh - yh))"
      unfolding dist_norm e1 norm_minus_cancel by (rule refl)
    then show "dist (qs n) (\<alpha> *\<^sub>R (xh - yh))
        \<le> ddn n + 2 * \<alpha> * dl n + 2 * dl n * dl n"
      using o7n[of n] by linarith
  qed
  have sumlim: "(\<lambda>n. u (xs n) + b (ys n)) \<longlonglongrightarrow> u xh + b yh"
  proof -
    have Lt: "(\<lambda>n. M - ddn n - 2 * \<alpha> * A * dl n
        + (\<alpha>/2) * (norm (xh - yh))\<^sup>2)
        \<longlonglongrightarrow> M - 0 - 2 * \<alpha> * A * 0 + (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
      by (intro tendsto_add tendsto_diff tendsto_mult tendsto_const ddt dlt)
    have Ut: "(\<lambda>n. M + (\<alpha>/2) * (norm (xs n - ys n))\<^sup>2)
        \<longlonglongrightarrow> M + (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
      by (intro tendsto_add tendsto_mult tendsto_const tendsto_power
          tendsto_norm tendsto_diff xst yst)
    have "(\<lambda>n. u (xs n) + b (ys n)) \<longlonglongrightarrow> M + (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
    proof (rule tendsto_sandwich[of
        "\<lambda>n. M - ddn n - 2 * \<alpha> * A * dl n + (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
        _ _ "\<lambda>n. M + (\<alpha>/2) * (norm (xs n - ys n))\<^sup>2"])
      show "\<forall>\<^sub>F n in sequentially.
          M - ddn n - 2 * \<alpha> * A * dl n + (\<alpha>/2) * (norm (xh - yh))\<^sup>2
          \<le> u (xs n) + b (ys n)"
        using o8n by (intro always_eventually allI)
      have up: "u (xs k) + b (ys k)
          \<le> M + (\<alpha>/2) * (norm (xs k - ys k))\<^sup>2" for k
        using mxb[of "xs k" "ys k"] by linarith
      show "\<forall>\<^sub>F n in sequentially.
          u (xs n) + b (ys n) \<le> M + (\<alpha>/2) * (norm (xs n - ys n))\<^sup>2"
        using up by (intro always_eventually allI)
      show "(\<lambda>n. M - ddn n - 2 * \<alpha> * A * dl n
          + (\<alpha>/2) * (norm (xh - yh))\<^sup>2)
          \<longlonglongrightarrow> M + (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
        using Lt by simp
    qed (rule Ut)
    moreover have "M + (\<alpha>/2) * (norm (xh - yh))\<^sup>2 = u xh + b yh"
      unfolding M_def by simp
    ultimately show ?thesis by simp
  qed
  have uxs: "(\<lambda>n. u (xs n)) \<longlonglongrightarrow> u xh"
    by (rule sum_squeeze_pair_fst[OF usc_eventually_lt[OF usc xst]
        usc_eventually_lt[OF uscb yst] sumlim])
  have bys: "(\<lambda>n. b (ys n)) \<longlonglongrightarrow> b yh"
  proof -
    have comm: "(\<lambda>n. b (ys n) + u (xs n)) = (\<lambda>n. u (xs n) + b (ys n))"
      by (rule ext) (rule add.commute)
    have commv: "b yh + u xh = u xh + b yh" by (rule add.commute)
    have s2: "(\<lambda>n. b (ys n) + u (xs n)) \<longlonglongrightarrow> b yh + u xh"
      unfolding comm commv by (rule sumlim)
    show ?thesis
      by (rule sum_squeeze_pair_fst[OF usc_eventually_lt[OF uscb yst]
          usc_eventually_lt[OF usc xst] s2])
  qed
  have wys: "(\<lambda>n. w (ys n)) \<longlonglongrightarrow> w yh"
  proof -
    have weq: "(\<lambda>n. w (ys n)) = (\<lambda>n. - b (ys n))"
      by (rule ext) (simp add: b_def)
    have wv: "- b yh = w yh" by (simp add: b_def)
    have "(\<lambda>n. - b (ys n)) \<longlonglongrightarrow> - b yh" by (rule tendsto_minus[OF bys])
    then show ?thesis unfolding weq wv .
  qed
  show ?thesis
    apply (rule exI[of _ xs])
    apply (rule exI[of _ ys])
    apply (rule exI[of _ ps])
    apply (rule exI[of _ qs])
    apply (rule exI[of _ Xs])
    apply (rule exI[of _ Ys])
    using jetu jetw ordfin xst uxs yst wys pst qst by blast
qed

section \<open>Deconvolving the quadratic penalty\<close>

lemma norm_sq_diff_expand:
  fixes a b :: "'a::euclidean_space"
  shows "(norm (a - b))\<^sup>2 = (norm a)\<^sup>2 - 2 * (a \<bullet> b) + (norm b)\<^sup>2"
  by (simp add: power2_norm_eq_inner inner_diff_left inner_diff_right
      inner_commute)

lemma deconv_sos_identity:
  fixes d r :: "'a::euclidean_space" and \<alpha> lam al :: real
  assumes l0: "0 < lam" and a0: "0 < \<alpha>" and la1: "2 * lam * \<alpha> < 1"
    and al: "al = \<alpha> / (1 - 2 * lam * \<alpha>)"
  shows "(al/2) * (norm (d - r))\<^sup>2 + (norm r)\<^sup>2 / (4*lam)
      - (\<alpha>/2) * (norm d)\<^sup>2
    = (al/(4*lam*\<alpha>)) * (norm (r - (2*lam*\<alpha>) *\<^sub>R d))\<^sup>2"
proof -
  define D where "D = (norm d)\<^sup>2"
  define R where "R = (norm r)\<^sup>2"
  define I where "I = d \<bullet> r"
  have e1: "(norm (d - r))\<^sup>2 = D - 2 * I + R"
    unfolding D_def R_def I_def by (rule norm_sq_diff_expand)
  have e2: "(norm (r - (2*lam*\<alpha>) *\<^sub>R d))\<^sup>2
      = R - (4*lam*\<alpha>) * I + (4 * lam\<^sup>2 * \<alpha>\<^sup>2) * D"
  proof -
    have "(norm (r - (2*lam*\<alpha>) *\<^sub>R d))\<^sup>2
        = (norm r)\<^sup>2 - 2 * (r \<bullet> (2*lam*\<alpha>) *\<^sub>R d)
          + (norm ((2*lam*\<alpha>) *\<^sub>R d))\<^sup>2"
      by (rule norm_sq_diff_expand)
    also have "r \<bullet> (2*lam*\<alpha>) *\<^sub>R d = (2*lam*\<alpha>) * I"
      unfolding I_def by (simp add: inner_commute)
    also have "(norm ((2*lam*\<alpha>) *\<^sub>R d))\<^sup>2 = (4 * lam\<^sup>2 * \<alpha>\<^sup>2) * D"
      unfolding D_def
      using l0 a0
      by (simp add: power_mult_distrib power2_eq_square abs_mult)
    finally show ?thesis unfolding R_def by (simp add: algebra_simps)
  qed
  have ne: "1 - 2 * lam * \<alpha> \<noteq> 0" using la1 by linarith
  have lne: "lam \<noteq> 0" using l0 by linarith
  have ane: "\<alpha> \<noteq> 0" using a0 by linarith
  have scalar: "(al/2) * (D - 2 * I + R) + R / (4*lam) - (\<alpha>/2) * D
      = (al/(4*lam*\<alpha>)) * (R - (4*lam*\<alpha>) * I + (4 * lam\<^sup>2 * \<alpha>\<^sup>2) * D)"
    unfolding al using ne lne ane
    by (simp add: field_simps power2_eq_square)
  show ?thesis
    unfolding e1 e2 D_def[symmetric] R_def[symmetric] by (rule scalar)
qed

lemma deconv_moreau_bound:
  fixes x y x' y' :: "'a::euclidean_space" and \<alpha> lam al :: real
  assumes l0: "0 < lam" and a0: "0 < \<alpha>" and la1: "2 * lam * \<alpha> < 1"
    and al: "al = \<alpha> / (1 - 2 * lam * \<alpha>)"
  shows "(\<alpha>/2) * (norm (x - y))\<^sup>2
      \<le> (al/2) * (norm (x' - y'))\<^sup>2
        + ((dist x' x)\<^sup>2 + (dist y' y)\<^sup>2) / (2*lam)"
proof -
  define s where "s = x - x'"
  define t where "t = y - y'"
  define r where "r = s - t"
  define d where "d = x - y"
  have d': "x' - y' = d - r" unfolding d_def r_def s_def t_def by simp
  have al0: "0 < al" unfolding al using a0 la1 by (simp add: field_simps)
  have half: "(norm r)\<^sup>2 \<le> 2 * ((norm s)\<^sup>2 + (norm t)\<^sup>2)"
  proof -
    have "norm r \<le> norm s + norm t"
      unfolding r_def by (rule norm_triangle_ineq4)
    then have "(norm r)\<^sup>2 \<le> (norm s + norm t)\<^sup>2"
      by (intro power_mono) auto
    also have "\<dots> \<le> 2 * ((norm s)\<^sup>2 + (norm t)\<^sup>2)"
      by (rule add_sq_le_double)
    finally show ?thesis .
  qed
  have pens: "(dist x' x)\<^sup>2 + (dist y' y)\<^sup>2 = (norm s)\<^sup>2 + (norm t)\<^sup>2"
    unfolding s_def t_def by (simp add: dist_norm norm_minus_commute)
  have p1: "(norm r)\<^sup>2 / (4*lam) \<le> ((norm s)\<^sup>2 + (norm t)\<^sup>2) / (2*lam)"
    using half l0 by (simp add: field_simps)
  have sos: "(\<alpha>/2) * (norm d)\<^sup>2
      \<le> (al/2) * (norm (d - r))\<^sup>2 + (norm r)\<^sup>2 / (4*lam)"
  proof -
    have nn: "0 \<le> (al/(4*lam*\<alpha>)) * (norm (r - (2*lam*\<alpha>) *\<^sub>R d))\<^sup>2"
      using al0 l0 a0 by (intro mult_nonneg_nonneg) auto
    show ?thesis
      using deconv_sos_identity[OF l0 a0 la1 al, of d r] nn by linarith
  qed
  have "(\<alpha>/2) * (norm (x - y))\<^sup>2
      \<le> (al/2) * (norm (x' - y'))\<^sup>2 + (norm r)\<^sup>2 / (4*lam)"
    using sos unfolding d_def[symmetric] d' by simp
  moreover have "((dist x' x)\<^sup>2 + (dist y' y)\<^sup>2) / (2*lam)
      = ((norm s)\<^sup>2 + (norm t)\<^sup>2) / (2*lam)"
    using pens by simp
  ultimately show ?thesis using p1 by linarith
qed

text \<open>The doubled functional of the \<open>lam\<close>-sup-convolutions with the inflated
  penalty \<open>al = \<alpha>/(1 - 2lam\<alpha>)\<close> never exceeds the original maximum \<open>M\<close> --- the
  \<open>\<le>\<close> half of the Moreau identity.\<close>

lemma deconv_doubled_le:
  fixes u b :: "'a::euclidean_space \<Rightarrow> real" and \<alpha> lam al M :: real
  assumes Bu: "\<And>y. u y \<le> Bu" and Bb: "\<And>y. b y \<le> Bb"
    and l0: "0 < lam" and a0: "0 < \<alpha>" and la1: "2 * lam * \<alpha> < 1"
    and al: "al = \<alpha> / (1 - 2 * lam * \<alpha>)"
    and mxb: "\<And>x y. u x + b y - (\<alpha>/2) * (norm (x - y))\<^sup>2 \<le> M"
  shows "supconv u lam x' + supconv b lam y'
      - (al/2) * (norm (x' - y'))\<^sup>2 \<le> M"
proof -
  define K where "K = M + (al/2) * (norm (x' - y'))\<^sup>2"
  have core: "(u xx - (dist x' xx)\<^sup>2 / (2*lam))
      + (b yy - (dist y' yy)\<^sup>2 / (2*lam)) \<le> K" for xx yy
  proof -
    have "u xx + b yy \<le> M + (\<alpha>/2) * (norm (xx - yy))\<^sup>2"
      using mxb[of xx yy] by linarith
    moreover have "(\<alpha>/2) * (norm (xx - yy))\<^sup>2
        \<le> (al/2) * (norm (x' - y'))\<^sup>2
          + ((dist x' xx)\<^sup>2 + (dist y' yy)\<^sup>2) / (2*lam)"
      by (rule deconv_moreau_bound[OF l0 a0 la1 al])
    moreover have "(dist x' xx)\<^sup>2 / (2*lam) + (dist y' yy)\<^sup>2 / (2*lam)
        = ((dist x' xx)\<^sup>2 + (dist y' yy)\<^sup>2) / (2*lam)"
      by (simp add: add_divide_distrib)
    ultimately show ?thesis unfolding K_def by linarith
  qed
  have step1: "supconv b lam y' \<le> K - (u xx - (dist x' xx)\<^sup>2 / (2*lam))" for xx
    unfolding supconv_def
    by (intro cSUP_least) (use core[of xx] in \<open>auto simp: algebra_simps\<close>)
  have step2: "supconv u lam x' \<le> K - supconv b lam y'"
  proof -
    have h: "u xx - (dist x' xx)\<^sup>2 / (2*lam) \<le> K - supconv b lam y'" for xx
      using step1[of xx] by linarith
    show ?thesis unfolding supconv_def[of u]
      by (intro cSUP_least) (use h in auto)
  qed
  then show ?thesis unfolding K_def by (simp add: algebra_simps)
qed

text \<open>With the inflated penalty, the regularised doubled functional attains
  the SAME maximum \<open>M\<close>, at the explicitly shifted point
  \<open>(xh - \<lambda>g, yh + \<lambda>g)\<close> where \<open>g = \<alpha>(xh - yh)\<close>.\<close>

lemma deconv_doubled_attains:
  fixes u b :: "'a::euclidean_space \<Rightarrow> real" and \<alpha> lam al M :: real
    and xh yh g :: 'a
  assumes Bu: "\<And>y. u y \<le> Bu" and Bb: "\<And>y. b y \<le> Bb"
    and l0: "0 < lam" and a0: "0 < \<alpha>" and la1: "2 * lam * \<alpha> < 1"
    and al: "al = \<alpha> / (1 - 2 * lam * \<alpha>)"
    and mxb: "\<And>x y. u x + b y - (\<alpha>/2) * (norm (x - y))\<^sup>2 \<le> M"
    and Mval: "M = u xh + b yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
    and gd: "g = \<alpha> *\<^sub>R (xh - yh)"
  shows "supconv u lam (xh - lam *\<^sub>R g) + supconv b lam (yh + lam *\<^sub>R g)
      - (al/2) * (norm ((xh - lam *\<^sub>R g) - (yh + lam *\<^sub>R g)))\<^sup>2 = M"
proof -
  have ne: "1 - 2 * lam * \<alpha> \<noteq> 0" using la1 by linarith
  have alid: "al * (1 - 2 * lam * \<alpha>) = \<alpha>" unfolding al using ne by simp
  have u1: "u xh - (dist (xh - lam *\<^sub>R g) xh)\<^sup>2 / (2*lam)
      \<le> supconv u lam (xh - lam *\<^sub>R g)"
    unfolding supconv_def
    by (intro cSUP_upper supconv_bdd_above[OF Bu l0]) auto
  have b1: "b yh - (dist (yh + lam *\<^sub>R g) yh)\<^sup>2 / (2*lam)
      \<le> supconv b lam (yh + lam *\<^sub>R g)"
    unfolding supconv_def
    by (intro cSUP_upper supconv_bdd_above[OF Bb l0]) auto
  have du: "(dist (xh - lam *\<^sub>R g) xh)\<^sup>2 = lam\<^sup>2 * (norm g)\<^sup>2"
    using l0 by (simp add: dist_norm norm_minus_commute
        power_mult_distrib power2_eq_square abs_mult)
  have db: "(dist (yh + lam *\<^sub>R g) yh)\<^sup>2 = lam\<^sup>2 * (norm g)\<^sup>2"
    using l0 by (simp add: dist_norm
        power_mult_distrib power2_eq_square abs_mult)
  have pend: "(xh - lam *\<^sub>R g) - (yh + lam *\<^sub>R g)
      = (1 - 2 * lam * \<alpha>) *\<^sub>R (xh - yh)"
  proof -
    have e1: "lam *\<^sub>R g = (lam * \<alpha>) *\<^sub>R (xh - yh)"
      unfolding gd by simp
    have e2: "(1 - 2 * lam * \<alpha>) *\<^sub>R (xh - yh)
        = (xh - yh) - (2 * lam * \<alpha>) *\<^sub>R (xh - yh)"
      by (simp add: scaleR_diff_left)
    have e3: "(lam * \<alpha>) *\<^sub>R (xh - yh) + (lam * \<alpha>) *\<^sub>R (xh - yh)
        = (2 * lam * \<alpha>) *\<^sub>R (xh - yh)"
      by (simp add: scaleR_add_left[symmetric])
    show ?thesis unfolding e1 e2 e3[symmetric] by (simp add: algebra_simps)
  qed
  have penn: "(norm ((xh - lam *\<^sub>R g) - (yh + lam *\<^sub>R g)))\<^sup>2
      = (1 - 2 * lam * \<alpha>)\<^sup>2 * (norm (xh - yh))\<^sup>2"
    unfolding pend
    by (simp add: power_mult_distrib power2_eq_square abs_mult)
  have gsq: "(norm g)\<^sup>2 = \<alpha>\<^sup>2 * (norm (xh - yh))\<^sup>2"
    unfolding gd using a0
    by (simp add: power_mult_distrib power2_eq_square abs_mult)
  have divu: "lam\<^sup>2 * (norm g)\<^sup>2 / (2*lam) = lam * (norm g)\<^sup>2 / 2"
    using l0 by (simp add: power2_eq_square)
  have penc: "(al/2) * ((1 - 2 * lam * \<alpha>)\<^sup>2 * (norm (xh - yh))\<^sup>2)
      = (\<alpha>/2) * (norm (xh - yh))\<^sup>2 - lam * \<alpha>\<^sup>2 * (norm (xh - yh))\<^sup>2"
  proof -
    have "(al/2) * ((1 - 2 * lam * \<alpha>)\<^sup>2 * (norm (xh - yh))\<^sup>2)
        = (al * (1 - 2 * lam * \<alpha>)) * ((1 - 2 * lam * \<alpha>)
            * (norm (xh - yh))\<^sup>2) / 2"
      by (simp add: power2_eq_square algebra_simps)
    also have "\<dots> = \<alpha> * ((1 - 2 * lam * \<alpha>) * (norm (xh - yh))\<^sup>2) / 2"
      unfolding alid by (rule refl)
    finally show ?thesis by (simp add: field_simps power2_eq_square)
  qed
  have low: "M \<le> supconv u lam (xh - lam *\<^sub>R g) + supconv b lam (yh + lam *\<^sub>R g)
      - (al/2) * (norm ((xh - lam *\<^sub>R g) - (yh + lam *\<^sub>R g)))\<^sup>2"
  proof -
    have "M = u xh + b yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2" by (rule Mval)
    moreover have "lam * (norm g)\<^sup>2 / 2 + lam * (norm g)\<^sup>2 / 2
        = lam * \<alpha>\<^sup>2 * (norm (xh - yh))\<^sup>2"
      unfolding gsq by simp
    ultimately show ?thesis
      using u1 b1 unfolding du db divu penn penc by linarith
  qed
  have high: "supconv u lam (xh - lam *\<^sub>R g) + supconv b lam (yh + lam *\<^sub>R g)
      - (al/2) * (norm ((xh - lam *\<^sub>R g) - (yh + lam *\<^sub>R g)))\<^sup>2 \<le> M"
    by (rule deconv_doubled_le[OF Bu Bb l0 a0 la1 al mxb])
  show ?thesis using low high by linarith
qed

section \<open>Semiconvexity bounds the forms of every superjet\<close>

lemma superjet_supconv_form_lower:
  fixes u :: "'a::euclidean_space \<Rightarrow> real" and h :: 'a
  assumes B: "\<And>y. u y \<le> B" and l0: "0 < lam"
    and jet: "(p, F) \<in> superjet (supconv u lam) x"
  shows "- ((norm h)\<^sup>2 / lam) \<le> h \<bullet> F h"
proof (cases "h = 0")
  case True
  have "linear F" using jet unfolding superjet_def by blast
  then have "F 0 = 0" by (rule linear_0)
  then show ?thesis unfolding True by simp
next
  case False
  define v where "v = supconv u lam"
  have linF: "linear F" using jet unfolding superjet_def v_def by blast
  have cvx: "convex_on UNIV (\<lambda>z. v z + (norm z)\<^sup>2 / (2*lam))"
    unfolding v_def by (rule supconv_semiconvex[OF B l0])
  have key: "2 * v z \<le> v (z + k) + v (z - k) + (norm k)\<^sup>2 / lam"
    for z k :: 'a
  proof -
    have mid: "(1 - 1/2) *\<^sub>R (z + k) + (1/2) *\<^sub>R (z - k) = z"
    proof -
      have "(1/2) *\<^sub>R (z + k) + (1/2) *\<^sub>R (z - k)
          = (1/2) *\<^sub>R z + (1/2) *\<^sub>R z"
        by (simp add: scaleR_add_right scaleR_diff_right)
      also have "\<dots> = ((1::real)/2 + 1/2) *\<^sub>R z"
        by (simp add: scaleR_add_left[symmetric])
      finally show ?thesis by simp
    qed
    have "v ((1 - 1/2) *\<^sub>R (z + k) + (1/2) *\<^sub>R (z - k))
        + (norm ((1 - 1/2) *\<^sub>R (z + k) + (1/2) *\<^sub>R (z - k)))\<^sup>2 / (2*lam)
        \<le> (1 - 1/2) * (v (z + k) + (norm (z + k))\<^sup>2 / (2*lam))
          + (1/2) * (v (z - k) + (norm (z - k))\<^sup>2 / (2*lam))"
      by (rule convex_onD[OF cvx]) auto
    then have h1: "v z + (norm z)\<^sup>2 / (2*lam)
        \<le> (v (z + k) + (norm (z + k))\<^sup>2 / (2*lam)) / 2
          + (v (z - k) + (norm (z - k))\<^sup>2 / (2*lam)) / 2"
      unfolding mid by simp
    have par: "(norm (z + k))\<^sup>2 + (norm (z - k))\<^sup>2
        = 2 * (norm z)\<^sup>2 + 2 * (norm k)\<^sup>2"
      unfolding norm_sq_add_expand[of z k] norm_sq_diff_expand[of z k]
      by simp
    have h2: "(norm (z + k))\<^sup>2 / (2*lam) / 2 + (norm (z - k))\<^sup>2 / (2*lam) / 2
        - (norm z)\<^sup>2 / (2*lam) = (norm k)\<^sup>2 / (2*lam)"
      using l0 par by (simp add: field_simps)
    have h3: "(norm k)\<^sup>2 / (2*lam) \<le> (norm k)\<^sup>2 / lam"
      using l0 by (simp add: field_simps)
    show ?thesis using h1 h2 h3 by argo
  qed
  have main: "- ((norm h)\<^sup>2 / lam) \<le> h \<bullet> F h + 2 * e * (norm h)\<^sup>2"
    if e: "0 < e" for e
  proof -
    obtain d where d: "0 < d" and sj: "\<And>k. norm k < d \<Longrightarrow>
        v (x + k) \<le> v x + p \<bullet> k + (k \<bullet> F k)/2 + e * (norm k)\<^sup>2"
      using jet e unfolding superjet_def v_def by blast
    define t where "t = min (d / (2 * norm h)) 1"
    have t0: "0 < t" unfolding t_def using d False by simp
    have t1: "t \<le> 1" unfolding t_def by simp
    have tnh: "norm (t *\<^sub>R h) < d"
    proof -
      have "t * norm h \<le> (d / (2 * norm h)) * norm h"
        unfolding t_def using norm_ge_zero
        by (intro mult_right_mono min.cobounded1) auto
      also have "\<dots> = d / 2" using False by simp
      finally show ?thesis using d t0 by (simp add: abs_mult)
    qed
    have s1: "v (x + t *\<^sub>R h) \<le> v x + p \<bullet> (t *\<^sub>R h)
        + ((t *\<^sub>R h) \<bullet> F (t *\<^sub>R h))/2 + e * (norm (t *\<^sub>R h))\<^sup>2"
      by (rule sj[OF tnh])
    have s2: "v (x - t *\<^sub>R h) \<le> v x + p \<bullet> (- (t *\<^sub>R h))
        + ((- (t *\<^sub>R h)) \<bullet> F (- (t *\<^sub>R h)))/2 + e * (norm (- (t *\<^sub>R h)))\<^sup>2"
      using sj[of "- (t *\<^sub>R h)"] tnh by simp
    have negF: "(- (t *\<^sub>R h)) \<bullet> F (- (t *\<^sub>R h)) = (t *\<^sub>R h) \<bullet> F (t *\<^sub>R h)"
    proof -
      have "F (- (t *\<^sub>R h)) = - F (t *\<^sub>R h)"
        using linF by (simp add: linear_neg)
      then show ?thesis by simp
    qed
    have scF: "(t *\<^sub>R h) \<bullet> F (t *\<^sub>R h) = t\<^sup>2 * (h \<bullet> F h)"
    proof -
      have "F (t *\<^sub>R h) = t *\<^sub>R F h" by (rule linear_cmul[OF linF])
      then show ?thesis by (simp add: power2_eq_square)
    qed
    have comb: "- ((norm (t *\<^sub>R h))\<^sup>2 / lam)
        \<le> (t *\<^sub>R h) \<bullet> F (t *\<^sub>R h) + 2 * e * (norm (t *\<^sub>R h))\<^sup>2"
      using key[of x "t *\<^sub>R h"] s1 s2 unfolding negF by simp
    have nsc: "(norm (t *\<^sub>R h))\<^sup>2 = t\<^sup>2 * (norm h)\<^sup>2"
      by (simp add: power_mult_distrib abs_mult power2_eq_square)
    have t2p: "0 < t\<^sup>2" using t0 by simp
    have sc: "t\<^sup>2 * (- ((norm h)\<^sup>2 / lam))
        \<le> t\<^sup>2 * (h \<bullet> F h + 2 * e * (norm h)\<^sup>2)"
      using comb unfolding scF nsc by (simp add: algebra_simps)
    have iff: "(t\<^sup>2 * (- ((norm h)\<^sup>2 / lam))
        \<le> t\<^sup>2 * (h \<bullet> F h + 2 * e * (norm h)\<^sup>2))
        = (- ((norm h)\<^sup>2 / lam) \<le> h \<bullet> F h + 2 * e * (norm h)\<^sup>2)"
      by (rule mult_le_cancel_left_pos[OF t2p])
    show ?thesis using sc iff by blast
  qed
  show ?thesis
  proof (rule field_le_epsilon)
    fix ee :: real assume ee: "0 < ee"
    have hpos: "0 < (norm h)\<^sup>2" using False by simp
    have e: "0 < ee / (2 * (norm h)\<^sup>2)" using ee hpos by simp
    have "- ((norm h)\<^sup>2 / lam)
        \<le> h \<bullet> F h + 2 * (ee / (2 * (norm h)\<^sup>2)) * (norm h)\<^sup>2"
      by (rule main[OF e])
    also have "2 * (ee / (2 * (norm h)\<^sup>2)) * (norm h)\<^sup>2 = ee"
      using hpos by simp
    finally show "- ((norm h)\<^sup>2 / lam) \<le> h \<bullet> F h + ee" .
  qed
qed

lemma usc_form_of_continuous:
  fixes f :: "'a::metric_space \<Rightarrow> real"
  assumes cf: "continuous_on UNIV f" and lt: "f z < c"
  shows "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> f y < c"
proof -
  have "isCont f z"
    using cf continuous_on_eq_continuous_at[OF open_UNIV] by blast
  then have "(f \<longlongrightarrow> f z) (at z)" by (simp add: isCont_def)
  from tendstoD[OF this, of "c - f z"] lt
  obtain d where d: "0 < d" and h: "\<And>y. y \<noteq> z \<Longrightarrow> dist y z < d \<Longrightarrow>
      \<bar>f y - f z\<bar> < c - f z"
    unfolding eventually_at by (auto simp: dist_real_def)
  have main: "f y < c" if dy: "dist z y < d" for y
  proof (cases "y = z")
    case True then show ?thesis using lt by simp
  next
    case False
    then show ?thesis using h[OF False] dy
      by (simp add: dist_commute abs_diff_less_iff)
  qed
  show ?thesis by (intro exI[of _ d] conjI d allI impI main)
qed

section \<open>The optimizer of a sup-convolution superjet\<close>

text \<open>At a point where the sup-convolution carries a superjet \<open>(p, F)\<close>, the
  attainment point of the inner supremum is exactly \<open>x + \<lambda>p\<close>: the quadratic
  minorant through the optimizer touches from below, so its gradient must
  agree with the superjet gradient.  This is the "magic property" that makes
  the sup-convolution displacement cancel against the deconvolved penalty's
  shift of the maximiser.\<close>

lemma supconv_optimizer_location:
  fixes u :: "'a::euclidean_space \<Rightarrow> real" and x ys p :: 'a
  assumes B: "\<And>y. u y \<le> B" and l0: "0 < lam"
    and opt: "supconv u lam x = u ys - (dist x ys)\<^sup>2 / (2*lam)"
    and jet: "(p, F) \<in> superjet (supconv u lam) x"
  shows "ys = x + lam *\<^sub>R p"
proof -
  define v where "v = supconv u lam"
  have touch: "u ys - (dist (x + k) ys)\<^sup>2 / (2*lam) \<le> v (x + k)" for k
    unfolding v_def supconv_def
    by (intro cSUP_upper supconv_bdd_above[OF B l0]) auto
  have expand: "(dist (x + k) ys)\<^sup>2
      = (norm (x - ys))\<^sup>2 + 2 * ((x - ys) \<bullet> k) + (norm k)\<^sup>2" for k
  proof -
    have "x + k - ys = (x - ys) + k" by simp
    then show ?thesis
      unfolding dist_norm using norm_sq_add_expand[of "x - ys" k] by (simp add: algebra_simps)
  qed
  have vx: "v x = u ys - (norm (x - ys))\<^sup>2 / (2*lam)"
    unfolding v_def using opt by (simp add: dist_norm)
  have lower: "((1/lam) *\<^sub>R (ys - x)) \<bullet> k - (norm k)\<^sup>2 / (2*lam)
      \<le> v (x + k) - v x" for k
  proof -
    have "u ys - ((norm (x - ys))\<^sup>2 + 2 * ((x - ys) \<bullet> k) + (norm k)\<^sup>2)
        / (2*lam) \<le> v (x + k)"
      using touch[of k] unfolding expand by simp
    moreover have "((1/lam) *\<^sub>R (ys - x)) \<bullet> k
        = - (2 * ((x - ys) \<bullet> k)) / (2*lam)"
      using l0 by (simp add: inner_diff_left field_simps)
    moreover have "((norm (x - ys))\<^sup>2 + 2 * ((x - ys) \<bullet> k) + (norm k)\<^sup>2)
        / (2*lam) = (norm (x - ys))\<^sup>2 / (2*lam)
          + (2 * ((x - ys) \<bullet> k)) / (2*lam) + (norm k)\<^sup>2 / (2*lam)"
      by (simp add: add_divide_distrib)
    ultimately show ?thesis unfolding vx by linarith
  qed
  have ex1: "\<exists>d>0. \<forall>k. norm k < d \<longrightarrow>
      v (x + k) \<le> v x + p \<bullet> k + (k \<bullet> F k)/2 + 1 * (norm k)\<^sup>2"
    using jet zero_less_one unfolding superjet_def v_def by blast
  then obtain d where d: "0 < d" and sj: "\<And>k. norm k < d \<Longrightarrow>
      v (x + k) \<le> v x + p \<bullet> k + (k \<bullet> F k)/2 + 1 * (norm k)\<^sup>2"
    by blast
  define DD where "DD = (1/lam) *\<^sub>R (ys - x) - p"
  have claim: "DD \<bullet> k \<le> 0" for k
  proof (cases "k = 0")
    case True then show ?thesis by simp
  next
    case False
    have linF: "linear F" using jet unfolding superjet_def by blast
    have small: "DD \<bullet> k \<le> ee" if ee: "0 < ee" for ee
    proof -
      define Ck where
        "Ck = \<bar>(k \<bullet> F k)/2 + (norm k)\<^sup>2 / (2*lam) + (norm k)\<^sup>2\<bar>"
      have Ck0: "0 \<le> Ck" unfolding Ck_def by simp
      define t where "t = min (min (d / (2 * norm k)) (ee / (Ck + 1))) 1"
      have t0: "0 < t" unfolding t_def using d False ee Ck0 by simp
      have tee: "t \<le> ee / (Ck + 1)" unfolding t_def by simp
      have tnk: "norm (t *\<^sub>R k) < d"
      proof -
        have "t * norm k \<le> (d / (2 * norm k)) * norm k"
          using norm_ge_zero unfolding t_def
          by (intro mult_right_mono) auto
        also have "\<dots> = d / 2" using False by simp
        finally show ?thesis using d t0 by (simp add: abs_mult)
      qed
      have A1: "((1/lam) *\<^sub>R (ys - x)) \<bullet> (t *\<^sub>R k)
          - (norm (t *\<^sub>R k))\<^sup>2 / (2*lam) \<le> v (x + t *\<^sub>R k) - v x"
        by (rule lower)
      have A2: "v (x + t *\<^sub>R k) - v x \<le> p \<bullet> (t *\<^sub>R k)
          + ((t *\<^sub>R k) \<bullet> F (t *\<^sub>R k))/2 + 1 * (norm (t *\<^sub>R k))\<^sup>2"
        using sj[OF tnk] by linarith
      have ddapp: "DD \<bullet> (t *\<^sub>R k)
          = ((1/lam) *\<^sub>R (ys - x)) \<bullet> (t *\<^sub>R k) - p \<bullet> (t *\<^sub>R k)"
        unfolding DD_def by (simp add: algebra_simps)
      have step: "DD \<bullet> (t *\<^sub>R k) \<le> ((t *\<^sub>R k) \<bullet> F (t *\<^sub>R k))/2
          + (norm (t *\<^sub>R k))\<^sup>2 / (2*lam) + (norm (t *\<^sub>R k))\<^sup>2"
        using A1 A2 unfolding ddapp by linarith
      have scF: "(t *\<^sub>R k) \<bullet> F (t *\<^sub>R k) = t\<^sup>2 * (k \<bullet> F k)"
      proof -
        have "F (t *\<^sub>R k) = t *\<^sub>R F k" by (rule linear_cmul[OF linF])
        then show ?thesis by (simp add: power2_eq_square)
      qed
      have nsc: "(norm (t *\<^sub>R k))\<^sup>2 = t\<^sup>2 * (norm k)\<^sup>2"
        by (simp add: power_mult_distrib abs_mult power2_eq_square)
      have ddsc: "DD \<bullet> (t *\<^sub>R k) = t * (DD \<bullet> k)"
        by simp
      have step2: "t * (DD \<bullet> k)
          \<le> t\<^sup>2 * ((k \<bullet> F k)/2 + (norm k)\<^sup>2 / (2*lam) + (norm k)\<^sup>2)"
        using step unfolding ddsc scF nsc by (simp add: algebra_simps)
      have brCk: "(k \<bullet> F k)/2 + (norm k)\<^sup>2 / (2*lam) + (norm k)\<^sup>2 \<le> Ck"
        unfolding Ck_def by (rule abs_ge_self)
      have s3: "t * (DD \<bullet> k) \<le> t\<^sup>2 * Ck"
      proof -
        have "t\<^sup>2 * ((k \<bullet> F k)/2 + (norm k)\<^sup>2 / (2*lam) + (norm k)\<^sup>2)
            \<le> t\<^sup>2 * Ck" using brCk by (intro mult_left_mono) auto
        then show ?thesis using step2 by linarith
      qed
      have s4: "t\<^sup>2 * Ck = t * (t * Ck)"
        by (simp add: power2_eq_square mult.assoc)
      have s5: "DD \<bullet> k \<le> t * Ck"
        using s3 unfolding s4 using t0
        by (simp add: mult_le_cancel_left_pos)
      have s6: "t * Ck \<le> (ee / (Ck + 1)) * Ck"
        using tee Ck0 by (intro mult_right_mono) auto
      have s7: "(ee / (Ck + 1)) * Ck \<le> ee"
      proof -
        have "(ee / (Ck + 1)) * Ck \<le> (ee / (Ck + 1)) * (Ck + 1)"
          using ee Ck0 by (intro mult_left_mono) auto
        also have "\<dots> = ee" using Ck0 by simp
        finally show ?thesis .
      qed
      show ?thesis using s5 s6 s7 by linarith
    qed
    show ?thesis
    proof (rule field_le_epsilon)
      fix e :: real assume "0 < e"
      then show "DD \<bullet> k \<le> 0 + e" using small[of e] by simp
    qed
  qed
  have DD0: "DD = 0"
  proof -
    have "DD \<bullet> DD \<le> 0" by (rule claim)
    moreover have "DD \<bullet> DD = (norm DD)\<^sup>2"
      by (simp add: power2_norm_eq_inner)
    ultimately have "(norm DD)\<^sup>2 \<le> 0" by linarith
    then have "norm DD = 0"
      using zero_le_power2[of "norm DD"] by simp
    then show ?thesis by simp
  qed
  have "(1/lam) *\<^sub>R (ys - x) = p" using DD0 unfolding DD_def by simp
  then have "lam *\<^sub>R ((1/lam) *\<^sub>R (ys - x)) = lam *\<^sub>R p" by simp
  then have "ys - x = lam *\<^sub>R p" using l0 by simp
  then show ?thesis by (metis add.commute diff_add_cancel)
qed

text \<open>A superjet of the sup-convolution descends to a superjet of \<open>u\<close> at the
  optimizer, with the same gradient and form.\<close>

lemma superjet_supconv_transfer:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> B" and l0: "0 < lam"
    and opt: "supconv u lam x = u ys - (dist x ys)\<^sup>2 / (2*lam)"
    and jet: "(p, F) \<in> superjet (supconv u lam) x"
  shows "(p, F) \<in> superjet u ys"
proof -
  have linF: "linear F" and symF: "\<And>a b. a \<bullet> F b = b \<bullet> F a"
    using jet unfolding superjet_def by blast+
  have tr: "\<And>k. (u (ys + k) - u ys - p \<bullet> k - (k \<bullet> F k)/2) / (norm k)\<^sup>2
      \<le> (supconv u lam (x + k) - supconv u lam x
          - p \<bullet> k - (k \<bullet> F k)/2) / (norm k)\<^sup>2"
    by (rule supconv_jet_transfer[OF B l0 opt])
  have h: "\<exists>d>0. \<forall>k. norm k < d \<longrightarrow>
      u (ys + k) \<le> u ys + p \<bullet> k + (k \<bullet> F k)/2 + e * (norm k)\<^sup>2"
    if e: "0 < e" for e
  proof -
    obtain d where d: "0 < d" and sj: "\<And>k. norm k < d \<Longrightarrow>
        supconv u lam (x + k) \<le> supconv u lam x + p \<bullet> k
          + (k \<bullet> F k)/2 + e * (norm k)\<^sup>2"
      using jet e unfolding superjet_def by blast
    have main: "u (ys + k) \<le> u ys + p \<bullet> k + (k \<bullet> F k)/2 + e * (norm k)\<^sup>2"
      if kd: "norm k < d" for k
    proof (cases "k = 0")
      case True then show ?thesis by simp
    next
      case False
      have nk: "0 < (norm k)\<^sup>2" using False by simp
      have "(supconv u lam (x + k) - supconv u lam x
          - p \<bullet> k - (k \<bullet> F k)/2) / (norm k)\<^sup>2 \<le> e"
        using sj[OF kd] nk by (simp add: pos_divide_le_eq)
      then have "(u (ys + k) - u ys - p \<bullet> k - (k \<bullet> F k)/2) / (norm k)\<^sup>2 \<le> e"
        using tr[of k] by linarith
      then have "u (ys + k) - u ys - p \<bullet> k - (k \<bullet> F k)/2 \<le> e * (norm k)\<^sup>2"
        using nk by (simp add: pos_divide_le_eq)
      then show ?thesis by linarith
    qed
    show ?thesis using d main by blast
  qed
  show ?thesis unfolding superjet_def using linF symF h by auto
qed

section \<open>Compactness for uniformly bounded symmetric forms\<close>

lemma bounded_symmetric_forms_subseq:
  fixes Fs :: "nat \<Rightarrow> real^'n::finite \<Rightarrow> real^'n" and c :: real
  assumes lin: "\<And>n. linear (Fs n)"
    and sym: "\<And>n a b. a \<bullet> Fs n b = b \<bullet> Fs n a"
    and bnd: "\<And>n v. \<bar>v \<bullet> Fs n v\<bar> \<le> c * (norm v)\<^sup>2"
  shows "\<exists>r F. strict_mono r \<and> linear F \<and> (\<forall>a b. a \<bullet> F b = b \<bullet> F a) \<and>
      (\<forall>v. (\<lambda>i. Fs (r i) v) \<longlonglongrightarrow> F v)"
proof -
  define As where "As = (\<lambda>n. matrix (Fs n))"
  define CB where "CB = real (card (Basis :: (real^'n^'n) set)) * c"
  have nb: "norm (As n) \<le> CB" for n
    unfolding As_def CB_def
    by (rule norm_matrix_le_of_form_bound[OF lin sym bnd])
  have bd: "bounded (range As)"
    unfolding bounded_iff using nb by blast
  obtain A r where r: "strict_mono r" and Ar: "(As \<circ> r) \<longlonglongrightarrow> A"
    using bounded_imp_convergent_subsequence[OF bd] by blast
  define F where "F = (\<lambda>v. A *v v)"
  have linF: "linear F" unfolding F_def by (rule matrix_vector_mul_linear)
  have pw: "(\<lambda>i. Fs (r i) v) \<longlonglongrightarrow> F v" for v
  proof -
    have ent: "(\<lambda>i. As (r i) $ j $ k) \<longlonglongrightarrow> A $ j $ k" for j k
      using tendsto_vec_nth[OF tendsto_vec_nth[OF Ar]]
      by (simp add: o_def)
    have comp: "(\<lambda>i. (As (r i) *v v) $ j) \<longlonglongrightarrow> (A *v v) $ j" for j
      unfolding matrix_vector_mult_def
      by (auto intro!: tendsto_sum tendsto_mult ent)
    have "(\<lambda>i. As (r i) *v v) \<longlonglongrightarrow> A *v v"
      by (rule vec_tendstoI) (rule comp)
    moreover have "As n *v v = Fs n v" for n
      unfolding As_def by (rule matrix_vec_apply[OF lin])
    ultimately show ?thesis unfolding F_def by simp
  qed
  have symF: "a \<bullet> F b = b \<bullet> F a" for a b
  proof -
    have t1: "(\<lambda>i. a \<bullet> Fs (r i) b) \<longlonglongrightarrow> a \<bullet> F b"
      by (intro tendsto_inner tendsto_const pw)
    have t2: "(\<lambda>i. b \<bullet> Fs (r i) a) \<longlonglongrightarrow> b \<bullet> F a"
      by (intro tendsto_inner tendsto_const pw)
    have "(\<lambda>i. a \<bullet> Fs (r i) b) = (\<lambda>i. b \<bullet> Fs (r i) a)"
      by (rule ext) (rule sym)
    then show ?thesis using t1 t2 LIMSEQ_unique by metis
  qed
  show ?thesis using r linF symF pw by blast
qed

text \<open>The route to the closed jets fixes the sup-convolution scale \<open>\<lambda>\<close> once
  and for all and DECONVOLVES the penalty instead: for \<open>2\<lambda>\<alpha> < 1\<close> the
  Moreau identity above shows that
  \<open>u\<^sup>\<lambda> \<oplus> b\<^sup>\<lambda> - (\<alpha>\<^sub>\<lambda>/2)\<parallel>x - y\<parallel>\<^sup>2\<close> with the inflated coefficient
  \<open>\<alpha>\<^sub>\<lambda> = \<alpha>/(1 - 2\<lambda>\<alpha>)\<close> attains the SAME maximum \<open>M\<close>, at the explicitly
  shifted point \<open>(xh - \<lambda>g, yh + \<lambda>g)\<close>, \<open>g = \<alpha>(xh - yh)\<close>.  Running the
  staged theorem on the sup-convolutions at this exact maximum produces
  jets whose forms are bounded on BOTH sides uniformly --- below by
  \<open>-(1/\<lambda>)I\<close> from semiconvexity of the sup-convolutions, above through the
  ordering --- so they have convergent subsequences; and the optimizer
  identity \<open>y\<^sup>* = x + \<lambda>p\<close> makes the sup-convolution displacement cancel
  the shift of the maximiser exactly, so the limit jets sit at
  \<open>(xh, yh)\<close> itself.  This is the classical Crandall--Ishii mechanism,
  specialised to the quadratic coupling.\<close>

section \<open>The Crandall--Ishii theorem on sums, closed-jet form\<close>

theorem theorem_on_sums_quadratic_closed:
  fixes u w :: "real^'n::finite \<Rightarrow> real" and \<alpha> lam :: real
    and xh yh :: "real^'n"
  assumes usc: "\<And>c z. u z < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> u y < c"
    and lsc: "\<And>c z. c < w z \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> c < w y"
    and Bu: "\<And>y. u y \<le> Bu" and Bw: "\<And>y. Bw' \<le> w y"
    and a0: "0 < \<alpha>"
    and mx: "\<And>x y. u x - w y - (\<alpha>/2) * (norm (x - y))\<^sup>2
        \<le> u xh - w yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
    and l0: "0 < lam" and la1: "2 * lam * \<alpha> < 1"
  shows "\<exists>X Y. (\<alpha> *\<^sub>R (xh - yh), X) \<in> superjet_cl u xh \<and>
     (\<alpha> *\<^sub>R (xh - yh), Y) \<in> subjet_cl w yh \<and>
     (\<forall>v. - ((norm v)\<^sup>2 / lam) \<le> v \<bullet> X v \<and> v \<bullet> X v \<le> v \<bullet> Y v \<and>
        v \<bullet> Y v \<le> (norm v)\<^sup>2 / lam)"
proof -
  define b where "b = (\<lambda>y. - w y)"
  have Bb: "\<And>y. b y \<le> - Bw'" unfolding b_def using Bw by simp
  have uscb: "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> b y < c" if lt: "b z < c" for c z
  proof -
    have "- c < w z" using lt unfolding b_def by simp
    from lsc[OF this] obtain e where e: "0 < e"
      and h: "\<forall>y. dist z y < e \<longrightarrow> - c < w y" by blast
    show ?thesis
    proof (intro exI[of _ e] conjI e allI impI)
      fix y assume "dist z y < e"
      then have "- c < w y" using h by blast
      then show "b y < c" unfolding b_def by linarith
    qed
  qed
  define M where "M = u xh + b yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
  have mxb: "\<And>x y. u x + b y - (\<alpha>/2) * (norm (x - y))\<^sup>2 \<le> M"
    unfolding M_def b_def using mx by simp
  define al where "al = \<alpha> / (1 - 2 * lam * \<alpha>)"
  have ne: "1 - 2 * lam * \<alpha> \<noteq> 0" using la1 by linarith
  have al0: "0 < al" unfolding al_def using a0 la1
    by (simp add: field_simps)
  have alid: "al * (1 - 2 * lam * \<alpha>) = \<alpha>" unfolding al_def using ne by simp
  define g where "g = \<alpha> *\<^sub>R (xh - yh)"
  define x0 where "x0 = xh - lam *\<^sub>R g"
  define y0 where "y0 = yh + lam *\<^sub>R g"
  define uL where "uL = supconv u lam"
  define bL where "bL = supconv b lam"
  have BuL: "\<And>x. uL x \<le> Bu" unfolding uL_def
    by (rule supconv_le[OF Bu l0])
  have BbL: "\<And>x. bL x \<le> - Bw'" unfolding bL_def
    by (rule supconv_le[OF Bb l0])
  have contuL: "continuous_on UNIV uL" unfolding uL_def
    by (rule supconv_continuous[OF Bu l0])
  have contbL: "continuous_on UNIV bL" unfolding bL_def
    by (rule supconv_continuous[OF Bb l0])
  have uscuL: "\<And>c z. uL z < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> uL y < c"
    by (rule usc_form_of_continuous[OF contuL])
  have uscbL: "\<And>c z. bL z < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> bL y < c"
    by (rule usc_form_of_continuous[OF contbL])
  have mxL: "\<And>x y. uL x + bL y - (al/2) * (norm (x - y))\<^sup>2 \<le> M"
    unfolding uL_def bL_def
    by (rule deconv_doubled_le[OF Bu Bb l0 a0 la1 al_def mxb])
  have att: "uL x0 + bL y0 - (al/2) * (norm (x0 - y0))\<^sup>2 = M"
    unfolding uL_def bL_def x0_def y0_def
    by (rule deconv_doubled_attains[OF Bu Bb l0 a0 la1 al_def mxb
        M_def g_def])
  have MvalL: "M = uL x0 + bL y0 - (al/2) * (norm (x0 - y0))\<^sup>2"
    using att by (rule sym)
  define A where "A = norm (x0 - y0) + 2"
  have Aval: "A = norm (x0 - y0) + 2" unfolding A_def by (rule refl)
  have Ann: "0 \<le> A" unfolding A_def
    using norm_ge_zero[of "x0 - y0"] by linarith
  define C where "C = 2 * al\<^sup>2 * A\<^sup>2"
  have C0: "0 \<le> C" unfolding C_def
    by (intro mult_nonneg_nonneg) auto
  define dl where "dl = (\<lambda>n :: nat. 1 / (real n + 2))"
  define q3 where "q3 = (\<lambda>n. dl n * (dl n)\<^sup>2)"
  define ee where "ee = (\<lambda>n. min (1 / (4 * al + 4)) (q3 n / (2 * C + 2)))"
  define ddn where "ddn = (\<lambda>n. q3 n / 8)"
  have dl0: "0 < dl n" for n unfolding dl_def by simp
  have dl1: "dl n < 1" for n unfolding dl_def by simp
  have dlhalf: "dl n \<le> 1/2" for n unfolding dl_def
    by (simp add: field_simps)
  have q30: "0 < q3 n" for n unfolding q3_def
    using dl0[of n] by (intro mult_pos_pos) auto
  have ee0: "0 < ee n" for n
  proof -
    have "0 < 1 / (4 * al + 4)" using al0 by simp
    moreover have "0 < q3 n / (2 * C + 2)"
      using q30[of n] C0 by (intro divide_pos_pos) auto
    ultimately show ?thesis unfolding ee_def by simp
  qed
  have ee4: "4 * al * ee n \<le> 1" for n
  proof -
    have h1: "ee n \<le> 1 / (4 * al + 4)"
      unfolding ee_def by (rule min.cobounded1)
    have "4 * al * ee n \<le> 4 * al * (1 / (4 * al + 4))"
      using h1 al0 by (intro mult_left_mono) auto
    also have "\<dots> \<le> 1" using al0 by (simp add: field_simps)
    finally show ?thesis .
  qed
  have dd0n: "0 < ddn n" for n
    unfolding ddn_def using q30[of n] by simp
  have gapn: "2 * al\<^sup>2 * A\<^sup>2 * ee n \<le> dl n * (dl n)\<^sup>2 / 2" for n
  proof -
    have le1: "ee n \<le> q3 n / (2 * C + 2)"
      unfolding ee_def by (rule min.cobounded2)
    have le2: "C * ee n \<le> C * (q3 n / (2 * C + 2))"
      by (rule mult_left_mono[OF le1 C0])
    have le3: "C * (q3 n / (2 * C + 2)) \<le> q3 n / 2"
    proof -
      have e1: "C * (q3 n / (2 * C + 2)) = (C / (2 * C + 2)) * q3 n"
        by simp
      have e2: "C / (2 * C + 2) \<le> 1 / 2"
        using C0 by (simp add: field_simps)
      have "(C / (2 * C + 2)) * q3 n \<le> (1 / 2) * q3 n"
        using e2 q30[of n] by (intro mult_right_mono) auto
      then show ?thesis unfolding e1 by simp
    qed
    have "C * ee n \<le> q3 n / 2" using le2 le3 by linarith
    then show ?thesis unfolding C_def q3_def by linarith
  qed
  have ddsmalln: "2 * ddn n < dl n * (dl n)\<^sup>2 / 2" for n
  proof -
    have "2 * ddn n = q3 n / 4" unfolding ddn_def by simp
    also have "q3 n / 4 < q3 n / 2" using q30[of n] by argo
    finally show ?thesis unfolding q3_def by simp
  qed
  define SP where "SP = (\<lambda>n (xy :: (real^'n) \<times> (real^'n))
      (pq :: (real^'n) \<times> (real^'n)) (XU :: real^'n \<Rightarrow> real^'n)
      (YU :: real^'n \<Rightarrow> real^'n).
    (fst pq, XU) \<in> superjet uL (fst xy) \<and>
    (snd pq, YU) \<in> superjet bL (snd xy) \<and>
    (\<forall>v. v \<bullet> XU v + v \<bullet> YU v \<le> 4 * dl n * (norm v)\<^sup>2) \<and>
    dist (fst xy) x0 \<le> dl n + 8 * ee n * al * A + sqrt (8 * ee n * ddn n) \<and>
    dist (snd xy) y0 \<le> dl n + 8 * ee n * al * A + sqrt (8 * ee n * ddn n) \<and>
    norm (fst pq - al *\<^sub>R (x0 - y0))
      \<le> ddn n + 2 * al * dl n + 2 * dl n * dl n \<and>
    norm (snd pq + al *\<^sub>R (x0 - y0))
      \<le> ddn n + 2 * al * dl n + 2 * dl n * dl n \<and>
    M - ddn n - 2 * al * A * dl n + (al/2) * (norm (x0 - y0))\<^sup>2
      \<le> uL (fst xy) + bL (snd xy))"
  have EX: "\<exists>xy pq XU YU. SP n xy pq XU YU" for n
    unfolding SP_def
    by (rule theorem_on_sums_stage[OF BuL BbL uscuL uscbL al0 mxL MvalL Aval
        ee0 ee4 dl0 dl0 dl1 gapn dd0n ddsmalln])
  obtain FF GG HH II where ALL: "\<forall>n. SP n (FF n) (GG n) (HH n) (II n)"
    using choice4[of SP, OF EX] by blast
  define xs where "xs = (\<lambda>n. fst (FF n))"
  define ys where "ys = (\<lambda>n. snd (FF n))"
  define ps where "ps = (\<lambda>n. fst (GG n))"
  define qs where "qs = (\<lambda>n. snd (GG n))"
  have sp: "SP n (FF n) (GG n) (HH n) (II n)" for n using ALL by blast
  have jetuL: "(ps n, HH n) \<in> superjet (supconv u lam) (xs n)" for n
    using sp[of n] unfolding SP_def xs_def ps_def uL_def by blast
  have jetbL: "(qs n, II n) \<in> superjet (supconv b lam) (ys n)" for n
    using sp[of n] unfolding SP_def ys_def qs_def bL_def by blast
  have ordn: "v \<bullet> HH n v + v \<bullet> II n v \<le> 4 * dl n * (norm v)\<^sup>2" for n v
    using sp[of n] unfolding SP_def by blast
  have o4n: "dist (xs n) x0
      \<le> dl n + 8 * ee n * al * A + sqrt (8 * ee n * ddn n)" for n
    using sp[of n] unfolding SP_def xs_def by blast
  have o5n: "dist (ys n) y0
      \<le> dl n + 8 * ee n * al * A + sqrt (8 * ee n * ddn n)" for n
    using sp[of n] unfolding SP_def ys_def by blast
  have o6n: "norm (ps n - al *\<^sub>R (x0 - y0))
      \<le> ddn n + 2 * al * dl n + 2 * dl n * dl n" for n
    using sp[of n] unfolding SP_def ps_def by blast
  have o7n: "norm (qs n + al *\<^sub>R (x0 - y0))
      \<le> ddn n + 2 * al * dl n + 2 * dl n * dl n" for n
    using sp[of n] unfolding SP_def qs_def by blast
  have dlt: "dl \<longlonglongrightarrow> 0"
  proof (rule tendsto_sandwich[of "\<lambda>_. 0" _ _
      "\<lambda>n. inverse (real (Suc n))"])
    show "\<forall>\<^sub>F n in sequentially. 0 \<le> dl n"
      using dl0 by (intro always_eventually allI) (simp add: less_imp_le)
    show "\<forall>\<^sub>F n in sequentially. dl n \<le> inverse (real (Suc n))"
      unfolding dl_def
      by (intro always_eventually allI) (simp add: field_simps)
    show "(\<lambda>_ :: nat. (0::real)) \<longlonglongrightarrow> 0" by (rule tendsto_const)
    show "(\<lambda>n. inverse (real (Suc n))) \<longlonglongrightarrow> 0"
      by (rule LIMSEQ_inverse_real_of_nat)
  qed
  have q3t: "q3 \<longlonglongrightarrow> 0"
  proof -
    have "(\<lambda>n. dl n * (dl n)\<^sup>2) \<longlonglongrightarrow> 0 * (0::real)\<^sup>2"
      by (intro tendsto_mult tendsto_power dlt)
    then show ?thesis unfolding q3_def by simp
  qed
  have eet: "ee \<longlonglongrightarrow> 0"
  proof (rule tendsto_sandwich[of "\<lambda>_. 0" _ _ "\<lambda>n. q3 n / (2 * C + 2)"])
    show "\<forall>\<^sub>F n in sequentially. 0 \<le> ee n"
      using ee0 by (intro always_eventually allI) (simp add: less_imp_le)
    show "\<forall>\<^sub>F n in sequentially. ee n \<le> q3 n / (2 * C + 2)"
      unfolding ee_def by (intro always_eventually allI min.cobounded2)
    have "(\<lambda>n. q3 n / (2 * C + 2)) \<longlonglongrightarrow> 0 / (2 * C + 2)"
      using C0 by (intro tendsto_divide q3t tendsto_const) auto
    then show "(\<lambda>n. q3 n / (2 * C + 2)) \<longlonglongrightarrow> 0" by simp
  qed simp
  have ddt: "ddn \<longlonglongrightarrow> 0"
  proof -
    have "(\<lambda>n. q3 n / 8) \<longlonglongrightarrow> 0 / 8"
      by (intro tendsto_divide q3t tendsto_const) auto
    then show ?thesis unfolding ddn_def by simp
  qed
  have bndt: "(\<lambda>n. dl n + 8 * ee n * al * A + sqrt (8 * ee n * ddn n))
      \<longlonglongrightarrow> 0"
  proof -
    have t2: "(\<lambda>n. 8 * ee n * ddn n) \<longlonglongrightarrow> 8 * 0 * 0"
      by (intro tendsto_mult tendsto_const eet ddt)
    have t3: "(\<lambda>n. sqrt (8 * ee n * ddn n)) \<longlonglongrightarrow> sqrt (8 * 0 * 0)"
      by (rule tendsto_real_sqrt[OF t2])
    have "(\<lambda>n. dl n + 8 * ee n * al * A + sqrt (8 * ee n * ddn n))
        \<longlonglongrightarrow> 0 + 8 * 0 * al * A + sqrt (8 * 0 * 0)"
      by (intro tendsto_add tendsto_mult tendsto_const dlt eet t3)
    then show ?thesis by simp
  qed
  have xst: "xs \<longlonglongrightarrow> x0"
    by (rule tendsto_of_dist_bound[OF o4n bndt])
  have yst: "ys \<longlonglongrightarrow> y0"
    by (rule tendsto_of_dist_bound[OF o5n bndt])
  have gbt: "(\<lambda>n. ddn n + 2 * al * dl n + 2 * dl n * dl n) \<longlonglongrightarrow> 0"
  proof -
    have "(\<lambda>n. ddn n + 2 * al * dl n + 2 * dl n * dl n)
        \<longlonglongrightarrow> 0 + 2 * al * 0 + 2 * 0 * 0"
      by (intro tendsto_add tendsto_mult tendsto_const ddt dlt)
    then show ?thesis by simp
  qed
  have galx: "al *\<^sub>R (x0 - y0) = g"
  proof -
    have e1: "lam *\<^sub>R g = (lam * \<alpha>) *\<^sub>R (xh - yh)"
      unfolding g_def by simp
    have e2: "(1 - 2 * lam * \<alpha>) *\<^sub>R (xh - yh)
        = (xh - yh) - (2 * lam * \<alpha>) *\<^sub>R (xh - yh)"
      by (simp add: scaleR_diff_left)
    have e3: "(lam * \<alpha>) *\<^sub>R (xh - yh) + (lam * \<alpha>) *\<^sub>R (xh - yh)
        = (2 * lam * \<alpha>) *\<^sub>R (xh - yh)"
      by (simp add: scaleR_add_left[symmetric])
    have pend: "x0 - y0 = (1 - 2 * lam * \<alpha>) *\<^sub>R (xh - yh)"
      unfolding x0_def y0_def e1 e2 e3[symmetric]
      by (simp add: algebra_simps)
    have "al *\<^sub>R (x0 - y0) = (al * (1 - 2 * lam * \<alpha>)) *\<^sub>R (xh - yh)"
      unfolding pend by simp
    then show ?thesis unfolding alid g_def by simp
  qed
  have pst: "ps \<longlonglongrightarrow> g"
  proof (rule tendsto_of_dist_bound[OF _ gbt])
    fix n
    show "dist (ps n) g \<le> ddn n + 2 * al * dl n + 2 * dl n * dl n"
      using o6n[of n] unfolding galx[symmetric] by (simp add: dist_norm)
  qed
  have qst: "qs \<longlonglongrightarrow> - g"
  proof (rule tendsto_of_dist_bound[OF _ gbt])
    fix n
    have "qs n - (- g) = qs n + al *\<^sub>R (x0 - y0)"
      unfolding galx by simp
    then show "dist (qs n) (- g) \<le> ddn n + 2 * al * dl n + 2 * dl n * dl n"
      using o7n[of n] by (simp add: dist_norm)
  qed
  have lowH: "- ((norm v)\<^sup>2 / lam) \<le> v \<bullet> HH n v" for n v
    by (rule superjet_supconv_form_lower[OF Bu l0 jetuL])
  have lowII: "- ((norm v)\<^sup>2 / lam) \<le> v \<bullet> II n v" for n v
    by (rule superjet_supconv_form_lower[OF Bb l0 jetbL])
  have cbH: "\<bar>v \<bullet> HH n v\<bar> \<le> (1/lam + 2) * (norm v)\<^sup>2" for n v
  proof -
    have d1: "(norm v)\<^sup>2 / lam = (1/lam) * (norm v)\<^sup>2" by simp
    have up: "v \<bullet> HH n v \<le> 4 * dl n * (norm v)\<^sup>2 + (1/lam) * (norm v)\<^sup>2"
      using ordn[of v n] lowII[of v n] unfolding d1 by linarith
    have "4 * dl n * (norm v)\<^sup>2 \<le> 2 * (norm v)\<^sup>2"
      using dlhalf[of n] by (intro mult_right_mono) auto
    then have up2: "v \<bullet> HH n v \<le> (1/lam + 2) * (norm v)\<^sup>2"
      using up by (simp add: algebra_simps)
    have lo: "- ((1/lam + 2) * (norm v)\<^sup>2) \<le> v \<bullet> HH n v"
    proof -
      have "- ((1/lam + 2) * (norm v)\<^sup>2) \<le> - ((1/lam) * (norm v)\<^sup>2)"
        by (simp add: algebra_simps)
      then show ?thesis using lowH[of v n] unfolding d1 by linarith
    qed
    show ?thesis using up2 lo by linarith
  qed
  have cbII: "\<bar>v \<bullet> II n v\<bar> \<le> (1/lam + 2) * (norm v)\<^sup>2" for n v
  proof -
    have d1: "(norm v)\<^sup>2 / lam = (1/lam) * (norm v)\<^sup>2" by simp
    have up: "v \<bullet> II n v \<le> 4 * dl n * (norm v)\<^sup>2 + (1/lam) * (norm v)\<^sup>2"
      using ordn[of v n] lowH[of v n] unfolding d1 by linarith
    have "4 * dl n * (norm v)\<^sup>2 \<le> 2 * (norm v)\<^sup>2"
      using dlhalf[of n] by (intro mult_right_mono) auto
    then have up2: "v \<bullet> II n v \<le> (1/lam + 2) * (norm v)\<^sup>2"
      using up by (simp add: algebra_simps)
    have lo: "- ((1/lam + 2) * (norm v)\<^sup>2) \<le> v \<bullet> II n v"
    proof -
      have "- ((1/lam + 2) * (norm v)\<^sup>2) \<le> - ((1/lam) * (norm v)\<^sup>2)"
        by (simp add: algebra_simps)
      then show ?thesis using lowII[of v n] unfolding d1 by linarith
    qed
    show ?thesis using up2 lo by linarith
  qed
  have linHH: "linear (HH n)" for n
    using jetuL[of n] unfolding superjet_def by blast
  have symHH: "\<And>a c. a \<bullet> HH n c = c \<bullet> HH n a" for n
    using jetuL[of n] unfolding superjet_def by blast
  have linII: "linear (II n)" for n
    using jetbL[of n] unfolding superjet_def by blast
  have symII: "\<And>a c. a \<bullet> II n c = c \<bullet> II n a" for n
    using jetbL[of n] unfolding superjet_def by blast
  obtain r1 Xoo where r1: "strict_mono r1" and linX: "linear Xoo"
    and symX: "\<forall>a c. a \<bullet> Xoo c = c \<bullet> Xoo a"
    and pwX: "\<forall>v. (\<lambda>i. HH (r1 i) v) \<longlonglongrightarrow> Xoo v"
    using bounded_symmetric_forms_subseq[of HH "1/lam + 2",
        OF linHH symHH cbH] by blast
  obtain r2 Yoo' where r2: "strict_mono r2" and linY': "linear Yoo'"
    and symY': "\<forall>a c. a \<bullet> Yoo' c = c \<bullet> Yoo' a"
    and pwY': "\<forall>v. (\<lambda>i. II (r1 (r2 i)) v) \<longlonglongrightarrow> Yoo' v"
    using bounded_symmetric_forms_subseq[of "\<lambda>i. II (r1 i)" "1/lam + 2",
        OF linII symII cbII] by blast
  define R where "R = r1 \<circ> r2"
  have Rmono: "strict_mono R" unfolding R_def
    by (rule strict_mono_o[OF r1 r2])
  have pwXR: "(\<lambda>i. HH (R i) v) \<longlonglongrightarrow> Xoo v" for v
  proof -
    have "((\<lambda>i. HH (r1 i) v) \<circ> r2) \<longlonglongrightarrow> Xoo v"
      using pwX by (intro LIMSEQ_subseq_LIMSEQ r2) blast
    then show ?thesis unfolding R_def o_def .
  qed
  have pwYR: "(\<lambda>i. II (R i) v) \<longlonglongrightarrow> Yoo' v" for v
    using pwY' unfolding R_def o_def by blast
  have optu: "\<forall>n. \<exists>yy. supconv u lam (xs n)
      = u yy - (dist (xs n) yy)\<^sup>2 / (2*lam)"
    using supconv_attained_usc[OF Bu l0 usc] by blast
  obtain xstar where xstarA: "\<forall>n. supconv u lam (xs n)
      = u (xstar n) - (dist (xs n) (xstar n))\<^sup>2 / (2*lam)"
    using choice[OF optu] by blast
  have xstar: "\<And>n. supconv u lam (xs n)
      = u (xstar n) - (dist (xs n) (xstar n))\<^sup>2 / (2*lam)"
    using xstarA by blast
  have optb: "\<forall>n. \<exists>yy. supconv b lam (ys n)
      = b yy - (dist (ys n) yy)\<^sup>2 / (2*lam)"
    using supconv_attained_usc[OF Bb l0 uscb] by blast
  obtain ystar where ystarA: "\<forall>n. supconv b lam (ys n)
      = b (ystar n) - (dist (ys n) (ystar n))\<^sup>2 / (2*lam)"
    using choice[OF optb] by blast
  have ystar: "\<And>n. supconv b lam (ys n)
      = b (ystar n) - (dist (ys n) (ystar n))\<^sup>2 / (2*lam)"
    using ystarA by blast
  have jetun: "(ps n, HH n) \<in> superjet u (xstar n)" for n
    by (rule superjet_supconv_transfer[OF Bu l0 xstar jetuL])
  have jetbn: "(qs n, II n) \<in> superjet b (ystar n)" for n
    by (rule superjet_supconv_transfer[OF Bb l0 ystar jetbL])
  have locu: "xstar n = xs n + lam *\<^sub>R ps n" for n
    by (rule supconv_optimizer_location[OF Bu l0 xstar jetuL])
  have locb: "ystar n = ys n + lam *\<^sub>R qs n" for n
    by (rule supconv_optimizer_location[OF Bb l0 ystar jetbL])
  have xstart: "xstar \<longlonglongrightarrow> xh"
  proof -
    have f: "xstar = (\<lambda>n. xs n + lam *\<^sub>R ps n)"
      by (rule ext) (rule locu)
    have "(\<lambda>n. xs n + lam *\<^sub>R ps n) \<longlonglongrightarrow> x0 + lam *\<^sub>R g"
      by (intro tendsto_add tendsto_scaleR tendsto_const xst pst)
    moreover have "x0 + lam *\<^sub>R g = xh" unfolding x0_def by simp
    ultimately show ?thesis unfolding f by simp
  qed
  have ystart: "ystar \<longlonglongrightarrow> yh"
  proof -
    have f: "ystar = (\<lambda>n. ys n + lam *\<^sub>R qs n)"
      by (rule ext) (rule locb)
    have "(\<lambda>n. ys n + lam *\<^sub>R qs n) \<longlonglongrightarrow> y0 + lam *\<^sub>R (- g)"
      by (intro tendsto_add tendsto_scaleR tendsto_const yst qst)
    moreover have "y0 + lam *\<^sub>R (- g) = yh" unfolding y0_def by simp
    ultimately show ?thesis unfolding f by simp
  qed
  define Lu where "Lu = uL x0 + lam * (norm g)\<^sup>2 / 2"
  define Lb where "Lb = bL y0 + lam * (norm g)\<^sup>2 / 2"
  have uxstart: "(\<lambda>n. u (xstar n)) \<longlonglongrightarrow> Lu"
  proof -
    have f: "(\<lambda>n. u (xstar n))
        = (\<lambda>n. uL (xs n) + lam * (norm (ps n))\<^sup>2 / 2)"
    proof (rule ext)
      fix n
      have d: "dist (xs n) (xstar n) = lam * norm (ps n)"
        unfolding locu using l0 by (simp add: dist_norm abs_mult)
      have "u (xstar n) = supconv u lam (xs n)
          + (dist (xs n) (xstar n))\<^sup>2 / (2*lam)"
        using xstar[of n] by linarith
      also have "(dist (xs n) (xstar n))\<^sup>2 / (2*lam)
          = lam * (norm (ps n))\<^sup>2 / 2"
        unfolding d using l0
        by (simp add: power_mult_distrib power2_eq_square)
      finally show "u (xstar n)
          = uL (xs n) + lam * (norm (ps n))\<^sup>2 / 2"
        unfolding uL_def by simp
    qed
    have c1: "(\<lambda>n. uL (xs n)) \<longlonglongrightarrow> uL x0"
    proof -
      have "isCont uL x0"
        using contuL continuous_on_eq_continuous_at[OF open_UNIV] by blast
      then show ?thesis by (rule isCont_tendsto_compose[OF _ xst])
    qed
    have c2: "(\<lambda>n. lam * (norm (ps n))\<^sup>2 / 2)
        \<longlonglongrightarrow> lam * (norm g)\<^sup>2 / 2"
      by (intro tendsto_divide tendsto_mult tendsto_const tendsto_power
          tendsto_norm pst) simp
    show ?thesis unfolding f Lu_def
      by (intro tendsto_add c1 c2)
  qed
  have bystart: "(\<lambda>n. b (ystar n)) \<longlonglongrightarrow> Lb"
  proof -
    have f: "(\<lambda>n. b (ystar n))
        = (\<lambda>n. bL (ys n) + lam * (norm (qs n))\<^sup>2 / 2)"
    proof (rule ext)
      fix n
      have d: "dist (ys n) (ystar n) = lam * norm (qs n)"
        unfolding locb using l0 by (simp add: dist_norm abs_mult)
      have "b (ystar n) = supconv b lam (ys n)
          + (dist (ys n) (ystar n))\<^sup>2 / (2*lam)"
        using ystar[of n] by linarith
      also have "(dist (ys n) (ystar n))\<^sup>2 / (2*lam)
          = lam * (norm (qs n))\<^sup>2 / 2"
        unfolding d using l0
        by (simp add: power_mult_distrib power2_eq_square)
      finally show "b (ystar n)
          = bL (ys n) + lam * (norm (qs n))\<^sup>2 / 2"
        unfolding bL_def by simp
    qed
    have c1: "(\<lambda>n. bL (ys n)) \<longlonglongrightarrow> bL y0"
    proof -
      have "isCont bL y0"
        using contbL continuous_on_eq_continuous_at[OF open_UNIV] by blast
      then show ?thesis by (rule isCont_tendsto_compose[OF _ yst])
    qed
    have c2: "(\<lambda>n. lam * (norm (qs n))\<^sup>2 / 2)
        \<longlonglongrightarrow> lam * (norm (- g))\<^sup>2 / 2"
      by (intro tendsto_divide tendsto_mult tendsto_const tendsto_power
          tendsto_norm qst) simp
    show ?thesis unfolding f Lb_def using c1 c2
      by (intro tendsto_add) simp_all
  qed
  have sumL: "Lu + Lb = u xh + b yh"
  proof -
    have pend: "x0 - y0 = (1 - 2 * lam * \<alpha>) *\<^sub>R (xh - yh)"
    proof -
      have e1: "lam *\<^sub>R g = (lam * \<alpha>) *\<^sub>R (xh - yh)"
        unfolding g_def by simp
      have e2: "(1 - 2 * lam * \<alpha>) *\<^sub>R (xh - yh)
          = (xh - yh) - (2 * lam * \<alpha>) *\<^sub>R (xh - yh)"
        by (simp add: scaleR_diff_left)
      have e3: "(lam * \<alpha>) *\<^sub>R (xh - yh) + (lam * \<alpha>) *\<^sub>R (xh - yh)
          = (2 * lam * \<alpha>) *\<^sub>R (xh - yh)"
        by (simp add: scaleR_add_left[symmetric])
      show ?thesis unfolding x0_def y0_def e1 e2 e3[symmetric]
        by (simp add: algebra_simps)
    qed
    have penn: "(norm (x0 - y0))\<^sup>2
        = (1 - 2 * lam * \<alpha>)\<^sup>2 * (norm (xh - yh))\<^sup>2"
      unfolding pend
      by (simp add: power_mult_distrib power2_eq_square abs_mult)
    have gsq: "(norm g)\<^sup>2 = \<alpha>\<^sup>2 * (norm (xh - yh))\<^sup>2"
      unfolding g_def using a0
      by (simp add: power_mult_distrib power2_eq_square abs_mult)
    have penc: "(al/2) * ((1 - 2 * lam * \<alpha>)\<^sup>2 * (norm (xh - yh))\<^sup>2)
        = (\<alpha>/2) * (norm (xh - yh))\<^sup>2 - lam * \<alpha>\<^sup>2 * (norm (xh - yh))\<^sup>2"
    proof -
      have "(al/2) * ((1 - 2 * lam * \<alpha>)\<^sup>2 * (norm (xh - yh))\<^sup>2)
          = (al * (1 - 2 * lam * \<alpha>)) * ((1 - 2 * lam * \<alpha>)
              * (norm (xh - yh))\<^sup>2) / 2"
        by (simp add: power2_eq_square algebra_simps)
      also have "\<dots> = \<alpha> * ((1 - 2 * lam * \<alpha>) * (norm (xh - yh))\<^sup>2) / 2"
        unfolding alid by (rule refl)
      finally show ?thesis by (simp add: field_simps power2_eq_square)
    qed
    have "Lu + Lb = (uL x0 + bL y0) + lam * (norm g)\<^sup>2"
      unfolding Lu_def Lb_def by simp
    also have "uL x0 + bL y0 = M + (al/2) * (norm (x0 - y0))\<^sup>2"
      using MvalL by linarith
    finally have "Lu + Lb = M + (al/2) * ((1 - 2 * lam * \<alpha>)\<^sup>2
        * (norm (xh - yh))\<^sup>2) + lam * (\<alpha>\<^sup>2 * (norm (xh - yh))\<^sup>2)"
      unfolding penn gsq by simp
    also have "\<dots> = M + (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
      unfolding penc by (simp add: algebra_simps)
    also have "\<dots> = u xh + b yh" unfolding M_def by simp
    finally show ?thesis .
  qed
  have LuLe: "Lu \<le> u xh"
  proof (rule ccontr)
    assume "\<not> Lu \<le> u xh"
    then have lt: "u xh < Lu" by linarith
    define c where "c = (u xh + Lu) / 2"
    have c1: "u xh < c" unfolding c_def using lt by argo
    have c2: "c < Lu" unfolding c_def using lt by argo
    have ev: "\<forall>\<^sub>F n in sequentially. u (xstar n) < c"
      by (rule usc_eventually_lt[OF usc xstart c1])
    then obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> u (xstar n) < c"
      unfolding eventually_sequentially by blast
    have "Lu \<le> c"
      by (rule LIMSEQ_le_const2[OF uxstart])
        (use N less_imp_le in blast)
    then show False using c2 by linarith
  qed
  have LbLe: "Lb \<le> b yh"
  proof (rule ccontr)
    assume "\<not> Lb \<le> b yh"
    then have lt: "b yh < Lb" by linarith
    define c where "c = (b yh + Lb) / 2"
    have c1: "b yh < c" unfolding c_def using lt by argo
    have c2: "c < Lb" unfolding c_def using lt by argo
    have ev: "\<forall>\<^sub>F n in sequentially. b (ystar n) < c"
      by (rule usc_eventually_lt[OF uscb ystart c1])
    then obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> b (ystar n) < c"
      unfolding eventually_sequentially by blast
    have "Lb \<le> c"
      by (rule LIMSEQ_le_const2[OF bystart])
        (use N less_imp_le in blast)
    then show False using c2 by linarith
  qed
  have LuEq: "Lu = u xh" and LbEq: "Lb = b yh"
    using sumL LuLe LbLe by linarith+
  have uxh: "(\<lambda>n. u (xstar n)) \<longlonglongrightarrow> u xh"
    using uxstart unfolding LuEq[symmetric] .
  have byh: "(\<lambda>n. b (ystar n)) \<longlonglongrightarrow> b yh"
    using bystart unfolding LbEq[symmetric] .
  have wyh: "(\<lambda>n. w (ystar n)) \<longlonglongrightarrow> w yh"
  proof -
    have f: "(\<lambda>n. w (ystar n)) = (\<lambda>n. - b (ystar n))"
      by (rule ext) (simp add: b_def)
    have v: "- b yh = w yh" by (simp add: b_def)
    have "(\<lambda>n. - b (ystar n)) \<longlonglongrightarrow> - b yh"
      by (rule tendsto_minus[OF byh])
    then show ?thesis unfolding f v .
  qed
  define Yoo where "Yoo = (\<lambda>h. - Yoo' h)"
  have memX: "(g, Xoo) \<in> superjet_cl u xh"
  proof -
    have exwit: "\<exists>xsq psq Xsq.
        (\<forall>i :: nat. (psq i, Xsq i) \<in> superjet u (xsq i)) \<and>
        xsq \<longlonglongrightarrow> xh \<and> (\<lambda>i. u (xsq i)) \<longlonglongrightarrow> u xh \<and>
        psq \<longlonglongrightarrow> g \<and> (\<forall>v. (\<lambda>i. Xsq i v) \<longlonglongrightarrow> Xoo v)"
      apply (rule exI[of _ "\<lambda>i. xstar (R i)"])
      apply (rule exI[of _ "\<lambda>i. ps (R i)"])
      apply (rule exI[of _ "\<lambda>i. HH (R i)"])
      apply (intro conjI allI)
      subgoal for i by (rule jetun)
      subgoal by (rule LIMSEQ_subseq_LIMSEQ[OF xstart Rmono,
          unfolded o_def])
      subgoal by (rule LIMSEQ_subseq_LIMSEQ[OF uxh Rmono,
          unfolded o_def])
      subgoal by (rule LIMSEQ_subseq_LIMSEQ[OF pst Rmono,
          unfolded o_def])
      subgoal for v by (rule pwXR)
      done
    show ?thesis unfolding superjet_cl_def
      using linX symX exwit by simp
  qed
  have memY: "(g, Yoo) \<in> subjet_cl w yh"
  proof -
    have jw: "(- qs n, \<lambda>h. - II n h) \<in> subjet w (ystar n)" for n
    proof -
      have h: "(qs n, II n) \<in> superjet (\<lambda>z. - w z) (ystar n)"
        using jetbn[of n] unfolding b_def .
      show ?thesis
        by (subst subjet_neg_superjet) (use h in simp)
    qed
    have exwit: "\<exists>xsq psq Xsq.
        (\<forall>i :: nat. (psq i, Xsq i) \<in> subjet w (xsq i)) \<and>
        xsq \<longlonglongrightarrow> yh \<and> (\<lambda>i. w (xsq i)) \<longlonglongrightarrow> w yh \<and>
        psq \<longlonglongrightarrow> g \<and> (\<forall>v. (\<lambda>i. Xsq i v) \<longlonglongrightarrow> Yoo v)"
      apply (rule exI[of _ "\<lambda>i. ystar (R i)"])
      apply (rule exI[of _ "\<lambda>i. - qs (R i)"])
      apply (rule exI[of _ "\<lambda>i h. - II (R i) h"])
      apply (intro conjI allI)
      subgoal for i by (rule jw)
      subgoal by (rule LIMSEQ_subseq_LIMSEQ[OF ystart Rmono,
          unfolded o_def])
      subgoal by (rule LIMSEQ_subseq_LIMSEQ[OF wyh Rmono,
          unfolded o_def])
      subgoal
      proof -
        have "(\<lambda>i. qs (R i)) \<longlonglongrightarrow> - g"
          by (rule LIMSEQ_subseq_LIMSEQ[OF qst Rmono, unfolded o_def])
        then have "(\<lambda>i. - qs (R i)) \<longlonglongrightarrow> - (- g)"
          by (rule tendsto_minus)
        then show ?thesis by simp
      qed
      subgoal for v
      proof -
        have "(\<lambda>i. - II (R i) v) \<longlonglongrightarrow> - Yoo' v"
          by (rule tendsto_minus[OF pwYR])
        then show ?thesis unfolding Yoo_def .
      qed
      done
    have linYoo: "linear Yoo" unfolding Yoo_def
      by (rule linear_compose_neg[OF linY'])
    have symYoo: "\<And>a c. a \<bullet> Yoo c = c \<bullet> Yoo a"
      unfolding Yoo_def using symY' by simp
    show ?thesis unfolding subjet_cl_def
      using linYoo symYoo exwit by simp
  qed
  have ordlim: "v \<bullet> Xoo v \<le> v \<bullet> Yoo v" for v
  proof -
    have s1: "(\<lambda>i. v \<bullet> HH (R i) v + v \<bullet> II (R i) v)
        \<longlonglongrightarrow> v \<bullet> Xoo v + v \<bullet> Yoo' v"
      by (intro tendsto_add tendsto_inner tendsto_const pwXR pwYR)
    have s2: "(\<lambda>i. 4 * dl (R i) * (norm v)\<^sup>2) \<longlonglongrightarrow> 4 * 0 * (norm v)\<^sup>2"
      by (intro tendsto_mult tendsto_const
          LIMSEQ_subseq_LIMSEQ[OF dlt Rmono, unfolded o_def])
    have "v \<bullet> Xoo v + v \<bullet> Yoo' v \<le> 4 * 0 * (norm v)\<^sup>2"
      by (rule LIMSEQ_le[OF s1 s2]) (use ordn in blast)
    then have "v \<bullet> Xoo v + v \<bullet> Yoo' v \<le> 0" by simp
    then show ?thesis unfolding Yoo_def by simp
  qed
  have lowlim: "- ((norm v)\<^sup>2 / lam) \<le> v \<bullet> Xoo v" for v
  proof -
    have s1: "(\<lambda>i. v \<bullet> HH (R i) v) \<longlonglongrightarrow> v \<bullet> Xoo v"
      by (intro tendsto_inner tendsto_const pwXR)
    show ?thesis
      by (rule LIMSEQ_le_const[OF s1]) (use lowH in blast)
  qed
  have uplim: "v \<bullet> Yoo v \<le> (norm v)\<^sup>2 / lam" for v
  proof -
    have s1: "(\<lambda>i. v \<bullet> II (R i) v) \<longlonglongrightarrow> v \<bullet> Yoo' v"
      by (intro tendsto_inner tendsto_const pwYR)
    have "- ((norm v)\<^sup>2 / lam) \<le> v \<bullet> Yoo' v"
      by (rule LIMSEQ_le_const[OF s1]) (use lowII in blast)
    then show ?thesis unfolding Yoo_def by simp
  qed
  show ?thesis
    apply (rule exI[of _ Xoo])
    apply (rule exI[of _ Yoo])
    using memX memY ordlim lowlim uplim unfolding g_def by blast
qed

(*<*)
end
(*>*)