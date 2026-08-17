section \<open>The Crandall--Ishii theorem on sums\<close>

(*<*)
theory Theorem_On_Sums
  imports Sup_Convolution "Symmetric_Matrix_Spectra.Matrix_Algebra"
begin

(*>*)

subsection \<open>Towards the theorem on sums: doubling of variables\<close>

text \<open>The development of the theorem on sums below follows
  Crandall--Ishii--Lions, \<^emph>\<open>User's guide to viscosity solutions\<close>, Bull.
  AMS 27 (1992), Lemma 3.1 of \<^cite>\<open>LaiShkolnikovSoner\<close>.  The quantitative core is purely algebraic:
  writing \<open>\<Phi>\<^sub>\<alpha>(x,y) = u x - w y - (\<alpha>/2) * norm (x - y)\<^sup>2\<close> and
  \<open>M\<^sub>\<alpha> = max \<Phi>\<^sub>\<alpha>\<close>, testing \<open>\<Phi>\<^sub>\<beta>\<close> at the maximizer of \<open>\<Phi>\<^sub>\<alpha>\<close> shows
  \<open>M\<^sub>\<alpha>\<close> nonincreasing and squeezes the penalty term, forcing
  \<open>\<alpha> * norm (x\<^sub>\<alpha> - y\<^sub>\<alpha>)\<^sup>2 \<longrightarrow> 0\<close> once \<open>M\<^sub>\<alpha>\<close> is known to converge.\<close>

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

text \<open>The limit half of Lemma 3.1 of \<^cite>\<open>LaiShkolnikovSoner\<close>: once \<open>M\<^sub>\<alpha>\<close> converges, the squeeze with
  \<open>\<beta> = \<alpha>/2\<close> traps \<open>(\<alpha>/4) * pen \<alpha>\<close> between \<open>0\<close> and
  \<open>M\<^bsub>\<alpha>/2\<^esub> - M\<^sub>\<alpha>\<close>, both tending to \<open>0\<close>: the penalty term vanishes,
  letting the two maximizers merge in the limit.\<close>

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

text \<open>And the hypothesis of the previous lemma is exactly what
  \<open>doubling_antitone\<close> plus \<open>doubling_ge_diagonal\<close> supply: \<open>M\<^sub>\<alpha>\<close> is
  antitone and bounded below by any diagonal value, hence convergent
  along \<open>at_top\<close>.\<close>

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


subsection \<open>Block structure on the product space\<close>

text \<open>The doubled function lives on \<open>'a \<times> 'b\<close>, itself a Euclidean space,
  so every result above applies to it verbatim.  Testing the product's
  negative semidefiniteness on the diagonal \<open>w = v\<close> kills the penalty
  term and leaves \<open>v \<cdot> X v \<le> v \<cdot> Y v\<close>, the matrix inequality of the
  theorem on sums; and a second-order expansion on the product restricts
  to each slice, letting the single product Hessian be read as two
  separate matrices.\<close>

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

text \<open>The doubled functional
  \<open>(x,y) \<mapsto> u x - w y - (\<alpha>/2) * norm (x - y)\<^sup>2\<close> must first be known
  semiconvex on the product.  Three closure properties suffice:
  semiconvexity adds (with the constants), it survives composition with
  \<open>fst\<close> and \<open>snd\<close>, and the concave penalty is itself semiconvex with
  constant \<open>2*\<alpha>\<close>.\<close>

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
    by (simp add: inner_commute algebra_simps)
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

text \<open>The concave penalty is semiconvex with constant \<open>2*\<alpha>\<close>.  Adding
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

text \<open>The doubled functional is semiconvex, with constant
  \<open>1/\<epsilon> + 1/\<epsilon> + 2*\<alpha>\<close> --- the hypothesis Rademacher, Alexandrov and
  Jensen need before being pointed at the doubling of variables, and
  what opens the theorem on sums.\<close>

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

text \<open>The doubled functional perturbed by \<open>-\<delta>\<parallel>z - \<xi>\<parallel>\<^sup>2\<close> is still
  semiconvex, with the constant raised by \<open>2\<delta>\<close>, turning a plain
  maximizer into a strict one, as Jensen's lemma needs.

  The perturbation splits across the two blocks,
  \<open>\<parallel>z - \<xi>\<parallel>\<^sup>2 = \<parallel>fst z - fst \<xi>\<parallel>\<^sup>2 + \<parallel>snd z - snd \<xi>\<parallel>\<^sup>2\<close>, so the perturbed
  functional keeps the doubled form downstream lemmas expect, and the
  cost is affine, since \<open>\<parallel>z\<parallel>\<^sup>2 - \<parallel>z - \<xi>\<parallel>\<^sup>2 = 2 z \<bullet> \<xi> - \<parallel>\<xi>\<parallel>\<^sup>2\<close>.\<close>

lemma norm_sq_diff_shift:
  fixes z c :: "'a::euclidean_space"
  shows "(norm z)\<^sup>2 - (norm (z - c))\<^sup>2 = 2 * (z \<bullet> c) - (norm c)\<^sup>2"
  by (simp add: power2_norm_eq_inner
      inner_commute algebra_simps)

theorem doubled_functional_semiconvex_shifted:
  fixes u v :: "'a::euclidean_space \<Rightarrow> real"
  assumes Bu: "\<And>y. u y \<le> Bu" and Bv: "\<And>y. v y \<le> Bv"
    and e: "0 < \<epsilon>" and a: "0 \<le> \<alpha>"
  shows "convex_on UNIV (\<lambda>z::'a \<times> 'a.
      ((supconv u \<epsilon> (fst z) + supconv v \<epsilon> (snd z)
          - (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2)
        - \<delta> * (norm (z - \<xi>))\<^sup>2)
      + ((1/\<epsilon> + 1/\<epsilon> + 2*\<alpha> + 2*\<delta>)/2) * (norm z)\<^sup>2)"
proof -
  have cvx: "convex_on UNIV (\<lambda>z::'a \<times> 'a.
      (supconv u \<epsilon> (fst z) + supconv v \<epsilon> (snd z)
        - (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2)
      + ((1/\<epsilon> + 1/\<epsilon> + 2*\<alpha>)/2) * (norm z)\<^sup>2)"
    by (rule doubled_functional_semiconvex[OF Bu Bv e a])
  have aff: "convex_on UNIV
      (\<lambda>z::'a \<times> 'a. (- (\<delta> * (norm \<xi>)\<^sup>2)) + inner z ((2*\<delta>) *\<^sub>R \<xi>))"
    by (rule convex_on_affine_inner)
  have eq: "(\<lambda>z::'a \<times> 'a.
        ((supconv u \<epsilon> (fst z) + supconv v \<epsilon> (snd z)
            - (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2)
          - \<delta> * (norm (z - \<xi>))\<^sup>2)
        + ((1/\<epsilon> + 1/\<epsilon> + 2*\<alpha> + 2*\<delta>)/2) * (norm z)\<^sup>2)
      = (\<lambda>z::'a \<times> 'a.
        ((supconv u \<epsilon> (fst z) + supconv v \<epsilon> (snd z)
            - (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2)
          + ((1/\<epsilon> + 1/\<epsilon> + 2*\<alpha>)/2) * (norm z)\<^sup>2)
        + ((- (\<delta> * (norm \<xi>)\<^sup>2)) + inner z ((2*\<delta>) *\<^sub>R \<xi>)))"
  proof (rule ext)
    fix z :: "'a \<times> 'a"
    have sh: "(norm z)\<^sup>2 - (norm (z - \<xi>))\<^sup>2 = 2 * (z \<bullet> \<xi>) - (norm \<xi>)\<^sup>2"
      by (rule norm_sq_diff_shift)
    have sh': "(norm (z - \<xi>))\<^sup>2 = (norm z)\<^sup>2 - 2 * (z \<bullet> \<xi>) + (norm \<xi>)\<^sup>2"
      using sh by linarith
    have iz: "inner z ((2*\<delta>) *\<^sub>R \<xi>) = 2 * \<delta> * (z \<bullet> \<xi>)"
      by simp    show "((supconv u \<epsilon> (fst z) + supconv v \<epsilon> (snd z)
            - (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2)
          - \<delta> * (norm (z - \<xi>))\<^sup>2)
        + ((1/\<epsilon> + 1/\<epsilon> + 2*\<alpha> + 2*\<delta>)/2) * (norm z)\<^sup>2
      = ((supconv u \<epsilon> (fst z) + supconv v \<epsilon> (snd z)
            - (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2)
          + ((1/\<epsilon> + 1/\<epsilon> + 2*\<alpha>)/2) * (norm z)\<^sup>2)
        + ((- (\<delta> * (norm \<xi>)\<^sup>2)) + inner z ((2*\<delta>) *\<^sub>R \<xi>))"
      unfolding iz sh' by (simp add: algebra_simps)
  qed
  show ?thesis
    unfolding eq by (rule convex_on_add[OF cvx aff])
qed

subsection \<open>The engine in general form\<close>
text \<open>\<open>supconv_jensen_alexandrov_point\<close> used only semiconvexity of the
  sup-convolution, which the doubled functional also has without being a
  sup-convolution.  So the engine is restated for an arbitrary semiconvex
  \<open>\<phi>\<close>, strengthened with the interiority \<open>dist x \<xi> < \<rho>\<close> that
  \<open>second_order_interior_max\<close> needs.\<close>

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
      \<and> (\<forall>k. - (c * (norm k)\<^sup>2) \<le> k \<bullet> X k)
      \<and> ((\<lambda>k. (\<phi> (x + k) - \<phi> x - q \<bullet> k - (k \<bullet> X k)/2) / (norm k)\<^sup>2)
          \<longlongrightarrow> 0) (at 0)"
proof -
  have r: "0 < r" using rho by simp
  define J where "J = {x \<in> cball \<xi> r. \<exists>p. norm p \<le> d
      \<and> (\<forall>y \<in> cball \<xi> r. \<phi> y + p \<bullet> y \<le> \<phi> x + p \<bullet> x)}"
  define N where "N = {y. \<not> (\<exists>q X. bounded_linear X \<and> (\<forall>v w. v \<bullet> X w = w \<bullet> X v)
      \<and> (\<forall>k. - (c * (norm k)\<^sup>2) \<le> k \<bullet> X k)
      \<and> ((\<lambda>k. (\<phi> (y + k) - \<phi> y - q \<bullet> k - (k \<bullet> X k)/2) / (norm k)\<^sup>2)
          \<longlongrightarrow> 0) (at 0))}"
  have nJ: "\<not> negligible J"
    unfolding J_def by (rule jensen_lemma[OF cvx c rho(1) rho(2) bnd d small])
  have nN: "negligible N"
    unfolding N_def by (rule semiconvex_alexandrov_bounded[OF cvx])
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
    and lbX: "\<forall>k. - (c * (norm k)\<^sup>2) \<le> k \<bullet> X k"
    and lim: "((\<lambda>k. (\<phi> (x + k) - \<phi> x - q \<bullet> k - (k \<bullet> X k)/2) / (norm k)\<^sup>2)
        \<longlongrightarrow> 0) (at 0)"
    unfolding N_def by blast
  show ?thesis
    using deep np xmax blX symX lbX lim by blast
qed

subsection \<open>Uniqueness of the second-order form, and block diagonality\<close>

text \<open>The quadratic form in a second-order expansion is unique: restricting
  to a ray \<open>t \<mapsto> t *\<^sub>R v\<close> makes the difference quotient constant in
  \<open>t\<close>, and a constant that tends to \<open>0\<close> is \<open>0\<close>.

  This avoids the textbook's \<open>A + \<epsilon> A\<^sup>2\<close> matrix argument: for
  \<open>a (fst z) + b (snd z)\<close> the two slice expansions reassemble into a
  block-diagonal quadratic form, and by uniqueness the product form
  equals it, so the off-diagonal blocks vanish exactly, not merely after
  an \<open>\<epsilon>\<close>-perturbation.\<close>

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

text \<open>The reusable ray step: along a fixed direction, \<open>F (t *\<^sub>R w) / t\<^sup>2\<close>
  converges to half the quadratic form at \<open>w\<close>.  Applying this to the
  product expansion and to the two slice expansions, and adding the
  latter two, identifies the product form with the block-diagonal one.\<close>

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

text \<open>Block diagonality: for \<open>a (fst z) + b (snd z)\<close> the product quadratic
  form is exactly the sum of the two slice forms, off-diagonal blocks
  vanishing identically.  Along the ray \<open>t *\<^sub>R (h,g)\<close> the product's
  difference quotient splits as a sum of the slice quotients, and the
  three ray limits force the identity, with no \<open>\<epsilon>\<close>-perturbation and no
  spectral theory.\<close>

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

text \<open>The penalty is a quadratic, so its second-order expansion is exact,
  with no remainder: gradient \<open>\<alpha> *\<^sub>R (Dz, -Dz)\<close>, quadratic form
  \<open>k \<mapsto> \<alpha> * norm (fst k - snd k)\<^sup>2\<close>.  Added to the expansion of \<open>\<Psi>\<close> it
  recovers the separated form \<open>a (fst z) + b (snd z)\<close> that
  \<open>product_form_block_diagonal\<close> needs; the quadratic form vanishes on
  the diagonal \<open>(v,v)\<close>, which is exactly why testing there kills the
  penalty and leaves only \<open>X \<preceq> Y\<close>.\<close>

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
    by (cases k) (simp add: algebra_simps)
  have e3: "k \<bullet> (\<alpha> *\<^sub>R (fst k - snd k, snd k - fst k))
      = \<alpha> * (norm (fst k - snd k))\<^sup>2"
    by (cases k) (simp add: power2_norm_eq_inner
        inner_commute algebra_simps)
  show ?thesis unfolding d1 e1 e2 e3 by (simp add: algebra_simps)
qed

text \<open>And the penalty's quadratic form is linear in \<open>k\<close> and vanishes on
  the diagonal.\<close>

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

text \<open>The theorem on sums, algebraic core: if the doubled functional
  \<open>a (fst z) + b (snd z) - (\<alpha>/2) * norm (fst z - snd z)\<^sup>2\<close> has a
  second-order expansion at \<open>zh\<close> with negative semidefinite form \<open>W\<close>
  (what an interior maximum supplies), adding the penalty's exact
  expansion turns the functional into the separated form
  \<open>a (fst z) + b (snd z)\<close> and, by block diagonality, splits \<open>W\<close> into its
  two slice matrices; testing on the diagonal \<open>(v,v)\<close> (where the penalty
  contributes nothing) leaves exactly the matrix inequality.

  With \<open>b = - w\<close> the second slice matrix is \<open>- Y\<close>, so the conclusion
  reads \<open>v \<cdot> X v \<le> v \<cdot> Y v\<close>, i.e. \<open>X \<preceq> Y\<close>: what the comparison
  principle feeds to degenerate ellipticity.\<close>

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

subsection \<open>The limit half of Lemma 3.1 of \<^cite>\<open>LaiShkolnikovSoner\<close>\<close>

text \<open>The remaining half of Crandall--Ishii--Lions Lemma 3.1 of \<^cite>\<open>LaiShkolnikovSoner\<close>: the common
  limit point of the two maximizers maximizes \<open>u - w\<close>.  Upper/lower
  semicontinuity of \<open>u\<close>/\<open>w\<close> enter only through two \<open>eventually\<close>
  statements below, so no semicontinuity predicate has to be fixed here.

  Combined with \<open>doubling_ge_diagonal\<close> (which gives \<open>S \<le> M\<^sub>\<alpha>\<close>) this
  pins \<open>lim M\<^sub>\<alpha> = S\<close>, letting the doubling argument start at an
  interior maximum of \<open>u - w\<close>.\<close>

lemma doubling_limit_maximises:
  fixes u w :: "'a::euclidean_space \<Rightarrow> real"
  assumes Mconv: "(M \<longlongrightarrow> L) sequentially"
    and usc: "\<And>e. 0 < e \<Longrightarrow> \<forall>\<^sub>F n in sequentially. u (X n) < u xh + e"
    and lsc: "\<And>e. 0 < e \<Longrightarrow> \<forall>\<^sub>F n in sequentially. w xh - e < w (Y n)"
    and le: "\<And>n. M n \<le> u (X n) - w (Y n)"
    and lower: "\<And>n. S \<le> M n"
  shows "S \<le> u xh - w xh"
proof -
  have LB: "L \<le> (u xh - w xh) + e" if e: "0 < e" for e
  proof -
    have e2: "0 < e/2" using e by simp
    have ev: "\<forall>\<^sub>F n in sequentially. M n \<le> (u xh - w xh) + e"
    proof (rule eventually_mono[OF eventually_conj[OF usc[OF e2] lsc[OF e2]]])
      fix n
      assume "u (X n) < u xh + e/2 \<and> w xh - e/2 < w (Y n)"
      thus "M n \<le> (u xh - w xh) + e" using le[of n] by linarith
    qed
    show ?thesis by (rule tendsto_upperbound[OF Mconv ev]) simp
  qed
  have L1: "L \<le> u xh - w xh" by (rule field_le_epsilon) (use LB in blast)
  have evS: "\<forall>\<^sub>F n in sequentially. S \<le> M n"
    by (rule always_eventually) (use lower in blast)
  have L2: "S \<le> L" by (rule tendsto_lowerbound[OF Mconv evS]) simp
  show ?thesis using L1 L2 by linarith
qed

subsection \<open>Transferring jets back: the sup-convolution's magic property\<close>

text \<open>\<^emph>\<open>Magic property\<close> of sup-convolutions, the reason the
  regularisation is harmless: if the supremum defining
  \<open>supconv u \<epsilon> x\<close> is attained at \<open>ys\<close>, shifting both arguments by the
  same \<open>k\<close> leaves the penalty unchanged, so the increment of \<open>u\<close> at
  \<open>ys\<close> is dominated by the increment of \<open>supconv u \<epsilon>\<close> at \<open>x\<close> ---
  consequently any second-order upper bound at \<open>x\<close> is inherited by \<open>u\<close>
  at \<open>ys\<close>, with no loss and no limit needed.\<close>

lemma supconv_dominates_shift:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> B" and e: "0 < \<epsilon>"
    and opt: "supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
  shows "u (ys + k) - u ys \<le> supconv u \<epsilon> (x + k) - supconv u \<epsilon> x"
proof -
  have d: "dist (x + k) (ys + k) = dist x ys" by (simp add: dist_norm)
  have "u (ys + k) - (dist (x + k) (ys + k))\<^sup>2 / (2*\<epsilon>)
      \<le> supconv u \<epsilon> (x + k)"
    unfolding supconv_def
    by (intro cSUP_upper supconv_bdd_above[OF B e]) simp
  hence step: "u (ys + k) - (dist x ys)\<^sup>2 / (2*\<epsilon>) \<le> supconv u \<epsilon> (x + k)"
    unfolding d .
  have base: "u ys = supconv u \<epsilon> x + (dist x ys)\<^sup>2 / (2*\<epsilon>)"
    using opt by simp
  show ?thesis using step base by simp
qed

text \<open>In quotient form: the difference quotient for \<open>u\<close> at \<open>ys\<close> is
  dominated by the one for \<open>supconv u \<epsilon>\<close> at \<open>x\<close>, which tends to \<open>0\<close> ---
  exactly the statement that \<open>(p, X)\<close> is a second-order superjet of
  \<open>u\<close> at \<open>ys\<close>.\<close>

lemma supconv_jet_transfer:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> B" and e: "0 < \<epsilon>"
    and opt: "supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
  shows "(u (ys + k) - u ys - p \<bullet> k - (k \<bullet> X k)/2) / (norm k)\<^sup>2
      \<le> (supconv u \<epsilon> (x + k) - supconv u \<epsilon> x - p \<bullet> k - (k \<bullet> X k)/2)
        / (norm k)\<^sup>2"
proof -
  have dom: "u (ys + k) - u ys \<le> supconv u \<epsilon> (x + k) - supconv u \<epsilon> x"
    by (rule supconv_dominates_shift[OF B e opt])
  have nn: "0 \<le> (norm k)\<^sup>2" by simp
  show ?thesis using dom by (intro divide_right_mono nn) simp
qed

subsection \<open>From abstract forms to matrices\<close>

text \<open>\<open>matrix_vec_apply\<close>, \<open>matrix_of_symmetric\<close>, \<open>matrix_symmetric_swap\<close>, \<open>has_derivative_quadratic_form\<close>, \<open>quadratic_test_derivative\<close>, \<open>quadratic_test_grad_derivative\<close> live in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


subsection \<open>Sign flip: superjets of \<open>- w\<close> are subjets of \<open>w\<close>\<close>

text \<open>The doubling regularises \<open>u\<close> and \<open>- w\<close> by sup-convolution, since
  \<open>supconv\<close> is what produces semiconvexity, but a supersolution
  condition speaks about \<open>w\<close> and needs a subjet.  The two are the same
  statement with all signs reversed: the difference quotient for \<open>- w\<close>
  with data \<open>(p, X)\<close> is exactly minus the one for \<open>w\<close> with data
  \<open>(- p, - X)\<close>, so an upper bound on one is a lower bound on the other.\<close>

lemma neg_jet_quotient:
  fixes w :: "'a::euclidean_space \<Rightarrow> real"
  shows "(((\<lambda>z. - w z) (ys + k)) - ((\<lambda>z. - w z) ys) - p \<bullet> k - (k \<bullet> X k)/2)
      / (norm k)\<^sup>2
      = - ((w (ys + k) - w ys - (- p) \<bullet> k
          - (k \<bullet> ((\<lambda>v. - X v) k))/2) / (norm k)\<^sup>2)"
proof -
  have e1: "(- p) \<bullet> k = - (p \<bullet> k)" by simp
  have e2: "k \<bullet> ((\<lambda>v. - X v) k) = - (k \<bullet> X k)" by simp
  have num: "((\<lambda>z. - w z) (ys + k)) - ((\<lambda>z. - w z) ys) - p \<bullet> k - (k \<bullet> X k)/2
      = - (w (ys + k) - w ys - (- p) \<bullet> k - (k \<bullet> ((\<lambda>v. - X v) k))/2)"
    unfolding e1 e2 by simp
  show ?thesis unfolding num by (rule minus_divide_left[symmetric])
qed

text \<open>Hence the transferred jet, in the form the supersolution needs.\<close>

lemma supconv_neg_jet_transfer:
  fixes w :: "'a::euclidean_space \<Rightarrow> real"
  assumes B: "\<And>y. - w y \<le> B" and e: "0 < \<epsilon>"
    and opt: "supconv (\<lambda>z. - w z) \<epsilon> x = (- w ys) - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
  shows "- ((w (ys + k) - w ys - (- p) \<bullet> k
          - (k \<bullet> ((\<lambda>v. - X v) k))/2) / (norm k)\<^sup>2)
      \<le> (supconv (\<lambda>z. - w z) \<epsilon> (x + k) - supconv (\<lambda>z. - w z) \<epsilon> x
          - p \<bullet> k - (k \<bullet> X k)/2) / (norm k)\<^sup>2"
proof -
  have "(((\<lambda>z. - w z) (ys + k)) - ((\<lambda>z. - w z) ys) - p \<bullet> k - (k \<bullet> X k)/2)
      / (norm k)\<^sup>2
      \<le> (supconv (\<lambda>z. - w z) \<epsilon> (x + k) - supconv (\<lambda>z. - w z) \<epsilon> x
          - p \<bullet> k - (k \<bullet> X k)/2) / (norm k)\<^sup>2"
    by (rule supconv_jet_transfer[OF B e opt])
  thus ?thesis unfolding neg_jet_quotient[symmetric] .
qed

text \<open>Reading the theorem on sums as an ordering hypothesis for a
  comparison argument.  \<open>sums_matrix_inequality\<close> concludes
  \<open>v \<cdot> X v + v \<cdot> Yb v \<le> 0\<close> where \<open>Yb\<close> is the slice matrix of the second
  factor; since that factor carries \<open>- w\<close>, the matrix a supersolution
  needs is \<open>Y = - Yb\<close>, and the inequality becomes
  \<open>v \<cdot> X v \<le> v \<cdot> Y v\<close>.\<close>

lemma sums_ord_of_inequality:
  fixes W :: "'a::euclidean_space \<times> 'a \<Rightarrow> 'a \<times> 'a"
  assumes ineq: "v \<bullet> fst (W (v, 0) + \<alpha> *\<^sub>R (v - 0, 0 - v))
      + v \<bullet> snd (W (0, v) + \<alpha> *\<^sub>R (0 - v, v - 0)) \<le> 0"
  shows "v \<bullet> (\<lambda>z. fst (W (z, 0) + \<alpha> *\<^sub>R (z - 0, 0 - z))) v
      \<le> v \<bullet> (\<lambda>z. - snd (W (0, z) + \<alpha> *\<^sub>R (0 - z, z - 0))) v"
proof -
  have neg: "v \<bullet> (- snd (W (0, v) + \<alpha> *\<^sub>R (0 - v, v - 0)))
      = - (v \<bullet> snd (W (0, v) + \<alpha> *\<^sub>R (0 - v, v - 0)))"
    by (rule inner_minus_right)
  show ?thesis using ineq unfolding neg by simp
qed

text \<open>Linearity of the two slice maps, the remaining hypotheses of the
  comparison argument besides the ordering.\<close>

lemma linear_slice_fst:
  fixes W :: "'a::euclidean_space \<times> 'a \<Rightarrow> 'a \<times> 'a"
  assumes lW: "linear W"
  shows "linear (\<lambda>z. fst (W (z, 0) + \<alpha> *\<^sub>R (z - 0, 0 - z)))"
proof (rule linearI)
  fix z1 z2 :: 'a
  have wa: "W (z1 + z2, 0) = W (z1, 0) + W (z2, 0)"
  proof -
    from lW have add: "\<forall>x y. W (x + y) = W x + W y"
      unfolding linear_iff by blast
    have "W ((z1, (0::'a)) + (z2, (0::'a))) = W (z1, 0) + W (z2, 0)"
      using add by blast
    thus ?thesis by simp
  qed
  show "fst (W (z1 + z2, 0) + \<alpha> *\<^sub>R ((z1 + z2) - 0, 0 - (z1 + z2)))
      = fst (W (z1, 0) + \<alpha> *\<^sub>R (z1 - 0, 0 - z1))
      + fst (W (z2, 0) + \<alpha> *\<^sub>R (z2 - 0, 0 - z2))"
    unfolding wa by (simp add: algebra_simps)
next
  fix c :: real and z :: 'a
  have ws: "W (c *\<^sub>R z, 0) = c *\<^sub>R W (z, 0)"
  proof -
    from lW have sc: "\<forall>r x. W (r *\<^sub>R x) = r *\<^sub>R W x"
      unfolding linear_iff by blast
    have "W (c *\<^sub>R (z, (0::'a))) = c *\<^sub>R W (z, 0)" using sc by blast
    thus ?thesis by simp
  qed
  show "fst (W (c *\<^sub>R z, 0) + \<alpha> *\<^sub>R ((c *\<^sub>R z) - 0, 0 - c *\<^sub>R z))
      = c *\<^sub>R fst (W (z, 0) + \<alpha> *\<^sub>R (z - 0, 0 - z))"
    unfolding ws by (simp add: algebra_simps)
qed

lemma linear_slice_snd:
  fixes W :: "'a::euclidean_space \<times> 'a \<Rightarrow> 'a \<times> 'a"
  assumes lW: "linear W"
  shows "linear (\<lambda>z. - snd (W (0, z) + \<alpha> *\<^sub>R (0 - z, z - 0)))"
proof (rule linearI)
  fix z1 z2 :: 'a
  have wa: "W (0, z1 + z2) = W (0, z1) + W (0, z2)"
  proof -
    from lW have add: "\<forall>x y. W (x + y) = W x + W y"
      unfolding linear_iff by blast
    have "W (((0::'a), z1) + ((0::'a), z2)) = W (0, z1) + W (0, z2)"
      using add by blast
    thus ?thesis by simp
  qed
  show "- snd (W (0, z1 + z2) + \<alpha> *\<^sub>R (0 - (z1 + z2), (z1 + z2) - 0))
      = - snd (W (0, z1) + \<alpha> *\<^sub>R (0 - z1, z1 - 0))
      + - snd (W (0, z2) + \<alpha> *\<^sub>R (0 - z2, z2 - 0))"
    unfolding wa by (simp add: algebra_simps)
next
  fix c :: real and z :: 'a
  have ws: "W (0, c *\<^sub>R z) = c *\<^sub>R W (0, z)"
  proof -
    from lW have sc: "\<forall>r x. W (r *\<^sub>R x) = r *\<^sub>R W x"
      unfolding linear_iff by blast
    have "W (c *\<^sub>R ((0::'a), z)) = c *\<^sub>R W (0, z)" using sc by blast
    thus ?thesis by simp
  qed
  show "- snd (W (0, c *\<^sub>R z) + \<alpha> *\<^sub>R (0 - c *\<^sub>R z, (c *\<^sub>R z) - 0))
      = c *\<^sub>R (- snd (W (0, z) + \<alpha> *\<^sub>R (0 - z, z - 0)))"
    unfolding ws by (simp add: algebra_simps)
qed

text \<open>The two symmetry hypotheses: pairing against \<open>(u, 0)\<close> turns
  \<open>u \<cdot> fst P\<close> into an inner product on the product space, so the
  symmetry of \<open>W\<close> transfers to each slice; the penalty contributes
  \<open>\<alpha> * (v \<cdot> w)\<close>, symmetric on its own.\<close>

lemma inner_fst_pair:
  fixes u :: "'a::euclidean_space" and P :: "'a \<times> 'a"
  shows "u \<bullet> fst P = (u, (0::'a)) \<bullet> P"
  by (cases P) simp

lemma inner_snd_pair:
  fixes u :: "'a::euclidean_space" and P :: "'a \<times> 'a"
  shows "u \<bullet> snd P = ((0::'a), u) \<bullet> P"
  by (cases P) simp

lemma sym_slice_fst:
  fixes W :: "'a::euclidean_space \<times> 'a \<Rightarrow> 'a \<times> 'a"
  assumes symW: "\<And>u u'. u \<bullet> W u' = u' \<bullet> W u"
  shows "v \<bullet> (\<lambda>z. fst (W (z, 0) + \<alpha> *\<^sub>R (z - 0, 0 - z))) w
      = w \<bullet> (\<lambda>z. fst (W (z, 0) + \<alpha> *\<^sub>R (z - 0, 0 - z))) v"
proof -
  have L: "v \<bullet> fst (W (w, 0) + \<alpha> *\<^sub>R (w - 0, 0 - w))
      = (v, (0::'a)) \<bullet> W (w, 0) + \<alpha> * (v \<bullet> w)"
    unfolding inner_fst_pair by (simp add: inner_add_right)
  have R: "w \<bullet> fst (W (v, 0) + \<alpha> *\<^sub>R (v - 0, 0 - v))
      = (w, (0::'a)) \<bullet> W (v, 0) + \<alpha> * (w \<bullet> v)"
    unfolding inner_fst_pair by (simp add: inner_add_right)
  have S: "(v, (0::'a)) \<bullet> W (w, 0) = (w, (0::'a)) \<bullet> W (v, 0)"
    by (rule symW)
  have C: "v \<bullet> w = w \<bullet> v" by (rule inner_commute)
  show ?thesis unfolding L R S C ..
qed

lemma sym_slice_snd:
  fixes W :: "'a::euclidean_space \<times> 'a \<Rightarrow> 'a \<times> 'a"
  assumes symW: "\<And>u u'. u \<bullet> W u' = u' \<bullet> W u"
  shows "v \<bullet> (\<lambda>z. - snd (W (0, z) + \<alpha> *\<^sub>R (0 - z, z - 0))) w
      = w \<bullet> (\<lambda>z. - snd (W (0, z) + \<alpha> *\<^sub>R (0 - z, z - 0))) v"
proof -
  have L: "v \<bullet> (- snd (W (0, w) + \<alpha> *\<^sub>R (0 - w, w - 0)))
      = - (((0::'a), v) \<bullet> W (0, w) + \<alpha> * (v \<bullet> w))"
    unfolding inner_minus_right inner_snd_pair
    by (simp add: inner_add_right)
  have R: "w \<bullet> (- snd (W (0, v) + \<alpha> *\<^sub>R (0 - v, v - 0)))
      = - (((0::'a), w) \<bullet> W (0, v) + \<alpha> * (w \<bullet> v))"
    unfolding inner_minus_right inner_snd_pair
    by (simp add: inner_add_right)
  have S: "((0::'a), v) \<bullet> W (0, w) = ((0::'a), w) \<bullet> W (0, v)"
    by (rule symW)
  have C: "v \<bullet> w = w \<bullet> v" by (rule inner_commute)
  show ?thesis unfolding L R S C ..
qed

subsection \<open>From a superjet to a genuine local maximum\<close>

text \<open>A second-order superjet does not by itself make \<open>u - \<phi>\<close> have a
  local maximum: the expansion only controls the remainder to
  \<open>o(norm k\<^sup>2)\<close>, which can be positive.  Adding a strictly convex
  correction \<open>(\<delta>/2) * norm k\<^sup>2\<close> absorbs it, and then the maximum is
  genuine.  This is the standard jet-to-test-function step; the \<open>\<delta>\<close> it
  introduces is why the theorem on sums is normally stated for closed
  second-order jets, since removing \<open>\<delta>\<close> at the end needs lower
  semicontinuity of the operator.\<close>

lemma superjet_local_max:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes lim: "((\<lambda>k. (u (xh + k) - u xh - p \<bullet> k - (k \<bullet> X k)/2)
      / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and d: "0 < \<delta>"
  shows "\<exists>e>0. \<forall>k. norm k < e \<longrightarrow>
      u (xh + k) - (p \<bullet> k + (k \<bullet> X k)/2 + (\<delta>/2) * (norm k)\<^sup>2) \<le> u xh"
proof -
  have d2: "0 < \<delta>/2" using d by simp
  from tendstoD[OF lim d2] obtain e where e: "0 < e"
    and b: "\<And>k. k \<noteq> 0 \<Longrightarrow> dist k 0 < e
      \<Longrightarrow> dist ((u (xh + k) - u xh - p \<bullet> k - (k \<bullet> X k)/2) / (norm k)\<^sup>2) 0
        < \<delta>/2"
    unfolding eventually_at by blast
  have main: "u (xh + k) - (p \<bullet> k + (k \<bullet> X k)/2 + (\<delta>/2) * (norm k)\<^sup>2) \<le> u xh"
    if nk: "norm k < e" for k
  proof (cases "k = 0")
    case True
    have "X 0 = 0 \<or> X 0 \<noteq> 0" by simp
    show ?thesis unfolding True by simp
  next
    case False
    have nn: "0 < (norm k)\<^sup>2" using False by simp
    have dk: "dist k 0 < e" using nk by (simp add: dist_norm)
    have babs: "\<bar>(u (xh + k) - u xh - p \<bullet> k - (k \<bullet> X k)/2)
        / (norm k)\<^sup>2\<bar> < \<delta>/2"
      using b[OF False dk] by (simp add: dist_real_def)
    have "(u (xh + k) - u xh - p \<bullet> k - (k \<bullet> X k)/2) / (norm k)\<^sup>2 < \<delta>/2"
      using babs by linarith
    hence "u (xh + k) - u xh - p \<bullet> k - (k \<bullet> X k)/2 < (\<delta>/2) * (norm k)\<^sup>2"
      using nn by (simp add: field_simps)
    thus ?thesis by simp
  qed
  show ?thesis using e main by blast
qed


(*<*)
end
(*>*)
