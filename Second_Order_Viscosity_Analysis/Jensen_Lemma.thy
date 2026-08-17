section \<open>Jensen's lemma for semiconvex functions\<close>

(*<*)
theory Jensen_Lemma
  imports Alexandrov
begin

(*>*)

subsection \<open>Towards Jensen's lemma\<close>

text \<open>The development of Jensen's lemma below follows
  Crandall--Ishii--Lions, \<^emph>\<open>User's guide to viscosity solutions\<close>, Bull.
  AMS 27 (1992).  First ingredient: if the centre's maximum beats the
  boundary by more than a linear perturbation can recover, every
  maximizer of the perturbed function is interior, so a first-order
  condition is available.\<close>

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
    by (rule tendsto_lowerbound[OF lim ev]) simp
qed

text \<open>Second ingredient: at an interior maximizer of \<open>\<phi> + p \<cdot> (-)\<close>, the
  convexified \<open>\<psi> = \<phi> + (c/2) * (norm -)\<^sup>2\<close> has explicit subgradient
  \<open>c *\<^sub>R x - p\<close> --- no differentiability of \<open>\<phi>\<close> needed, since \<open>\<psi>\<close>'s
  subdifferential is nonempty by convexity and maximality forces its
  unique element.\<close>

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
        by (simp add: algebra_simps)
      have sq: "(norm (x + t *\<^sub>R v))\<^sup>2 - (norm x)\<^sup>2
          = 2*t*(x \<bullet> v) + t\<^sup>2 * (norm v)\<^sup>2"
      proof -
        have e1: "(norm (x + t *\<^sub>R v))\<^sup>2 = (x + t *\<^sub>R v) \<bullet> (x + t *\<^sub>R v)"
          by (rule power2_norm_eq_inner)
        have e2: "(norm x)\<^sup>2 = x \<bullet> x" by (rule power2_norm_eq_inner)
        have e3: "(norm v)\<^sup>2 = v \<bullet> v" by (rule power2_norm_eq_inner)
        have e4: "(x + t *\<^sub>R v) \<bullet> (x + t *\<^sub>R v)
            = x \<bullet> x + 2*t*(x \<bullet> v) + (t*t)*(v \<bullet> v)"
          by (simp add: inner_commute
              algebra_simps)
        show ?thesis unfolding e1 e4 e2 e3 by (simp add: power2_eq_square)
      qed
      have "t * (q \<bullet> v)
          \<le> - (t * (p \<bullet> v)) + (c/2) * (2*t*(x \<bullet> v) + t\<^sup>2 * (norm v)\<^sup>2)"
        using sd mx unfolding sq by linarith
      also have "\<dots> = t * ((c *\<^sub>R x - p) \<bullet> v + ((c/2) * (norm v)\<^sup>2) * t)"
        by (simp add: power2_eq_square algebra_simps)
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

text \<open>Third ingredient: at a maximizer of \<open>\<phi> + p \<cdot> (-)\<close>, \<open>\<psi>\<close> also
  satisfies the reverse (semiconcavity) inequality with the same vector,
  pinning its Bregman divergence at \<open>x\<close> between \<open>0\<close> and
  \<open>(c/2) * (norm (z - x))\<^sup>2\<close> --- the two-sided bound forcing the
  resolvent's derivative into \<open>[1/(1+c), 1]\<close>.\<close>

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
      by (simp add: inner_commute algebra_simps)
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

text \<open>A uniform interiority margin: bounding \<open>\<phi>\<close> on the whole annulus
  \<open>\<rho> \<le> dist y \<xi> \<le> r\<close>, not just the sphere, puts every maximizer
  strictly inside \<open>ball \<xi> \<rho>\<close>, keeping a common distance \<open>r - \<rho>\<close> from
  the boundary --- what makes the co-coercivity argument below
  localizable.\<close>

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

text \<open>Co-coercivity, localized: if \<open>\<psi>\<close> is convex with the semiconcave
  upper bound at \<open>x\<close> on \<open>cball \<xi> r\<close>, then for any step \<open>s\<close> with
  \<open>s * c \<le> 1\<close> keeping the test point in the ball,
  \<open>(s/2) * norm (q - q')\<^sup>2\<close> is dominated by the Bregman divergence; the
  textbook's optimal \<open>s = 1/c\<close> is replaced by a smaller \<open>s\<close> that keeps
  the test point inside \<open>cball \<xi> r\<close>.\<close>

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
    unfolding y_def by (simp add: algebra_simps)
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

text \<open>The reverse Baillon--Haddad implication, localized: adding the two
  co-coercivity estimates collapses the Bregman divergences into
  \<open>(q - q') \<cdot> (x - x')\<close>, and Cauchy--Schwarz bounds \<open>norm (q - q')\<close> by
  \<open>norm (x - x') / s\<close> --- a convex, \<open>c\<close>-semiconcave function on a ball
  has a Lipschitz selection of subgradients there.\<close>

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

text \<open>Routine set-up for Jensen's lemma: a semiconvex function is
  continuous (subtract the quadratic from the continuous convex \<open>\<psi>\<close>),
  so the perturbed function attains its maximum on the compact ball; a
  ball of positive radius is not negligible, which is the contradiction
  the argument runs into.\<close>

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

text \<open>Jensen's lemma: for a semiconvex \<open>\<phi>\<close> whose maximum over
  \<open>cball \<xi> r\<close> at the centre beats the surrounding annulus by more than
  the perturbation can recover, the set of points that maximize some
  small linear perturbation of \<open>\<phi>\<close> is not negligible.

  The usual proof estimates the measure from below by a Jacobian
  determinant, needing Hadamard's inequality or a spectral theorem,
  neither available in this HOL-Analysis.  Only positivity is used
  downstream, and that needs no determinants: the map
  \<open>P x = c *\<^sub>R x - grad \<psi> x\<close> is a genuine, Lipschitz function on \<open>K\<close>
  (its subdifferential is a singleton there, by
  \<open>interior_max_subdiff_unique\<close> and localized
  \<open>subdiff_lipschitz_of_semiconcave\<close>), and it maps \<open>K\<close> onto
  \<open>cball 0 d\<close>.  A negligible \<open>K\<close> would therefore have negligible image,
  yet that image contains a ball.\<close>

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
      unfolding P_def by (simp add: algebra_simps)
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


(*<*)
end
(*>*)
