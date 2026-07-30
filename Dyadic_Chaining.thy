section \<open>Deterministic dyadic chaining\<close>

text \<open>
  Plan step A4 (STATUS.md 25h), second tranche: the deterministic half of the
  Kolmogorov tightness argument. Given per-level bounds \<open>c j\<close> on the dyadic
  increments of a function at every level \<open>j \<ge> n\<close>, any two dyadic points at
  distance \<open>\<le> 1/2^n\<close> have images at distance \<open>\<le> c n + 2 * sum of the higher-level
  bounds\<close>. This is Klenke's step (21.8), but stated UNIFORMLY: the level \<open>n\<close> is a
  parameter, not an \<open>\<omega>\<close>-dependent quantity as in the AFP's Kolmogorov-Chentsov
  proof (whose constants depend on the sample point through \<open>n\<^sub>0\<close>, which is why
  that entry yields a modification but not the tail bound tightness needs).

  The argument: anchor each dyadic point \<open>u\<close> at every level \<open>j\<close> by
  \<open>\<lfloor>2^j u\<rfloor> / 2^j\<close>. Successive anchors differ by \<open>0\<close> or \<open>1/2^(j+1)\<close>, so the
  anchor chain from the point's own level down to level \<open>n\<close> telescopes into the
  sum of the per-level bounds; the two level-\<open>n\<close> anchors of points at distance
  \<open>\<le> 1/2^n\<close> are equal or adjacent.
\<close>

theory Dyadic_Chaining
  imports "Kolmogorov_Chentsov.Dyadic_Interval"
begin

subsection \<open>Floor anchor arithmetic\<close>

lemma floor_double_bounds:
  fixes y :: real
  shows "2 * \<lfloor>y\<rfloor> \<le> \<lfloor>2 * y\<rfloor>" and "\<lfloor>2 * y\<rfloor> \<le> 2 * \<lfloor>y\<rfloor> + 1"
proof -
  have le: "real_of_int \<lfloor>y\<rfloor> \<le> y" and lt: "y < real_of_int \<lfloor>y\<rfloor> + 1"
    using floor_correct[of y] by simp_all
  from le have "real_of_int (2 * \<lfloor>y\<rfloor>) \<le> 2 * y" by simp
  thus "2 * \<lfloor>y\<rfloor> \<le> \<lfloor>2 * y\<rfloor>" by (rule le_floor_iff[THEN iffD2])
  from lt have "2 * y < real_of_int (2 * \<lfloor>y\<rfloor> + 1) + 1" by linarith
  thus "\<lfloor>2 * y\<rfloor> \<le> 2 * \<lfloor>y\<rfloor> + 1" by (rule floor_le_iff[THEN iffD2])
qed

lemma anchor_succ_cases:
  fixes u :: real
  shows "\<lfloor>2 ^ Suc j * u\<rfloor> = 2 * \<lfloor>2 ^ j * u\<rfloor> \<or>
         \<lfloor>2 ^ Suc j * u\<rfloor> = 2 * \<lfloor>2 ^ j * u\<rfloor> + 1"
proof -
  have eq: "2 ^ Suc j * u = 2 * (2 ^ j * u)" by simp
  from floor_double_bounds[of "2 ^ j * u"] show ?thesis
    unfolding eq[symmetric] by linarith
qed

subsection \<open>Dyadic anchors\<close>

text \<open>
  The level-\<open>j\<close> anchor of \<open>u\<close> is the largest dyadic of denominator \<open>2^j\<close> below
  \<open>u\<close>. Successive anchors coincide or differ by exactly one level-\<open>Suc j\<close> step.
\<close>

abbreviation danchor :: "nat \<Rightarrow> real \<Rightarrow> real" where
  "danchor j u \<equiv> real_of_int \<lfloor>2 ^ j * u\<rfloor> / 2 ^ j"

lemma danchor_mem:
  "0 \<le> u \<Longrightarrow> u \<le> T \<Longrightarrow> danchor j u \<in> dyadic_interval_step j 0 T"
  by (rule dyadic_interval_step_mem) auto

lemma danchor_self:
  assumes "u \<in> dyadic_interval_step m 0 T"
  shows "danchor m u = u"
proof -
  from assms obtain k where k: "u = real_of_int k / 2 ^ m"
    using dyadic_interval_step_iff by blast
  hence "2 ^ m * u = real_of_int k" by simp
  thus ?thesis by (simp add: k)
qed

lemma danchor_le: "danchor j u \<le> u"
  by (simp add: floor_pow2_leq)

lemma danchor_gt: "u - 1 / 2 ^ j < danchor j u"
proof -
  have "2 ^ j * u < real_of_int \<lfloor>2 ^ j * u\<rfloor> + 1"
    using floor_correct[of "2 ^ j * u"] by simp
  hence "(2 ^ j * u - 1) / 2 ^ j < danchor j u"
    by (intro divide_strict_right_mono) simp_all
  thus ?thesis by (simp add: field_simps)
qed

lemma danchor_nonneg: "0 \<le> u \<Longrightarrow> 0 \<le> danchor j u"
  by simp

subsection \<open>The chaining step and the anchor chain\<close>

lemma anchor_chain_step:
  fixes f :: "real \<Rightarrow> 'b::metric_space"
  assumes u0: "0 \<le> u" and uT: "u \<le> T"
    and H: "\<And>k. k \<in> {1..\<lfloor>2 ^ Suc j * T\<rfloor>} \<Longrightarrow>
            dist (f (real_of_int (k - 1) / 2 ^ Suc j))
                 (f (real_of_int k / 2 ^ Suc j)) \<le> c"
    and c0: "0 \<le> c"
  shows "dist (f (danchor j u)) (f (danchor (Suc j) u)) \<le> c"
proof (cases rule: disjE[OF anchor_succ_cases[of j u]])
  case 1
  have "danchor (Suc j) u = danchor j u"
    unfolding 1 by simp
  thus ?thesis by (simp add: c0)
next
  case 2
  let ?k = "\<lfloor>2 ^ Suc j * u\<rfloor>"
  have prev: "real_of_int (?k - 1) / 2 ^ Suc j = danchor j u"
    unfolding 2 by simp
  have k1: "1 \<le> ?k"
    unfolding 2 using u0 by simp
  have kT: "?k \<le> \<lfloor>2 ^ Suc j * T\<rfloor>"
    by (intro floor_mono mult_left_mono uT) simp
  show ?thesis
    using H[of ?k] k1 kT unfolding prev by simp
qed

lemma anchor_chain:
  fixes f :: "real \<Rightarrow> 'b::metric_space" and c :: "nat \<Rightarrow> real"
  assumes u0: "0 \<le> u" and uT: "u \<le> T"
    and H: "\<And>j k. n < j \<Longrightarrow> j \<le> m \<Longrightarrow> k \<in> {1..\<lfloor>2 ^ j * T\<rfloor>} \<Longrightarrow>
            dist (f (real_of_int (k - 1) / 2 ^ j)) (f (real_of_int k / 2 ^ j)) \<le> c j"
    and c0: "\<And>j. 0 \<le> c j"
    and nm: "n \<le> m"
  shows "dist (f (danchor n u)) (f (danchor m u)) \<le> (\<Sum>j\<in>{n<..m}. c j)"
  using nm H
proof (induction m)
  case 0
  hence "n = 0" by simp
  thus ?case by simp
next
  case (Suc m)
  show ?case
  proof (cases "n = Suc m")
    case True
    thus ?thesis by simp
  next
    case False
    with Suc.prems(1) have nm: "n \<le> m" by simp
    have IH: "dist (f (danchor n u)) (f (danchor m u)) \<le> (\<Sum>j\<in>{n<..m}. c j)"
      by (rule Suc.IH[OF nm]) (rule Suc.prems(2), simp_all)
    have step: "dist (f (danchor m u)) (f (danchor (Suc m) u)) \<le> c (Suc m)"
      by (rule anchor_chain_step[OF u0 uT _ c0])
         (rule Suc.prems(2), insert nm, simp_all)
    have "dist (f (danchor n u)) (f (danchor (Suc m) u))
        \<le> dist (f (danchor n u)) (f (danchor m u))
          + dist (f (danchor m u)) (f (danchor (Suc m) u))"
      by (rule dist_triangle)
    also have "\<dots> \<le> (\<Sum>j\<in>{n<..m}. c j) + c (Suc m)"
      using IH step by (rule add_mono)
    also have "\<dots> = (\<Sum>j\<in>{n<..Suc m}. c j)"
    proof -
      have "{n<..Suc m} = insert (Suc m) {n<..m}"
        using nm by auto
      thus ?thesis by simp
    qed
    finally show ?thesis .
  qed
qed

subsection \<open>The chaining bound\<close>

lemma anchor_gap:
  fixes u v :: real
  assumes u0: "0 \<le> u" and uv: "u \<le> v" and gap: "v - u \<le> 1 / 2 ^ n"
  shows "\<lfloor>2 ^ n * v\<rfloor> = \<lfloor>2 ^ n * u\<rfloor> \<or> \<lfloor>2 ^ n * v\<rfloor> = \<lfloor>2 ^ n * u\<rfloor> + 1"
proof -
  have lo: "\<lfloor>2 ^ n * u\<rfloor> \<le> \<lfloor>2 ^ n * v\<rfloor>"
    by (intro floor_mono mult_left_mono uv) simp
  have "2 ^ n * v - 2 ^ n * u = 2 ^ n * (v - u)" by (simp add: algebra_simps)
  also have "\<dots> \<le> 2 ^ n * (1 / 2 ^ n)"
    by (intro mult_left_mono gap) simp
  also have "\<dots> = 1" by simp
  finally have "2 ^ n * v \<le> 2 ^ n * u + 1" by linarith
  hence "\<lfloor>2 ^ n * v\<rfloor> \<le> \<lfloor>2 ^ n * u + 1\<rfloor>" by (rule floor_mono)
  hence hi: "\<lfloor>2 ^ n * v\<rfloor> \<le> \<lfloor>2 ^ n * u\<rfloor> + 1" by simp
  from lo hi show ?thesis by linarith
qed

theorem dyadic_chaining:
  fixes f :: "real \<Rightarrow> 'b::metric_space" and c :: "nat \<Rightarrow> real"
  assumes u: "u \<in> dyadic_interval_step m 0 T" and v: "v \<in> dyadic_interval_step m 0 T"
    and gap: "\<bar>u - v\<bar> \<le> 1 / 2 ^ n"
    and nm: "n \<le> m"
    and H: "\<And>j k. n \<le> j \<Longrightarrow> j \<le> m \<Longrightarrow> k \<in> {1..\<lfloor>2 ^ j * T\<rfloor>} \<Longrightarrow>
            dist (f (real_of_int (k - 1) / 2 ^ j)) (f (real_of_int k / 2 ^ j)) \<le> c j"
    and c0: "\<And>j. 0 \<le> c j"
  shows "dist (f u) (f v) \<le> c n + 2 * (\<Sum>j\<in>{n<..m}. c j)"
proof -
  have main: "dist (f u) (f v) \<le> c n + 2 * (\<Sum>j\<in>{n<..m}. c j)"
    if u: "u \<in> dyadic_interval_step m 0 T" and v: "v \<in> dyadic_interval_step m 0 T"
      and uv: "u \<le> v" and gap: "v - u \<le> 1 / 2 ^ n" for u v
  proof -
    have u0: "0 \<le> u" using dyadic_step_geq[OF u] by simp
    have uT: "u \<le> T" by (rule dyadic_step_leq[OF u])
    have v0: "0 \<le> v" using dyadic_step_geq[OF v] by simp
    have vT: "v \<le> T" by (rule dyadic_step_leq[OF v])
    have chainH: "dist (f (real_of_int (k - 1) / 2 ^ j)) (f (real_of_int k / 2 ^ j)) \<le> c j"
      if "n < j" "j \<le> m" "k \<in> {1..\<lfloor>2 ^ j * T\<rfloor>}" for j k
      using that by (intro H) simp_all
    have cu: "dist (f u) (f (danchor n u)) \<le> (\<Sum>j\<in>{n<..m}. c j)"
    proof -
      have "dist (f (danchor n u)) (f (danchor m u)) \<le> (\<Sum>j\<in>{n<..m}. c j)"
        by (rule anchor_chain[where f=f and c=c, OF u0 uT chainH c0 nm])
      thus ?thesis unfolding danchor_self[OF u] by (simp add: dist_commute)
    qed
    have cv: "dist (f (danchor n v)) (f v) \<le> (\<Sum>j\<in>{n<..m}. c j)"
    proof -
      have "dist (f (danchor n v)) (f (danchor m v)) \<le> (\<Sum>j\<in>{n<..m}. c j)"
        by (rule anchor_chain[where f=f and c=c, OF v0 vT chainH c0 nm])
      thus ?thesis unfolding danchor_self[OF v] .
    qed
    have mid: "dist (f (danchor n u)) (f (danchor n v)) \<le> c n"
    proof (cases rule: disjE[OF anchor_gap[OF u0 uv gap]])
      case 1
      have "danchor n v = danchor n u" unfolding 1 by simp
      thus ?thesis by (simp add: c0)
    next
      case 2
      let ?k = "\<lfloor>2 ^ n * v\<rfloor>"
      have prev: "real_of_int (?k - 1) / 2 ^ n = danchor n u"
        unfolding 2 by simp
      have k1: "1 \<le> ?k"
        unfolding 2 using u0 by simp
      have kT: "?k \<le> \<lfloor>2 ^ n * T\<rfloor>"
        by (intro floor_mono mult_left_mono vT) simp
      show ?thesis
        using H[of n ?k] k1 kT nm unfolding prev by simp
    qed
    have tri: "dist (f u) (f v) \<le> dist (f u) (f (danchor n u))
          + (dist (f (danchor n u)) (f (danchor n v)) + dist (f (danchor n v)) (f v))"
      using dist_triangle[of "f u" "f v" "f (danchor n u)"]
            dist_triangle[of "f (danchor n u)" "f v" "f (danchor n v)"]
      by linarith
    from tri cu mid cv show ?thesis by linarith
  qed
  from gap have g1: "u - v \<le> 1 / 2 ^ n" and g2: "v - u \<le> 1 / 2 ^ n"
    by linarith+
  show ?thesis
  proof (cases "u \<le> v")
    case True
    from main[OF u v True g2] show ?thesis .
  next
    case False
    hence "v \<le> u" by simp
    from main[OF v u this g1] show ?thesis by (simp add: dist_commute)
  qed
qed

subsection \<open>Extension from the dyadics to the interval by continuity\<close>

text \<open>
  The consumer applies the chaining bound to a continuous path known to have
  small dyadic increments at all levels \<open>\<ge> n\<close>. The dyadic bound extends to ALL
  pairs in \<open>{0..T}\<close> at distance strictly below \<open>1/2^n\<close>: approximate both points
  by their anchors, whose mutual distance eventually stays below \<open>1/2^n\<close>, and
  pass to the limit. The strictness of the gap hypothesis is what absorbs the
  anchor approximation error.
\<close>

lemma dyadic_modulus_extension:
  fixes f :: "real \<Rightarrow> 'b::metric_space" and K :: real
  assumes cont: "continuous_on {0..T} f"
    and K: "\<And>m w z. w \<in> dyadic_interval_step m 0 T \<Longrightarrow> z \<in> dyadic_interval_step m 0 T \<Longrightarrow>
              \<bar>w - z\<bar> \<le> 1 / 2 ^ n \<Longrightarrow> dist (f w) (f z) \<le> K"
    and u: "u \<in> {0..T}" and v: "v \<in> {0..T}"
    and gap: "\<bar>u - v\<bar> < 1 / 2 ^ n"
  shows "dist (f u) (f v) \<le> K"
proof -
  have u0: "0 \<le> u" and uT: "u \<le> T" using u by simp_all
  have v0: "0 \<le> v" and vT: "v \<le> T" using v by simp_all
  have umem: "danchor m u \<in> {0..T}" for m
    using danchor_nonneg[OF u0] danchor_le[of m u] uT by (auto intro: order_trans)
  have vmem: "danchor m v \<in> {0..T}" for m
    using danchor_nonneg[OF v0] danchor_le[of m v] vT by (auto intro: order_trans)
  have ulim: "(\<lambda>m. danchor m u) \<longlonglongrightarrow> u" by (rule floor_pow2_lim)
  have vlim: "(\<lambda>m. danchor m v) \<longlonglongrightarrow> v" by (rule floor_pow2_lim)
  have flim: "(\<lambda>m. dist (f (danchor m u)) (f (danchor m v))) \<longlonglongrightarrow> dist (f u) (f v)"
  proof (intro tendsto_dist)
    show "(\<lambda>m. f (danchor m u)) \<longlonglongrightarrow> f u"
      by (rule continuous_on_tendsto_compose[OF cont ulim]) (use u umem in auto)
    show "(\<lambda>m. f (danchor m v)) \<longlonglongrightarrow> f v"
      by (rule continuous_on_tendsto_compose[OF cont vlim]) (use v vmem in auto)
  qed
  have small: "eventually (\<lambda>m. (2::real) / 2 ^ m \<le> 1 / 2 ^ n - \<bar>u - v\<bar>) sequentially"
  proof -
    have lim2: "(\<lambda>m. (2::real) / 2 ^ m) \<longlonglongrightarrow> 0"
      by (intro LIMSEQ_divide_realpow_zero) simp_all
    have "eventually (\<lambda>m. (2::real) / 2 ^ m < 1 / 2 ^ n - \<bar>u - v\<bar>) sequentially"
      by (rule order_tendstoD(2)[OF lim2]) (use gap in simp)
    thus ?thesis by (rule eventually_mono) simp
  qed
  have bnd: "eventually (\<lambda>m. dist (f (danchor m u)) (f (danchor m v)) \<le> K) sequentially"
    using small
  proof (rule eventually_mono)
    fix m assume sm: "(2::real) / 2 ^ m \<le> 1 / 2 ^ n - \<bar>u - v\<bar>"
    have pos: "0 < (1::real) / 2 ^ m" by simp
    have du: "\<bar>danchor m u - u\<bar> \<le> 1 / 2 ^ m"
      unfolding abs_diff_le_iff using danchor_le[of m u] danchor_gt[of u m] pos
      by (intro conjI) linarith+
    have dv: "\<bar>v - danchor m v\<bar> \<le> 1 / 2 ^ m"
      unfolding abs_diff_le_iff using danchor_le[of m v] danchor_gt[of v m] pos
      by (intro conjI) linarith+
    have t1: "\<bar>danchor m u - danchor m v\<bar> \<le> \<bar>danchor m u - u\<bar> + \<bar>u - danchor m v\<bar>"
      using abs_triangle_ineq[of "danchor m u - u" "u - danchor m v"] by simp
    have t2: "\<bar>u - danchor m v\<bar> \<le> \<bar>u - v\<bar> + \<bar>v - danchor m v\<bar>"
      using abs_triangle_ineq[of "u - v" "v - danchor m v"] by simp
    have gapm: "\<bar>danchor m u - danchor m v\<bar> \<le> 1 / 2 ^ n"
      using sm du dv t1 t2 by linarith
    show "dist (f (danchor m u)) (f (danchor m v)) \<le> K"
      by (rule K[OF danchor_mem[OF u0 uT] danchor_mem[OF v0 vT] gapm])
  qed
  show ?thesis
    by (rule tendsto_upperbound[OF flim bnd]) simp
qed

end
