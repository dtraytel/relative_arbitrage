section \<open>Rademacher's theorem\<close>

(*<*)
theory Rademacher
  imports Convex_Subgradients
begin

(*>*)

subsection \<open>Rademacher, dimension one\<close>

text \<open>The development of Rademacher's and Alexandrov's theorems below
  follows Evans--Gariepy, \<^emph>\<open>Measure Theory and Fine Properties of
  Functions\<close>.  A Lipschitz function on the line is differentiable a.e.
  (\<open>Lebesgue_differentiation_thm\<close>); the codomain may be any Euclidean
  space, needed for the resolvent later.\<close>

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

text \<open>Sections of a Lipschitz map along any line are Lipschitz curves,
  differentiable a.e. --- the slicing input to Rademacher's Fubini step.\<close>

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

text \<open>The set of points where the difference quotient along a fixed
  direction converges is Borel.\<close>

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

text \<open>A Borel set with all lines in a fixed basis direction negligible is
  itself negligible, by Fubini for \<open>lborel\<close>; Borel-ness is essential.\<close>

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

text \<open>A differentiable curve has a difference-quotient limit: the
  derivative applied to \<open>1\<close>.\<close>

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

text \<open>Arbitrary directions reduce to the basis-direction case via an
  orthogonal map carrying \<open>v \<noteq> 0\<close> to a scaled basis vector.\<close>

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

text \<open>The directional derivative is named by the sequential limit along
  \<open>t = 1/(n+1)\<close>, so measurability follows from
  \<open>borel_measurable_lim_metric\<close>.\<close>

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

text \<open>The Lipschitz bound passes to the derivative, \<open>|D_v f| \<le> B |v|\<close>,
  making \<open>ddir\<close> integrable on boxes.\<close>

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

text \<open>On a line, a Lipschitz function is absolutely continuous with a.e.
  derivative \<open>ddir\<close>, so the fundamental theorem of calculus recovers
  increments of \<open>f\<close> as integrals of \<open>ddir\<close>.\<close>

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

text \<open>The direction map \<open>v \<mapsto> D_v f x\<close> is positively homogeneous and
  Lipschitz in \<open>v\<close> with the same constant as \<open>f\<close>, before linearity is
  known.\<close>

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

text \<open>A countable family of directions is handled simultaneously, since a
  countable union of negligible sets is negligible.\<close>

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

text \<open>The last step of Rademacher's theorem: directional derivatives along
  a dense set of directions that agree with a bounded linear map extend
  to Fr\'echet differentiability, by compactness of the unit sphere.\<close>

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

text \<open>An exact split of the \<open>(u+v)\<close>-quotient into a \<open>u\<close>-quotient at \<open>x\<close>
  and a \<open>v\<close>-quotient at \<open>x + t u\<close>, the latter converging to
  \<open>D_v f x\<close> only after integration.\<close>

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

text \<open>A box and its small translate overlap in almost all of their volume;
  \<open>Int_interval\<close> keeps the overlap a box, giving an explicit content
  formula.\<close>

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

text \<open>A bounded Borel function with vanishing integral over every open box
  vanishes a.e., since \<open>g\<^sup>+\<close> and \<open>g\<^sup>-\<close> agree as measures on the generator
  of boxes.\<close>

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

text \<open>Two facts for the dominated-convergence step below: the difference
  quotients are uniformly bounded and Borel measurable in \<open>x\<close> for fixed
  \<open>t\<close>.\<close>

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

text \<open>Since \<open>ddir\<close> is the limit along \<open>t = 1/(n+1)\<close>, dominated
  convergence applies directly, bounded by \<open>B |v|\<close>.\<close>

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

text \<open>The shifted quotient integrates over a shifted box, by translation
  invariance of Lebesgue measure.\<close>

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

text \<open>Integrating the algebraic split over a box gives an exact identity:
  the \<open>(u+v)\<close>-quotient equals the \<open>v\<close>-quotient over the translated box
  plus the \<open>u\<close>-quotient over the original.\<close>

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

text \<open>The quotients converge to \<open>ddir\<close> in L1, not merely pointwise a.e.,
  letting the domain wobble by \<open>t u\<close>.\<close>

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

text \<open>Translating a box preserves its content, so the overlap defect
  \<open>2(content B - content (B \<inter> (B+w)))\<close> tends to \<open>0\<close>.\<close>

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
text \<open>Two building blocks for the moving-domain bound: integrability on a
  finite-measure set, and the symmetric-difference indicator integral.\<close>

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

text \<open>The moving-domain bound: swapping the domain of integration changes
  the integral of a bounded function by at most the bound times the
  symmetric difference's measure.\<close>

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

text \<open>Integrals over an open box and its closure agree (negligible
  frontier), and the defect along \<open>w\<^sub>n = u/(n+1)\<close> tends to zero.\<close>

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

text \<open>The quotient integrated over the translated box still converges to
  the integral of \<open>ddir\<close> over the original, the error splitting into a
  domain part and an ordinary dominated-convergence part.\<close>

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

text \<open>Passing to the limit in \<open>box_integral_add_split\<close> gives additivity
  of the box integrals of \<open>ddir\<close> itself.\<close>

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

text \<open>Bridges the Bochner and ennreal statements: an integrable function
  with vanishing integral has equal positive and negative parts.\<close>

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

subsection \<open>Almost-everywhere additivity in the direction\<close>

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

text \<open>The direction map of a Lipschitz function is additive a.e.: every
  box integral of the defect vanishes and boxes generate the Borel sets.\<close>

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

text \<open>The candidate derivative at a good point is the linear map from the
  directional derivatives along the basis vectors; agreement with
  \<open>ddir\<close> on a dense set of directions remains.\<close>

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

text \<open>Rational combinations of the basis are countable and dense, by
  \<open>norm_le_l1\<close>.\<close>

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

text \<open>\<open>AE_ball_countable\<close> collapses the countably many a.e. statements
  --- existence, additivity, homogeneity along rational directions ---
  into one.\<close>

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

text \<open>A partial basis combination has the expected coordinates and
  vanishes only if all coefficients do, keeping induction sums nonzero.\<close>

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

text \<open>The induction needs its partial sums, and the basis vectors
  themselves, to be legitimate rational directions.\<close>

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

text \<open>The induction turning pairwise additivity and homogeneity into the
  full coordinate formula, skipping zero coefficients to keep sums
  nonzero.\<close>

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

text \<open>Rademacher's theorem: a Lipschitz function on a Euclidean space is
  differentiable a.e.  Directional derivatives along dense rational
  directions, depending linearly on them, extend by density to Fr\'echet
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

text \<open>Alexandrov's theorem differentiates the resolvent
  \<open>\<real>\<^sup>n \<rightarrow> \<real>\<^sup>n\<close>, so Rademacher is lifted componentwise to vector-valued
  maps.\<close>

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


(*<*)
end
(*>*)
