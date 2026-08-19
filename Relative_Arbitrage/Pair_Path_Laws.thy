section \<open>Families of pair path laws, and their limits\<close>

(*<*)
theory Pair_Path_Laws
  imports Pair_Path_Space
begin

(*>*)

text \<open>Laws of pair paths as a family: the second-moment bounds that make a
  family tight, the compactness of the family of laws under those bounds, the
  Brownian continuation on the half-line, and the transfer of the exit
  functional to a limit law.\<close>


text \<open>The single obligation of \<open>vshift_sup_usc_of_seq_compact\<close> asks for a
  family of laws in which every sequence has a weakly convergent
  subsequence with limit in the family. Lemma 2.2
  (\<open>market_path_laws_convergent_subsequence\<close>) provides the subsequence
  for market path laws; Lemma 2.3 must put the limit back. The family
  below does this definitionally, as the weak closure of the market path
  laws: sequential compactness of the closure needs only extraction on
  the base set and metrizability of the weak topology
  (\<open>seq_compact_closure_of\<close>), and every closure point is a probability
  measure with the right \<open>sets\<close> since total mass survives weak limits.

  Identifying \<open>Sup (vshift T A x ` mkt_law_closure \<dots>)\<close> with the
  market-form value function \<open>val_fn\<close> is the pushforward analysis of
  Larsson--Ruf Prop. 2.2. The theorem at the end of this section gives
  clause (1) of Theorem 1.1 for the law-level value function of the
  closure, with no compactness hypothesis left.\<close>

lemma psd_mat_1: "psd (mat 1 :: real^'n::finite^'n)"
  unfolding psd_def
proof (intro conjI allI)
  show "transpose (mat 1 :: real^'n^'n) = mat 1"
    by simp
  fix x :: "real^'n"
  show "0 \<le> x \<bullet> (mat 1 *v x)"
    by simp
qed

lemma comp_shift_split:
  fixes x v :: "real^'n::finite" and w :: "real^'n^'n"
  shows "outerp x + ((outerp v - w) + (\<chi> i j. x $ i * v $ j + v $ i * x $ j))
       = outerp (x + v) - w"
  by (simp add: outerp_def vec_eq_iff algebra_simps)

text \<open>\<open>bounded_linear_cross\<close> lives in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>

lemma continuous_on_iglue:
  fixes \<omega> \<omega>' :: "(real \<Rightarrow> 'a::real_normed_vector \<times> 'b::real_normed_vector)"
  assumes r: "0 \<le> r"
    and c1: "continuous_on {0..r} \<omega>"
    and c2: "continuous_on {0..} \<omega>'"
  shows "continuous_on {0..}
      (\<lambda>t. if t \<le> r then \<omega> t else \<omega> r + (\<omega>' (t - r) - \<omega>' 0))"
proof -
  let ?f = "\<lambda>t. if t \<le> r then \<omega> t else \<omega> r + (\<omega>' (t - r) - \<omega>' 0)"
  have U: "{0..} = {0..r} \<union> {r..}" using r by auto
  have A: "continuous_on {0..r} ?f"
    by (rule continuous_on_eq[OF c1]) simp
  have B: "continuous_on {r..} ?f"
  proof (rule continuous_on_eq)
    have "continuous_on {r..} (\<lambda>t. \<omega>' (t - r))"
      by (rule continuous_on_compose2[OF c2 continuous_on_diff
            [OF continuous_on_id continuous_on_const]]) auto
    then show "continuous_on {r..} (\<lambda>t. \<omega> r + (\<omega>' (t - r) - \<omega>' 0))"
      by (intro continuous_intros)
  next
    fix t :: real assume "t \<in> {r..}"
    then show "\<omega> r + (\<omega>' (t - r) - \<omega>' 0) = ?f t" by (cases "t = r") auto
  qed
  show ?thesis unfolding U by (rule continuous_on_closed_Un[OF _ _ A B]) auto
qed

subsection \<open>The Brownian continuation on the half-line\<close>

text \<open>The witness of \<open>bmpair_law_in_paper_pair_class\<close> without
  the horizon cap: Brownian motion paired with the covariation \<open>Y\<^sub>t = t \<sqdot> I\<close>.
  Cutting it at \<open>S\<close> returns \<open>bmpair\<close> exactly, so every restriction of
  its law is the horizon-\<open>S\<close> witness and lies in the class.\<close>

definition acont :: "(real \<Rightarrow> real^'n::finite^'n) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real^'n^'n"
  where "acont a tv s = (if s \<le> tv then a s else mat 1)"

text \<open>Time-measurability is inherited by the continuation: the locale
  assumption \<open>acov_time_measurable\<close> is stated on the nonnegative axis
  only, matching (1.7)'s "a.e. \<open>t \<ge> 0\<close>", and nothing more is available
  since for \<open>u < 0 \<le> tv\<close> the continuation still reads \<open>a u\<close>.

  A trap: \<open>lborel\<close> is polymorphic and \<^typ>\<open>real^'n^'n\<close> carries
  an \<^class>\<open>ord\<close> instance, so an unannotated binder in
  \<open>(\<lambda>u. \<dots>) \<in> borel_measurable lborel\<close> can silently elaborate at the
  matrix type instead of \<open>real\<close>. Pin \<open>lborel :: real measure\<close> and
  annotate every binder.\<close>

lemma pair_test_integrable:
  fixes N :: "('n::finite pairpath) measure" and h :: "('n pairpath) \<Rightarrow> real"
  assumes P: "prob_space N"
    and setsN: "sets N = sets (path_borel T :: ('n pairpath) measure)"
    and st: "0 \<le> s" and ts: "s \<le> t" and tT: "t \<le> T"
    and hc: "continuous_map
        (mtopology_of (path_metric s :: ('n pairpath) metric)) euclideanreal h"
    and hb: "\<And>g. \<bar>h g\<bar> \<le> B"
    and C0: "0 \<le> C"
    and Cs: "(\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> s) $ i)\<^sup>2) \<partial>N) \<le> ennreal C"
    and Ct: "(\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> t) $ i)\<^sup>2) \<partial>N) \<le> ennreal C"
  shows "integrable N
      (\<lambda>\<omega>. h (restrict \<omega> {0..s}) * (fst (\<omega> t) $ i - fst (\<omega> s) $ i))"
proof -
  have fm: "finite_measure N" using P by (simp add: prob_space_def)
  show ?thesis
    by (rule integrable_of_sq_integrable[OF fm
          pair_test_measurable[OF setsN st ts tT hc]
          pair_test_sq_bound(1)[OF P setsN st ts tT hc hb C0 Cs Ct]])
qed

subsection \<open>A second-moment bound in nn-integral form\<close>

lemma acont_set_borel_measurable:
  fixes a :: "real \<Rightarrow> real^'n::finite^'n"
  assumes a: "set_borel_measurable lborel {0..} a"
  shows "set_borel_measurable lborel {0..} (acont a tv)"
proof -
  have "(\<lambda>u::real. indicat_real {0..} u *\<^sub>R acont a tv u)
      = (\<lambda>u::real. if u \<le> tv then indicat_real {0..} u *\<^sub>R a u
             else (if u < 0 then 0 else (mat 1 :: real^'n^'n)))"
    by (rule ext) (simp add: acont_def)
  moreover have "(\<lambda>u::real. if u \<le> tv then indicat_real {0..} u *\<^sub>R a u
             else (if u < 0 then 0 else (mat 1 :: real^'n^'n)))
      \<in> borel_measurable (lborel :: real measure)"
  proof (rule measurable_If)
    show "(\<lambda>u::real. indicat_real {0..} u *\<^sub>R a u)
        \<in> borel_measurable (lborel :: real measure)"
      using a unfolding set_borel_measurable_def .
    \<comment> \<open>the \<^verbatim>\<open>if u < 0\<close> form, not an indicator: the \<open>measurable\<close>
        method reduces the branch condition to \<open>open {..<0}\<close>, whereas the
        indicator form leaves the FALSE goal \<open>open {0..}\<close>.\<close>
    show "(\<lambda>u::real. if u < 0 then 0 else (mat 1 :: real^'n^'n))
        \<in> borel_measurable (lborel :: real measure)"
      by measurable
    show "{u \<in> space (lborel :: real measure). u \<le> tv} \<in> sets lborel"
      by simp
  qed
  ultimately show ?thesis unfolding set_borel_measurable_def by simp
qed

text \<open>Hence the continued volatility has all its difference quotients in the
  constraint set --- which is exactly the covariation condition of
  \<open>exit_class\<close>, holding for every \<open>0 \<le> s < t\<close> with no stopping
  caveat, as (1.7) demands.\<close>

subsection \<open>The running covariation built from a continued volatility\<close>

text \<open>The volatility side of the bridge: \<open>Yint a t = \<integral>₀ᵗ a\<close> starts at
  \<open>0\<close>, has increments given by interval integrals, and --- for the
  continued density --- difference quotients in the constraint set for every
  \<open>0 \<le> s < t\<close>: the covariation half of \<open>exit_class\<close>.\<close>

lemma path_eval_measurable_natural_filtration':
  fixes U u v :: real
  assumes v: "v \<in> {0..u}"
  shows "(\<lambda>\<omega> :: (real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector}). \<omega> v) \<in> borel_measurable (natural_filtration
      (path_borel U :: ((real \<Rightarrow> 'a \<times> 'b)) measure)
      0 (\<lambda>v \<omega>. \<omega> v) u)"
  unfolding natural_filtration_def
  by (rule measurable_family_vimage_algebra) (use v in auto)

lemma pair_law_limit_sq_nn_bound:
  fixes Qm :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and Q :: "('n pairpath) measure"
  assumes wc: "weak_conv_on Qm Q sequentially
      (mtopology_of (path_metric T :: ('n pairpath) metric))"
    and u: "u \<in> {0..T}" and C0: "0 \<le> C"
    and bnd: "\<And>m. (\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> u) $ i)\<^sup>2) \<partial>(Qm m)) \<le> ennreal C"
  shows "(\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> u) $ i)\<^sup>2) \<partial>Q) \<le> ennreal C"
  by (rule weak_conv_on_nn_integral_le
      [OF wc pair_eval_coord_sq_cont[OF u] _ C0 bnd]) simp

subsection \<open>The martingale identity passes to the weak limit\<close>

lemma cols_mult_transpose:
  fixes w :: "'m::finite \<Rightarrow> real^'n::finite"
  shows "(\<chi> i j. w j $ i) ** transpose (\<chi> i j. w j $ i)
       = (\<Sum>j\<in>UNIV. outerp (w j))"
proof -
  have "((\<chi> i j. w j $ i) ** transpose (\<chi> i j. w j $ i)) $ i $ l
      = (\<Sum>j\<in>UNIV. w j $ i * w j $ l)" for i l
    by (simp add: matrix_matrix_mult_def transpose_def)
  moreover have "(\<Sum>j\<in>UNIV. outerp (w j)) $ i $ l
      = (\<Sum>j\<in>UNIV. w j $ i * w j $ l)" for i l
    by (induction "UNIV :: 'm set" rule: infinite_finite_induct)
      (simp_all add: outerp_def)
  ultimately show ?thesis by (simp add: vec_eq_iff)
qed

text \<open>\<open>exists_enum_of_card\<close> lives in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


subsection \<open>Continuity of the Gaussian member in its volatility\<close>

text \<open>\<open>dist_pair_le\<close> lives in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

lemma trace_outerp_mult:
  fixes B :: "real^'n::finite^'n" and v :: "real^'n"
  shows "trace (outerp v ** B) = v \<bullet> (B *v v)"
  by (subst trace_mul_sym) (rule trace_mult_outerp)

lemma quadform_outerp:
  fixes q z :: "real^'n::finite"
  shows "z \<bullet> (outerp q *v z) = (q \<bullet> z)\<^sup>2"
  by (simp add: outerp_eq_outer_prod power2_eq_square inner_commute)

section \<open>The relaxed operator, and the inequality the class really gives\<close>

text \<open>Eq. (1.9) takes its infimum over \<open>feasible\<close>, which carries the
  orthogonality constraint \<open>a *v p = 0\<close> on top of the spectral bounds; the
  class of (1.7) carries no such constraint, its covariation directions
  living in \<open>sconstraint\<close>.  The two are related in one direction,

    \<open>feasible\<close> \<open>k L p\<close> \<open>\<subseteq>\<close> \<open>sconstraint\<close> \<open>k L\<close>

  (\<open>suff_volatile_cap_in_sconstraint\<close>), so the infimum over
  the larger set is smaller: \<open>ell_op_s \<le> ell_op\<close>.  Naming the relaxed
  operator keeps the missing ingredient --- orthogonality of the optimal
  direction to the gradient --- visible instead of buried.\<close>

definition Yint :: "(real \<Rightarrow> real^'n::finite^'n) \<Rightarrow> real \<Rightarrow> real^'n^'n"
  where "Yint a t = set_lebesgue_integral lborel {0..t} a"

subsection \<open>What a second-moment bound gives the tightness argument\<close>

text \<open>The \<open>Y\<close>-side of the pair tightness costs nothing: the class's
  difference quotients lie a.s. in \<open>sconstraint k L\<close>, whose elements have
  norm at most \<open>n\<sqdot>L\<close> (\<open>sconstraint_norm_le\<close>), so \<open>diffquot_lipschitz\<close>
  makes \<open>Y\<close> a.s. \<open>n\<sqdot>L\<close>-Lipschitz --- the \<open>Y\<close>-event of
  \<open>pair_holder_charge_split\<close> with probability one, leaving only the
  \<open>X\<close>-side Hoelder estimate.\<close>

lemma nonbinding_horizon_ex:
  fixes rK :: real
  assumes k: "k < CARD('n::finite)"
  shows "\<exists>T :: real. 0 < T \<and> rK * rK / real (CARD('n) - k) < T
       \<and> 2 * (rK * rK) / real (CARD('n) - k) < T"
proof -
  have nk: "0 < real (CARD('n) - k)" using k by simp
  define B :: real where "B = 2 * (rK * rK) / real (CARD('n) - k)"
  have B0: "0 \<le> B" unfolding B_def using nk by simp
  have le: "rK * rK / real (CARD('n) - k) \<le> B"
    unfolding B_def using nk by (intro divide_right_mono) auto
  show ?thesis
  proof (intro exI[of _ "B + 1"] conjI)
    show "0 < B + 1" using B0 by simp
    show "rK * rK / real (CARD('n) - k) < B + 1" using le by simp
    show "2 * (rK * rK) / real (CARD('n) - k) < B + 1"
      unfolding B_def[symmetric] by simp
  qed
qed

text \<open>\<^bold>\<open>Clause (0): finiteness.\<close>\<close>

lemma restrict_in_mspace:
  fixes \<omega> :: "(real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})"
  assumes st: "0 \<le> s" and sT: "s \<le> T"
    and w: "\<omega> \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
  shows "restrict \<omega> {0..s} \<in> mspace (path_metric s :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
proof -
  have "(\<lambda>f :: (real \<Rightarrow> 'a \<times> 'b). restrict f {0..s})
      \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)
        \<rightarrow> mspace (path_metric s :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    using Lipschitz_restrict_path_metric[OF st sT]
    unfolding Lipschitz_continuous_map_def by blast
  then show ?thesis using w by blast
qed

lemma nat_filt_eval:
  fixes Q :: "((real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})) measure"
  assumes b: "0 \<le> b" and ba: "b \<le> a"
  shows "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> b)
      \<in> natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v) a \<rightarrow>\<^sub>M borel"
  unfolding natural_filtration_def
  by (rule measurable_family_vimage_algebra) (use b ba in auto)

lemma standard_borel_path_metric:
  "standard_borel (path_borel U :: ((real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})) measure)"
  unfolding standard_borel_def
  by (intro exI[of _ "mtopology_of (path_metric U :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"]
      conjI Polish_space_path_metric refl)

lemma mspace_path_metric_ne:
  assumes U: "0 \<le> U"
  shows "mspace (path_metric U :: ((real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})) metric) \<noteq> {}"
proof -
  have "continuous_on {0..U} (\<lambda>t. (0 :: 'a \<times> 'b))"
    by (rule continuous_on_const)
  then have "restrict (\<lambda>t. (0 :: 'a \<times> 'b)) {0..U}
      \<in> mspace (path_metric U :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    by (rule mspace_path_metricI)
  then show ?thesis by blast
qed

lemma sq_coord_split:
  fixes v :: "real^'n::finite" and w :: "real^'n^'n"
  shows "(v $ i)\<^sup>2 = (outerp v - w) $ i $ i + w $ i $ i"
  by (simp add: outerp_def power2_eq_square)

lemma ipath_eval_measurable_sets:
  fixes Q :: "(real \<Rightarrow> 'b::polish_space) measure"
  assumes setsQ: "sets Q = sets (ipath_space :: ((real \<Rightarrow> 'b) measure))" and v: "0 \<le> v"
  shows "(\<lambda>w. w v) \<in> borel_measurable Q"
  unfolding measurable_cong_sets[OF setsQ refl] by (rule ipath_eval_measurable[OF v])

lemma standard_borel_ne_path_metric:
  assumes U: "0 \<le> U"
  shows "standard_borel_ne (path_borel U :: ((real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})) measure)"
proof -
  have "space (path_borel U :: ((real \<Rightarrow> 'a \<times> 'b)) measure) \<noteq> {}"
    using mspace_path_metric_ne[OF U] by (simp add: space_borel_of)
  then show ?thesis
    unfolding standard_borel_ne_def standard_borel_ne_axioms_def
    using standard_borel_path_metric by blast
qed

text \<open>The regular conditional distribution itself.  The AFP's
  \<open>disintegration\<close> constrains rectangles only, which suffices because the
  next step converts it to \<open>ksemi\<close>, for which the almost-sure and integral
  forms are already proved.\<close>

lemma path_eval_natural_filtration:
  fixes M :: "((real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})) measure"
  assumes t0: "0 \<le> t" and tu: "t \<le> u"
  shows "(\<lambda>w :: (real \<Rightarrow> 'a \<times> 'b). w t)
      \<in> natural_filtration M 0 (\<lambda>v w. w v) u \<rightarrow>\<^sub>M borel"
  unfolding natural_filtration_def
  by (rule measurable_family_vimage_algebra) (use t0 tu in auto)

text \<open>The time change itself: reading a delayed path at \<open>u\<close> is reading the
  base path at \<open>\<rho> u\<close>.  Pure arithmetic, no membership.\<close>

lemma pair_law_eval_measurable:
  fixes N :: "((real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})) measure"
  assumes setsN: "sets N = sets (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  shows "(\<lambda>\<omega>. \<omega> u) \<in> borel_measurable N"
proof (cases "u \<in> {0..T}")
  case True
  have "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> u)
      \<in> (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)
        \<rightarrow>\<^sub>M borel"
    using continuous_map_measurable[OF continuous_map_path_eval[OF True]]
    by (simp add: borel_of_euclidean)
  then show ?thesis using measurable_cong_sets[OF setsN refl] by blast
next
  case False
  \<comment> \<open>off the horizon the coordinate is the constant \<open>undefined\<close>: points of
      the capped path space are extensional on \<open>{0..T}\<close>.\<close>
  have spN: "space N = mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    by (rule space_of_path_sets[OF setsN])
  show ?thesis
  proof (rule measurableI)
    show "\<And>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> \<in> space N \<Longrightarrow> \<omega> u \<in> space borel" by simp
    fix C :: "('a \<times> 'b) set"
    assume "C \<in> sets borel"
    have "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> u) -` C \<inter> space N
        = (if undefined \<in> C then space N else {})"
      using spN False by (auto simp: path_metric_def extensional_def)
    then show "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> u) -` C \<inter> space N \<in> sets N" by simp
  qed
qed

lemma frozen_set_measurable:
  fixes c T :: real
  assumes T0: "0 \<le> T"
  shows "{w \<in> space (path_borel T :: ((real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})) measure).
      \<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> c \<longrightarrow> w u = 0}
    \<in> sets (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
proof -
  let ?B = "(path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  let ?D = "{0..min c T} \<inter> (\<rat> :: real set)"
  have spB: "space ?B = mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    by (simp add: space_borel_of)
  have cnt: "countable ?D" by (simp add: countable_rat)
  have ev: "(\<lambda>w :: (real \<Rightarrow> 'a \<times> 'b). w q) \<in> borel_measurable ?B" for q
    by (rule pair_law_eval_measurable[OF refl])
  have single: "{w \<in> space ?B. w q = 0} \<in> sets ?B" for q
  proof -
    have "{w \<in> space ?B. w q = 0} = (\<lambda>w :: (real \<Rightarrow> 'a \<times> 'b). w q) -` {0} \<inter> space ?B"
      by auto
    then show ?thesis
      using measurable_sets[OF ev borel_closed[OF closed_singleton]] by simp
  qed
  have eq: "{w \<in> space ?B. \<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> c \<longrightarrow> w u = 0}
      = {w \<in> space ?B. \<forall>q \<in> ?D. w q = 0}"
  proof (rule set_eqI, rule iffI)
    fix w assume "w \<in> {w \<in> space ?B. \<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> c \<longrightarrow> w u = 0}"
    then show "w \<in> {w \<in> space ?B. \<forall>q \<in> ?D. w q = 0}" using T0 by auto
  next
    fix w assume h: "w \<in> {w \<in> space ?B. \<forall>q \<in> ?D. w q = 0}"
    then have wm: "w \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
      using spB by simp
    have cw: "continuous_on {0..T} w" by (rule mspace_path_metricD[OF wm])
    show "w \<in> {w \<in> space ?B. \<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> c \<longrightarrow> w u = 0}"
    proof (intro CollectI conjI allI impI)
      show "w \<in> space ?B" using h by blast
      fix u assume uT: "u \<in> {0..T}" and uc: "u \<le> c"
      have d0: "0 \<le> min c T" using uT uc by auto
      have sub: "{0..min c T} \<subseteq> {0..T}" by auto
      show "w u = 0"
      proof (rule vanishes_of_rational[OF d0 continuous_on_subset[OF cw sub]])
        fix q :: real assume "q \<in> \<rat>" and "q \<in> {0..min c T}"
        then show "w q = 0" using h by auto
      next
        show "u \<in> {0..min c T}" using uT uc by auto
      qed
    qed
  qed
  have "{w \<in> space ?B. \<forall>q \<in> ?D. w q = 0} \<in> sets ?B"
  proof (cases "?D = {}")
    case True
    then have "{w \<in> space ?B. \<forall>q \<in> ?D. w q = 0} = space ?B" by simp
    then show ?thesis by simp
  next
    case False
    have sub: "(\<lambda>q. {w \<in> space ?B. w q = 0}) ` ?D \<subseteq> sets ?B"
      using single by blast
    have "(\<Inter>q \<in> ?D. {w \<in> space ?B. w q = 0}) \<in> sets ?B"
      by (rule sets.countable_INT'[OF cnt False sub])
    moreover have "{w \<in> space ?B. \<forall>q \<in> ?D. w q = 0}
        = (\<Inter>q \<in> ?D. {w \<in> space ?B. w q = 0})" using False by auto
    ultimately show ?thesis by simp
  qed
  then show ?thesis unfolding eq .
qed

lemma dist_eval_measurable:
  fixes x :: "real^'n::finite"
  shows "(\<lambda>\<omega> :: 'n pairpath. dist (fst (\<omega> r)) x)
      \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
proof -
  have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> r) \<in> borel_measurable
      (path_borel T :: ('n pairpath) measure)"
    by (rule pair_law_eval_measurable[OF refl])
  have c: "(\<lambda>pr :: (real^'n) \<times> (real^'n^'n). dist (fst pr) x)
      \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  show ?thesis by (rule measurable_compose[OF ev c])
qed

lemma pair_holder_of_components:
  fixes \<omega> :: "(real \<Rightarrow> 'a::real_normed_vector \<times> 'b::real_normed_vector)"
  assumes T: "0 \<le> T" and ga: "0 < ga" "ga \<le> 1" and c: "0 \<le> c" and B: "0 \<le> B"
    and X: "\<And>u v. u \<in> {0..T} \<Longrightarrow> v \<in> {0..T}
        \<Longrightarrow> norm (fst (\<omega> v) - fst (\<omega> u)) \<le> c * \<bar>v - u\<bar> powr ga"
    and Y: "\<And>u v. u \<in> {0..T} \<Longrightarrow> v \<in> {0..T}
        \<Longrightarrow> norm (snd (\<omega> v) - snd (\<omega> u)) \<le> B * \<bar>v - u\<bar>"
    and st: "s \<in> {0..T}" "t \<in> {0..T}"
  shows "norm (\<omega> t - \<omega> s) \<le> (c + B * T powr (1 - ga)) * \<bar>t - s\<bar> powr ga"
proof -
  have split: "\<omega> t - \<omega> s = (fst (\<omega> t) - fst (\<omega> s), snd (\<omega> t) - snd (\<omega> s))"
    by (simp add: prod_eq_iff)
  have "norm (\<omega> t - \<omega> s)
      \<le> norm (fst (\<omega> t) - fst (\<omega> s)) + norm (snd (\<omega> t) - snd (\<omega> s))"
    unfolding split by (rule norm_Pair_le)
  also have "\<dots> \<le> c * \<bar>t - s\<bar> powr ga + B * \<bar>t - s\<bar>"
    by (intro add_mono X[OF st] Y[OF st])
  also have "\<dots> \<le> c * \<bar>t - s\<bar> powr ga + B * T powr (1 - ga) * \<bar>t - s\<bar> powr ga"
    by (intro add_left_mono lipschitz_imp_holder_bound[OF T ga B st])
  also have "\<dots> = (c + B * T powr (1 - ga)) * \<bar>t - s\<bar> powr ga"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

text \<open>Hence the compact set: pair paths starting at \<open>(x, 0)\<close> whose
  \<open>X\<close>-part obeys a Hoelder-\<open>ga\<close> bound and whose \<open>Y\<close>-part is
  \<open>B\<close>-Lipschitz form a subset of a compact pair-Hoelder ball. This is the
  set the tightness estimate has to charge; the \<open>X\<close>-side probability
  bound is \<open>Path_Tightness.path_law_holder_ball_bound_vec\<close> and the
  \<open>Y\<close>-side holds with probability one by \<open>diffquot_lipschitz\<close>.\<close>

lemma natural_filtration_eq_restrict_vimage:
  fixes Q :: "((real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})) measure"
  assumes setsQ: "sets Q = sets (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
    and s: "0 \<le> s" and sT: "s \<le> T"
    and A: "A \<in> sets (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u) s)"
  obtains Bs where
    "Bs \<in> sets (path_borel s :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
    and "A = (\<lambda>\<omega>. restrict \<omega> {0..s}) -` Bs \<inter> space Q"
proof -
  let ?PS = "mtopology_of (path_metric s :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
  let ?p = "\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). restrict \<omega> {0..s}"
  let ?V = "vimage_algebra (space Q) ?p (borel_of ?PS)"
  have spQ: "space Q = mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    by (rule space_of_path_sets[OF setsQ])
  have pin: "?p \<in> space Q \<rightarrow> space (borel_of ?PS)"
    using restrict_in_mspace[OF s sT] spQ by (auto simp: space_borel_of)
  have pV: "?p \<in> ?V \<rightarrow>\<^sub>M borel_of ?PS"
    by (rule measurable_vimage_algebra1[OF pin])
  have evV: "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> u) \<in> ?V \<rightarrow>\<^sub>M borel" if u: "u \<in> {0..s}" for u
  proof -
    have "(\<lambda>g :: (real \<Rightarrow> 'a \<times> 'b). g u) \<in> borel_of ?PS \<rightarrow>\<^sub>M borel"
      using continuous_map_measurable[OF continuous_map_path_eval[OF u]]
      by (simp add: borel_of_euclidean)
    from measurable_compose[OF pV this]
    have "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). ?p \<omega> u) \<in> ?V \<rightarrow>\<^sub>M borel" .
    moreover have "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). ?p \<omega> u) = (\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> u)"
      using u by (rule_tac ext) simp
    ultimately show ?thesis by simp
  qed
  have fam: "{(\<lambda>u \<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> u) i | i. i \<in> {0..s}}
      \<subseteq> ?V \<rightarrow>\<^sub>M (borel :: ('a \<times> 'b) measure)"
    using evV by blast
  have "family_vimage_algebra (space ?V)
      {(\<lambda>u \<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> u) i | i. i \<in> {0..s}}
      (borel :: ('a \<times> 'b) measure) \<subseteq> ?V"
    using fam measurable_family_iff_sets by blast
  then have inc: "sets (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u) s) \<subseteq> sets ?V"
    unfolding natural_filtration_def by simp
  from A inc have "A \<in> sets ?V" by blast
  then obtain Bs where "Bs \<in> sets (borel_of ?PS)" and "A = ?p -` Bs \<inter> space Q"
    using sets_vimage_algebra2[OF pin] by blast
  then show thesis by (rule that)
qed

subsection \<open>The limit law's process is a martingale\<close>

text \<open>\<open>fst_coord_borel\<close> lives in @{theory Continuous_Time_Martingales.Integrability_Criteria}.\<close>

theorem compactin_pair_holder_ball:
  fixes x :: "real^'n::finite"
  assumes T: "0 \<le> T" and ga: "0 < ga" and c: "0 \<le> c"
  shows "compactin (mtopology_of (path_metric T :: ('n pairpath) metric))
      {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
         \<omega> 0 = (x, 0)
         \<and> (\<forall>u\<in>{0..T}. \<forall>v\<in>{0..T}. norm (\<omega> v - \<omega> u) \<le> c * \<bar>v - u\<bar> powr ga)}"
  by (rule compactin_path_holder_ball[OF T ga c])

lemma outerp_sq: "outerp u ** outerp u = (u \<bullet> u) *\<^sub>R outerp u"
proof -
  have "(outerp u ** outerp u) $ i $ j = ((u \<bullet> u) *\<^sub>R outerp u) $ i $ j"
    for i j
  proof -
    have "(outerp u ** outerp u) $ i $ j
        = (\<Sum>l\<in>UNIV. (u $ i * u $ l) * (u $ l * u $ j))"
      by (simp add: outerp_def matrix_matrix_mult_def)
    also have "\<dots> = u $ i * u $ j * (\<Sum>l\<in>UNIV. u $ l * u $ l)"
      by (simp add: sum_distrib_left mult_ac)
    also have "\<dots> = ((u \<bullet> u) *\<^sub>R outerp u) $ i $ j"
      by (simp add: outerp_def inner_vec_def mult_ac)
    finally show ?thesis .
  qed
  then show ?thesis by (simp add: vec_eq_iff)
qed

lemma pair_holder_ball_mem:
  fixes \<omega> :: "'n::finite pairpath" and x :: "real^'n"
  assumes T: "0 \<le> T" and ga: "0 < ga" "ga \<le> 1" and c: "0 \<le> c" and B: "0 \<le> B"
    and mem: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
    and start: "\<omega> 0 = (x, 0)"
    and X: "\<And>u v. u \<in> {0..T} \<Longrightarrow> v \<in> {0..T}
        \<Longrightarrow> norm (fst (\<omega> v) - fst (\<omega> u)) \<le> c * \<bar>v - u\<bar> powr ga"
    and Y: "\<And>u v. u \<in> {0..T} \<Longrightarrow> v \<in> {0..T}
        \<Longrightarrow> norm (snd (\<omega> v) - snd (\<omega> u)) \<le> B * \<bar>v - u\<bar>"
  shows "\<omega> \<in> {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
      \<omega> 0 = (x, 0)
      \<and> (\<forall>u\<in>{0..T}. \<forall>v\<in>{0..T}.
           norm (\<omega> v - \<omega> u) \<le> (c + B * T powr (1 - ga)) * \<bar>v - u\<bar> powr ga)}"
  using mem start
  by (auto intro!: pair_holder_of_components[OF T ga c B X Y])

text \<open>The tightness criterion the pair laws are checked against: since
  \<open>compactin_pair_holder_ball\<close> supplies the compact set outright, a
  family of pair laws is tight as soon as, for every \<open>e\<close>, some Hoelder
  ball carries all but \<open>e\<close> of every law's mass.\<close>

lemma outerp_add:
  fixes a b :: "real^'n::finite"
  shows "outerp (a + b) = outerp a + outerp b
      + ((\<chi> i j. a $ i * b $ j) + (\<chi> i j. b $ i * a $ j))"
  by (simp add: outerp_def vec_eq_iff algebra_simps)

lemma outerp_zero: "outerp (0 :: real^'n::finite) = 0"
  by (simp add: outerp_def vec_eq_iff)

text \<open>Clause (iv).  Beyond \<open>r\<close> the glued pair is \<open>(X\<^sub>r + W, Y\<^sub>r + \<langle>W\<rangle>)\<close>, so
  its compensated process expands as

    \<open>(outerp X\<^sub>r - Y\<^sub>r) + (outerp W - \<langle>W\<rangle>) + (X\<^sub>r \<otimes> W + W \<otimes> X\<^sub>r)\<close>:

  one compensated martingale from each factor, plus a cross term that is a
  martingale only because the factors are independent
  (\<open>martingale_pair_mult\<close>, entrywise through \<open>martingale_matI\<close>).\<close>

lemma tilted_local_touching:
  fixes W :: "real^'n::finite \<Rightarrow> real" and M :: "real^'n^'n"
    and x \<eta> :: "real^'n"
  assumes lsc: "\<And>a z. a < W z \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> a < W y"
    and rho0: "0 < \<rho>" and c0: "0 < c"
    and sep: "\<And>z. z \<in> cball x \<rho> \<Longrightarrow>
      W x + ((z - x) \<bullet> (M *v (z - x))) / 2 + c * ((z - x) \<bullet> (z - x)) \<le> W z"
    and hsmall: "norm \<eta> < c * \<rho>"
  obtains y where "dist x y < \<rho>" and "norm (y - x) \<le> norm \<eta> / c"
    and "\<And>w. dist y w < \<rho> - dist x y \<Longrightarrow>
      W y - (((y - x) \<bullet> (M *v (y - x))) / 2 + \<eta> \<bullet> (y - x))
        \<le> W w - (((w - x) \<bullet> (M *v (w - x))) / 2 + \<eta> \<bullet> (w - x))"
proof -
  define Q where "Q = (\<lambda>z :: real^'n. ((z - x) \<bullet> (M *v (z - x))) / 2)"
  define \<psi> where "\<psi> = (\<lambda>z :: real^'n. Q z + \<eta> \<bullet> (z - x))"
  have Qx: "Q x = 0" unfolding Q_def by simp
  have cpsi: "continuous_on UNIV \<psi>"
    unfolding \<psi>_def Q_def by (rule continuous_on_quad_tilt)
  have flsc: "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> a < W y - \<psi> y"
    if "a < W z - \<psi> z" for a and z :: "real^'n"
    by (rule lsc_diff_continuous[OF lsc cpsi that])
  have sep': "\<And>z. z \<in> cball x \<rho> \<Longrightarrow>
      W x + Q z + c * ((z - x) \<bullet> (z - x)) \<le> W z"
    unfolding Q_def by (rule sep)
  have Bnd: "W x - norm \<eta> * \<rho> \<le> W z - \<psi> z" if zc: "z \<in> cball x \<rho>" for z
  proof -
    have s: "W x + Q z + c * ((z - x) \<bullet> (z - x)) \<le> W z" by (rule sep'[OF zc])
    have q0: "0 \<le> c * ((z - x) \<bullet> (z - x))"
      by (rule mult_nonneg_nonneg[OF less_imp_le[OF c0] inner_ge_zero])
    have n1: "norm (z - x) \<le> \<rho>"
      using zc by (simp add: dist_norm norm_minus_commute)
    have "norm \<eta> * norm (z - x) \<le> norm \<eta> * \<rho>"
      by (rule mult_left_mono[OF n1 norm_ge_zero])
    then have cs: "\<eta> \<bullet> (z - x) \<le> norm \<eta> * \<rho>"
      using norm_cauchy_schwarz[of \<eta> "z - x"] by linarith
    show ?thesis unfolding \<psi>_def using s q0 cs by linarith
  qed
  have cc: "compact (cball x \<rho>)" by simp
  have ne: "cball x \<rho> \<noteq> {}" using rho0 by auto
  obtain y where yc: "y \<in> cball x \<rho>"
    and ymin: "\<And>w. w \<in> cball x \<rho> \<Longrightarrow> W y - \<psi> y \<le> W w - \<psi> w"
  proof (rule lsc_attains_inf_gen[OF flsc Bnd cc ne])
    fix z :: "real^'n" assume a1: "z \<in> cball x \<rho>"
      and a2: "\<And>w. w \<in> cball x \<rho> \<Longrightarrow> W z - \<psi> z \<le> W w - \<psi> w"
    show thesis by (rule that[OF a1 a2])
  qed
  have xc: "x \<in> cball x \<rho>" using rho0 by simp
  have close: "norm (y - x) \<le> norm \<eta> / c"
  proof (rule tilted_minimiser_close[OF sep' Qx c0 xc yc])
    fix z :: "real^'n" assume zc: "z \<in> cball x \<rho>"
    show "W y - Q y - \<eta> \<bullet> (y - x) \<le> W z - Q z - \<eta> \<bullet> (z - x)"
      using ymin[OF zc] unfolding \<psi>_def by simp
  qed
  have hlt: "norm \<eta> / c < \<rho>"
    using hsmall c0 by (simp add: pos_divide_less_eq mult.commute)
  have dxy: "dist x y < \<rho>"
  proof -
    have "dist x y = norm (y - x)" by (simp add: dist_norm norm_minus_commute)
    then show ?thesis using close hlt by linarith
  qed
  have loc: "W y - \<psi> y \<le> W w - \<psi> w" if dw: "dist y w < \<rho> - dist x y" for w
  proof -
    have "dist x w \<le> dist x y + dist y w" by (rule dist_triangle)
    then have "dist x w < \<rho>" using dw by linarith
    then have "w \<in> cball x \<rho>" by (auto simp: dist_commute)
    then show ?thesis by (rule ymin)
  qed
  show ?thesis
  proof (rule that[OF dxy close])
    fix w :: "real^'n" assume dw: "dist y w < \<rho> - dist x y"
    show "W y - (((y - x) \<bullet> (M *v (y - x))) / 2 + \<eta> \<bullet> (y - x))
        \<le> W w - (((w - x) \<bullet> (M *v (w - x))) / 2 + \<eta> \<bullet> (w - x))"
      using loc[OF dw] by (simp add: \<psi>_def Q_def)
  qed
qed

text \<open>Assembling the separation for the value function.  On a small
  enough ball the touching hypothesis and the strict quadratic minorant
  combine into exactly the separation \<open>tilted_local_touching\<close> wants:
  the touching gives \<open>\<phi> z - \<phi> x \<le> W z - W x\<close> and the minorant gives
  \<open>Q\<^sub>\<epsilon>(z) + (\<epsilon>/4)\<bar>z - x\<bar>\<^sup>2 \<le> \<phi> z - \<phi> x\<close>.  The radius is also shrunk
  below the distance to the complement of \<open>interior K\<close>, so that every
  point of the ball is an admissible touching point in its own right.\<close>

theorem tight_on_set_pair_holder_charge:
  fixes \<Gamma> :: "(('n::finite) pairpath) measure set" and x :: "real^'n"
  assumes T: "0 \<le> T" and ga: "0 < ga"
    and fm: "\<And>N. N \<in> \<Gamma> \<Longrightarrow> finite_measure N"
    and st: "\<And>N. N \<in> \<Gamma> \<Longrightarrow> sets (path_borel T :: ('n pairpath) measure) = sets N"
    and charge: "\<And>e. 0 < e \<Longrightarrow> \<exists>c. 0 \<le> c \<and> (\<forall>N\<in>\<Gamma>. measure N (space N -
      {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
         \<omega> 0 = (x, 0)
         \<and> (\<forall>u\<in>{0..T}. \<forall>v\<in>{0..T}.
              norm (\<omega> v - \<omega> u) \<le> c * \<bar>v - u\<bar> powr ga)}) < e)"
  shows "tight_on_set (mtopology_of (path_metric T :: ('n pairpath) metric)) \<Gamma>"
  unfolding tight_on_set_def
proof (intro conjI)
  show "\<forall>M\<in>\<Gamma>. finite_measure M \<and> sets (path_borel T :: ('n pairpath) measure) = sets M"
    using fm st by blast
next
  show "\<forall>e>0. \<exists>K.
      compactin (mtopology_of (path_metric T :: ('n pairpath) metric)) K
      \<and> (\<forall>M\<in>\<Gamma>. measure M (space M - K) < e)"
  proof (intro allI impI)
    fix e :: real assume e: "0 < e"
    obtain c where c: "0 \<le> c"
      and ch: "\<And>N. N \<in> \<Gamma> \<Longrightarrow> measure N (space N -
        {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
           \<omega> 0 = (x, 0)
           \<and> (\<forall>u\<in>{0..T}. \<forall>v\<in>{0..T}.
                norm (\<omega> v - \<omega> u) \<le> c * \<bar>v - u\<bar> powr ga)}) < e"
      using charge[OF e] by blast
    show "\<exists>K.
        compactin (mtopology_of (path_metric T :: ('n pairpath) metric)) K
        \<and> (\<forall>M\<in>\<Gamma>. measure M (space M - K) < e)"
      by (intro exI[of _ "{\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
             \<omega> 0 = (x, 0)
             \<and> (\<forall>u\<in>{0..T}. \<forall>v\<in>{0..T}.
                  norm (\<omega> v - \<omega> u) \<le> c * \<bar>v - u\<bar> powr ga)}"] conjI ballI
          compactin_pair_holder_ball[OF T ga c] ch)
  qed
qed

text \<open>The charge splits along the components: the \<open>X\<close>-side Hoelder event and
  the \<open>Y\<close>-side Lipschitz event intersect inside a pair Hoelder ball
  (\<open>pair_holder_of_components\<close>), so their complements cover the ball's
  complement and subadditivity finishes; here the \<open>Y\<close>-event has
  probability one, so only the \<open>X\<close>-side estimate carries content.\<close>

lemma pair_holder_charge_split:
  fixes N :: "(('n::finite) pairpath) measure" and x :: "real^'n"
    and T ga c B :: real
    and AX :: "real \<Rightarrow> (('n) pairpath) set" and AY :: "(('n) pairpath) set"
  assumes AX_def: "AX = (\<lambda>c. {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
      fst (\<omega> 0) = x
      \<and> (\<forall>u\<in>{0..T}. \<forall>v\<in>{0..T}.
           norm (fst (\<omega> v) - fst (\<omega> u)) \<le> c * \<bar>v - u\<bar> powr ga)})"
    and AY_def: "AY = {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
      snd (\<omega> 0) = 0
      \<and> (\<forall>u\<in>{0..T}. \<forall>v\<in>{0..T}. norm (snd (\<omega> v) - snd (\<omega> u)) \<le> B * \<bar>v - u\<bar>)}"
  assumes T: "0 \<le> T" and ga: "0 < ga" "ga \<le> 1" and c: "0 \<le> c" and B: "0 \<le> B"
    and fm: "finite_measure N"
    and sp: "space N = mspace (path_metric T :: ('n pairpath) metric)"
    and mX: "AX c \<in> sets N" and mY: "AY \<in> sets N"
  shows "measure N (space N -
      {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
         \<omega> 0 = (x, 0)
         \<and> (\<forall>u\<in>{0..T}. \<forall>v\<in>{0..T}.
              norm (\<omega> v - \<omega> u)
                \<le> (c + B * T powr (1 - ga)) * \<bar>v - u\<bar> powr ga)})
      \<le> measure N (space N - AX c) + measure N (space N - AY)"
proof -
  interpret FM: finite_measure N by fact
  have sub: "AX c \<inter> AY \<subseteq> {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
      \<omega> 0 = (x, 0)
      \<and> (\<forall>u\<in>{0..T}. \<forall>v\<in>{0..T}.
           norm (\<omega> v - \<omega> u)
             \<le> (c + B * T powr (1 - ga)) * \<bar>v - u\<bar> powr ga)}"
  proof
    fix \<omega> assume w: "\<omega> \<in> AX c \<inter> AY"
    then have mem: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
      and x0: "fst (\<omega> 0) = x" and y0: "snd (\<omega> 0) = 0"
      and Xb: "\<And>u v. u \<in> {0..T} \<Longrightarrow> v \<in> {0..T}
          \<Longrightarrow> norm (fst (\<omega> v) - fst (\<omega> u)) \<le> c * \<bar>v - u\<bar> powr ga"
      and Yb: "\<And>u v. u \<in> {0..T} \<Longrightarrow> v \<in> {0..T}
          \<Longrightarrow> norm (snd (\<omega> v) - snd (\<omega> u)) \<le> B * \<bar>v - u\<bar>"
      unfolding AX_def AY_def by auto
    have "\<omega> 0 = (x, 0)" using x0 y0 by (simp add: prod_eq_iff)
    then show "\<omega> \<in> {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
        \<omega> 0 = (x, 0)
        \<and> (\<forall>u\<in>{0..T}. \<forall>v\<in>{0..T}.
             norm (\<omega> v - \<omega> u)
               \<le> (c + B * T powr (1 - ga)) * \<bar>v - u\<bar> powr ga)}"
      using mem
      by (auto intro!: pair_holder_of_components[OF T ga c B Xb Yb])
  qed
  have "space N - {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
      \<omega> 0 = (x, 0)
      \<and> (\<forall>u\<in>{0..T}. \<forall>v\<in>{0..T}.
           norm (\<omega> v - \<omega> u)
             \<le> (c + B * T powr (1 - ga)) * \<bar>v - u\<bar> powr ga)}
      \<subseteq> (space N - AX c) \<union> (space N - AY)"
    using sub by blast
  then have "measure N (space N -
      {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
         \<omega> 0 = (x, 0)
         \<and> (\<forall>u\<in>{0..T}. \<forall>v\<in>{0..T}.
              norm (\<omega> v - \<omega> u)
                \<le> (c + B * T powr (1 - ga)) * \<bar>v - u\<bar> powr ga)})
      \<le> measure N ((space N - AX c) \<union> (space N - AY))"
    using mX mY sp
    by (intro FM.finite_measure_mono sets.Un sets.compl_sets) auto
  also have "\<dots> \<le> measure N (space N - AX c) + measure N (space N - AY)"
    using mX mY
    by (intro measure_subadditive sets.compl_sets)
      (auto simp: FM.emeasure_eq_measure)
  finally show ?thesis .
qed

section \<open>Passing the martingale identities through the weak limit\<close>

text \<open>\<open>unif_integrable_of_L2_bound\<close>, \<open>weak_conv_integral_of_L2_bound\<close> live in @{theory Continuous_Path_Spaces.Path_Tightness}.\<close>


section \<open>Which clauses survive a weak limit\<close>

text \<open>Lemma 2.3 of the paper says the class is closed, passing each defining
  clause of (1.7) to the limit law. The paper uses Prokhorov followed by
  Skorokhod's representation theorem; this instead uses the closed-set
  half of the portmanteau theorem (\<open>weak_conv_closed_full_mass\<close>), needing
  no almost-sure realisation.

  This section discharges the two clauses that are closed conditions on
  a single path: the starting point \<open>(x, 0)\<close> and the covariation
  constraint of (1.7). Portmanteau gives them only for the countably many
  rational pairs \<open>s < t\<close>, and path continuity upgrades that to all real
  pairs (\<open>diffquot_all_of_rational\<close>), as in the paper's own argument. The
  remaining two clauses are the martingale properties, which go through
  the integrated identities instead (\<open>weak_conv_integral_of_L2_bound\<close>).\<close>

subsection \<open>Full mass of the two closed clauses on a class member\<close>

lemma trace_outerp:
  fixes v :: "real^'n::finite"
  shows "trace (outerp v) = v \<bullet> v"
  by (simp add: outerp_def trace_def inner_vec_def)

lemma closedin_start_point:
  fixes x :: "real^'n::finite"
  assumes T: "0 \<le> T"
  shows "closedin (mtopology_of (path_metric T :: ('n pairpath) metric))
      {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric). \<omega> 0 = (x, 0)}"
proof -
  have z: "(0::real) \<in> {0..T}" using T by simp
  have "closedin (mtopology_of (path_metric T :: ('n pairpath) metric))
      {\<omega> \<in> topspace (mtopology_of (path_metric T :: ('n pairpath) metric)).
         \<omega> 0 \<in> {(x, 0)}}"
    by (intro closedin_continuous_map_preimage_gen
          [where Y = euclidean, simplified]
        continuous_map_path_eval[OF z] closed_singleton closedin_topspace)
  then show ?thesis by simp
qed

lemma X_eval_entry_measurable:
  "(\<lambda>p' :: 'n::finite pairpath. fst (p' u) $ c) \<in> borel_measurable
     (path_borel T :: ('n pairpath) measure)"
proof (rule measurable_compose[OF pair_law_eval_measurable[OF refl]])
  have f: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n) \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  show "(\<lambda>pr :: (real^'n) \<times> (real^'n^'n). fst pr $ c) \<in> borel_measurable borel"
    by (rule measurable_compose[OF f borel_measurable_nth])
qed

lemma euOrth_mset_cond:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n"
    and G :: "real^'n \<Rightarrow> real^'n" and h :: real
  assumes SFc: "continuous_on UNIV SF" and Gc: "continuous_on UNIV G"
  shows "{\<omega> \<in> space (path_borel T :: ('n pairpath) measure).
      \<forall>j<m. transpose (SF (fst (\<omega> (real j * h))))
          *v G (fst (\<omega> (real j * h))) = 0 \<longrightarrow>
        G (fst (\<omega> (real j * h))) \<bullet>
          (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0}
    \<in> sets (path_borel T :: ('n pairpath) measure)"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  have evm: "(\<lambda>\<omega> :: 'n pairpath. \<omega> u) \<in> ?B \<rightarrow>\<^sub>M borel" for u
    by (rule pair_law_eval_measurable[OF refl])
  have mfst: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
      \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI[OF
        continuous_on_fst[OF continuous_on_id]])
  have evf: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> u)) \<in> ?B \<rightarrow>\<^sub>M borel" for u
    by (rule measurable_compose[OF evm mfst])
  have condm: "(\<lambda>\<omega> :: 'n pairpath.
      transpose (SF (fst (\<omega> (real j * h))))
        *v G (fst (\<omega> (real j * h)))) \<in> ?B \<rightarrow>\<^sub>M borel" for j
  proof -
    have c: "continuous_on UNIV (\<lambda>w :: real^'n. transpose (SF w) *v G w)"
    proof -
      have ct: "continuous_on UNIV (\<lambda>w :: real^'n. transpose (SF w))"
      proof -
        have e: "(\<lambda>w :: real^'n. transpose (SF w))
            = (\<lambda>w. \<chi> i j. SF w $ j $ i)"
          by (rule ext) (simp add: transpose_def)
        have entry: "continuous_on UNIV (\<lambda>w :: real^'n. SF w $ j $ i)"
          for i j
        proof -
          have bl: "bounded_linear (\<lambda>A :: real^'n^'n. A $ j $ i)"
            using bounded_linear_vec_nth bounded_linear_compose by blast
          show ?thesis
            by (rule continuous_on_compose2[OF
                linear_continuous_on[OF bl] SFc]) auto
        qed
        show ?thesis unfolding e
          by (intro continuous_on_vec_lambda entry)
      qed
      have prodc: "continuous_on UNIV (\<lambda>w :: real^'n.
          transpose (SF w) *v G w)"
      proof -
        have e: "(\<lambda>w :: real^'n. transpose (SF w) *v G w)
            = (\<lambda>w. \<chi> i. (\<Sum>l\<in>UNIV. transpose (SF w) $ i $ l * G w $ l))"
          by (rule ext) (simp add: matrix_vector_mult_def)
        have entry: "continuous_on UNIV (\<lambda>w :: real^'n.
            \<Sum>l\<in>UNIV. transpose (SF w) $ i $ l * G w $ l)" for i
        proof -
          have tc: "continuous_on UNIV
              (\<lambda>w :: real^'n. transpose (SF w) $ i $ l)" for l
          proof -
            have bl: "bounded_linear (\<lambda>A :: real^'n^'n. A $ i $ l)"
              using bounded_linear_vec_nth bounded_linear_compose by blast
            show ?thesis
              by (rule continuous_on_compose2[OF
                  linear_continuous_on[OF bl] ct]) auto
          qed
          have gc: "continuous_on UNIV (\<lambda>w :: real^'n. G w $ l)" for l
            by (rule continuous_on_compose2[OF
                linear_continuous_on[OF bounded_linear_vec_nth] Gc]) auto
          show ?thesis
            by (intro continuous_on_sum continuous_on_mult tc gc)
        qed
        show ?thesis unfolding e
          by (intro continuous_on_vec_lambda entry)
      qed
      show ?thesis by (rule prodc)
    qed
    show ?thesis
      by (rule measurable_compose[OF evf
          borel_measurable_continuous_onI[OF c]])
  qed
  have orthm: "(\<lambda>\<omega> :: 'n pairpath.
      G (fst (\<omega> (real j * h))) \<bullet>
        (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))))
      \<in> ?B \<rightarrow>\<^sub>M borel" for j
  proof -
    have gc: "(\<lambda>\<omega> :: 'n pairpath. G (fst (\<omega> (real j * h))))
        \<in> ?B \<rightarrow>\<^sub>M borel"
      by (rule measurable_compose[OF evf
          borel_measurable_continuous_onI[OF Gc]])
    have dc: "(\<lambda>\<omega> :: 'n pairpath.
        fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h)))
        \<in> ?B \<rightarrow>\<^sub>M borel"
      by (intro borel_measurable_diff evf)
    show ?thesis by (intro borel_measurable_inner gc dc)
  qed
  have per: "{\<omega> \<in> space ?B.
      transpose (SF (fst (\<omega> (real j * h))))
        *v G (fst (\<omega> (real j * h))) = 0 \<longrightarrow>
      G (fst (\<omega> (real j * h))) \<bullet>
        (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0}
      \<in> sets ?B" for j
  proof -
    have cset: "{\<omega> \<in> space ?B.
        transpose (SF (fst (\<omega> (real j * h))))
          *v G (fst (\<omega> (real j * h))) = 0} \<in> sets ?B"
    proof -
      have "{\<omega> \<in> space ?B.
          transpose (SF (fst (\<omega> (real j * h))))
            *v G (fst (\<omega> (real j * h))) = 0}
          = (\<lambda>\<omega> :: 'n pairpath.
            transpose (SF (fst (\<omega> (real j * h))))
              *v G (fst (\<omega> (real j * h)))) -` {0} \<inter> space ?B"
        by auto
      then show ?thesis
        using measurable_sets[OF condm[of j], of "{0}"]
        by (simp add: borel_closed)
    qed
    have oset: "{\<omega> \<in> space ?B.
        G (fst (\<omega> (real j * h))) \<bullet>
          (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0}
        \<in> sets ?B"
    proof -
      have "{\<omega> \<in> space ?B.
          G (fst (\<omega> (real j * h))) \<bullet>
            (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0}
          = (\<lambda>\<omega> :: 'n pairpath.
            G (fst (\<omega> (real j * h))) \<bullet>
              (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))))
            -` {0} \<inter> space ?B"
        by auto
      then show ?thesis
        using measurable_sets[OF orthm[of j], of "{0}"]
        by (simp add: borel_closed)
    qed
    have eq: "{\<omega> \<in> space ?B.
        transpose (SF (fst (\<omega> (real j * h))))
          *v G (fst (\<omega> (real j * h))) = 0 \<longrightarrow>
        G (fst (\<omega> (real j * h))) \<bullet>
          (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0}
        = (space ?B - {\<omega> \<in> space ?B.
            transpose (SF (fst (\<omega> (real j * h))))
              *v G (fst (\<omega> (real j * h))) = 0})
          \<union> {\<omega> \<in> space ?B.
            G (fst (\<omega> (real j * h))) \<bullet>
              (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0}"
      by auto
    show ?thesis unfolding eq
      by (intro sets.Un sets.Diff sets.top cset oset)
  qed
  show ?thesis
  proof (induction m)
    case 0
    show ?case by simp
  next
    case (Suc m)
    have eq: "{\<omega> \<in> space ?B. \<forall>j<Suc m.
        transpose (SF (fst (\<omega> (real j * h))))
          *v G (fst (\<omega> (real j * h))) = 0 \<longrightarrow>
        G (fst (\<omega> (real j * h))) \<bullet>
          (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0}
        = {\<omega> \<in> space ?B. \<forall>j<m.
            transpose (SF (fst (\<omega> (real j * h))))
              *v G (fst (\<omega> (real j * h))) = 0 \<longrightarrow>
            G (fst (\<omega> (real j * h))) \<bullet>
              (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0}
          \<inter> {\<omega> \<in> space ?B.
            transpose (SF (fst (\<omega> (real m * h))))
              *v G (fst (\<omega> (real m * h))) = 0 \<longrightarrow>
            G (fst (\<omega> (real m * h))) \<bullet>
              (fst (\<omega> (real (Suc m) * h)) - fst (\<omega> (real m * h))) = 0}"
      by (auto simp: less_Suc_eq)
    show ?case unfolding eq by (intro sets.Int Suc.IH per)
  qed
qed

lemma exit_class_path_cont:
  fixes Q :: "((real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})) measure"
  assumes T: "0 \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
    and w: "\<omega> \<in> space Q"
  shows "continuous_on {0..} (\<lambda>s. \<omega> (min s T))"
proof -
  have "\<omega> \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    using w space_of_path_sets[OF setsQ] by simp
  from mspace_path_metricD[OF this] have c: "continuous_on {0..T} \<omega>" .
  have m: "continuous_on {0..} (\<lambda>s :: real. min s T)"
    by (intro continuous_intros)
  have mim: "(\<lambda>s :: real. min s T) ` {0..} \<subseteq> {0..T}" using T by auto
  show ?thesis by (rule continuous_on_compose2[OF c m mim])
qed

lemma exit_class_coord_paths_cont:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and w: "\<omega> \<in> space Q"
  shows "continuous_on {0..} (\<lambda>s. fst (\<omega> (min s T)) $ i)"
proof -
  have c2: "continuous_on {0..} (\<lambda>s. fst (\<omega> (min s T)))"
    by (rule continuous_on_fst[OF exit_class_path_cont[OF T setsQ w]])
  have c3: "continuous_on UNIV (\<lambda>v :: real^'n. v $ i)"
    by (rule linear_continuous_on[OF bounded_linear_vec_nth])
  show ?thesis by (rule continuous_on_compose2[OF c3 c2]) simp
qed

lemma horn_B_locally_constant:
  fixes W :: "real^'n::finite \<Rightarrow> real" and M :: "real^'n^'n" and x :: "real^'n"
  assumes lsc: "\<And>a z. a < W z \<Longrightarrow> \<exists>d>0. \<forall>u. dist z u < d \<longrightarrow> a < W u"
    and symM: "transpose M = M" and inv: "invertible M"
    and rho: "0 < \<rho>" and c0: "0 < c"
    and h0: "0 < h" and hle: "h \<le> c * \<rho>"
    and sep: "\<And>z. z \<in> cball x \<rho> \<Longrightarrow>
      W x + ((z - x) \<bullet> (M *v (z - x))) / 2 + c * ((z - x) \<bullet> (z - x)) \<le> W z"
    and hornB: "\<And>\<eta> y. norm \<eta> < h \<Longrightarrow> dist x y < \<rho> \<Longrightarrow>
      norm (y - x) \<le> norm \<eta> / c \<Longrightarrow>
      (\<And>w. dist y w < \<rho> - dist x y \<Longrightarrow>
        W y - (((y - x) \<bullet> (M *v (y - x))) / 2 + \<eta> \<bullet> (y - x))
          \<le> W w - (((w - x) \<bullet> (M *v (w - x))) / 2 + \<eta> \<bullet> (w - x)))
      \<Longrightarrow> M *v (y - x) + \<eta> = 0"
  obtains r where "0 < r" and "\<And>y. dist x y < r \<Longrightarrow> W y = W x"
proof -
  obtain C where C0: "0 \<le> C"
    and Cb: "\<And>u :: real^'n. - (C * (norm u * norm u)) \<le> (u \<bullet> (M *v u)) / 2"
  proof (rule quad_form_bounded_below[where M = M])
    fix CC :: real
    assume a1: "0 \<le> CC"
      and a2: "\<And>u :: real^'n.
        - (CC * (norm u * norm u)) \<le> (u \<bullet> (M *v u)) / 2"
    show thesis by (rule that[OF a1 a2])
  qed
  have bl: "bounded_linear ((*v) M)" by (rule matrix_vector_mul_bounded_linear)
  define N where "N = onorm ((*v) M)"
  have N0: "0 \<le> N" unfolding N_def by (rule onorm_pos_le[OF bl])
  have N1: "0 < N + 1" using N0 by simp
  define r0 where "r0 = min (\<rho> / 2) (h / (2 * (N + 1)))"
  have r00: "0 < r0" unfolding r0_def using rho h0 N1 by simp
  have cp: "0 < c * \<rho>" using c0 rho by simp
  have pinch0: "W y - C * (dist y w * dist y w) \<le> W w"
    if dy: "dist x y < r0" and dw: "dist y w < \<rho> - dist x y"
    for y w :: "real^'n"
  proof -
    define \<eta> where "\<eta> = - (M *v (y - x))"
    have nyx: "norm (y - x) = dist x y"
      by (simp add: dist_norm norm_minus_commute)
    have e1: "norm \<eta> = norm (M *v (y - x))" unfolding \<eta>_def by simp
    have e2: "norm (M *v (y - x)) \<le> N * norm (y - x)"
      unfolding N_def by (rule onorm[OF bl])
    have s1: "N * norm (y - x) \<le> N * r0"
      by (rule mult_left_mono) (use nyx dy N0 in auto)
    have s2: "N * r0 \<le> (N + 1) * r0"
      by (rule mult_right_mono) (use r00 in auto)
    have hb: "norm \<eta> \<le> (N + 1) * r0" using e1 e2 s1 s2 by linarith
    have q1: "(N + 1) * r0 \<le> (N + 1) * (h / (2 * (N + 1)))"
      by (rule mult_left_mono) (use r0_def N1 in auto)
    have q2: "(N + 1) * (h / (2 * (N + 1))) = h / 2"
      using N1 by (simp add: field_simps)
    have hlth: "norm \<eta> < h" using hb q1 q2 h0 by linarith
    have hlt: "norm \<eta> < c * \<rho>" using hlth hle by linarith
    obtain y' where dxy': "dist x y' < \<rho>"
      and cl': "norm (y' - x) \<le> norm \<eta> / c"
      and loc': "\<And>w. dist y' w < \<rho> - dist x y' \<Longrightarrow>
        W y' - (((y' - x) \<bullet> (M *v (y' - x))) / 2 + \<eta> \<bullet> (y' - x))
          \<le> W w - (((w - x) \<bullet> (M *v (w - x))) / 2 + \<eta> \<bullet> (w - x))"
    proof (rule tilted_local_touching[OF lsc rho c0 sep hlt])
      fix yy :: "real^'n"
      assume b1: "dist x yy < \<rho>" and b2: "norm (yy - x) \<le> norm \<eta> / c"
        and b3: "\<And>w. dist yy w < \<rho> - dist x yy \<Longrightarrow>
          W yy - (((yy - x) \<bullet> (M *v (yy - x))) / 2 + \<eta> \<bullet> (yy - x))
            \<le> W w - (((w - x) \<bullet> (M *v (w - x))) / 2 + \<eta> \<bullet> (w - x))"
      show thesis by (rule that[OF b1 b2 b3])
    qed
    have g0: "M *v (y' - x) + \<eta> = 0"
      by (rule hornB[OF hlth dxy' cl' loc'])
    have meq: "M *v (y' - x) = M *v (y - x)"
      using g0 unfolding \<eta>_def by (simp add: algebra_simps)
    have yeq: "y' = y"
      using invertible_matrix_vector_inj[OF inv meq] by simp
    show ?thesis
    proof (rule quad_minimality_pinch[OF symM Cb])
      show "M *v (y - x) + \<eta> = 0" using g0 unfolding yeq .
      show "W y - (((y - x) \<bullet> (M *v (y - x))) / 2 + \<eta> \<bullet> (y - x))
          \<le> W w - (((w - x) \<bullet> (M *v (w - x))) / 2 + \<eta> \<bullet> (w - x))"
        using loc'[of w] dw unfolding yeq by simp
    qed
  qed
  define r where "r = min r0 (\<rho> / 4)"
  have r0': "0 < r" unfolding r_def using r00 rho by simp
  have pin: "W u - C * (dist u w * dist u w) \<le> W w"
    if ub: "u \<in> ball x r" and wb: "w \<in> ball x r" for u w :: "real^'n"
  proof -
    have du: "dist x u < r" using ub by simp
    have dw: "dist x w < r" using wb by simp
    have a1: "dist x u < r0" using du unfolding r_def by simp
    have a2: "dist u w < \<rho> - dist x u"
    proof -
      have t: "dist u w \<le> dist u x + dist x w" by (rule dist_triangle)
      have "dist u x < r" using du by (simp add: dist_commute)
      then have lt2: "dist u w < 2 * r" using t dw by linarith
      have g1: "2 * r \<le> \<rho> / 2" unfolding r_def using rho by simp
      have g2: "dist x u < \<rho> / 4" using du unfolding r_def by simp
      show ?thesis using lt2 g1 g2 rho by linarith
    qed
    show ?thesis by (rule pinch0[OF a1 a2])
  qed
  have const: "W y = W x" if dy: "dist x y < r" for y :: "real^'n"
  proof (rule pinch_implies_constant[OF r0' C0])
    show "\<And>u w. u \<in> ball x r \<Longrightarrow> w \<in> ball x r \<Longrightarrow>
        W u - C * (dist u w * dist u w) \<le> W w"
      by (rule pin)
    show "y \<in> ball x r" using dy by simp
  qed
  show ?thesis by (rule that[OF r0']) (use const in blast)
qed

text \<open>The second horn dies here.  Suppose \<open>v\<^sub>*\<close> were constant \<open>= c\<close> on a
  ball around \<open>x\<close> whose closure lies in \<open>K\<close>.  The envelope's own defining
  property supplies points \<open>z\<close> arbitrarily close to \<open>x\<close> at which \<open>v\<close>
  itself is within \<open>\<theta>/2\<close> of \<open>c\<close>.  But the deterministic-radius member
  started at such a \<open>z\<close> stays inside the ball for a time \<open>\<theta>\<close> that does
  not shrink with \<open>z\<close>, and its endpoint is again in the ball where
  \<open>v \<ge> c\<close>; so \<open>exit_val_ball_lower_plus\<close> gives \<open>v z \<ge> \<theta> + c\<close>.  Those two
  are incompatible.

  The hypothesis \<open>c < T/2\<close> is what keeps the horizon cap inert.  It
  cannot be dropped: if \<open>v \<equiv> T\<close> on an open set then \<open>v\<^sub>*\<close> is locally
  constant there, and no contradiction is available --- indeed the
  supersolution inequality itself fails at such a point, since a
  constant test function would demand \<open>1 \<le> F\<^sup>*(0,0) = 0\<close>.  For a
  bounded \<open>K\<close> the hypothesis is discharged by
  \<open>exit_val_le_ball_bound\<close> once \<open>T\<close> exceeds twice the ball
  bound.\<close>

lemma exit_class_comp_paths_cont:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and w: "\<omega> \<in> space Q"
  shows "continuous_on {0..}
      (\<lambda>s. (fst (\<omega> (min s T)) $ i)\<^sup>2 - snd (\<omega> (min s T)) $ i $ i)"
proof -
  have cx: "continuous_on {0..} (\<lambda>s. fst (\<omega> (min s T)) $ i)"
    by (rule exit_class_coord_paths_cont[OF T setsQ w])
  have c2: "continuous_on {0..} (\<lambda>s. snd (\<omega> (min s T)))"
    by (rule continuous_on_snd[OF exit_class_path_cont[OF T setsQ w]])
  have c3: "continuous_on UNIV (\<lambda>v :: real^'n^'n. v $ i)"
    by (rule linear_continuous_on[OF bounded_linear_vec_nth])
  have c4: "continuous_on {0..} (\<lambda>s. snd (\<omega> (min s T)) $ i)"
    by (rule continuous_on_compose2[OF c3 c2]) simp
  have c5: "continuous_on UNIV (\<lambda>v :: real^'n. v $ i)"
    by (rule linear_continuous_on[OF bounded_linear_vec_nth])
  have cy: "continuous_on {0..} (\<lambda>s. snd (\<omega> (min s T)) $ i $ i)"
    by (rule continuous_on_compose2[OF c5 c4]) simp
  show ?thesis
    by (rule continuous_on_diff[OF continuous_on_power[OF cx] cy])
qed

lemma path_eval_at_measurable_time:
  fixes M :: "'a measure" and g :: "'a \<Rightarrow> real"
    and X :: "'a \<Rightarrow> (real \<Rightarrow> 'b::{polish_space,real_normed_vector} \<times> 'x::{polish_space,real_normed_vector})"
  assumes T0: "0 \<le> T"
    and Xm: "X \<in> M \<rightarrow>\<^sub>M (path_borel T :: ((real \<Rightarrow> 'b \<times> 'x)) measure)"
    and gm: "g \<in> borel_measurable M"
    and g0: "\<And>w. w \<in> space M \<Longrightarrow> 0 \<le> g w"
    and gT: "\<And>w. w \<in> space M \<Longrightarrow> g w \<le> T"
  shows "(\<lambda>w. X w (g w)) \<in> borel_measurable M"
proof -
  define gn where "gn n w = max 0 (min T (real_of_int \<lceil>2^n * g w\<rceil> / 2^n))"
    for n :: nat and w :: 'a
  have gnrange: "gn n w \<in> {0..T}" for n w using T0 by (simp add: gn_def)

  \<comment> \<open>each approximant is measurable: countably many dyadic values\<close>
  have stepm: "(\<lambda>w. X w (gn n w)) \<in> borel_measurable M" for n
  proof -
    have fj: "(\<lambda>w. X w (max 0 (min T (real_of_int j / 2^n)))) \<in> borel_measurable M"
      for j :: int
      by (rule measurable_compose[OF Xm pair_law_eval_measurable[OF refl]])
    have cj: "(\<lambda>w. \<lceil>2^n * g w\<rceil>) \<in> M \<rightarrow>\<^sub>M count_space UNIV"
      using gm by measurable
    have "(\<lambda>w. X w (max 0 (min T (real_of_int \<lceil>2^n * g w\<rceil> / 2^n))))
        \<in> borel_measurable M"
      by (rule measurable_compose_countable[OF fj cj])
    then show ?thesis unfolding gn_def .
  qed

  \<comment> \<open>and they converge, inside each path, by continuity of that path\<close>
  have conv: "(\<lambda>n. X w (gn n w)) \<longlonglongrightarrow> X w (g w)" if w: "w \<in> space M" for w
  proof -
    have cont: "continuous_on {0..T} (X w)"
    proof (rule mspace_path_metricD)
      show "X w \<in> mspace (path_metric T :: ((real \<Rightarrow> 'b \<times> 'x)) metric)"
        using measurable_space[OF Xm w] by (simp add: space_borel_of)
    qed
    have bnd: "\<bar>real_of_int \<lceil>2^n * g w\<rceil> / 2^n - g w\<bar> \<le> (1/2)^n" for n
    proof -
      have p: "(0 :: real) < 2^n" by simp
      have lo: "2^n * g w \<le> real_of_int \<lceil>2^n * g w\<rceil>" by (rule le_of_int_ceiling)
      have hi: "real_of_int \<lceil>2^n * g w\<rceil> < 2^n * g w + 1"
        using ceiling_correct[of "2^n * g w"] by simp
      have "0 \<le> real_of_int \<lceil>2^n * g w\<rceil> / 2^n - g w"
        using lo p by (simp add: field_simps)
      moreover have "real_of_int \<lceil>2^n * g w\<rceil> / 2^n - g w \<le> 1 / 2^n"
      proof -
        have "real_of_int \<lceil>2^n * g w\<rceil> \<le> 2^n * g w + 1" using hi by simp
        then have "real_of_int \<lceil>2^n * g w\<rceil> / 2^n \<le> (2^n * g w + 1) / 2^n"
          by (rule divide_right_mono) simp
        also have "\<dots> = g w + 1 / 2^n" using p by (simp add: field_simps)
        finally show ?thesis by simp
      qed      ultimately show ?thesis by (simp add: power_one_over)
    qed
    have "(\<lambda>n. real_of_int \<lceil>2^n * g w\<rceil> / 2^n - g w) \<longlonglongrightarrow> 0"
    proof (rule Lim_null_comparison)
      show "\<forall>\<^sub>F n in sequentially.
          norm (real_of_int \<lceil>2^n * g w\<rceil> / 2^n - g w) \<le> (1/2)^n"
        using bnd by simp
      show "(\<lambda>n. ((1 :: real)/2)^n) \<longlonglongrightarrow> 0"
        by (rule LIMSEQ_realpow_zero) simp_all
    qed
    then have "(\<lambda>n. real_of_int \<lceil>2^n * g w\<rceil> / 2^n) \<longlonglongrightarrow> g w"
      by (rule Lim_transform[OF tendsto_const])
    then have "(\<lambda>n. gn n w) \<longlonglongrightarrow> max 0 (min T (g w))"
      unfolding gn_def by (intro tendsto_max tendsto_min tendsto_const)
    then have gconv: "(\<lambda>n. gn n w) \<longlonglongrightarrow> g w"
      using g0[OF w] gT[OF w] by simp
    show ?thesis
    proof (rule continuous_on_tendsto_compose[OF cont gconv])
      show "\<forall>\<^sub>F n in sequentially. gn n w \<in> {0..T}" using gnrange by simp
      show "g w \<in> {0..T}" using g0[OF w] gT[OF w] by simp
    qed
  qed
  show ?thesis by (rule borel_measurable_LIMSEQ_metric[OF stepm conv])
qed

text \<open>Both halves of the split are again capped paths.  Freezing and
  rebasing preserve continuity, and @{thm [source] mspace_path_metricI} does
  the extensionality --- both maps are \<open>restrict\<close>ed by construction.\<close>

lemma pairpath_start_sets:
  fixes x :: "real^'n::finite"
  shows "{\<omega> \<in> space (ipath_space :: (('n pairpath) measure)).
      fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0} \<in> sets ipath_space"
proof -
  have m: "(\<lambda>\<omega> :: 'n pairpath. \<omega> 0) \<in> borel_measurable ipath_space"
    by (rule ipath_eval_measurable) simp
  have "{\<omega> \<in> space (ipath_space :: (('n pairpath) measure)).
      fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0}
      = (\<lambda>\<omega> :: 'n pairpath. \<omega> 0) -` {(x, 0)} \<inter> space ipath_space"
    by (auto simp: prod_eq_iff)
  also have "\<dots> \<in> sets (ipath_space :: (('n pairpath) measure))"
    by (rule measurable_sets[OF m]) simp
  finally show ?thesis .
qed

lemma measurable_into_path_metric:
  fixes f :: "'a \<Rightarrow> (real \<Rightarrow> 'b::{polish_space,real_normed_vector} \<times> 'x::{polish_space,real_normed_vector})"
  assumes into: "\<And>w. w \<in> space M
      \<Longrightarrow> f w \<in> mspace (path_metric T :: ((real \<Rightarrow> 'b \<times> 'x)) metric)"
    and dm: "\<And>a. a \<in> mspace (path_metric T :: ((real \<Rightarrow> 'b \<times> 'x)) metric)
      \<Longrightarrow> (\<lambda>w. mdist (path_metric T :: ((real \<Rightarrow> 'b \<times> 'x)) metric) (f w) a)
          \<in> borel_measurable M"
  shows "f \<in> M \<rightarrow>\<^sub>M (path_borel T :: ((real \<Rightarrow> 'b \<times> 'x)) measure)"
proof -
  let ?m = "path_metric T :: ((real \<Rightarrow> 'b \<times> 'x)) metric"
  let ?B = "borel_of (mtopology_of ?m)"
  interpret MS: Metric_space "mspace ?m" "mdist ?m"
    by (rule Metric_space_mspace_mdist)
  let ?balls = "{MS.mball a \<epsilon> | a \<epsilon>. a \<in> mspace ?m \<and> \<epsilon> > 0}"
  have sub: "?balls \<subseteq> Pow (mspace ?m)" using MS.mball_subset_mspace by auto
  have base: "base_in (mtopology_of ?m) ?balls"
    using MS.mtopology_base_in_balls by (simp add: mtopology_of_def)
  have "?B = sigma (topspace (mtopology_of ?m)) ?balls"
    by (rule borel_of_second_countable'
        [OF second_countable_path_metric base_is_subbase[OF base]])
  then have setsB: "sets ?B = sigma_sets (mspace ?m) ?balls"
    using sets_measure_of[OF sub] by simp
  show ?thesis
  proof (rule measurable_sigma_sets[OF setsB sub])
    show "f \<in> space M \<rightarrow> mspace ?m" using into by blast
  next
    fix A assume "A \<in> ?balls"
    then obtain a e where A: "A = MS.mball a e" and am: "a \<in> mspace ?m"
      and epos: "e > 0" by blast
    have ball: "(\<omega> \<in> MS.mball a e) = (\<omega> \<in> mspace ?m \<and> mdist ?m \<omega> a < e)"
      for \<omega> :: "(real \<Rightarrow> 'b \<times> 'x)"
      using am by (simp only: MS.in_mball MS.commute conj_commute simp_thms)
    have "f -` A \<inter> space M = {w \<in> space M. mdist ?m (f w) a < e}"
      unfolding A using into by (auto simp only: ball vimage_eq Int_iff)    then show "f -` A \<inter> space M \<in> sets M" using dm[OF am] by simp
  qed
qed

text \<open>Hypothesis (ii) of the criterion: the distance to a fixed path is a
  sup of evaluations over the rationals (@{thm [source] path_mdist_le_iff}),
  hence a countable intersection.\<close>

lemma mdist_measurable_of_eval:
  fixes f :: "'a \<Rightarrow> (real \<Rightarrow> 'b::{polish_space,real_normed_vector} \<times> 'x::{polish_space,real_normed_vector})"
  assumes T0: "0 \<le> T"
    and into: "\<And>w. w \<in> space M
      \<Longrightarrow> f w \<in> mspace (path_metric T :: ((real \<Rightarrow> 'b \<times> 'x)) metric)"
    and am: "a \<in> mspace (path_metric T :: ((real \<Rightarrow> 'b \<times> 'x)) metric)"
    and ev: "\<And>t. (\<lambda>w. f w t) \<in> borel_measurable M"
  shows "(\<lambda>w. mdist (path_metric T :: ((real \<Rightarrow> 'b \<times> 'x)) metric) (f w) a)
      \<in> borel_measurable M"
proof (rule borel_measurable_iff_le[THEN iffD2], intro allI)
  fix q :: real
  have cnt: "countable ({0..T} \<inter> \<rat>)" by (simp add: countable_rat)
  have ne: "{0..T} \<inter> \<rat> \<noteq> {}" using T0 by auto
  have eq: "{w \<in> space M. mdist (path_metric T :: ((real \<Rightarrow> 'b \<times> 'x)) metric) (f w) a \<le> q}
      = (\<Inter>t \<in> {0..T} \<inter> \<rat>. {w \<in> space M. dist (f w t) (a t) \<le> q})"
    using ne by (auto simp: path_mdist_le_iff[OF T0 into am])
  have inner: "{w \<in> space M. dist (f w t) (a t) \<le> q} \<in> sets M" for t
    using ev[of t] by measurable
  show "{w \<in> space M. mdist (path_metric T :: ((real \<Rightarrow> 'b \<times> 'x)) metric) (f w) a \<le> q}
      \<in> sets M"
    unfolding eq by (intro sets.countable_INT'[OF cnt ne]) (auto simp: inner)qed

text \<open>Hence both halves of the split are measurable maps of the path.  Only
  Borel measurability of \<open>\<theta>\<close> is used here; the stopping-time property is
  what makes the kernel a function of the past, entering later through
  @{thm [source] stopped_adapted_of_cont}.\<close>

lemma euXi_term_cont:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n" and M :: "real^'n^'n"
    and h :: real
  assumes SFc: "continuous_on UNIV SF"
  shows "continuous_on UNIV (\<lambda>ab :: ((real^'n) \<times> (real^'n^'n))
        \<times> ((real^'n) \<times> (real^'n^'n)).
      trace (M ** (outerp (fst (fst ab) - fst (snd ab))
        - h *\<^sub>R (SF (fst (snd ab)) ** transpose (SF (fst (snd ab)))))))"
proof -
  have entry: "continuous_on UNIV (\<lambda>z :: real^'n. SF z $ i $ j)" for i j
  proof -
    have bl: "bounded_linear (\<lambda>A :: real^'n^'n. A $ i $ j)"
      using bounded_linear_vec_nth bounded_linear_compose by blast
    show ?thesis
      by (rule continuous_on_compose2[OF linear_continuous_on[OF bl] SFc])
        auto
  qed
  have proj2: "continuous_on UNIV (\<lambda>ab :: ((real^'n) \<times> (real^'n^'n))
      \<times> ((real^'n) \<times> (real^'n^'n)). fst (snd ab))"
    by (intro continuous_on_fst continuous_on_snd continuous_on_id)
  have proj1: "continuous_on UNIV (\<lambda>ab :: ((real^'n) \<times> (real^'n^'n))
      \<times> ((real^'n) \<times> (real^'n^'n)). fst (fst ab))"
    by (intro continuous_on_fst continuous_on_id)
  have SFcomp: "continuous_on UNIV (\<lambda>ab :: ((real^'n) \<times> (real^'n^'n))
      \<times> ((real^'n) \<times> (real^'n^'n)). SF (fst (snd ab)) $ i $ j)" for i j
    by (rule continuous_on_compose2[OF entry proj2]) auto
  have vcomp1: "continuous_on UNIV (\<lambda>ab :: ((real^'n) \<times> (real^'n^'n))
      \<times> ((real^'n) \<times> (real^'n^'n)). fst (fst ab) $ i)" for i
    by (rule continuous_on_compose2[OF
        linear_continuous_on[OF bounded_linear_vec_nth] proj1]) auto
  have vcomp2: "continuous_on UNIV (\<lambda>ab :: ((real^'n) \<times> (real^'n^'n))
      \<times> ((real^'n) \<times> (real^'n^'n)). fst (snd ab) $ i)" for i
    by (rule continuous_on_compose2[OF
        linear_continuous_on[OF bounded_linear_vec_nth] proj2]) auto
  have inner: "continuous_on UNIV (\<lambda>ab :: ((real^'n) \<times> (real^'n^'n))
      \<times> ((real^'n) \<times> (real^'n^'n)).
      outerp (fst (fst ab) - fst (snd ab))
        - h *\<^sub>R (SF (fst (snd ab)) ** transpose (SF (fst (snd ab)))))"
  proof -
    have e: "(\<lambda>ab :: ((real^'n) \<times> (real^'n^'n))
          \<times> ((real^'n) \<times> (real^'n^'n)).
        outerp (fst (fst ab) - fst (snd ab))
          - h *\<^sub>R (SF (fst (snd ab)) ** transpose (SF (fst (snd ab)))))
        = (\<lambda>ab. \<chi> i j. (fst (fst ab) $ i - fst (snd ab) $ i)
              * (fst (fst ab) $ j - fst (snd ab) $ j)
            - h * (\<Sum>l\<in>UNIV. SF (fst (snd ab)) $ i $ l
                * SF (fst (snd ab)) $ j $ l))"
      by (rule ext) (simp add: outerp_def matrix_matrix_mult_def
          transpose_def
          vec_eq_iff)
    show ?thesis unfolding e
      by (intro continuous_on_vec_lambda continuous_intros
          SFcomp vcomp1 vcomp2)
  qed
  show ?thesis
    by (rule continuous_on_compose2[OF
        linear_continuous_on[OF bounded_linear_trace_mult_left] inner]) auto
qed

lemma iexit_fst_measurable_ipath:
  fixes K :: "(real^'n::finite) set"
  assumes K: "closed K"
  shows "(\<lambda>\<omega> :: 'n pairpath. iexit K (\<lambda>t. fst (\<omega> t)))
      \<in> borel_measurable (ipath_space :: (('n pairpath) measure))"
proof (rule iexit_measurable_gen[OF K])
  have fstB: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n) \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  show "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> t)) \<in> borel_measurable ipath_space"
    if "0 \<le> t" for t
    by (rule measurable_compose[OF ipath_eval_measurable[OF that] fstB])
next
  fix \<omega> :: "'n pairpath"
  assume "\<omega> \<in> space (ipath_space :: (('n pairpath) measure))"
  then have "\<omega> \<in> ipath" by simp
  then have c: "continuous_on {0..} \<omega>" by (rule ipath_continuous_on) simp
  have g: "continuous_on UNIV (fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)"
    by (intro continuous_intros)
  show "continuous_on {0..} (\<lambda>t. fst (\<omega> t))"
    by (rule continuous_on_compose2[OF g c]) auto
qed

lemma open_quad_bad_event_region:
  fixes x q :: "real^'n::finite" and M :: "real^'n^'n"
    and t T thr :: real and RO :: "(real^'n) set"
  assumes t0: "0 \<le> t" and tT: "t \<le> T" and RO: "open RO"
  shows "openin (mtopology_of (path_metric T :: ('n pairpath) metric))
      {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
        (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> RO)
        \<and> q \<bullet> (fst (\<omega> t) - x)
          + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x))) < thr}"
proof -
  have T0: "0 \<le> T" using t0 tT by linarith
  let ?pm = "path_metric T :: ('n pairpath) metric"
  have o1: "openin (mtopology_of ?pm)
      {\<omega> \<in> mspace ?pm. \<forall>s\<in>{0..t}. \<omega> s \<in> fst -` RO}"
    by (rule open_stay_inside[OF T0 open_vimage_fst[OF RO] t0 tT])
  have c0: "continuous_on UNIV
      (\<lambda>p :: (real^'n) \<times> (real^'n^'n). fst p - x)"
    by (intro continuous_intros)
  have c1: "continuous_on UNIV
      (\<lambda>p :: (real^'n) \<times> (real^'n^'n). M *v (fst p - x))"
    by (rule continuous_on_compose2[OF
        linear_continuous_on[OF matvec_blin] c0]) auto
  have cq: "continuous_on UNIV
      (\<lambda>p :: (real^'n) \<times> (real^'n^'n). q \<bullet> (fst p - x))"
    by (rule continuous_on_compose2[OF
        linear_continuous_on[OF bounded_linear_inner_right] c0]) auto
  have cin: "continuous_on UNIV
      (\<lambda>p :: (real^'n) \<times> (real^'n^'n).
        (fst p - x) \<bullet> (M *v (fst p - x)))"
    by (rule bounded_bilinear.continuous_on[OF bounded_bilinear_inner c0 c1])
  have contf: "continuous_on UNIV
      (\<lambda>p :: (real^'n) \<times> (real^'n^'n).
        q \<bullet> (fst p - x) + (1/2) * ((fst p - x) \<bullet> (M *v (fst p - x))))"
    by (intro continuous_on_add continuous_on_mult
        continuous_on_const cq cin)
  have oU: "open {p :: (real^'n) \<times> (real^'n^'n).
      q \<bullet> (fst p - x) + (1/2) * ((fst p - x) \<bullet> (M *v (fst p - x))) < thr}"
    by (rule open_Collect_less[OF contf continuous_on_const])
  have o2: "openin (mtopology_of ?pm)
      {\<omega> \<in> mspace ?pm. \<omega> t \<in> {p. q \<bullet> (fst p - x)
        + (1/2) * ((fst p - x) \<bullet> (M *v (fst p - x))) < thr}}"
    by (rule open_eval_preimage[OF _ oU]) (use t0 tT in simp)
  have eq: "{\<omega> \<in> mspace ?pm.
      (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> RO)
      \<and> q \<bullet> (fst (\<omega> t) - x)
        + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x))) < thr}
      = {\<omega> \<in> mspace ?pm. \<forall>s\<in>{0..t}. \<omega> s \<in> fst -` RO}
        \<inter> {\<omega> \<in> mspace ?pm. \<omega> t \<in> {p. q \<bullet> (fst p - x)
          + (1/2) * ((fst p - x) \<bullet> (M *v (fst p - x))) < thr}}"
    by auto
  show ?thesis unfolding eq by (rule openin_Int[OF o1 o2])
qed

subsection \<open>The bad event vanishes on a region\<close>

text \<open>The vanishing-probability theorem \<open>eulerp_bad_event_null\<close>, over an arbitrary bounded open stay-region:
  the kill and the trace margin hold on the region, which is contained
  in a ball of radius \<open>Rn\<close> around the quadratic's centre, and the same
  Chebyshev-plus-gap dissection gives the \<open>A h + B h\<^sup>2\<close> bound once the
  mesh is fine.\<close>

lemma path_sets_fst_continuous:
  fixes N :: "((real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})) measure"
  assumes setsN: "sets N = sets (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
    and w: "\<omega> \<in> space N"
  shows "continuous_on {0..T} (\<lambda>t. fst (\<omega> t))"
proof -
  have "\<omega> \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    using w space_of_path_sets[OF setsN] by simp
  then have "continuous_on {0..T} \<omega>" by (rule mspace_path_metric_continuous)
  then show ?thesis by (rule continuous_on_fst)
qed

lemma horizon_sq_int_martingale_stopped:
  fixes Q :: "'a measure" and Z :: "real \<Rightarrow> 'a \<Rightarrow> real" and \<tau> :: "'a \<Rightarrow> real"
  assumes T0: "0 < T"
    and HZ: "horizon_sq_int_martingale Q F Z T"
    and cap: "\<And>s \<omega>. Z s \<omega> = Z (min s T) \<omega>"
    and contT: "\<And>\<omega>. \<omega> \<in> space Q \<Longrightarrow> continuous_on {0..T} (\<lambda>s. Z s \<omega>)"
    and tnn: "\<And>\<omega>. 0 \<le> \<tau> \<omega>"
    and tstop: "\<And>s. 0 \<le> s \<Longrightarrow> {\<omega> \<in> space Q. \<tau> \<omega> \<le> s} \<in> sets (F s)"
  shows "martingale Q F 0 (\<lambda>v \<omega>. Z (min v (\<tau> \<omega>)) \<omega>)"
    and "\<And>s. 0 \<le> s \<Longrightarrow> integrable Q (\<lambda>\<omega>. (Z (min s (\<tau> \<omega>)) \<omega>)\<^sup>2)"
proof -
  interpret HM: horizon_sq_int_martingale Q F Z T by (rule HZ)
  have T0': "0 \<le> T" using T0 by simp
  have mgZ: "martingale Q F 0 Z" by (rule HM.martingale_axioms)
  have adp: "adapted_process Q F 0 Z" by unfold_locales
  have cont0: "continuous_on {0..} (\<lambda>s. Z s \<omega>)" if w: "\<omega> \<in> space Q" for \<omega>
  proof -
    have m: "continuous_on {0..} (\<lambda>s :: real. min s T)"
      by (intro continuous_intros)
    have im: "(\<lambda>s :: real. min s T) ` {0..} \<subseteq> {0..T}" using T0' by auto
    have "continuous_on {0..} (\<lambda>s. Z (min s T) \<omega>)"
      by (rule continuous_on_compose2[OF contT[OF w] m im])
    then show ?thesis using cap by simp
  qed
  have contu: "continuous_on {0..u} (\<lambda>s. Z s \<omega>)"
    if w: "\<omega> \<in> space Q" for \<omega> u
    by (rule continuous_on_subset[OF cont0[OF w]]) auto
  have domT: "AE \<omega> in Q. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> T \<longrightarrow> \<bar>Z s \<omega>\<bar> \<le> HM.Dsup \<omega>"
    by (rule HM.Dsup_dominates) (intro AE_I2 contu)
  have domA: "AE \<omega> in Q. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow> \<bar>Z s \<omega>\<bar> \<le> HM.Dsup \<omega>" for u
    using domT
  proof (rule eventually_mono)
    fix \<omega> :: 'a
    assume h: "\<forall>s. 0 \<le> s \<longrightarrow> s \<le> T \<longrightarrow> \<bar>Z s \<omega>\<bar> \<le> HM.Dsup \<omega>"
    show "\<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow> \<bar>Z s \<omega>\<bar> \<le> HM.Dsup \<omega>"
    proof (intro allI impI)
      fix s :: real assume s: "0 \<le> s"
      have "\<bar>Z (min s T) \<omega>\<bar> \<le> HM.Dsup \<omega>" using h s T0' by simp
      then show "\<bar>Z s \<omega>\<bar> \<le> HM.Dsup \<omega>" using cap[of s \<omega>] by simp
    qed
  qed
  have tnn': "\<And>\<omega>. \<omega> \<in> space Q \<Longrightarrow> 0 \<le> \<tau> \<omega>" by (rule tnn)
  have stad: "(\<lambda>\<omega>. Z (min v (\<tau> \<omega>)) \<omega>) \<in> borel_measurable (F v)"
    if v: "0 \<le> v" for v
    by (rule stopped_adapted_of_cont[OF adp tnn' tstop cont0 v])
  show mgs: "martingale Q F 0 (\<lambda>v \<omega>. Z (min v (\<tau> \<omega>)) \<omega>)"
  proof (rule optional_stopping[where D = "\<lambda>_. HM.Dsup"])
    show "martingale Q F 0 Z" by (rule mgZ)
    show "\<And>\<omega>. \<omega> \<in> space Q \<Longrightarrow> 0 \<le> \<tau> \<omega>" by (rule tnn')
    show "\<And>s. 0 \<le> s \<Longrightarrow> {\<omega> \<in> space Q. \<tau> \<omega> \<le> s} \<in> sets (F s)" by (rule tstop)
    show "\<And>u. 0 < u \<Longrightarrow> AE \<omega> in Q. continuous_on {0..u} (\<lambda>s. Z s \<omega>)"
      by (intro AE_I2 contu)
    show "\<And>u. 0 < u \<Longrightarrow> AE \<omega> in Q.
        \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow> \<bar>Z s \<omega>\<bar> \<le> HM.Dsup \<omega>" by (rule domA)
    show "\<And>u. 0 < u \<Longrightarrow> integrable Q HM.Dsup" by (rule HM.Dsup_integrable)
    show "\<And>v. 0 \<le> v \<Longrightarrow> (\<lambda>\<omega>. Z (min v (\<tau> \<omega>)) \<omega>) \<in> borel_measurable (F v)"
      by (rule stad)
  qed
  show "integrable Q (\<lambda>\<omega>. (Z (min s (\<tau> \<omega>)) \<omega>)\<^sup>2)" if s: "0 \<le> s" for s
  proof -
    have m: "(\<lambda>\<omega>. Z (min s (\<tau> \<omega>)) \<omega>) \<in> borel_measurable Q"
      by (rule measurable_from_subalg[OF HM.subalgebras[OF s] stad[OF s]])
    then have m2: "(\<lambda>\<omega>. (Z (min s (\<tau> \<omega>)) \<omega>)\<^sup>2) \<in> borel_measurable Q" by simp
    have ae: "AE \<omega> in Q. norm ((Z (min s (\<tau> \<omega>)) \<omega>)\<^sup>2) \<le> norm ((HM.Dsup \<omega>)\<^sup>2)"
      using domA[of s]
    proof (rule eventually_mono)
      fix \<omega> :: 'a
      assume h: "\<forall>v. 0 \<le> v \<longrightarrow> v \<le> s \<longrightarrow> \<bar>Z v \<omega>\<bar> \<le> HM.Dsup \<omega>"
      have a: "0 \<le> min s (\<tau> \<omega>)" using s tnn[of \<omega>] by simp
      have b: "min s (\<tau> \<omega>) \<le> s" by simp
      have le: "\<bar>Z (min s (\<tau> \<omega>)) \<omega>\<bar> \<le> HM.Dsup \<omega>" using h a b by blast
      have "(Z (min s (\<tau> \<omega>)) \<omega>)\<^sup>2 = \<bar>Z (min s (\<tau> \<omega>)) \<omega>\<bar>\<^sup>2" by simp
      also have "\<dots> \<le> (HM.Dsup \<omega>)\<^sup>2" by (rule power_mono[OF le abs_ge_zero])
      finally show "norm ((Z (min s (\<tau> \<omega>)) \<omega>)\<^sup>2) \<le> norm ((HM.Dsup \<omega>)\<^sup>2)"
        by simp
    qed
    show ?thesis
      by (rule Bochner_Integration.integrable_bound
          [OF HM.Dsup_sq_integrable m2 ae])
  qed
qed

text \<open>\<open>martingale_cong_ge\<close> lives in
  @{theory Continuous_Time_Martingales.Martingale_Algebra},
  general at any \<open>t\<^sub>0\<close> and with the equation oriented \<open>X u = Y u\<close> rather than
  \<open>Y u = X u\<close>.\<close>

subsection \<open>\<open>QH\<close> and \<open>QHC\<close> for the stopped past law\<close>

text \<open>Both clauses by the same three steps: stop the class's horizon
  martingale at \<open>\<theta>\<close> (@{thm [source] horizon_sq_int_martingale_stopped}),
  push the result forward along \<open>pstopped\<close>
  (\<open>martingale_pair_law\<close>, with
  \<open>pstopped_eval_filtration\<close> as its adaptedness input and
  \<open>P\<close>'s own filtration --- a stopped path carries no more information than
  the past, so unlike the delayed class there is no time change here), and
  carry the square-integrability across with
  \<open>integrable_distr_eq\<close>.\<close>

lemma path_eval_measurable_natural_filtration:
  fixes U v :: real
  assumes v: "v \<in> {0..U}"
  shows "(\<lambda>\<omega> :: (real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector}). \<omega> v) \<in> borel_measurable (natural_filtration
      (path_borel U :: ((real \<Rightarrow> 'a \<times> 'b)) measure)
      0 (\<lambda>v \<omega>. \<omega> v) U)"
  unfolding natural_filtration_def
  by (rule measurable_family_vimage_algebra) (use v in auto)

lemma sets_natural_filtration_path_subset:
  fixes U u :: real
  shows "sets (natural_filtration
        (path_borel U :: ((real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})) measure)
        0 (\<lambda>v \<omega>. \<omega> v) u)
      \<subseteq> sets (path_borel U :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
proof -
  let ?m = "path_metric U :: ((real \<Rightarrow> 'a \<times> 'b)) metric"
  let ?B = "borel_of (mtopology_of ?m)"
  have "(\<Union>i\<in>{0..u}.
      {(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> i) -` A \<inter> space ?B | A. A \<in> sets borel})
      \<subseteq> sets ?B"
  proof clarsimp
    fix i :: real and A :: "('a \<times> 'b) set"
    assume "A \<in> sets borel"
    then show "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> i) -` A \<inter> space ?B \<in> sets ?B"
      by (rule measurable_sets[OF pair_law_eval_measurable[OF refl]])
  qed
  then show ?thesis
    unfolding sets_natural_filtration by (rule sets.sigma_sets_subset)
qed

text \<open>The metric half.  @{thm [source] path_mdist_le_iff} turns the sup
  distance into a condition at the rational times only, countably many, so
  \<open>sets.countable_INT'\<close> applies.  The intersection must be over
  a nonempty index set to keep \<open>\<omega> \<in> space \<FF>\<close> on the \<open>\<supseteq>\<close> side; over an empty
  one it would be the universe.\<close>

lemma mdist_measurable_natural_filtration:
  fixes U :: real and f :: "(real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})"
  assumes U: "0 \<le> U" and f: "f \<in> mspace (path_metric U :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
  shows "(\<lambda>\<omega>. mdist (path_metric U :: ((real \<Rightarrow> 'a \<times> 'b)) metric) f \<omega>)
      \<in> borel_measurable (natural_filtration
          (path_borel U :: ((real \<Rightarrow> 'a \<times> 'b)) measure)
          0 (\<lambda>v \<omega>. \<omega> v) U)"
proof -
  let ?m = "path_metric U :: ((real \<Rightarrow> 'a \<times> 'b)) metric"
  let ?B = "borel_of (mtopology_of ?m)"
  let ?F = "natural_filtration ?B 0 (\<lambda>v \<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> v) U"
  have spF: "space ?F = mspace ?m" by (simp add: space_borel_of)
  have Q0: "(0::real) \<in> {0..U} \<inter> \<rat>" using U by simp
  have neQ: "{0..U} \<inter> (\<rat> :: real set) \<noteq> {}" using Q0 by blast
  have cQ: "countable ({0..U} \<inter> (\<rat> :: real set))"
    by (rule countable_subset[OF _ countable_rat]) simp
  show ?thesis
  proof (subst borel_measurable_iff_le, intro allI)
    fix q :: real
    have iff: "mdist ?m f \<omega> \<le> q \<longleftrightarrow> (\<forall>t\<in>{0..U} \<inter> \<rat>. dist (f t) (\<omega> t) \<le> q)"
      if w: "\<omega> \<in> mspace ?m" for \<omega> :: "(real \<Rightarrow> 'a \<times> 'b)"
      by (rule path_mdist_le_iff[OF U f w])
    have mem: "{\<omega> \<in> space ?F. dist (f t) (\<omega> t) \<le> q} \<in> sets ?F"
      if t: "t \<in> {0..U} \<inter> \<rat>" for t
    proof -
      have m: "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). dist (f t) (\<omega> t)) \<in> borel_measurable ?F"
        using path_eval_measurable_natural_filtration[of t U] t
        by (intro borel_measurable_dist) auto
      show ?thesis using iffD1[OF borel_measurable_iff_le m] by blast
    qed
    have seteq: "{\<omega> \<in> space ?F. mdist ?m f \<omega> \<le> q}
        = (\<Inter>t \<in> {0..U} \<inter> \<rat>. {\<omega> \<in> space ?F. dist (f t) (\<omega> t) \<le> q})"
    proof
      show "{\<omega> \<in> space ?F. mdist ?m f \<omega> \<le> q}
          \<subseteq> (\<Inter>t \<in> {0..U} \<inter> \<rat>. {\<omega> \<in> space ?F. dist (f t) (\<omega> t) \<le> q})"
        using iff spF by auto
    next
      show "(\<Inter>t \<in> {0..U} \<inter> \<rat>. {\<omega> \<in> space ?F. dist (f t) (\<omega> t) \<le> q})
          \<subseteq> {\<omega> \<in> space ?F. mdist ?m f \<omega> \<le> q}"
      proof
        fix \<omega> :: "(real \<Rightarrow> 'a \<times> 'b)"
        assume w: "\<omega> \<in> (\<Inter>t \<in> {0..U} \<inter> \<rat>.
            {\<omega> \<in> space ?F. dist (f t) (\<omega> t) \<le> q})"
        have sp: "\<omega> \<in> space ?F" using w Q0 by blast
        then have mw: "\<omega> \<in> mspace ?m" using spF by simp
        have "\<forall>t\<in>{0..U} \<inter> \<rat>. dist (f t) (\<omega> t) \<le> q" using w by blast
        then have "mdist ?m f \<omega> \<le> q" using iff[OF mw] by blast
        then show "\<omega> \<in> {\<omega> \<in> space ?F. mdist ?m f \<omega> \<le> q}" using sp by simp
      qed
    qed
    have "(\<Inter>t \<in> {0..U} \<inter> \<rat>. {\<omega> \<in> space ?F. dist (f t) (\<omega> t) \<le> q})
        \<in> sets ?F"
      by (rule sets.countable_INT'[OF cQ neQ]) (use mem in auto)
    then show "{\<omega> \<in> space ?F. mdist ?m f \<omega> \<le> q} \<in> sets ?F"
      unfolding seteq .
  qed
qed

text \<open>Hence every metric ball is a filtration event.\<close>

lemma mball_in_natural_filtration:
  fixes U :: real and f :: "(real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})"
  assumes U: "0 \<le> U" and f: "f \<in> mspace (path_metric U :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
  shows "Metric_space.mball (mspace (path_metric U :: ((real \<Rightarrow> 'a \<times> 'b)) metric))
        (mdist (path_metric U :: ((real \<Rightarrow> 'a \<times> 'b)) metric)) f e
      \<in> sets (natural_filtration
          (path_borel U :: ((real \<Rightarrow> 'a \<times> 'b)) measure)
          0 (\<lambda>v \<omega>. \<omega> v) U)"
proof -
  let ?m = "path_metric U :: ((real \<Rightarrow> 'a \<times> 'b)) metric"
  let ?B = "borel_of (mtopology_of ?m)"
  let ?F = "natural_filtration ?B 0 (\<lambda>v \<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> v) U"
  interpret MS: Metric_space "mspace ?m" "mdist ?m"
    by (rule Metric_space_mspace_mdist)
  have spF: "space ?F = mspace ?m" by (simp add: space_borel_of)
  have mb: "MS.mball f e = {\<omega> \<in> space ?F. mdist ?m f \<omega> < e}"
  proof (rule set_eqI)
    fix \<omega> :: "(real \<Rightarrow> 'a \<times> 'b)"
    have "(\<omega> \<in> MS.mball f e)
        = (f \<in> mspace ?m \<and> \<omega> \<in> mspace ?m \<and> mdist ?m f \<omega> < e)"
      by (rule MS.in_mball)
    also have "\<dots> = (\<omega> \<in> mspace ?m \<and> mdist ?m f \<omega> < e)"
      by (simp only: eqTrueI[OF f] simp_thms)
    also have "\<dots> = (\<omega> \<in> {\<omega> \<in> space ?F. mdist ?m f \<omega> < e})"
      by (simp only: spF mem_Collect_eq)
    finally show "(\<omega> \<in> MS.mball f e)
        = (\<omega> \<in> {\<omega> \<in> space ?F. mdist ?m f \<omega> < e})" .
  qed
  have "{\<omega> \<in> space ?F. mdist ?m f \<omega> < e} \<in> sets ?F"
    by (rule borel_measurable_less[OF mdist_measurable_natural_filtration[OF U f]
        borel_measurable_const])
  then show ?thesis unfolding mb[symmetric] .
qed

text \<open>And the balls generate: the path space is second countable, so its
  Borel \<open>\<sigma>\<close>-algebra is generated by any base
  (\<open>borel_of_second_countable'\<close>), and the balls are one.\<close>

theorem sets_natural_filtration_path:
  fixes U :: real
  assumes U: "0 \<le> U"
  shows "sets (natural_filtration
        (path_borel U :: ((real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})) measure)
        0 (\<lambda>v \<omega>. \<omega> v) U)
      = sets (path_borel U :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
proof -
  let ?m = "path_metric U :: ((real \<Rightarrow> 'a \<times> 'b)) metric"
  let ?B = "borel_of (mtopology_of ?m)"
  let ?F = "natural_filtration ?B 0 (\<lambda>v \<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> v) U"
  interpret MS: Metric_space "mspace ?m" "mdist ?m"
    by (rule Metric_space_mspace_mdist)
  let ?balls = "{MS.mball a \<epsilon> | a \<epsilon>. a \<in> mspace ?m \<and> \<epsilon> > 0}"
  have spF: "space ?F = mspace ?m" by (simp add: space_borel_of)
  have sub: "?balls \<subseteq> Pow (mspace ?m)" using MS.mball_subset_mspace by auto
  have base: "base_in (mtopology_of ?m) ?balls"
    using MS.mtopology_base_in_balls by (simp add: mtopology_of_def)
  have "?B = sigma (topspace (mtopology_of ?m)) ?balls"
    by (rule borel_of_second_countable'
        [OF second_countable_path_metric base_is_subbase[OF base]])
  then have "sets ?B = sigma_sets (mspace ?m) ?balls"
    using sets_measure_of[OF sub] by simp
  also have "\<dots> \<subseteq> sets ?F"
  proof -
    have "?balls \<subseteq> sets ?F" using mball_in_natural_filtration[OF U] by blast
    then have "sigma_sets (space ?F) ?balls \<subseteq> sets ?F"
      by (rule sets.sigma_sets_subset)
    then show ?thesis using spF by simp
  qed
  finally show ?thesis
    using sets_natural_filtration_path_subset[of U U] by blast
qed

subsection \<open>The conditioning rectangle lives in the past-plus-\<open>i\<close> filtration\<close>

text \<open>What \<open>integral_ksemi_rect_of_set_integral\<close> hands to the
  martingale property of \<open>P\<close> is the set \<open>\<phi> \<^sup>-\<^sup>1 (A \<times> A')\<close>.  For the martingale
  property to apply at time \<open>r + i\<close> that set must lie in \<open>\<F>\<^sub>(\<^sub>r\<^sub>+\<^sub>i\<^sub>)\<close>: the
  past factor is in \<open>\<F>\<^sub>r\<close> by @{thm [source] sets_natural_filtration_path},
  since \<open>A\<close> ranges over all Borel sets of the \<open>r\<close>-path space and not merely
  over the cut law's natural filtration, and the future factor is in
  \<open>\<F>\<^sub>(\<^sub>r\<^sub>+\<^sub>i\<^sub>)\<close> by \<open>pfut_filtration_measurable\<close>.\<close>

text \<open>\<open>sets_natural_filtration_mono\<close> and \<open>natural_filtration_cong_space\<close> live
  in @{theory Continuous_Time_Martingales.Natural_Filtration}.\<close>

lemma psd_kernel_eq:
  fixes a :: "real^'n::finite^'n" and q :: "real^'n"
  assumes a: "psd a" and z: "q \<bullet> (a *v q) = 0"
  shows "a *v q = 0"
proof -
  have sym: "transpose a = a" using a by (simp add: psd_def)
  have nn: "0 \<le> y \<bullet> (a *v y)" for y using a by (simp add: psd_def)
  have cross: "z \<bullet> (a *v q) = 0" for z
  proof (rule ccontr)
    assume ne: "z \<bullet> (a *v q) \<noteq> 0"
    define Bc where "Bc = z \<bullet> (a *v q)"
    define Ac where "Ac = z \<bullet> (a *v z)"
    have Bc0: "Bc \<noteq> 0" using ne by (simp add: Bc_def)
    have Ac0: "0 \<le> Ac" by (simp add: Ac_def nn)
    have qa: "q \<bullet> (a *v z) = Bc"
    proof -
      have "q \<bullet> (a *v z) = (transpose a *v q) \<bullet> z"
        by (rule inner_transpose_matrix)
      also have "\<dots> = (a *v q) \<bullet> z" using sym by simp
      also have "\<dots> = z \<bullet> (a *v q)" by (rule inner_commute)
      finally show ?thesis by (simp add: Bc_def)
    qed
    have expand: "(q + r *\<^sub>R z) \<bullet> (a *v (q + r *\<^sub>R z))
        = 2 * r * Bc + r\<^sup>2 * Ac" for r
    proof -
      have lin: "a *v (q + r *\<^sub>R z) = a *v q + r *\<^sub>R (a *v z)"
        by (simp add: matrix_vector_mult_def vec_eq_iff sum.distrib
            sum_distrib_left algebra_simps)
      show ?thesis
        unfolding lin
        by (simp add: z qa Bc_def Ac_def power2_eq_square
            algebra_simps)
    qed
    show False
    proof (cases "Ac = 0")
      case True
      have "0 \<le> 2 * (- Bc) * Bc + (- Bc)\<^sup>2 * Ac"
        using nn[of "q + (- Bc) *\<^sub>R z"] expand[of "- Bc"] by simp
      then have "Bc * Bc \<le> 0" using True by (simp add: power2_eq_square)
      moreover have "0 < Bc * Bc"
        using Bc0 by (cases "0 < Bc") (auto intro: mult_pos_pos mult_neg_neg
            simp: not_less le_less)
      ultimately show False by linarith
    next
      case False
      then have AcP: "0 < Ac" using Ac0 by simp
      define r where "r = - Bc / Ac"
      have "0 \<le> 2 * r * Bc + r\<^sup>2 * Ac"
        using nn[of "q + r *\<^sub>R z"] expand[of r] by simp
      also have "2 * r * Bc + r\<^sup>2 * Ac = - (Bc\<^sup>2 / Ac)"
        unfolding r_def using AcP by (simp add: power2_eq_square field_simps)
      finally have h: "Bc\<^sup>2 / Ac \<le> 0" by simp
      have "0 < Bc * Bc"
        using Bc0 by (cases "0 < Bc") (auto intro: mult_pos_pos mult_neg_neg
            simp: not_less le_less)
      then have "0 < Bc\<^sup>2 / Ac"
        using AcP by (simp add: power2_eq_square)
      with h show False by linarith
    qed
  qed
  have "(a *v q) \<bullet> (a *v q) = 0" using cross[of "a *v q"] by simp
  then show ?thesis by simp
qed

section \<open>Sums of outer products: the toolkit\<close>

text \<open>\<open>onormal_subset\<close> lives in
  @{theory Symmetric_Matrix_Spectra.Orthonormal_Families}.\<close>

lemma pair_eval_F_cont:
  fixes F :: "(real^'n::finite) \<times> (real^'n^'n) \<Rightarrow> real"
  assumes Fc: "continuous_on UNIV F" and t: "t \<in> {0..T}"
  shows "continuous_map
      (mtopology_of (path_metric T :: ('n pairpath) metric))
      euclideanreal (\<lambda>\<omega>. F (\<omega> t))"
proof -
  have ev: "continuous_map (mtopology_of (path_metric T :: ('n pairpath) metric))
      euclidean (\<lambda>\<omega>. \<omega> t)"
    by (rule continuous_map_path_eval[OF t])
  have Fm: "continuous_map (euclidean :: ((real^'n) \<times> (real^'n^'n)) topology)
      euclideanreal F"
    using Fc by simp
  show ?thesis
    using continuous_map_compose[OF ev Fm] by (simp add: o_def)
qed

lemma pair_eval_F_sq_cont:
  fixes F :: "(real^'n::finite) \<times> (real^'n^'n) \<Rightarrow> real"
  assumes Fc: "continuous_on UNIV F" and t: "t \<in> {0..T}"
  shows "continuous_map
      (mtopology_of (path_metric T :: ('n pairpath) metric))
      euclideanreal (\<lambda>\<omega>. (F (\<omega> t))\<^sup>2)"
proof -
  have "continuous_map
      (mtopology_of (path_metric T :: ('n pairpath) metric)) euclideanreal
      (\<lambda>\<omega>. F (\<omega> t) * F (\<omega> t))"
    by (rule continuous_map_real_mult[OF pair_eval_F_cont[OF Fc t]
          pair_eval_F_cont[OF Fc t]])
  then show ?thesis by (simp add: power2_eq_square)
qed

lemma matvec_sum_outer:
  fixes S :: "(real^'n::finite) set" and c :: "real^'n \<Rightarrow> real"
  assumes finS: "finite S"
  shows "(\<Sum>u\<in>S. c u *\<^sub>R outer_prod u u) *v z = (\<Sum>u\<in>S. (c u * (u \<bullet> z)) *\<^sub>R u)"
proof -
  have "(\<Sum>u\<in>S. c u *\<^sub>R outer_prod u u) *v z
      = (\<Sum>u\<in>S. (c u *\<^sub>R outer_prod u u) *v z)"
    by (rule matrix_vector_mult_sum)
  also have "\<dots> = (\<Sum>u\<in>S. (c u * (u \<bullet> z)) *\<^sub>R u)"
    by (rule sum.cong[OF refl])
      (simp add: scaleR_matrix_vector)
  finally show ?thesis .
qed

lemma pair_test_F_functional_cont:
  fixes F :: "(real^'n::finite) \<times> (real^'n^'n) \<Rightarrow> real"
    and h :: "('n pairpath) \<Rightarrow> real"
  assumes Fc: "continuous_on UNIV F"
    and st: "0 \<le> s" and sT: "s \<le> T" and tI: "t \<in> {0..T}"
    and hc: "continuous_map
        (mtopology_of (path_metric s :: ('n pairpath) metric)) euclideanreal h"
  shows "continuous_map
      (mtopology_of (path_metric T :: ('n pairpath) metric)) euclideanreal
      (\<lambda>\<omega>. h (restrict \<omega> {0..s}) * (F (\<omega> t) - F (\<omega> s)))"
proof -
  let ?PT = "mtopology_of (path_metric T :: ('n pairpath) metric)"
  have sI: "s \<in> {0..T}" using st sT by simp
  have part1: "continuous_map ?PT euclideanreal (\<lambda>\<omega>. F (\<omega> t) - F (\<omega> s))"
    by (intro continuous_map_diff pair_eval_F_cont[OF Fc] tI sI)
  have rc: "continuous_map ?PT
      (mtopology_of (path_metric s :: ('n pairpath) metric))
      (\<lambda>\<omega>. restrict \<omega> {0..s})"
    by (rule Lipschitz_continuous_imp_continuous_map
        [OF Lipschitz_restrict_path_metric[OF st sT]])
  have part2: "continuous_map ?PT euclideanreal (\<lambda>\<omega>. h (restrict \<omega> {0..s}))"
    using continuous_map_compose[OF rc hc] by (simp add: o_def)
  show ?thesis by (rule continuous_map_real_mult[OF part2 part1])
qed

lemma quadform_sum_outer:
  fixes S :: "(real^'n::finite) set" and c :: "real^'n \<Rightarrow> real"
  assumes finS: "finite S"
  shows "z \<bullet> ((\<Sum>u\<in>S. c u *\<^sub>R outer_prod u u) *v z) = (\<Sum>u\<in>S. c u * (u \<bullet> z)\<^sup>2)"
proof -
  have "z \<bullet> ((\<Sum>u\<in>S. c u *\<^sub>R outer_prod u u) *v z)
      = z \<bullet> (\<Sum>u\<in>S. (c u * (u \<bullet> z)) *\<^sub>R u)"
    by (simp add: matvec_sum_outer[OF finS])
  also have "\<dots> = (\<Sum>u\<in>S. z \<bullet> ((c u * (u \<bullet> z)) *\<^sub>R u))"
    by (rule inner_sum_right)
  also have "\<dots> = (\<Sum>u\<in>S. c u * (u \<bullet> z)\<^sup>2)"
    by (rule sum.cong[OF refl])
      (simp add: inner_commute power2_eq_square
        algebra_simps)
  finally show ?thesis .
qed

lemma pair_law_F_measurable:
  fixes N :: "('n::finite pairpath) measure"
    and F :: "(real^'n) \<times> (real^'n^'n) \<Rightarrow> real"
  assumes Fc: "continuous_on UNIV F"
    and setsN: "sets N = sets (path_borel T :: ('n pairpath) measure)"
    and u: "u \<in> {0..T}"
  shows "(\<lambda>\<omega>. F (\<omega> u)) \<in> borel_measurable N"
proof -
  have "(\<lambda>\<omega> :: 'n pairpath. F (\<omega> u))
      \<in> (path_borel T :: ('n pairpath) measure)
        \<rightarrow>\<^sub>M borel"
    using continuous_map_measurable[OF pair_eval_F_cont[OF Fc u]]
    by (simp add: borel_of_euclidean)
  then show ?thesis using measurable_cong_sets[OF setsN refl] by blast
qed

lemma traceM_sum_outer:
  fixes S :: "(real^'n::finite) set" and c :: "real^'n \<Rightarrow> real"
    and M :: "real^'n^'n"
  shows "trace (M ** (\<Sum>u\<in>S. c u *\<^sub>R outer_prod u u))
      = (\<Sum>u\<in>S. c u * (u \<bullet> (M *v u)))"
proof -
  have "M ** (\<Sum>u\<in>S. c u *\<^sub>R outer_prod u u)
      = (\<Sum>u\<in>S. M ** (c u *\<^sub>R outer_prod u u))"
    by (rule matrix_mult_sum_right)
  then have "trace (M ** (\<Sum>u\<in>S. c u *\<^sub>R outer_prod u u))
      = (\<Sum>u\<in>S. trace (M ** (c u *\<^sub>R outer_prod u u)))"
    by (simp add: trace_matrix_sum)
  also have "\<dots> = (\<Sum>u\<in>S. c u * (u \<bullet> (M *v u)))"
  proof (rule sum.cong[OF refl])
    fix u assume "u \<in> S"
    have "trace (M ** (c u *\<^sub>R outer_prod u u))
        = c u * trace (M ** outer_prod u u)"
      by (rule trace_mult_scaleR)
    also have "trace (M ** outer_prod u u) = u \<bullet> (M *v u)"
      using trace_mult_outerp[of M u] by (simp add: outerp_eq_outer_prod)
    finally show "trace (M ** (c u *\<^sub>R outer_prod u u))
        = c u * (u \<bullet> (M *v u))" .
  qed
  finally show ?thesis .
qed

text \<open>\<open>trace_mult_add\<close> lives in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>

lemma pair_law_F_sq_measurable:
  fixes N :: "('n::finite pairpath) measure"
    and F :: "(real^'n) \<times> (real^'n^'n) \<Rightarrow> real"
  assumes Fc: "continuous_on UNIV F"
    and setsN: "sets N = sets (path_borel T :: ('n pairpath) measure)"
    and u: "u \<in> {0..T}"
  shows "(\<lambda>\<omega>. (F (\<omega> u))\<^sup>2) \<in> borel_measurable N"
proof -
  have "(\<lambda>\<omega> :: 'n pairpath. (F (\<omega> u))\<^sup>2)
      \<in> (path_borel T :: ('n pairpath) measure)
        \<rightarrow>\<^sub>M borel"
    using continuous_map_measurable[OF pair_eval_F_sq_cont[OF Fc u]]
    by (simp add: borel_of_euclidean)
  then show ?thesis using measurable_cong_sets[OF setsN refl] by blast
qed

lemma onormal_parseval:
  fixes B :: "(real^'n::finite) set"
  assumes B: "onormal B" and sp: "span B = UNIV"
  shows "(\<Sum>u\<in>B. (u \<bullet> z)\<^sup>2) = z \<bullet> z"
proof -
  have finB: "finite B" by (rule onormal_finite[OF B])
  have "(\<Sum>u\<in>B. (u \<bullet> z)\<^sup>2) = (\<Sum>u\<in>B. 1 * (u \<bullet> z)\<^sup>2)" by simp
  also have "\<dots> = z \<bullet> ((\<Sum>u\<in>B. 1 *\<^sub>R outer_prod u u) *v z)"
    by (rule quadform_sum_outer[OF finB, symmetric])
  also have "(\<Sum>u\<in>B. (1::real) *\<^sub>R outer_prod u u) = (\<Sum>u\<in>B. outer_prod u u)"
    by simp
  also have "\<dots> = mat 1" by (rule onormal_complete[OF B sp])
  also have "z \<bullet> (mat 1 *v z) = z \<bullet> z" by simp
  finally show ?thesis .
qed

lemma pair_law_F_sq_integrable_of_nn_bound:
  fixes N :: "('n::finite pairpath) measure"
    and F :: "(real^'n) \<times> (real^'n^'n) \<Rightarrow> real"
  assumes Fc: "continuous_on UNIV F"
    and setsN: "sets N = sets (path_borel T :: ('n pairpath) measure)"
    and u: "u \<in> {0..T}"
    and bnd: "(\<integral>\<^sup>+\<omega>. ennreal ((F (\<omega> u))\<^sup>2) \<partial>N) \<le> ennreal C"
  shows "integrable N (\<lambda>\<omega>. (F (\<omega> u))\<^sup>2)"
proof -
  have m: "(\<lambda>\<omega>. (F (\<omega> u))\<^sup>2) \<in> borel_measurable N"
    by (rule pair_law_F_sq_measurable[OF Fc setsN u])
  have lt: "(\<integral>\<^sup>+\<omega>. ennreal (norm ((F (\<omega> u))\<^sup>2)) \<partial>N) < \<infinity>"
  proof -
    have "(\<integral>\<^sup>+\<omega>. ennreal (norm ((F (\<omega> u))\<^sup>2)) \<partial>N) \<le> ennreal C"
      using bnd by simp
    also have "ennreal C < \<infinity>" by simp
    finally show ?thesis .
  qed
  show ?thesis unfolding integrable_iff_bounded using m lt by blast
qed

lemma euOrth_mset:
  fixes G :: "real^'n::finite \<Rightarrow> real^'n" and h :: real
  assumes Gc: "continuous_on UNIV G"
  shows "{\<omega> \<in> space (path_borel T :: ('n pairpath) measure).
      \<forall>j<m. G (fst (\<omega> (real j * h))) \<bullet>
        (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0}
    \<in> sets (path_borel T :: ('n pairpath) measure)"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  have per: "{\<omega> \<in> space ?B. G (fst (\<omega> (real j * h))) \<bullet>
      (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0}
      \<in> sets ?B" for j
  proof -
    have evu: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (real (Suc j) * h)) \<in> ?B \<rightarrow>\<^sub>M borel"
      by (rule pair_law_eval_measurable[OF refl])
    have evv: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (real j * h)) \<in> ?B \<rightarrow>\<^sub>M borel"
      by (rule pair_law_eval_measurable[OF refl])
    have pairm: "(\<lambda>\<omega> :: 'n pairpath.
        (\<omega> (real (Suc j) * h), \<omega> (real j * h))) \<in> ?B \<rightarrow>\<^sub>M borel"
      using evu evv by (simp add: borel_prod[symmetric])
    have contf: "(\<lambda>ab :: ((real^'n) \<times> (real^'n^'n))
          \<times> ((real^'n) \<times> (real^'n^'n)).
        G (fst (snd ab)) \<bullet> (fst (fst ab) - fst (snd ab)))
        \<in> borel_measurable borel"
    proof (intro borel_measurable_continuous_onI)
      have p1: "continuous_on UNIV (\<lambda>ab :: ((real^'n) \<times> (real^'n^'n))
          \<times> ((real^'n) \<times> (real^'n^'n)). fst (fst ab))"
        by (intro continuous_on_fst continuous_on_id)
      have p2: "continuous_on UNIV (\<lambda>ab :: ((real^'n) \<times> (real^'n^'n))
          \<times> ((real^'n) \<times> (real^'n^'n)). fst (snd ab))"
        by (intro continuous_on_fst continuous_on_snd continuous_on_id)
      have Gcomp: "continuous_on UNIV (\<lambda>ab :: ((real^'n) \<times> (real^'n^'n))
          \<times> ((real^'n) \<times> (real^'n^'n)). G (fst (snd ab)))"
        by (rule continuous_on_compose2[OF Gc p2]) auto
      show "continuous_on UNIV (\<lambda>ab :: ((real^'n) \<times> (real^'n^'n))
          \<times> ((real^'n) \<times> (real^'n^'n)).
          G (fst (snd ab)) \<bullet> (fst (fst ab) - fst (snd ab)))"
        by (intro continuous_intros Gcomp p1 p2)
    qed
    have fm: "(\<lambda>\<omega> :: 'n pairpath. G (fst (\<omega> (real j * h))) \<bullet>
        (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))))
        \<in> borel_measurable ?B"
      using measurable_compose[OF pairm contf] by simp
    have "{\<omega> \<in> space ?B. G (fst (\<omega> (real j * h))) \<bullet>
        (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0}
        = (\<lambda>\<omega> :: 'n pairpath. G (fst (\<omega> (real j * h))) \<bullet>
          (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))))
          -` {0} \<inter> space ?B"
      by auto
    then show ?thesis using measurable_sets[OF fm] by simp
  qed
  show ?thesis
  proof (induction m)
    case 0
    show ?case by simp
  next
    case (Suc m)
    have eq: "{\<omega> \<in> space ?B. \<forall>j<Suc m. G (fst (\<omega> (real j * h))) \<bullet>
        (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0}
        = {\<omega> \<in> space ?B. \<forall>j<m. G (fst (\<omega> (real j * h))) \<bullet>
            (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0}
          \<inter> {\<omega> \<in> space ?B. G (fst (\<omega> (real m * h))) \<bullet>
            (fst (\<omega> (real (Suc m) * h)) - fst (\<omega> (real m * h))) = 0}"
      by (auto simp: less_Suc_eq)
    show ?case unfolding eq by (intro sets.Int Suc.IH per)
  qed
qed

lemma onormal_span_parseval:
  fixes S :: "(real^'n::finite) set"
  assumes S: "onormal S" and x: "x \<in> span S"
  shows "(\<Sum>u\<in>S. (u \<bullet> x)\<^sup>2) = x \<bullet> x"
proof -
  have finS: "finite S" by (rule onormal_finite[OF S])
  have "x \<bullet> x = x \<bullet> (\<Sum>u\<in>S. (u \<bullet> x) *\<^sub>R u)"
    by (simp add: onormal_expand[OF S x])
  also have "\<dots> = (\<Sum>u\<in>S. x \<bullet> ((u \<bullet> x) *\<^sub>R u))"
    by (rule inner_sum_right)
  also have "\<dots> = (\<Sum>u\<in>S. (u \<bullet> x)\<^sup>2)"
    by (rule sum.cong[OF refl])
      (simp add: inner_commute power2_eq_square)
  finally show ?thesis by simp
qed

section \<open>Selecting a value-minimal index set: the threshold argument\<close>

text \<open>\<open>exists_min_subset\<close> lives in @{theory Symmetric_Matrix_Spectra.Ky_Fan}.\<close>

lemma pair_law_F_sq_mean_of_nn_bound:
  fixes N :: "('n::finite pairpath) measure"
    and F :: "(real^'n) \<times> (real^'n^'n) \<Rightarrow> real"
  assumes int: "integrable N (\<lambda>\<omega>. (F (\<omega> u))\<^sup>2)" and C0: "0 \<le> C"
    and bnd: "(\<integral>\<^sup>+\<omega>. ennreal ((F (\<omega> u))\<^sup>2) \<partial>N) \<le> ennreal C"
  shows "(\<integral>\<omega>. (F (\<omega> u))\<^sup>2 \<partial>N) \<le> C"
proof -
  have "ennreal (\<integral>\<omega>. (F (\<omega> u))\<^sup>2 \<partial>N) = (\<integral>\<^sup>+\<omega>. ennreal ((F (\<omega> u))\<^sup>2) \<partial>N)"
    by (rule nn_integral_eq_integral[OF int, symmetric]) simp
  also have "\<dots> \<le> ennreal C" by (rule bnd)
  finally show ?thesis using C0 by simp
qed

lemma pair_test_F_measurable:
  fixes N :: "('n::finite pairpath) measure" and h :: "('n pairpath) \<Rightarrow> real"
    and F :: "(real^'n) \<times> (real^'n^'n) \<Rightarrow> real"
  assumes Fc: "continuous_on UNIV F"
    and setsN: "sets N = sets (path_borel T :: ('n pairpath) measure)"
    and st: "0 \<le> s" and ts: "s \<le> t" and tT: "t \<le> T"
    and hc: "continuous_map
        (mtopology_of (path_metric s :: ('n pairpath) metric)) euclideanreal h"
  shows "(\<lambda>\<omega>. h (restrict \<omega> {0..s}) * (F (\<omega> t) - F (\<omega> s)))
      \<in> borel_measurable N"
proof -
  have sT: "s \<le> T" using ts tT by simp
  have tI: "t \<in> {0..T}" using st ts tT by simp
  have "(\<lambda>\<omega> :: 'n pairpath. h (restrict \<omega> {0..s}) * (F (\<omega> t) - F (\<omega> s)))
      \<in> (path_borel T :: ('n pairpath) measure)
        \<rightarrow>\<^sub>M borel"
    using continuous_map_measurable
      [OF pair_test_F_functional_cont[OF Fc st sT tI hc]]
    by (simp add: borel_of_euclidean)
  then show ?thesis using measurable_cong_sets[OF setsN refl] by blast
qed

lemma weighted_min_value:
  fixes w c :: "'a \<Rightarrow> real"
  assumes finB: "finite B" and m1: "1 \<le> m" and mB: "m \<le> card B"
    and c0: "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> c u" and c1: "\<And>u. u \<in> B \<Longrightarrow> c u \<le> 1"
    and csum: "real m \<le> (\<Sum>u\<in>B. c u)"
  obtains S where "S \<subseteq> B" and "m \<le> card S"
    and "(\<Sum>u\<in>S. w u) \<le> (\<Sum>u\<in>B. c u * w u)"
proof -
  obtain S0 where S0: "S0 \<subseteq> B" and cS0: "card S0 = m"
    and least: "\<forall>u\<in>S0. \<forall>v\<in>B - S0. w u \<le> w v"
    using exists_min_subset[OF finB mB] by blast
  have finS0: "finite S0" using S0 finB by (rule finite_subset)
  have neS0: "S0 \<noteq> {}" using cS0 m1 by auto
  define Neg where "Neg = {u \<in> B. w u < 0}"
  have finNeg: "finite Neg" unfolding Neg_def using finB by simp
  define \<tau> where "\<tau> = Max (w ` S0)"
  have tauS0: "\<And>u. u \<in> S0 \<Longrightarrow> w u \<le> \<tau>"
    unfolding \<tau>_def by (intro Max_ge finite_imageI finS0) blast
  have tauout: "\<And>v. v \<in> B - S0 \<Longrightarrow> \<tau> \<le> w v"
    unfolding \<tau>_def
    by (intro Max.boundedI finite_imageI finS0)
      (use neS0 least in blast)+
  show ?thesis
  proof (cases "Neg \<subseteq> S0")
    case True
    \<comment> \<open>the threshold is \<open>max \<tau> 0\<close>; every term is compared against it\<close>
    define tp where "tp = max \<tau> 0"
    have tp0: "0 \<le> tp" by (simp add: tp_def)
    have key: "0 \<le> (\<Sum>u\<in>B. c u * w u) - (\<Sum>u\<in>S0. w u)"
    proof -
      have split: "(\<Sum>u\<in>B. c u * w u)
          = (\<Sum>u\<in>S0. c u * w u) + (\<Sum>u\<in>B - S0. c u * w u)"
        using sum.subset_diff[OF S0 finB, of "\<lambda>u. c u * w u"] by simp
      have inS: "\<And>u. u \<in> S0 \<Longrightarrow> (c u - 1) * tp \<le> (c u - 1) * w u"
      proof -
        fix u assume u: "u \<in> S0"
        have wle: "w u \<le> tp" using tauS0[OF u] by (simp add: tp_def)
        have cle: "c u - 1 \<le> 0" using c1 S0 u by auto
        show "(c u - 1) * tp \<le> (c u - 1) * w u"
          using mult_left_mono_neg[OF wle cle] by simp
      qed
      have outS: "\<And>u. u \<in> B - S0 \<Longrightarrow> c u * tp \<le> c u * w u"
      proof -
        fix u assume u: "u \<in> B - S0"
        have w0: "0 \<le> w u" using True u unfolding Neg_def by auto
        have wge: "tp \<le> w u"
          using tauout[OF u] w0 by (simp add: tp_def)
        have c0': "0 \<le> c u" using c0 u by auto
        show "c u * tp \<le> c u * w u"
          by (rule mult_left_mono[OF wge c0'])
      qed
      have "(\<Sum>u\<in>B. c u * w u) - (\<Sum>u\<in>S0. w u)
          = (\<Sum>u\<in>S0. (c u - 1) * w u) + (\<Sum>u\<in>B - S0. c u * w u)"
        unfolding split by (simp add: sum_subtractf algebra_simps)
      moreover have "(\<Sum>u\<in>S0. (c u - 1) * tp) + (\<Sum>u\<in>B - S0. c u * tp)
          \<le> (\<Sum>u\<in>S0. (c u - 1) * w u) + (\<Sum>u\<in>B - S0. c u * w u)"
        by (intro add_mono sum_mono inS outS)
      moreover have "(\<Sum>u\<in>S0. (c u - 1) * tp) + (\<Sum>u\<in>B - S0. c u * tp)
          = tp * ((\<Sum>u\<in>B. c u) - real m)"
      proof -
        have h1: "(\<Sum>u\<in>S0. (c u - 1) * tp)
            = (\<Sum>u\<in>S0. c u * tp) - real m * tp"
          by (simp add: sum_subtractf cS0 algebra_simps)
        have h2: "(\<Sum>u\<in>S0. c u * tp) + (\<Sum>u\<in>B - S0. c u * tp)
            = (\<Sum>u\<in>B. c u * tp)"
          using sum.subset_diff[OF S0 finB, of "\<lambda>u. c u * tp"] by simp
        have h3: "(\<Sum>u\<in>B. c u * tp) = (\<Sum>u\<in>B. c u) * tp"
          by (simp add: sum_distrib_right)
        show ?thesis using h1 h2 h3 by (simp add: algebra_simps)
      qed
      moreover have "0 \<le> tp * ((\<Sum>u\<in>B. c u) - real m)"
        using tp0 csum by simp
      ultimately show ?thesis by linarith
    qed
    show ?thesis
      by (rule that[of S0]) (use S0 cS0 key in auto)
  next
    case False
    \<comment> \<open>a negative weight escaped the minimal set, so \<open>\<tau> < 0\<close> and taking all
      negatives on top of \<open>S0\<close> costs nothing\<close>
    obtain vn where vn: "vn \<in> Neg" "vn \<notin> S0" using False by blast
    have tneg: "\<tau> < 0"
    proof -
      have "\<tau> \<le> w vn"
        using tauout vn unfolding Neg_def by auto
      also have "w vn < 0" using vn unfolding Neg_def by auto
      finally show ?thesis .
    qed
    define S where "S = S0 \<union> Neg"
    have SB: "S \<subseteq> B" unfolding S_def Neg_def using S0 by auto
    have finS: "finite S" using SB finB by (rule finite_subset)
    have cardS: "m \<le> card S"
      unfolding S_def using cS0 card_mono[OF finS[unfolded S_def], of S0]
      by simp
    have inS: "\<And>u. u \<in> S \<Longrightarrow> w u \<le> 0"
    proof -
      fix u assume "u \<in> S"
      then consider "u \<in> S0" | "u \<in> Neg" unfolding S_def by blast
      then show "w u \<le> 0"
      proof cases
        case 1 then show ?thesis using tauS0 tneg by fastforce
      next
        case 2 then show ?thesis unfolding Neg_def by auto
      qed
    qed
    have key: "0 \<le> (\<Sum>u\<in>B. c u * w u) - (\<Sum>u\<in>S. w u)"
    proof -
      have split: "(\<Sum>u\<in>B. c u * w u)
          = (\<Sum>u\<in>S. c u * w u) + (\<Sum>u\<in>B - S. c u * w u)"
        using sum.subset_diff[OF SB finB, of "\<lambda>u. c u * w u"] by simp
      have t1: "0 \<le> (\<Sum>u\<in>S. (c u - 1) * w u)"
      proof (rule sum_nonneg)
        fix u assume u: "u \<in> S"
        have c1': "c u - 1 \<le> 0" using c1 SB u by auto
        have w0: "w u \<le> 0" by (rule inS[OF u])
        show "0 \<le> (c u - 1) * w u" by (rule mult_nonpos_nonpos[OF c1' w0])
      qed
      have t2: "0 \<le> (\<Sum>u\<in>B - S. c u * w u)"
      proof (rule sum_nonneg)
        fix u assume u: "u \<in> B - S"
        have "0 \<le> w u" using u unfolding S_def Neg_def by auto
        then show "0 \<le> c u * w u" using c0 u by auto
      qed
      have "(\<Sum>u\<in>B. c u * w u) - (\<Sum>u\<in>S. w u)
          = (\<Sum>u\<in>S. (c u - 1) * w u) + (\<Sum>u\<in>B - S. c u * w u)"
        unfolding split by (simp add: sum_subtractf algebra_simps)
      with t1 t2 show ?thesis by linarith
    qed
    show ?thesis
      by (rule that[of S]) (use SB cardS key in auto)
  qed
qed

section \<open>From the convexified constraint to a feasible witness\<close>

text \<open>The step the paper never needs to make explicit: a matrix of the
  convexified constraint set that kills \<open>q\<close> dominates, in any linear
  value, a matrix of the original feasible set of Eq. (1.9).  The
  construction is a capped spectral split: write \<open>b\<close> in its eigenbasis,
  cut the eigenvalues at \<open>1\<close>, decompose the capped part by the threshold
  selection --- its atoms are projections, so they carry eigenvalue cap
  \<open>1\<close> --- and hand the excess, bounded by \<open>L - 1\<close>, to the chosen atom.
  The cap closes at \<open>1 + (L-1) = L\<close>, exactly why the split must happen at
  level \<open>1\<close> and nowhere else.  Orthogonality to \<open>q\<close> survives because every
  eigendirection that carries weight is orthogonal to \<open>q\<close> already.\<close>

lemma pair_test_F_sq_bound:
  fixes N :: "('n::finite pairpath) measure" and h :: "('n pairpath) \<Rightarrow> real"
    and F :: "(real^'n) \<times> (real^'n^'n) \<Rightarrow> real"
  assumes P: "prob_space N" and Fc: "continuous_on UNIV F"
    and setsN: "sets N = sets (path_borel T :: ('n pairpath) measure)"
    and st: "0 \<le> s" and ts: "s \<le> t" and tT: "t \<le> T"
    and hc: "continuous_map
        (mtopology_of (path_metric s :: ('n pairpath) metric)) euclideanreal h"
    and hb: "\<And>g. \<bar>h g\<bar> \<le> B"
    and C0: "0 \<le> C"
    and Cs: "(\<integral>\<^sup>+\<omega>. ennreal ((F (\<omega> s))\<^sup>2) \<partial>N) \<le> ennreal C"
    and Ct: "(\<integral>\<^sup>+\<omega>. ennreal ((F (\<omega> t))\<^sup>2) \<partial>N) \<le> ennreal C"
  shows "integrable N (\<lambda>\<omega>. (h (restrict \<omega> {0..s}) * (F (\<omega> t) - F (\<omega> s)))\<^sup>2)"
    and "(\<integral>\<omega>. (h (restrict \<omega> {0..s}) * (F (\<omega> t) - F (\<omega> s)))\<^sup>2 \<partial>N)
        \<le> 4 * B\<^sup>2 * C"
proof -
  let ?f = "\<lambda>\<omega> :: 'n pairpath. h (restrict \<omega> {0..s}) * (F (\<omega> t) - F (\<omega> s))"
  let ?D = "\<lambda>\<omega> :: 'n pairpath. 2 * B\<^sup>2 * ((F (\<omega> t))\<^sup>2 + (F (\<omega> s))\<^sup>2)"
  have sI: "s \<in> {0..T}" using st ts tT by simp
  have tI: "t \<in> {0..T}" using st ts tT by simp
  have B0: "0 \<le> B" by (rule order_trans[OF abs_ge_zero hb])
  have iss: "integrable N (\<lambda>\<omega>. (F (\<omega> s))\<^sup>2)"
    by (rule pair_law_F_sq_integrable_of_nn_bound[OF Fc setsN sI Cs])
  have itt: "integrable N (\<lambda>\<omega>. (F (\<omega> t))\<^sup>2)"
    by (rule pair_law_F_sq_integrable_of_nn_bound[OF Fc setsN tI Ct])
  have fm: "?f \<in> borel_measurable N"
    by (rule pair_test_F_measurable[OF Fc setsN st ts tT hc])
  have fsqm: "(\<lambda>\<omega>. (?f \<omega>)\<^sup>2) \<in> borel_measurable N" using fm by measurable
  have dom_int: "integrable N ?D"
    by (intro integrable_mult_right Bochner_Integration.integrable_add itt iss)
  have ptwise: "(?f \<omega>)\<^sup>2 \<le> ?D \<omega>" for \<omega>
  proof -
    have hsq: "(h (restrict \<omega> {0..s}))\<^sup>2 \<le> B\<^sup>2"
    proof -
      have "\<bar>h (restrict \<omega> {0..s})\<bar>\<^sup>2 \<le> B\<^sup>2"
        by (rule power_mono[OF hb abs_ge_zero])
      then show ?thesis by simp
    qed
    have e1: "2 * ((F (\<omega> t))\<^sup>2 + (F (\<omega> s))\<^sup>2) - (F (\<omega> t) - F (\<omega> s))\<^sup>2
        = (F (\<omega> t) + F (\<omega> s))\<^sup>2"
      by (simp add: power2_diff power2_sum)
    have sq_le: "(F (\<omega> t) - F (\<omega> s))\<^sup>2 \<le> 2 * ((F (\<omega> t))\<^sup>2 + (F (\<omega> s))\<^sup>2)"
      using e1 zero_le_power2[of "F (\<omega> t) + F (\<omega> s)"] by linarith
    have "(?f \<omega>)\<^sup>2 = (h (restrict \<omega> {0..s}))\<^sup>2 * (F (\<omega> t) - F (\<omega> s))\<^sup>2"
      by (simp add: power_mult_distrib)
    also have "\<dots> \<le> B\<^sup>2 * (F (\<omega> t) - F (\<omega> s))\<^sup>2"
      by (rule mult_right_mono[OF hsq zero_le_power2])
    also have "\<dots> \<le> B\<^sup>2 * (2 * ((F (\<omega> t))\<^sup>2 + (F (\<omega> s))\<^sup>2))"
      by (rule mult_left_mono[OF sq_le zero_le_power2])
    also have "\<dots> = ?D \<omega>" by simp
    finally show ?thesis .
  qed
  show fsq_int: "integrable N (\<lambda>\<omega>. (?f \<omega>)\<^sup>2)"
  proof (rule Bochner_Integration.integrable_bound[OF dom_int fsqm])
    show "AE \<omega> in N. norm ((?f \<omega>)\<^sup>2) \<le> norm (?D \<omega>)"
    proof (intro AE_I2)
      fix \<omega> :: "'n pairpath"
      have "0 \<le> ?D \<omega>" by simp
      then show "norm ((?f \<omega>)\<^sup>2) \<le> norm (?D \<omega>)" using ptwise[of \<omega>] by simp
    qed
  qed
  have Bs: "(\<integral>\<omega>. (F (\<omega> s))\<^sup>2 \<partial>N) \<le> C"
    by (rule pair_law_F_sq_mean_of_nn_bound[OF iss C0 Cs])
  have Bt: "(\<integral>\<omega>. (F (\<omega> t))\<^sup>2 \<partial>N) \<le> C"
    by (rule pair_law_F_sq_mean_of_nn_bound[OF itt C0 Ct])
  have "(\<integral>\<omega>. (?f \<omega>)\<^sup>2 \<partial>N) \<le> (\<integral>\<omega>. ?D \<omega> \<partial>N)"
    by (rule integral_mono[OF fsq_int dom_int]) (rule ptwise)
  also have "(\<integral>\<omega>. ?D \<omega> \<partial>N)
      = 2 * B\<^sup>2 * ((\<integral>\<omega>. (F (\<omega> t))\<^sup>2 \<partial>N) + (\<integral>\<omega>. (F (\<omega> s))\<^sup>2 \<partial>N))"
    by (simp add: Bochner_Integration.integral_add[OF itt iss])
  also have "\<dots> \<le> 2 * B\<^sup>2 * (2 * C)"
    by (rule mult_left_mono) (use Bs Bt zero_le_power2 in auto)
  also have "\<dots> = 4 * B\<^sup>2 * C" by simp
  finally show "(\<integral>\<omega>. (?f \<omega>)\<^sup>2 \<partial>N) \<le> 4 * B\<^sup>2 * C" .
qed

lemma norm_outerp: "norm (outerp (v :: real^'n::finite)) = norm v * norm v"
proof -
  have "outerp v = outer_prod v v" by (simp add: outerp_def outer_prod_def)
  then show ?thesis by (simp add: norm_outer_prod)
qed

text \<open>\<open>pair_fst_borel\<close>, \<open>pair_snd_borel\<close> live in @{theory Continuous_Time_Martingales.Integrability_Criteria}.\<close>

lemma outerp_borel:
  "(outerp :: real^'n::finite \<Rightarrow> real^'n^'n) \<in> borel_measurable borel"
proof -
  have e: "(outerp :: real^'n \<Rightarrow> real^'n^'n) = (\<lambda>v. \<chi> i j. v $ i * v $ j)"
    by (rule ext) (simp add: outerp_def)
  show ?thesis unfolding e
    by (intro borel_measurable_continuous_onI continuous_on_vec_lambda
        continuous_intros)
qed

lemma comp_eval_entry_measurable:
  "(\<lambda>p' :: 'n::finite pairpath. (outerp (fst (p' u)) - snd (p' u)) $ cc $ dd)
     \<in> borel_measurable
       (path_borel T :: ('n pairpath) measure)"
proof (rule measurable_compose[OF pair_law_eval_measurable[OF refl]])
  have f: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n) \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  have s: "(snd :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n^'n) \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  have o: "(\<lambda>pr :: (real^'n) \<times> (real^'n^'n). outerp (fst pr))
      \<in> borel_measurable borel"
    by (rule measurable_compose[OF f outerp_borel])
  have dm: "(\<lambda>pr :: (real^'n) \<times> (real^'n^'n). outerp (fst pr) - snd pr)
      \<in> borel_measurable borel"
    by (rule borel_measurable_diff[OF o s])
  have n1: "(\<lambda>v :: real^'n^'n. v $ cc) \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI)
      (rule linear_continuous_on[OF bounded_linear_vec_nth])
  have n2: "(\<lambda>v :: real^'n. v $ dd) \<in> borel_measurable borel"
    by (rule borel_measurable_nth)
  show "(\<lambda>pr :: (real^'n) \<times> (real^'n^'n). (outerp (fst pr) - snd pr) $ cc $ dd)
      \<in> borel_measurable borel"
    by (rule measurable_compose[OF measurable_compose[OF dm n1] n2])
qed

lemma pair_test_F_integrable:
  fixes N :: "('n::finite pairpath) measure" and h :: "('n pairpath) \<Rightarrow> real"
    and F :: "(real^'n) \<times> (real^'n^'n) \<Rightarrow> real"
  assumes P: "prob_space N" and Fc: "continuous_on UNIV F"
    and setsN: "sets N = sets (path_borel T :: ('n pairpath) measure)"
    and st: "0 \<le> s" and ts: "s \<le> t" and tT: "t \<le> T"
    and hc: "continuous_map
        (mtopology_of (path_metric s :: ('n pairpath) metric)) euclideanreal h"
    and hb: "\<And>g. \<bar>h g\<bar> \<le> B"
    and C0: "0 \<le> C"
    and Cs: "(\<integral>\<^sup>+\<omega>. ennreal ((F (\<omega> s))\<^sup>2) \<partial>N) \<le> ennreal C"
    and Ct: "(\<integral>\<^sup>+\<omega>. ennreal ((F (\<omega> t))\<^sup>2) \<partial>N) \<le> ennreal C"
  shows "integrable N (\<lambda>\<omega>. h (restrict \<omega> {0..s}) * (F (\<omega> t) - F (\<omega> s)))"
proof -
  have fmN: "finite_measure N" using P by (simp add: prob_space_def)
  show ?thesis
    by (rule integrable_of_sq_integrable[OF fmN
          pair_test_F_measurable[OF Fc setsN st ts tT hc]
          pair_test_F_sq_bound(1)[OF P Fc setsN st ts tT hc hb C0 Cs Ct]])
qed

subsection \<open>The test identity and its weak limit, generically\<close>

theorem martingale_test_F:
  fixes N :: "('n::finite pairpath) measure" and h :: "('n pairpath) \<Rightarrow> real"
    and F :: "(real^'n) \<times> (real^'n^'n) \<Rightarrow> real"
  assumes P: "prob_space N"
    and setsN: "sets N = sets (path_borel T :: ('n pairpath) measure)"
    and mgF: "martingale N (natural_filtration N 0 (\<lambda>u \<omega>. \<omega> u)) 0
        (\<lambda>u \<omega>. F (\<omega> (min u T)))"
    and st: "0 \<le> s" and ts: "s \<le> t" and tT: "t \<le> T"
    and hm: "h \<in> borel_measurable (path_borel s :: ('n pairpath) measure)"
    and hb: "\<And>g. \<bar>h g\<bar> \<le> B"
  shows "(\<integral>\<omega>. h (restrict \<omega> {0..s}) * (F (\<omega> t) - F (\<omega> s)) \<partial>N) = 0"
proof -
  let ?FF = "natural_filtration N 0 (\<lambda>u \<omega> :: 'n pairpath. \<omega> u)"
  let ?Y = "\<lambda>u \<omega> :: 'n pairpath. F (\<omega> (min u T))"
  let ?Z = "\<lambda>\<omega> :: 'n pairpath. h (restrict \<omega> {0..s})"
  have sT: "s \<le> T" using ts tT by simp
  have t0: "0 \<le> t" using st ts by simp
  have mt: "min t T = t" using tT by simp
  have ms: "min s T = s" using sT by simp
  interpret P: prob_space N by (rule P)
  interpret MY: martingale N ?FF 0 ?Y by (rule mgF)
  have Zm: "?Z \<in> borel_measurable (?FF s)"
    by (rule past_test_measurable_natural_filtration[OF setsN st sT hm])
  have ZM: "?Z \<in> borel_measurable N"
    by (rule measurable_from_subalg[OF MY.subalgebras[OF st] Zm])
  have prod_int: "integrable N (\<lambda>\<omega>. ?Z \<omega> * ?Y u \<omega>)" if u: "0 \<le> u" for u
  proof (rule Bochner_Integration.integrable_bound)
    show "integrable N (\<lambda>\<omega>. \<bar>B\<bar> * \<bar>?Y u \<omega>\<bar>)"
      by (intro integrable_mult_right Bochner_Integration.integrable_abs
          MY.integrable[OF u])
    show "(\<lambda>\<omega>. ?Z \<omega> * ?Y u \<omega>) \<in> borel_measurable N"
      using ZM borel_measurable_integrable[OF MY.integrable[OF u]]
      by measurable
    show "AE \<omega> in N. norm (?Z \<omega> * ?Y u \<omega>) \<le> norm (\<bar>B\<bar> * \<bar>?Y u \<omega>\<bar>)"
    proof (intro AE_I2)
      fix \<omega> :: "'n pairpath"
      have "\<bar>?Z \<omega>\<bar> \<le> \<bar>B\<bar>" using hb[of "restrict \<omega> {0..s}"] by simp
      then have "\<bar>?Z \<omega> * ?Y u \<omega>\<bar> \<le> \<bar>B\<bar> * \<bar>?Y u \<omega>\<bar>"
        by (simp add: abs_mult mult_right_mono)
      then show "norm (?Z \<omega> * ?Y u \<omega>) \<le> norm (\<bar>B\<bar> * \<bar>?Y u \<omega>\<bar>)" by simp
    qed
  qed
  have int_t: "integrable N (\<lambda>\<omega>. ?Z \<omega> * ?Y t \<omega>)" by (rule prod_int[OF t0])
  have int_s: "integrable N (\<lambda>\<omega>. ?Z \<omega> * ?Y s \<omega>)" by (rule prod_int[OF st])
  have eqts: "(\<integral>\<omega>. ?Z \<omega> * ?Y t \<omega> \<partial>N) = (\<integral>\<omega>. ?Z \<omega> * ?Y s \<omega> \<partial>N)"
    by (rule martingale_bounded_test[OF mgF st ts Zm int_t int_s])
  have "(\<integral>\<omega>. ?Z \<omega> * (?Y t \<omega> - ?Y s \<omega>) \<partial>N)
      = (\<integral>\<omega>. ?Z \<omega> * ?Y t \<omega> \<partial>N) - (\<integral>\<omega>. ?Z \<omega> * ?Y s \<omega> \<partial>N)"
    using Bochner_Integration.integral_diff[OF int_t int_s]
    by (simp add: right_diff_distrib)
  then show ?thesis using eqts mt ms by simp
qed

theorem martingale_test_F_limit:
  fixes Qm :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and Q :: "('n pairpath) measure" and h :: "('n pairpath) \<Rightarrow> real"
    and F :: "(real^'n) \<times> (real^'n^'n) \<Rightarrow> real"
  assumes Fc: "continuous_on UNIV F"
    and Pm: "\<And>m. prob_space (Qm m)"
    and setsm: "\<And>m. sets (Qm m) = sets (path_borel T :: ('n pairpath) measure)"
    and mgm: "\<And>m. martingale (Qm m) (natural_filtration (Qm m) 0 (\<lambda>u \<omega>. \<omega> u)) 0
        (\<lambda>u \<omega>. F (\<omega> (min u T)))"
    and wc: "weak_conv_on Qm Q sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
    and prob: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and C0: "0 \<le> C"
    and nnm: "\<And>m u. u \<in> {0..T} \<Longrightarrow>
        (\<integral>\<^sup>+\<omega>. ennreal ((F (\<omega> u))\<^sup>2) \<partial>(Qm m)) \<le> ennreal C"
    and st: "0 \<le> s" and ts: "s \<le> t" and tT: "t \<le> T"
    and hc: "continuous_map
        (mtopology_of (path_metric s :: ('n pairpath) metric)) euclideanreal h"
    and hb: "\<And>g. \<bar>h g\<bar> \<le> B"
  shows "(\<integral>\<omega>. h (restrict \<omega> {0..s}) * (F (\<omega> t) - F (\<omega> s)) \<partial>Q) = 0"
proof -
  let ?f = "\<lambda>\<omega> :: 'n pairpath. h (restrict \<omega> {0..s}) * (F (\<omega> t) - F (\<omega> s))"
  have sT: "s \<le> T" using ts tT by simp
  have sI: "s \<in> {0..T}" using st sT by simp
  have tI: "t \<in> {0..T}" using st ts tT by simp
  have B0: "0 \<le> B" by (rule order_trans[OF abs_ge_zero hb])
  have fmm: "finite_measure (Qm m)" for m
    using Pm by (simp add: prob_space_def)
  have fmQ: "finite_measure Q" using prob by (simp add: prob_space_def)
  have nnQ: "(\<integral>\<^sup>+\<omega>. ennreal ((F (\<omega> u))\<^sup>2) \<partial>Q) \<le> ennreal C" if u: "u \<in> {0..T}"
    for u
    by (rule weak_conv_on_nn_integral_le
        [OF wc pair_eval_F_sq_cont[OF Fc u] _ C0 nnm[OF u]]) simp
  have intm: "integrable (Qm m) ?f" for m
    by (rule pair_test_F_integrable[OF Pm Fc setsm st ts tT hc hb C0
          nnm[OF sI] nnm[OF tI]])
  have intQ: "integrable Q ?f"
    by (rule pair_test_F_integrable[OF prob Fc setsQ st ts tT hc hb C0
          nnQ[OF sI] nnQ[OF tI]])
  have lim: "(\<lambda>m. \<integral>\<omega>. ?f \<omega> \<partial>(Qm m)) \<longlonglongrightarrow> (\<integral>\<omega>. ?f \<omega> \<partial>Q)"
  proof (rule weak_conv_integral_of_L2_bound)
    show "weak_conv_on Qm Q sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))" by (rule wc)
    show "continuous_map (mtopology_of (path_metric T :: ('n pairpath) metric))
        euclideanreal ?f"
      by (rule pair_test_F_functional_cont[OF Fc st sT tI hc])
    show "\<And>m. finite_measure (Qm m)" by (rule fmm)
    show "finite_measure Q" by (rule fmQ)
    show "\<And>m. integrable (Qm m) ?f" by (rule intm)
    show "integrable Q ?f" by (rule intQ)
    show "\<And>m Rr. integrable (Qm m) (\<lambda>w. max (- Rr) (min Rr (?f w)))"
      by (rule clamp_integrable[OF fmm borel_measurable_integrable[OF intm]])
    show "\<And>Rr. integrable Q (\<lambda>w. max (- Rr) (min Rr (?f w)))"
      by (rule clamp_integrable[OF fmQ borel_measurable_integrable[OF intQ]])
    show "\<And>m Rr. integrable (Qm m)
        (\<lambda>w. \<bar>?f w\<bar> * indicat_real {z. Rr < \<bar>z\<bar>} (?f w))"
      by (rule tail_integrable[OF intm])
    show "\<And>Rr. integrable Q (\<lambda>w. \<bar>?f w\<bar> * indicat_real {z. Rr < \<bar>z\<bar>} (?f w))"
      by (rule tail_integrable[OF intQ])
    show "0 \<le> 4 * B\<^sup>2 * C" using C0 by simp
    show "\<And>m. (\<integral>w. (?f w)\<^sup>2 \<partial>(Qm m)) \<le> 4 * B\<^sup>2 * C"
      by (rule pair_test_F_sq_bound(2)[OF Pm Fc setsm st ts tT hc hb C0
            nnm[OF sI] nnm[OF tI]])
    show "(\<integral>w. (?f w)\<^sup>2 \<partial>Q) \<le> 4 * B\<^sup>2 * C"
      by (rule pair_test_F_sq_bound(2)[OF prob Fc setsQ st ts tT hc hb C0
            nnQ[OF sI] nnQ[OF tI]])
    show "\<And>m. integrable (Qm m) (\<lambda>w. (?f w)\<^sup>2)"
      by (rule pair_test_F_sq_bound(1)[OF Pm Fc setsm st ts tT hc hb C0
            nnm[OF sI] nnm[OF tI]])
    show "integrable Q (\<lambda>w. (?f w)\<^sup>2)"
      by (rule pair_test_F_sq_bound(1)[OF prob Fc setsQ st ts tT hc hb C0
            nnQ[OF sI] nnQ[OF tI]])
  qed
  have hm: "h \<in> borel_measurable (path_borel s :: ('n pairpath) measure)"
    using continuous_map_measurable[OF hc] by (simp add: borel_of_euclidean)
  have zero: "(\<integral>\<omega>. ?f \<omega> \<partial>(Qm m)) = 0" for m
    by (rule martingale_test_F[OF Pm setsm mgm st ts tT hm hb])
  have z: "(\<lambda>m. \<integral>\<omega>. ?f \<omega> \<partial>(Qm m)) \<longlonglongrightarrow> 0" using zero by simp
  show ?thesis by (rule tendsto_unique[OF _ lim z]) simp
qed

subsection \<open>The set-integral identity and martingale reassembly,
  generically\<close>

lemma subalgebra_natural_filtration_path:
  fixes Q :: "((real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})) measure"
  assumes setsQ: "sets Q = sets (path_borel S :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  shows "subalgebra Q (natural_filtration Q 0 (\<lambda>v w. w v) u)"
proof -
  let ?B = "(path_borel S :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  have "natural_filtration Q 0 (\<lambda>v w :: (real \<Rightarrow> 'a \<times> 'b). w v) u
      = natural_filtration ?B 0 (\<lambda>v w. w v) u"
    by (rule natural_filtration_cong_space)
       (simp add: sets_eq_imp_space_eq[OF setsQ])
  then have "sets (natural_filtration Q 0 (\<lambda>v w :: (real \<Rightarrow> 'a \<times> 'b). w v) u)
      \<subseteq> sets Q"
    using sets_natural_filtration_path_subset[of S u] setsQ by simp
  then show ?thesis unfolding subalgebra_def by simp
qed

lemma sigma_finite_subalgebra_natural_filtration_path:
  fixes Q :: "((real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})) measure"
  assumes PS: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel S :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  shows "sigma_finite_subalgebra Q (natural_filtration Q 0 (\<lambda>v w. w v) u)"
proof (rule finite_measure_subalgebra_is_sigma_finite)
  show "finite_measure_subalgebra Q
      (natural_filtration Q 0 (\<lambda>v w :: (real \<Rightarrow> 'a \<times> 'b). w v) u)"
    by (simp add: finite_measure_subalgebra_def
        finite_measure_subalgebra_axioms_def prob_space.finite_measure[OF PS]
        subalgebra_natural_filtration_path[OF setsQ])
qed

theorem integrable_and_set_integral_eq_of_rational_times:
  fixes Q :: "((real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})) measure"
    and Z :: "real \<Rightarrow> (real \<Rightarrow> 'a \<times> 'b) \<Rightarrow> real"
  assumes S: "0 \<le> S"
    and setsQ: "sets Q = sets (path_borel S :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
    and PS: "prob_space Q"
    and Zm: "\<And>u. u \<in> {0..S} \<Longrightarrow>
        Z u \<in> borel_measurable (natural_filtration Q 0 (\<lambda>v w. w v) u)"
    and Zint: "\<And>q. q \<in> \<rat> \<Longrightarrow> q \<in> {0..S} \<Longrightarrow> integrable Q (Z q)"
    and ZintS: "integrable Q (Z S)"
    and Zcont: "\<And>w. w \<in> space Q \<Longrightarrow> continuous_on {0..S} (\<lambda>u. Z u w)"
    and rat: "\<And>q A. q \<in> \<rat> \<Longrightarrow> q \<in> {0..S} \<Longrightarrow>
        A \<in> sets (natural_filtration Q 0 (\<lambda>v w. w v) q) \<Longrightarrow>
        set_lebesgue_integral Q A (Z q) = set_lebesgue_integral Q A (Z S)"
    and i: "i \<in> {0..S}"
  shows "integrable Q (Z i)
      \<and> (\<forall>A \<in> sets (natural_filtration Q 0 (\<lambda>v w. w v) i).
          set_lebesgue_integral Q A (Z i) = set_lebesgue_integral Q A (Z S))"
proof (cases "i = S")
  case True
  then show ?thesis using ZintS by simp
next
  case False
  let ?F = "\<lambda>u. natural_filtration Q 0 (\<lambda>v w :: (real \<Rightarrow> 'a \<times> 'b). w v) u"
  interpret PQ: prob_space Q by (rule PS)
  have iS: "i < S" using i False by simp
  have SS: "S \<in> {0..S}" using S by simp

  \<comment> \<open>rationals decreasing to \<open>i\<close> from above, inside the horizon\<close>
  have ex: "\<exists>q\<in>(\<rat> :: real set). i < q \<and> q < min S (i + inverse (real (Suc n)))"
    for n
  proof (rule Rats_dense_in_real)
    show "i < min S (i + inverse (real (Suc n)))" using iS by simp
  qed
  then obtain q :: "nat \<Rightarrow> real" where qrat: "\<And>n. q n \<in> \<rat>"
    and qgt: "\<And>n. i < q n"
    and qlt: "\<And>n. q n < min S (i + inverse (real (Suc n)))" by metis
  have qle: "q n \<le> S" for n using qlt[of n] by simp
  have q0S: "q n \<in> {0..S}" for n using i qgt[of n] qle[of n] by simp
  have qconv: "q \<longlonglongrightarrow> i"
  proof (rule tendsto_sandwich[of "\<lambda>_. i" _ _ "\<lambda>n. i + inverse (real (Suc n))"])
    show "\<forall>\<^sub>F n in sequentially. i \<le> q n" using qgt by (simp add: less_imp_le)
    show "\<forall>\<^sub>F n in sequentially. q n \<le> i + inverse (real (Suc n))"
      using qlt by (simp add: less_imp_le)
  qed (use LIMSEQ_inverse_real_of_nat_add in auto)

  \<comment> \<open>the filtration facts\<close>
  have subA: "subalgebra Q (?F u)" for u
    by (rule subalgebra_natural_filtration_path[OF setsQ])
  have sfs: "sigma_finite_subalgebra Q (?F u)" for u
    by (rule sigma_finite_subalgebra_natural_filtration_path[OF PS setsQ])
  have ZmQ: "Z u \<in> borel_measurable Q" if u: "u \<in> {0..S}" for u
    by (rule measurable_from_subalg[OF subA Zm[OF u]])

  \<comment> \<open>uniform integrability, straight off the averaging form\<close>
  have ui: "unif_integrable Q (\<lambda>n. Z (q n))"
  proof (rule prob_space.unif_integrable_of_averaging[OF PS])
    show "integrable Q (Z S)" by (rule ZintS)
    show "sigma_finite_subalgebra Q (?F (q n))" for n by (rule sfs)
    show "integrable Q (Z (q n))" for n by (rule Zint[OF qrat q0S])
    show "Z (q n) \<in> borel_measurable (?F (q n))" for n by (rule Zm[OF q0S])
    show "set_lebesgue_integral Q B (Z S) = set_lebesgue_integral Q B (Z (q n))"
      if "B \<in> sets (?F (q n))" for n B
      by (rule rat[OF qrat q0S that, symmetric])
  qed

  \<comment> \<open>pointwise convergence, from path continuity\<close>
  have conv: "AE w in Q. (\<lambda>n. Z (q n) w) \<longlonglongrightarrow> Z i w"
  proof (rule AE_I2)
    fix w :: "(real \<Rightarrow> 'a \<times> 'b)" assume w: "w \<in> space Q"
    have "((\<lambda>u. Z u w) \<circ> q) \<longlonglongrightarrow> Z i w"
      using Zcont[OF w] q0S i qconv by (simp add: continuous_on_sequentially)
    then show "(\<lambda>n. Z (q n) w) \<longlonglongrightarrow> Z i w" by (simp add: o_def)
  qed

  \<comment> \<open>integrability at the IRRATIONAL time comes free from the same argument\<close>
  have Zi: "integrable Q (Z i)"
    by (rule finite_measure.unif_integrable_limit_integrable
        [OF PQ.finite_measure_axioms ui ZmQ[OF i] conv])
  have vit: "(\<lambda>n. \<integral>w. \<bar>Z (q n) w - Z i w\<bar> \<partial>Q) \<longlonglongrightarrow> 0"
    by (rule finite_measure.vitali_convergence
        [OF PQ.finite_measure_axioms ui ZmQ[OF i] conv])

  \<comment> \<open>and the set integrals follow the \<open>L\<^sup>1\<close> limit\<close>
  have main: "set_lebesgue_integral Q A (Z i) = set_lebesgue_integral Q A (Z S)"
    if A: "A \<in> sets (?F i)" for A
  proof -
    have AQ: "A \<in> sets Q" using A subA[of i] by (auto simp: subalgebra_def)
    have AF: "A \<in> sets (?F (q n))" for n
      using A sets_natural_filtration_mono[of i "q n"] qgt[of n] by auto
    have bnd: "\<bar>set_lebesgue_integral Q A (Z S) - set_lebesgue_integral Q A (Z i)\<bar>
        \<le> (\<integral>w. \<bar>Z (q n) w - Z i w\<bar> \<partial>Q)" for n
    proof -
      have s1: "set_integrable Q A (Z (q n))"
        unfolding set_integrable_def
        by (rule integrable_mult_indicator[OF AQ Zint[OF qrat q0S]])
      have s2: "set_integrable Q A (Z i)"
        unfolding set_integrable_def
        by (rule integrable_mult_indicator[OF AQ Zi])
      have dd: "integrable Q (\<lambda>w. indicat_real A w *\<^sub>R (Z (q n) w - Z i w))"
        by (rule integrable_mult_indicator[OF AQ
            Bochner_Integration.integrable_diff[OF Zint[OF qrat q0S] Zi]])
      have d1: "integrable Q (\<lambda>w. \<bar>indicat_real A w *\<^sub>R (Z (q n) w - Z i w)\<bar>)"
        by (rule integrable_abs[OF dd])
      have d2: "integrable Q (\<lambda>w. \<bar>Z (q n) w - Z i w\<bar>)"
        by (intro integrable_abs Bochner_Integration.integrable_diff
            Zint[OF qrat q0S] Zi)
      have "\<bar>set_lebesgue_integral Q A (Z S) - set_lebesgue_integral Q A (Z i)\<bar>
          = \<bar>set_lebesgue_integral Q A (Z (q n))
              - set_lebesgue_integral Q A (Z i)\<bar>"
        using rat[OF qrat q0S AF] by simp
      also have "\<dots> = \<bar>\<integral>w. indicat_real A w *\<^sub>R (Z (q n) w - Z i w) \<partial>Q\<bar>"
        using set_integral_diff(2)[OF s1 s2]
        unfolding set_lebesgue_integral_def by (simp add: scaleR_diff_right)
      also have "\<dots> \<le> (\<integral>w. \<bar>indicat_real A w *\<^sub>R (Z (q n) w - Z i w)\<bar> \<partial>Q)"
        by (rule integral_abs_bound)
      also have "\<dots> \<le> (\<integral>w. \<bar>Z (q n) w - Z i w\<bar> \<partial>Q)"
        by (rule integral_mono[OF d1 d2]) (simp add: indicator_def)
      finally show ?thesis .
    qed
    have "\<bar>set_lebesgue_integral Q A (Z S)
        - set_lebesgue_integral Q A (Z i)\<bar> \<le> 0"
      by (rule LIMSEQ_le_const[OF vit]) (use bnd in blast)
    then show ?thesis by simp
  qed
  show ?thesis using Zi main by blast
qed

subsection \<open>From a generating \<open>\<pi>\<close>-system to the whole sub-\<open>\<sigma>\<close>-algebra\<close>

text \<open>The conditioning set \<open>A'\<close> of \<open>pfut_rcd_X_increment_zero\<close>
  also ranges over a countable family, so what arrives at almost every \<open>p'\<close>
  is the vanishing of the set integral on a \<open>\<pi>\<close>-system only.  Upgrading that
  to the generated \<open>\<sigma>\<close>-algebra is a Dynkin argument: \<open>sigma_sets_induct_disjoint\<close> does the induction and \<open>lebesgue_integral_countable_add\<close> discharges its disjoint-union case.  The
  lemma is stated for a general measure and generating \<open>\<pi>\<close>-system, and also
  serves clause (iv).\<close>

text \<open>\<open>set_integral_zero_of_generator\<close> lives in
  @{theory Continuous_Time_Martingales.Natural_Filtration}: passing the
  vanishing of set integrals from a generating \<open>\<pi>\<close>-system to the whole
  generated \<open>\<sigma>\<close>-algebra.\<close>

text \<open>The \<open>\<pi>\<close>-system for the previous lemma: \<open>\<F>\<^sub>s\<close> is the pullback of the
  \<open>s\<close>-path space's Borel sets along \<open>pcut\<close>, via @{thm [source]
  natural_filtration_eq_restrict_vimage} and \<open>pcut_vimage_natural_filtration\<close>, so second countability of that space
  (@{thm [source] second_countable_path_metric}) hands over a countable base
  with no limit argument.\<close>

theorem martingale_event_F_limit:
  fixes Qm :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and Q :: "('n pairpath) measure"
    and F :: "(real^'n) \<times> (real^'n^'n) \<Rightarrow> real"
  assumes Fc: "continuous_on UNIV F"
    and Pm: "\<And>m. prob_space (Qm m)"
    and setsm: "\<And>m. sets (Qm m) = sets (path_borel T :: ('n pairpath) measure)"
    and mgm: "\<And>m. martingale (Qm m) (natural_filtration (Qm m) 0 (\<lambda>u \<omega>. \<omega> u)) 0
        (\<lambda>u \<omega>. F (\<omega> (min u T)))"
    and wc: "weak_conv_on Qm Q sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
    and prob: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and C0: "0 \<le> C"
    and nnm: "\<And>m u. u \<in> {0..T} \<Longrightarrow>
        (\<integral>\<^sup>+\<omega>. ennreal ((F (\<omega> u))\<^sup>2) \<partial>(Qm m)) \<le> ennreal C"
    and st: "0 \<le> s" and ts: "s \<le> t" and tT: "t \<le> T"
    and Bs: "Bs \<in> sets (path_borel s :: ('n pairpath) measure)"
  shows "(\<integral>\<omega>. indicat_real Bs (restrict \<omega> {0..s}) * (F (\<omega> t) - F (\<omega> s)) \<partial>Q)
      = 0"
proof -
  let ?PS = "mtopology_of (path_metric s :: ('n pairpath) metric)"
  let ?g = "\<lambda>\<omega> :: 'n pairpath. F (\<omega> t) - F (\<omega> s)"
  let ?p = "\<lambda>\<omega> :: 'n pairpath. restrict \<omega> {0..s}"
  have sT: "s \<le> T" using ts tT by simp
  have sI: "s \<in> {0..T}" using st sT by simp
  have tI: "t \<in> {0..T}" using st ts tT by simp
  have fmQ: "finite_measure Q" using prob by (simp add: prob_space_def)
  have nnQ: "(\<integral>\<^sup>+\<omega>. ennreal ((F (\<omega> u))\<^sup>2) \<partial>Q) \<le> ennreal C" if u: "u \<in> {0..T}"
    for u
    by (rule weak_conv_on_nn_integral_le
        [OF wc pair_eval_F_sq_cont[OF Fc u] _ C0 nnm[OF u]]) simp
  have onec: "continuous_map ?PS euclideanreal (\<lambda>_. 1 :: real)" by simp
  have one_b: "\<And>g :: 'n pairpath. \<bar>(\<lambda>_. 1 :: real) g\<bar> \<le> 1" by simp
  have gint: "integrable Q ?g"
  proof -
    have "integrable Q (\<lambda>\<omega>. (\<lambda>_. 1 :: real) (?p \<omega>) * (F (\<omega> t) - F (\<omega> s)))"
      by (rule pair_test_F_integrable[OF prob Fc setsQ st ts tT onec one_b C0
            nnQ[OF sI] nnQ[OF tI]])
    then show ?thesis by simp
  qed
  have gmeasQ: "?g \<in> borel_measurable Q"
    by (rule borel_measurable_integrable[OF gint])
  have rc: "continuous_map
      (mtopology_of (path_metric T :: ('n pairpath) metric)) ?PS ?p"
    by (rule Lipschitz_continuous_imp_continuous_map
        [OF Lipschitz_restrict_path_metric[OF st sT]])
  have pimQ: "?p \<in> Q \<rightarrow>\<^sub>M borel_of ?PS"
    using continuous_map_measurable[OF rc] measurable_cong_sets[OF setsQ refl]
    by blast
  define gp where "gp = (\<lambda>\<omega> :: 'n pairpath. max (?g \<omega>) 0)"
  define gm where "gm = (\<lambda>\<omega> :: 'n pairpath. max (- ?g \<omega>) 0)"
  have gp0: "\<And>\<omega>. 0 \<le> gp \<omega>" and gm0: "\<And>\<omega>. 0 \<le> gm \<omega>"
    unfolding gp_def gm_def by simp_all
  have gdiff: "gp \<omega> - gm \<omega> = ?g \<omega>" for \<omega>
    unfolding gp_def gm_def by (simp add: max_def)
  have gpm: "gp \<in> borel_measurable Q" and gmm: "gm \<in> borel_measurable Q"
    unfolding gp_def gm_def
    by (intro borel_measurable_max gmeasQ borel_measurable_const
        borel_measurable_uminus)+
  have gpi: "integrable Q gp" and gmi: "integrable Q gm"
    unfolding gp_def gm_def
    by (rule Bochner_Integration.integrable_max
        [OF gint Bochner_Integration.integrable_zero],
        rule Bochner_Integration.integrable_max
        [OF Bochner_Integration.integrable_minus[OF gint]
            Bochner_Integration.integrable_zero])
  define N1 where "N1 = distr (density Q (\<lambda>\<omega>. ennreal (gp \<omega>))) (borel_of ?PS) ?p"
  define N2 where "N2 = distr (density Q (\<lambda>\<omega>. ennreal (gm \<omega>))) (borel_of ?PS) ?p"
  have sN1: "sets N1 = sets (borel_of ?PS)"
    and sN2: "sets N2 = sets (borel_of ?PS)"
    unfolding N1_def N2_def by simp_all
  have pdm: "?p \<in> density Q (\<lambda>\<omega>. ennreal (w \<omega>)) \<rightarrow>\<^sub>M borel_of ?PS" for w
    using pimQ measurable_cong_sets[OF sets_density refl] by blast
  have push: "(\<integral>y. u y \<partial>(distr (density Q (\<lambda>\<omega>. ennreal (w \<omega>)))
        (borel_of ?PS) ?p)) = (\<integral>\<omega>. u (?p \<omega>) * w \<omega> \<partial>Q)"
    if um: "u \<in> borel_measurable (borel_of ?PS)"
    and wm: "w \<in> borel_measurable Q" and w0: "\<And>\<omega>. 0 \<le> w \<omega>" for u w
  proof -
    have cmp: "(\<lambda>\<omega>. u (?p \<omega>)) \<in> borel_measurable Q"
      using measurable_comp[OF pimQ um] by (simp add: o_def)
    have "(\<integral>y. u y \<partial>(distr (density Q (\<lambda>\<omega>. ennreal (w \<omega>))) (borel_of ?PS) ?p))
        = (\<integral>\<omega>. u (?p \<omega>) \<partial>(density Q (\<lambda>\<omega>. ennreal (w \<omega>))))"
      by (rule Bochner_Integration.integral_distr[OF pdm um])
    also have "\<dots> = (\<integral>\<omega>. u (?p \<omega>) * w \<omega> \<partial>Q)"
      by (subst integral_density)
        (use cmp wm w0 in \<open>auto simp: mult.commute\<close>)
    finally show ?thesis .
  qed
  have finw: "finite_measure (distr (density Q (\<lambda>\<omega>. ennreal (w \<omega>)))
      (borel_of ?PS) ?p)"
    if wm: "w \<in> borel_measurable Q" and w0: "\<And>\<omega>. 0 \<le> w \<omega>"
    and wi: "integrable Q w" for w
  proof (rule finite_measureI)
    let ?D = "density Q (\<lambda>\<omega>. ennreal (w \<omega>))"
    have sp: "space (distr ?D (borel_of ?PS) ?p) = space (borel_of ?PS)" by simp
    have pre: "?p -` space (borel_of ?PS) \<inter> space ?D = space Q"
      using measurable_space[OF pdm[of w]] by auto
    have "emeasure (distr ?D (borel_of ?PS) ?p)
        (space (distr ?D (borel_of ?PS) ?p))
        = emeasure ?D (?p -` space (borel_of ?PS) \<inter> space ?D)"
      unfolding sp by (intro emeasure_distr pdm) (metis sets.top space_borel_of)
    also have "\<dots> = emeasure ?D (space Q)" unfolding pre ..
    also have "\<dots> = (\<integral>\<^sup>+\<omega>. ennreal (w \<omega>) * indicator (space Q) \<omega> \<partial>Q)"
      by (intro emeasure_density measurable_compose[OF wm measurable_ennreal]) auto
    also have "\<dots> = (\<integral>\<^sup>+\<omega>. ennreal (w \<omega>) \<partial>Q)"
      by (intro nn_integral_cong) (simp add: indicator_def)
    also have "\<dots> = ennreal (\<integral>\<omega>. w \<omega> \<partial>Q)"
      by (rule nn_integral_eq_integral[OF wi]) (use w0 in simp)
    also have "\<dots> < \<infinity>" by simp
    finally show "emeasure (distr ?D (borel_of ?PS) ?p)
        (space (distr ?D (borel_of ?PS) ?p)) \<noteq> \<infinity>" by simp
  qed
  have finN1: "finite_measure N1" unfolding N1_def by (rule finw[OF gpm gp0 gpi])
  have finN2: "finite_measure N2" unfolding N2_def by (rule finw[OF gmm gm0 gmi])
  have NEQ: "N1 = N2"
  proof (rule metric_measure_eqI_bounded_cts[OF sN1 sN2 finN1 finN2])
    fix u :: "'n pairpath \<Rightarrow> real"
    assume uc: "continuous_map ?PS euclideanreal u"
    assume ub: "\<exists>B. \<forall>y\<in>topspace ?PS. \<bar>u y\<bar> \<le> B"
    then obtain B where B: "\<And>y. y \<in> topspace ?PS \<Longrightarrow> \<bar>u y\<bar> \<le> B" by blast
    define B' where "B' = max B 0"
    have B'0: "0 \<le> B'" unfolding B'_def by simp
    let ?u = "\<lambda>y. rclamp B' (u y)"
    have ucl: "continuous_map ?PS euclideanreal ?u"
      using continuous_map_compose[OF uc rclamp_cont] by (simp add: o_def)
    have ubd: "\<And>y. \<bar>?u y\<bar> \<le> B'" by (rule rclamp_bound[OF B'0])
    have uagree: "?u y = u y"
      if y: "y \<in> mspace (path_metric s :: ('n pairpath) metric)" for y
    proof (rule rclamp_id)
      have "\<bar>u y\<bar> \<le> B" using B y by simp
      then show "\<bar>u y\<bar> \<le> B'" unfolding B'_def by simp
    qed
    have um: "u \<in> borel_measurable (borel_of ?PS)"
      using continuous_map_measurable[OF uc] by (simp add: borel_of_euclidean)
    have ucm: "?u \<in> borel_measurable (borel_of ?PS)"
      using continuous_map_measurable[OF ucl] by (simp add: borel_of_euclidean)
    have same: "(\<integral>y. u y \<partial>Nj) = (\<integral>y. ?u y \<partial>Nj)"
      if sj: "sets Nj = sets (borel_of ?PS)" for Nj
    proof (rule integral_cong_AE)
      show "u \<in> borel_measurable Nj"
        using um measurable_cong_sets[OF sj refl] by blast
      show "?u \<in> borel_measurable Nj"
        using ucm measurable_cong_sets[OF sj refl] by blast
      have "space Nj = mspace (path_metric s :: ('n pairpath) metric)"
        using sets_eq_imp_space_eq[OF sj] by (simp add: space_borel_of)
      then show "AE y in Nj. u y = ?u y"
        by (intro AE_I2) (simp add: uagree)
    qed
    have zero: "(\<integral>\<omega>. ?u (?p \<omega>) * ?g \<omega> \<partial>Q) = 0"
      by (rule martingale_test_F_limit
          [OF Fc Pm setsm mgm wc prob setsQ C0 nnm st ts tT ucl ubd])
    have i1: "integrable Q (\<lambda>\<omega>. ?u (?p \<omega>) * gp \<omega>)"
      and i2: "integrable Q (\<lambda>\<omega>. ?u (?p \<omega>) * gm \<omega>)"
    proof -
      have cmp: "(\<lambda>\<omega>. ?u (?p \<omega>)) \<in> borel_measurable Q"
        using measurable_comp[OF pimQ ucm] by (simp add: o_def)
      show "integrable Q (\<lambda>\<omega>. ?u (?p \<omega>) * gp \<omega>)"
        by (rule Bochner_Integration.integrable_bound
            [OF integrable_mult_right[OF gpi, of B'] _ ])
          (use cmp gpm ubd gp0 B'0 in
            \<open>auto intro!: borel_measurable_times
              simp: abs_mult mult_right_mono\<close>)
      show "integrable Q (\<lambda>\<omega>. ?u (?p \<omega>) * gm \<omega>)"
        by (rule Bochner_Integration.integrable_bound
            [OF integrable_mult_right[OF gmi, of B'] _ ])
          (use cmp gmm ubd gm0 B'0 in
            \<open>auto intro!: borel_measurable_times
              simp: abs_mult mult_right_mono\<close>)
    qed
    have "(\<integral>y. ?u y \<partial>N1) - (\<integral>y. ?u y \<partial>N2)
        = (\<integral>\<omega>. ?u (?p \<omega>) * gp \<omega> \<partial>Q) - (\<integral>\<omega>. ?u (?p \<omega>) * gm \<omega> \<partial>Q)"
      unfolding N1_def N2_def
      by (simp add: push[OF ucm gpm gp0] push[OF ucm gmm gm0])
    also have "\<dots> = (\<integral>\<omega>. ?u (?p \<omega>) * gp \<omega> - ?u (?p \<omega>) * gm \<omega> \<partial>Q)"
      by (rule Bochner_Integration.integral_diff[OF i1 i2, symmetric])
    also have "\<dots> = (\<integral>\<omega>. ?u (?p \<omega>) * ?g \<omega> \<partial>Q)"
    proof -
      have fe: "(\<lambda>\<omega>. ?u (?p \<omega>) * gp \<omega> - ?u (?p \<omega>) * gm \<omega>)
          = (\<lambda>\<omega>. ?u (?p \<omega>) * ?g \<omega>)"
        by (rule ext) (simp add: gdiff[symmetric] right_diff_distrib)
      show ?thesis by (simp only: fe)
    qed
    also have "\<dots> = 0" by (rule zero)
    finally have "(\<integral>y. ?u y \<partial>N1) = (\<integral>y. ?u y \<partial>N2)" by simp
    then show "(\<integral>y. u y \<partial>N1) = (\<integral>y. u y \<partial>N2)"
      using same[OF sN1] same[OF sN2] by simp
  qed
  have iB1: "integrable Q (\<lambda>\<omega>. indicat_real Bs (?p \<omega>) * gp \<omega>)"
    and iB2: "integrable Q (\<lambda>\<omega>. indicat_real Bs (?p \<omega>) * gm \<omega>)"
  proof -
    have cmp: "(\<lambda>\<omega>. indicat_real Bs (?p \<omega>)) \<in> borel_measurable Q"
      using measurable_comp[OF pimQ borel_measurable_indicator[OF Bs]]
      by (simp add: o_def)
    show "integrable Q (\<lambda>\<omega>. indicat_real Bs (?p \<omega>) * gp \<omega>)"
      by (rule Bochner_Integration.integrable_bound[OF gpi _])
        (use cmp gpm gp0 in
          \<open>auto intro!: borel_measurable_times simp: indicator_def\<close>)
    show "integrable Q (\<lambda>\<omega>. indicat_real Bs (?p \<omega>) * gm \<omega>)"
      by (rule Bochner_Integration.integrable_bound[OF gmi _])
        (use cmp gmm gm0 in
          \<open>auto intro!: borel_measurable_times simp: indicator_def\<close>)
  qed
  have "(\<integral>\<omega>. indicat_real Bs (?p \<omega>) * gp \<omega> \<partial>Q) = (\<integral>y. indicat_real Bs y \<partial>N1)"
    unfolding N1_def
    by (rule push[OF borel_measurable_indicator[OF Bs] gpm gp0, symmetric])
  also have "\<dots> = (\<integral>y. indicat_real Bs y \<partial>N2)" unfolding NEQ ..
  also have "\<dots> = (\<integral>\<omega>. indicat_real Bs (?p \<omega>) * gm \<omega> \<partial>Q)"
    unfolding N2_def
    by (rule push[OF borel_measurable_indicator[OF Bs] gmm gm0])
  finally have keq: "(\<integral>\<omega>. indicat_real Bs (?p \<omega>) * gp \<omega> \<partial>Q)
      = (\<integral>\<omega>. indicat_real Bs (?p \<omega>) * gm \<omega> \<partial>Q)" .
  have feB: "(\<lambda>\<omega>. indicat_real Bs (?p \<omega>) * gp \<omega>
        - indicat_real Bs (?p \<omega>) * gm \<omega>)
      = (\<lambda>\<omega>. indicat_real Bs (?p \<omega>) * ?g \<omega>)"
    by (rule ext) (simp add: gdiff[symmetric] right_diff_distrib)
  have "(\<integral>\<omega>. indicat_real Bs (?p \<omega>) * ?g \<omega> \<partial>Q)
      = (\<integral>\<omega>. indicat_real Bs (?p \<omega>) * gp \<omega> - indicat_real Bs (?p \<omega>) * gm \<omega> \<partial>Q)"
    by (simp only: feB)
  also have "\<dots> = (\<integral>\<omega>. indicat_real Bs (?p \<omega>) * gp \<omega> \<partial>Q)
      - (\<integral>\<omega>. indicat_real Bs (?p \<omega>) * gm \<omega> \<partial>Q)"
    by (rule Bochner_Integration.integral_diff[OF iB1 iB2])
  also have "\<dots> = 0" using keq by simp
  finally show ?thesis .
qed

lemma countable_Int_stable_generator_path:
  fixes s :: real
  obtains D where
    "countable D"
    and "Int_stable D"
    and "D \<subseteq> Pow (mspace (path_metric s :: ((real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})) metric))"
    and "mspace (path_metric s :: ((real \<Rightarrow> 'a \<times> 'b)) metric) \<in> D"
    and "sets (path_borel s :: ((real \<Rightarrow> 'a \<times> 'b)) measure)
        = sigma_sets (mspace (path_metric s :: ((real \<Rightarrow> 'a \<times> 'b)) metric)) D"
proof -
  let ?m = "path_metric s :: ((real \<Rightarrow> 'a \<times> 'b)) metric"
  let ?X = "mtopology_of ?m"
  have sc: "second_countable ?X" by (rule second_countable_path_metric)
  \<comment> \<open>NB the base must not be called \<open>OO\<close>: that name is the relation-composition
      operator and the statement then fails to parse\<close>
  then obtain BB where cB: "countable BB" and bB: "base_in ?X BB"
    using second_countable_base_in by blast
  have Bsub: "U \<subseteq> mspace ?m" if "U \<in> BB" for U
    using base_in_subset[OF bB that] by simp
  define B1 where "B1 = insert (mspace ?m) BB"
  have cB1: "countable B1" unfolding B1_def using cB by simp
  have B1sub: "U \<subseteq> mspace ?m" if "U \<in> B1" for U
    using that Bsub unfolding B1_def by auto
  define FF where "FF = {F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> B1}"
  define D where "D = (\<lambda>F. \<Inter> F) ` FF"

  \<comment> \<open>membership in \<open>D\<close>, introduced and eliminated WITHOUT search: \<open>blast\<close> on
      the existential behind an image diverges (it has to invent the witness)\<close>
  have DE: "\<And>A. A \<in> D \<Longrightarrow> (\<And>F. A = \<Inter> F \<Longrightarrow> finite F \<Longrightarrow> F \<noteq> {} \<Longrightarrow> F \<subseteq> B1 \<Longrightarrow> thesis')
      \<Longrightarrow> thesis'" for thesis'
  proof -
    fix A assume AD: "A \<in> D"
      and W: "\<And>F. A = \<Inter> F \<Longrightarrow> finite F \<Longrightarrow> F \<noteq> {} \<Longrightarrow> F \<subseteq> B1 \<Longrightarrow> thesis'"
    from AD obtain F where Aeq: "A = \<Inter> F" and FF: "F \<in> FF"
      unfolding D_def by (rule imageE)
    from FF have "finite F" "F \<noteq> {}" "F \<subseteq> B1" unfolding FF_def by simp_all
    with Aeq show thesis' by (rule W)
  qed
  have DI: "\<Inter> F \<in> D" if "finite F" "F \<noteq> {}" "F \<subseteq> B1" for F
  proof -
    have "F \<in> FF" unfolding FF_def using that by simp
    then show ?thesis unfolding D_def by (rule image_eqI[OF refl])
  qed

  have cD: "countable D"
    unfolding D_def FF_def
    by (intro countable_image
        countable_subset[OF _ countable_Collect_finite_subset[OF cB1]]) auto
  have Dpow: "D \<subseteq> Pow (mspace ?m)"
  proof
    fix A assume "A \<in> D"
    then show "A \<in> Pow (mspace ?m)"
    proof (rule DE)
      fix F assume Aeq: "A = \<Inter> F" and F: "finite F" "F \<noteq> {}" "F \<subseteq> B1"
      from F(2) obtain U where U: "U \<in> F" by blast
      have "A \<subseteq> U" unfolding Aeq using U by blast
      moreover have "U \<subseteq> mspace ?m" using U F(3) B1sub by blast
      ultimately show "A \<in> Pow (mspace ?m)" by auto
    qed
  qed
  have Dtop: "mspace ?m \<in> D"
  proof -
    have "\<Inter> {mspace ?m} \<in> D"
      by (rule DI) (simp_all add: B1_def)
    then show ?thesis by simp
  qed
  have DInt: "Int_stable D"
    unfolding Int_stable_def
  proof (intro ballI)
    fix A B assume A: "A \<in> D" and B: "B \<in> D"
    from A show "A \<inter> B \<in> D"
    proof (rule DE)
      fix F assume Aeq: "A = \<Inter> F" and F: "finite F" "F \<noteq> {}" "F \<subseteq> B1"
      from B show "A \<inter> B \<in> D"
      proof (rule DE)
        fix G assume Beq: "B = \<Inter> G" and G: "finite G" "G \<noteq> {}" "G \<subseteq> B1"
        have "A \<inter> B = \<Inter> (F \<union> G)"
          unfolding Aeq Beq by (simp add: Inter_Un_distrib)
        moreover have "\<Inter> (F \<union> G) \<in> D"
          by (rule DI) (use F G in auto)
        ultimately show "A \<inter> B \<in> D" by simp
      qed
    qed
  qed

  \<comment> \<open>the base already generates, and closing under finite intersections
      changes nothing\<close>
  have Bpow: "BB \<subseteq> Pow (mspace ?m)" using Bsub by auto
  have bsets: "sets (borel_of ?X) = sigma_sets (mspace ?m) BB"
  proof -
    have "borel_of ?X = sigma (topspace ?X) BB"
      by (rule borel_of_second_countable'[OF sc base_is_subbase[OF bB]])
    then have "borel_of ?X = sigma (mspace ?m) BB" by simp
    then show ?thesis using sets_measure_of[OF Bpow] by simp
  qed
  have Deq: "sigma_sets (mspace ?m) D = sigma_sets (mspace ?m) BB"
  proof (rule sigma_sets_eqI)
    fix A assume A: "A \<in> D"
    interpret SA: sigma_algebra "mspace ?m" "sigma_sets (mspace ?m) BB"
      by (rule sigma_algebra_sigma_sets[OF Bpow])
    from A show "A \<in> sigma_sets (mspace ?m) BB"
    proof (rule DE)
      fix F assume Aeq: "A = \<Inter> F" and F: "finite F" "F \<noteq> {}" "F \<subseteq> B1"
      have "U \<in> sigma_sets (mspace ?m) BB" if "U \<in> F" for U
        using that F(3) unfolding B1_def by (auto simp: sigma_sets_top)
      then have "(\<Inter>U\<in>F. U) \<in> sigma_sets (mspace ?m) BB"
        by (rule SA.finite_INT[OF F(1) F(2)])
      then show "A \<in> sigma_sets (mspace ?m) BB" unfolding Aeq by simp
    qed
  next
    fix U assume U: "U \<in> BB"
    have "\<Inter> {U} \<in> D" by (rule DI) (use U in \<open>simp_all add: B1_def\<close>)
    then have "U \<in> D" by simp
    then show "U \<in> sigma_sets (mspace ?m) D" by (rule sigma_sets.Basic)
  qed
  have Dsets: "sets (borel_of ?X) = sigma_sets (mspace ?m) D"
    unfolding bsets Deq ..
  show thesis by (rule that[OF cD DInt Dpow Dtop Dsets])
qed

text \<open>And its pullback: the countable \<open>\<pi>\<close>-system for \<open>\<F>\<^sub>s\<close> that the
  conditioning sets of clause (iii)/(iv) range over.\<close>

theorem martingale_F_limit:
  fixes Qm :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and Q :: "('n pairpath) measure"
    and F :: "(real^'n) \<times> (real^'n^'n) \<Rightarrow> real"
  assumes T: "0 \<le> T" and Fc: "continuous_on UNIV F"
    and Pm: "\<And>m. prob_space (Qm m)"
    and setsm: "\<And>m. sets (Qm m) = sets (path_borel T :: ('n pairpath) measure)"
    and mgm: "\<And>m. martingale (Qm m) (natural_filtration (Qm m) 0 (\<lambda>u \<omega>. \<omega> u)) 0
        (\<lambda>u \<omega>. F (\<omega> (min u T)))"
    and wc: "weak_conv_on Qm Q sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
    and prob: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and C0: "0 \<le> C"
    and nnm: "\<And>m u. u \<in> {0..T} \<Longrightarrow>
        (\<integral>\<^sup>+\<omega>. ennreal ((F (\<omega> u))\<^sup>2) \<partial>(Qm m)) \<le> ennreal C"
  shows "martingale Q (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)) 0
      (\<lambda>u \<omega>. F (\<omega> (min u T)))"
proof -
  let ?FF = "natural_filtration Q 0 (\<lambda>u \<omega> :: 'n pairpath. \<omega> u)"
  let ?Y = "\<lambda>u \<omega> :: 'n pairpath. F (\<omega> (min u T))"
  have spQ: "space Q = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsQ])
  have finQ: "finite_measure Q" using prob by (simp add: prob_space_def)
  have SP: "Stochastic_Process.stochastic_process Q (0::real)
      (\<lambda>u \<omega> :: 'n pairpath. \<omega> u)"
    by unfold_locales (rule pair_law_eval_measurable[OF setsQ])
  interpret SF: finite_filtered_measure Q ?FF 0
    by (rule Stochastic_Process.stochastic_process.finite_filtered_measure_natural_filtration[OF SP finQ])
  have mI: "min u T \<in> {0..T}" if "0 \<le> u" for u using that T by simp
  have nnQ: "(\<integral>\<^sup>+\<omega>. ennreal ((F (\<omega> u))\<^sup>2) \<partial>Q) \<le> ennreal C" if u: "u \<in> {0..T}"
    for u
    by (rule weak_conv_on_nn_integral_le
        [OF wc pair_eval_F_sq_cont[OF Fc u] _ C0 nnm[OF u]]) simp
  have Fb: "F \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI[OF Fc])
  have iY: "integrable Q (?Y u)" if u: "0 \<le> u" for u
  proof (rule integrable_of_sq_integrable[OF finQ])
    show "?Y u \<in> borel_measurable Q"
      by (rule pair_law_F_measurable[OF Fc setsQ mI[OF u]])
    show "integrable Q (\<lambda>\<omega>. (?Y u \<omega>)\<^sup>2)"
      by (rule pair_law_F_sq_integrable_of_nn_bound
          [OF Fc setsQ mI[OF u] nnQ[OF mI[OF u]]])
  qed
  show ?thesis
  proof (rule SF.martingale_of_set_integral_eq)
    show "adapted_process Q ?FF 0 ?Y"
    proof (unfold_locales)
      fix u :: real assume u: "0 \<le> u"
      have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u T)) \<in> ?FF u \<rightarrow>\<^sub>M borel"
        unfolding natural_filtration_def
        by (rule measurable_family_vimage_algebra) (use u T in auto)
      show "?Y u \<in> borel_measurable (?FF u)"
        by (rule measurable_compose[OF ev Fb])
    qed
    show "\<And>u. 0 \<le> u \<Longrightarrow> integrable Q (?Y u)" by (rule iY)
    fix A and u v :: real
    assume A: "A \<in> ?FF u" and uv: "0 \<le> u" "u \<le> v"
    have v0: "0 \<le> v" using uv by simp
    have Ai: "A \<in> sets Q"
      using A SF.subalgebras[OF uv(1)] by (auto simp: subalgebra_def)
    have siY: "set_integrable Q A (?Y w)" if w: "0 \<le> w" for w
      unfolding set_integrable_def
      by (rule integrable_mult_indicator[OF Ai iY[OF w]])
    show "set_lebesgue_integral Q A (?Y u) = set_lebesgue_integral Q A (?Y v)"
    proof (cases "u \<le> T")
      case False
      then have "min u T = T" and "min v T = T" using uv by simp_all
      then show ?thesis by simp
    next
      case True
      have mu: "min u T = u" using True by simp
      have tI: "min v T \<in> {0..T}" by (rule mI[OF v0])
      have tT: "min v T \<le> T" using tI by simp
      have ut: "u \<le> min v T" using True uv by simp
      obtain Bs where Bs: "Bs \<in> sets (path_borel u :: ('n pairpath) measure)"
        and Aeq: "A = (\<lambda>\<omega>. restrict \<omega> {0..u}) -` Bs \<inter> space Q"
        using natural_filtration_eq_restrict_vimage[OF setsQ uv(1) True A]
        by blast
      have ind: "indicat_real A \<omega> = indicat_real Bs (restrict \<omega> {0..u})"
        if "\<omega> \<in> space Q" for \<omega> using Aeq that by (simp add: indicator_def)
      have zero: "(\<integral>\<omega>. indicat_real Bs (restrict \<omega> {0..u})
          * (F (\<omega> (min v T)) - F (\<omega> u)) \<partial>Q) = 0"
        by (rule martingale_event_F_limit
            [OF Fc Pm setsm mgm wc prob setsQ C0 nnm uv(1) ut tT Bs])
      have mR: "(\<lambda>\<omega> :: 'n pairpath. indicat_real Bs (restrict \<omega> {0..u})
            * (F (\<omega> (min v T)) - F (\<omega> u))) \<in> borel_measurable Q"
      proof -
        have rm: "(\<lambda>\<omega> :: 'n pairpath. restrict \<omega> {0..u}) \<in> Q \<rightarrow>\<^sub>M
            (path_borel u :: ('n pairpath) measure)"
          using continuous_map_measurable
            [OF Lipschitz_continuous_imp_continuous_map
              [OF Lipschitz_restrict_path_metric[OF uv(1) True]]]
            measurable_cong_sets[OF setsQ refl] by blast
        have im: "(\<lambda>\<omega> :: 'n pairpath. indicat_real Bs (restrict \<omega> {0..u}))
            \<in> borel_measurable Q"
          by (rule measurable_compose[OF rm borel_measurable_indicator[OF Bs]])
        have c1: "(\<lambda>\<omega> :: 'n pairpath. F (\<omega> (min v T))) \<in> borel_measurable Q"
          by (rule pair_law_F_measurable[OF Fc setsQ tI])
        have c2: "(\<lambda>\<omega> :: 'n pairpath. F (\<omega> u)) \<in> borel_measurable Q"
          using True uv(1) by (intro pair_law_F_measurable[OF Fc setsQ]) simp
        show ?thesis by (intro borel_measurable_times im
            borel_measurable_diff c1 c2)
      qed
      have mD: "(\<lambda>\<omega>. indicat_real A \<omega> *\<^sub>R ?Y v \<omega>
          - indicat_real A \<omega> *\<^sub>R ?Y u \<omega>) \<in> borel_measurable Q"
        using siY[OF v0] siY[OF uv(1)]
        by (intro borel_measurable_diff)
          (auto simp: set_integrable_def dest: borel_measurable_integrable)
      have "(\<integral>\<omega>. indicat_real A \<omega> *\<^sub>R ?Y v \<omega> \<partial>Q)
          - (\<integral>\<omega>. indicat_real A \<omega> *\<^sub>R ?Y u \<omega> \<partial>Q)
          = (\<integral>\<omega>. indicat_real A \<omega> *\<^sub>R ?Y v \<omega>
              - indicat_real A \<omega> *\<^sub>R ?Y u \<omega> \<partial>Q)"
        using siY[OF v0] siY[OF uv(1)]
        by (intro Bochner_Integration.integral_diff[symmetric])
          (auto simp: set_integrable_def)
      also have "\<dots> = (\<integral>\<omega>. indicat_real Bs (restrict \<omega> {0..u})
          * (F (\<omega> (min v T)) - F (\<omega> u)) \<partial>Q)"
      proof (rule integral_cong_AE[OF mD mR])
        show "AE \<omega> in Q. indicat_real A \<omega> *\<^sub>R ?Y v \<omega>
            - indicat_real A \<omega> *\<^sub>R ?Y u \<omega>
            = indicat_real Bs (restrict \<omega> {0..u})
              * (F (\<omega> (min v T)) - F (\<omega> u))"
          by (intro AE_I2) (simp add: ind mu right_diff_distrib)
      qed
      also have "\<dots> = 0" by (rule zero)
      finally show ?thesis
        unfolding set_lebesgue_integral_def by simp
    qed
  qed
qed

section \<open>The compensated clause of Lemma 2.3\<close>

text \<open>\<open>prod_minus_sq_bound\<close>, \<open>fourth_power_sum_bound\<close>, \<open>zero_le_fourth\<close> live in @{theory Continuous_Path_Spaces.Increment_Moments}.\<close>


subsection \<open>The compensated functional\<close>

lemma radial_sq_upto:
  fixes \<omega> :: "'n::finite pairpath" and y\<^sub>0 x :: "real^'n"
    and TT e cn :: real and RO :: "(real^'n) set"
  assumes wm: "\<omega> \<in> mspace (path_metric TT :: ('n pairpath) metric)"
    and grow: "\<And>t. 0 < t \<Longrightarrow> t \<le> TT \<Longrightarrow>
      (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> RO) \<Longrightarrow>
      (norm (fst (\<omega> t) - y\<^sub>0))\<^sup>2 = (norm (x - y\<^sub>0))\<^sup>2 + t * cn"
    and e0: "0 < e" and eT: "e \<le> TT"
    and inside: "\<And>s. 0 \<le> s \<Longrightarrow> s < e \<Longrightarrow> fst (\<omega> s) \<in> RO"
  shows "(norm (fst (\<omega> e) - y\<^sub>0))\<^sup>2 = (norm (x - y\<^sub>0))\<^sup>2 + e * cn"
proof -
  define g where "g = (\<lambda>s. (norm (fst (\<omega> s) - y\<^sub>0))\<^sup>2)"
  have gc: "continuous_on {0..TT} g"
  proof -
    have wc: "continuous_on {0..TT} \<omega>"
      by (rule mspace_path_metricD[OF wm])
    have fc: "continuous_on {0..TT} (\<lambda>s. fst (\<omega> s))"
      by (rule continuous_on_fst[OF wc])
    show ?thesis
      unfolding g_def by (intro continuous_intros fc)
  qed
  define tj where "tj = (\<lambda>j. e - e / (2 * real (Suc j)))"
  have tjl: "0 < tj j" for j
  proof -
    have "e / (2 * real (Suc j)) \<le> e / 2"
    proof (rule divide_left_mono)
      show "2 \<le> 2 * real (Suc j)" by simp
      show "0 \<le> e" using e0 by linarith
      show "0 < 2 * real (Suc j) * 2" by simp
    qed
    then show ?thesis unfolding tj_def using e0 by linarith
  qed
  have tju: "tj j < e" for j
  proof -
    have "0 < e / (2 * real (Suc j))" using e0 by simp
    then show ?thesis unfolding tj_def by linarith
  qed
  have tjT: "tj j \<le> TT" for j using tju[of j] eT by linarith
  have glow: "g (tj j) = (norm (x - y\<^sub>0))\<^sup>2 + tj j * cn" for j
    unfolding g_def
  proof (rule grow)
    show "0 < tj j" by (rule tjl)
    show "tj j \<le> TT" by (rule tjT)
    show "\<forall>s\<in>{0..tj j}. fst (\<omega> s) \<in> RO"
    proof
      fix s assume s: "s \<in> {0..tj j}"
      then have "0 \<le> s" and "s < e" using tju[of j] by auto
      then show "fst (\<omega> s) \<in> RO" by (rule inside)
    qed
  qed
  have tjlim: "tj \<longlonglongrightarrow> e"
  proof -
    have eq: "(\<lambda>j. (e / 2) * inverse (real (Suc j)))
        = (\<lambda>j. e / (2 * real (Suc j)))"
      by (rule ext) (simp add: field_simps)
    have "(\<lambda>j. (e / 2) * inverse (real (Suc j))) \<longlonglongrightarrow> (e / 2) * 0"
      by (intro tendsto_mult tendsto_const LIMSEQ_inverse_real_of_nat)
    then have "(\<lambda>j. e / (2 * real (Suc j))) \<longlonglongrightarrow> 0"
      unfolding eq by simp
    then have "(\<lambda>j. e - e / (2 * real (Suc j))) \<longlonglongrightarrow> e - 0"
      by (intro tendsto_diff tendsto_const)
    then show ?thesis unfolding tj_def by simp
  qed
  have gcomp: "(\<lambda>j. g (tj j)) \<longlonglongrightarrow> g e"
  proof -
    have inS: "\<forall>n. tj n \<in> {0..TT}"
      using tjl tjT by (auto intro: less_imp_le)
    have eS: "e \<in> {0..TT}" using e0 eT by auto
    have "(g \<circ> tj) \<longlonglongrightarrow> g e"
      using continuous_on_sequentially[THEN iffD1, OF gc] inS eS tjlim
      by blast
    then show ?thesis by (simp add: o_def)
  qed
  have vlim: "(\<lambda>j. (norm (x - y\<^sub>0))\<^sup>2 + tj j * cn)
      \<longlonglongrightarrow> (norm (x - y\<^sub>0))\<^sup>2 + e * cn"
    by (intro tendsto_add tendsto_const tendsto_mult tjlim)
  have "(\<lambda>j. g (tj j)) \<longlonglongrightarrow> (norm (x - y\<^sub>0))\<^sup>2 + e * cn"
    using vlim unfolding glow by simp
  then have "g e = (norm (x - y\<^sub>0))\<^sup>2 + e * cn"
    using gcomp LIMSEQ_unique by blast
  then show ?thesis unfolding g_def .
qed

lemma martingale_of_rational_set_integral_eq:
  fixes Q :: "((real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})) measure"
    and Z :: "real \<Rightarrow> (real \<Rightarrow> 'a \<times> 'b) \<Rightarrow> real"
  assumes S: "0 \<le> S"
    and setsQ: "sets Q = sets (path_borel S :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
    and PS: "prob_space Q"
    and Zm: "\<And>u. u \<in> {0..S} \<Longrightarrow>
        Z u \<in> borel_measurable (natural_filtration Q 0 (\<lambda>v w. w v) u)"
    and Zm': "\<And>u. 0 \<le> u \<Longrightarrow>
        Z u \<in> borel_measurable (natural_filtration Q 0 (\<lambda>v w. w v) u)"
    and Zint: "\<And>q. q \<in> \<rat> \<Longrightarrow> q \<in> {0..S} \<Longrightarrow> integrable Q (Z q)"
    and ZintS: "integrable Q (Z S)"
    and Zcont: "\<And>w. w \<in> space Q \<Longrightarrow> continuous_on {0..S} (\<lambda>u. Z u w)"
    and Zcap: "\<And>u. S \<le> u \<Longrightarrow> Z u = Z S"
    and rat: "\<And>q A. q \<in> \<rat> \<Longrightarrow> q \<in> {0..S} \<Longrightarrow>
        A \<in> sets (natural_filtration Q 0 (\<lambda>v w. w v) q) \<Longrightarrow>
        set_lebesgue_integral Q A (Z q) = set_lebesgue_integral Q A (Z S)"
  shows "martingale Q (natural_filtration Q 0 (\<lambda>v w. w v)) 0 Z"
proof -
  let ?F = "\<lambda>u. natural_filtration Q 0 (\<lambda>v w :: (real \<Rightarrow> 'a \<times> 'b). w v) u"
  have fm: "filtered_measure Q ?F 0"
  proof (intro filtered_measure.intro)
    show "subalgebra Q (?F u)" if "(0::real) \<le> u" for u
      by (rule subalgebra_natural_filtration_path[OF setsQ])
    show "sets (?F u) \<subseteq> sets (?F v)" if "(0::real) \<le> u" "u \<le> v" for u v
      by (rule sets_natural_filtration_mono[OF that(2)])
  qed
  interpret SFF: sigma_finite_filtered_measure Q ?F 0
    by (intro sigma_finite_filtered_measure.intro
        sigma_finite_filtered_measure_axioms.intro fm
        sigma_finite_subalgebra_natural_filtration_path[OF PS setsQ])

  \<comment> \<open>integrability AND the identity against the terminal value, both at
      every time in the horizon and both out of the rational data\<close>
  have both: "integrable Q (Z u)
      \<and> (\<forall>A \<in> sets (?F u). set_lebesgue_integral Q A (Z u)
          = set_lebesgue_integral Q A (Z S))"
    if u: "u \<in> {0..S}" for u
    by (rule integrable_and_set_integral_eq_of_rational_times
        [OF S setsQ PS Zm Zint ZintS Zcont rat u])
  have Zall: "integrable Q (Z u)" if u: "0 \<le> u" for u
  proof (cases "u \<le> S")
    case True
    have "u \<in> {0..S}" using u True by simp
    from both[OF this] show ?thesis by blast
  next
    case False
    have "S \<le> u" using False by simp
    then have "Z u = Z S" by (rule Zcap)
    then show ?thesis using ZintS by simp
  qed
  have term_eq: "set_lebesgue_integral Q A (Z u) = set_lebesgue_integral Q A (Z S)"
    if u: "0 \<le> u" and A: "A \<in> sets (?F u)" for u A
  proof (cases "u \<le> S")
    case True
    have "u \<in> {0..S}" using u True by simp
    from both[OF this] show ?thesis using A by blast
  next
    case False
    have "S \<le> u" using False by simp
    then have "Z u = Z S" by (rule Zcap)
    then show ?thesis by (rule arg_cong)
  qed

  show ?thesis
  proof (rule SFF.martingale_of_set_integral_eq)
    show "adapted_process Q ?F 0 Z"
    proof (intro adapted_process.intro adapted_process_axioms.intro)
      show "filtered_measure Q ?F 0" by (rule fm)
      show "Z u \<in> borel_measurable (?F u)" if "(0::real) \<le> u" for u
        by (rule Zm'[OF that])
    qed
    show "integrable Q (Z u)" if "(0::real) \<le> u" for u by (rule Zall[OF that])
    fix A and u v :: real
    assume u: "0 \<le> u" and uv: "u \<le> v" and A: "A \<in> ?F u"
    have AF: "A \<in> sets (?F u)" using A by simp
    have AFv: "A \<in> sets (?F v)"
      using AF sets_natural_filtration_mono[OF uv] by blast
    have "set_lebesgue_integral Q A (Z u) = set_lebesgue_integral Q A (Z S)"
      by (rule term_eq[OF u AF])
    also have "\<dots> = set_lebesgue_integral Q A (Z v)"
      by (rule term_eq[OF _ AFv, symmetric]) (use u uv in simp)
    finally show "set_lebesgue_integral Q A (Z u)
        = set_lebesgue_integral Q A (Z v)" .
  qed
qed

subsection \<open>Clause (iii) for the conditional law\<close>

text \<open>The two pointwise facts about the capped coordinate that the fixed-law
  lemma asks for.  Neither depends on the measure: the natural filtration
  only sees \<open>space Q\<close>, and continuity in time is a property of the path.\<close>

lemma comp_entry_eq:
  fixes p :: "(real^'n::finite) \<times> (real^'n^'n)"
  shows "(outerp (fst p) - snd p) $ i $ j = fst p $ i * fst p $ j - snd p $ i $ j"
  by (simp add: outerp_def)

lemma comp_entry_cont:
  shows "continuous_on UNIV
      (\<lambda>p :: (real^'n::finite) \<times> (real^'n^'n). (outerp (fst p) - snd p) $ i $ j)"
proof -
  have e: "(\<lambda>p :: (real^'n) \<times> (real^'n^'n). (outerp (fst p) - snd p) $ i $ j)
      = (\<lambda>p. fst p $ i * fst p $ j - snd p $ i $ j)"
    by (rule ext) (rule comp_entry_eq)
  show ?thesis unfolding e by (intro continuous_intros)
qed

text \<open>The fourth moment of the coordinate itself, not of an increment: the
  start clause pins \<open>X\<^sub>0 = x\<close>, so \<open>(a+b)\<^sup>4 \<le> 8(a\<^sup>4+b\<^sup>4)\<close> turns the increment
  bound into an absolute one, uniform over the whole class.\<close>

lemma eval_component_measurable_nf:
  fixes Q :: "('n::finite pairpath) measure"
  assumes S: "0 \<le> S" and u: "0 \<le> u"
  shows "(\<lambda>w :: 'n pairpath. fst (w (min u S)) $ c)
      \<in> borel_measurable (natural_filtration Q 0 (\<lambda>v w. w v) u)"
proof -
  let ?F = "natural_filtration Q 0 (\<lambda>v w :: 'n pairpath. w v) u"
  have ev: "(\<lambda>w :: 'n pairpath. w (min u S)) \<in> borel_measurable ?F"
    unfolding natural_filtration_def
    by (rule measurable_family_vimage_algebra) (use S u in auto)
  have f1: "(\<lambda>w :: 'n pairpath. fst (w (min u S))) \<in> borel_measurable ?F"
    by (rule measurable_compose[OF ev pair_fst_borel])
  have "(\<lambda>w :: 'n pairpath. fst (w (min u S)) \<bullet> (axis c 1 :: real^'n))
      \<in> borel_measurable ?F"
    by (intro borel_measurable_inner f1 borel_measurable_const)
  then show ?thesis by (simp add: inner_axis)
qed

lemma eval_component_continuous:
  fixes w :: "'n::finite pairpath"
  assumes w: "w \<in> mspace (path_metric S :: ('n pairpath) metric)"
  shows "continuous_on {0..S} (\<lambda>u. fst (w (min u S)) $ c)"
proof -
  have "continuous_on {0..S} w" by (rule mspace_path_metricD[OF w])
  then have "continuous_on {0..S} (\<lambda>u. fst (w u))" by (rule continuous_on_fst)
  then have c1: "continuous_on {0..S} (\<lambda>u. fst (w u) $ c)"
    by (rule bounded_linear.continuous_on[OF bounded_linear_vec_nth])
  have "continuous_on {0..S} (\<lambda>u. fst (w (min u S)) $ c)
      = continuous_on {0..S} (\<lambda>u. fst (w u) $ c)"
    by (rule continuous_on_cong[OF refl]) simp
  then show ?thesis using c1 by simp
qed

text \<open>Clause (iii) of (1.7) for the conditional law, assembled from:

  \<^item> \<open>pfut_rcd_X_increment_zero\<close>, supplying one almost-sure
    condition per \<open>(q, A', c)\<close>, countably many since \<open>q\<close> is rational,
    \<open>A'\<close> ranges over the \<open>\<pi>\<close>-system of
    \<open>countable_pi_system_natural_filtration_path\<close>, and \<open>c\<close>
    ranges over the finite index type;
  \<^item> \<open>AE_ball_countable'\<close>, turning "for each, almost surely"
    into "almost surely, for all";
  \<^item> at a fixed good \<open>p'\<close>, @{thm [source] set_integral_zero_of_generator}
    widening the \<open>\<pi>\<close>-system to \<open>\<F>\<^sub>q\<close> and
    @{thm [source] martingale_of_rational_set_integral_eq} widening the
    rational times to all times;
  \<^item> @{thm [source] martingale_vecI}, putting the finitely many components
    back together.\<close>

lemma open_quad_bad_event:
  fixes x q :: "real^'n::finite" and M :: "real^'n^'n"
    and t T rb thr :: real
  assumes t0: "0 \<le> t" and tT: "t \<le> T"
  shows "openin (mtopology_of (path_metric T :: ('n pairpath) metric))
      {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
        (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> ball x rb)
        \<and> q \<bullet> (fst (\<omega> t) - x)
          + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x))) < thr}"
proof -
  have T0: "0 \<le> T" using t0 tT by linarith
  let ?pm = "path_metric T :: ('n pairpath) metric"
  have o1: "openin (mtopology_of ?pm)
      {\<omega> \<in> mspace ?pm. \<forall>s\<in>{0..t}. \<omega> s \<in> fst -` ball x rb}"
    by (rule open_stay_inside[OF T0 open_vimage_fst[OF open_ball] t0 tT])
  have c0: "continuous_on UNIV
      (\<lambda>p :: (real^'n) \<times> (real^'n^'n). fst p - x)"
    by (intro continuous_intros)
  have c1: "continuous_on UNIV
      (\<lambda>p :: (real^'n) \<times> (real^'n^'n). M *v (fst p - x))"
    by (rule continuous_on_compose2[OF
        linear_continuous_on[OF matvec_blin] c0]) auto
  have cq: "continuous_on UNIV
      (\<lambda>p :: (real^'n) \<times> (real^'n^'n). q \<bullet> (fst p - x))"
    by (rule continuous_on_compose2[OF
        linear_continuous_on[OF bounded_linear_inner_right] c0]) auto
  have cin: "continuous_on UNIV
      (\<lambda>p :: (real^'n) \<times> (real^'n^'n).
        (fst p - x) \<bullet> (M *v (fst p - x)))"
    by (rule bounded_bilinear.continuous_on[OF bounded_bilinear_inner c0 c1])
  have contf: "continuous_on UNIV
      (\<lambda>p :: (real^'n) \<times> (real^'n^'n).
        q \<bullet> (fst p - x) + (1/2) * ((fst p - x) \<bullet> (M *v (fst p - x))))"
    by (intro continuous_on_add continuous_on_mult
        continuous_on_const cq cin)
  have oU: "open {p :: (real^'n) \<times> (real^'n^'n).
      q \<bullet> (fst p - x) + (1/2) * ((fst p - x) \<bullet> (M *v (fst p - x))) < thr}"
    by (rule open_Collect_less[OF contf continuous_on_const])
  have o2: "openin (mtopology_of ?pm)
      {\<omega> \<in> mspace ?pm. \<omega> t \<in> {p. q \<bullet> (fst p - x)
        + (1/2) * ((fst p - x) \<bullet> (M *v (fst p - x))) < thr}}"
    by (rule open_eval_preimage[OF _ oU]) (use t0 tT in simp)
  have eq: "{\<omega> \<in> mspace ?pm.
      (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> ball x rb)
      \<and> q \<bullet> (fst (\<omega> t) - x)
        + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x))) < thr}
      = {\<omega> \<in> mspace ?pm. \<forall>s\<in>{0..t}. \<omega> s \<in> fst -` ball x rb}
        \<inter> {\<omega> \<in> mspace ?pm. \<omega> t \<in> {p. q \<bullet> (fst p - x)
          + (1/2) * ((fst p - x) \<bullet> (M *v (fst p - x))) < thr}}"
    by auto
  show ?thesis unfolding eq by (rule openin_Int[OF o1 o2])
qed

text \<open>At mesh \<open>c / (i + 1)\<close> the bad-event probability is at most
  \<open>A h + B h\<^sup>2\<close> once the mesh is fine enough, so it tends to zero.  At the
  last grid point \<open>m h \<le> t\<close>, on the almost-sure event of
  \<open>eulerp_quad_lower\<close>, staying in-ball through \<open>t\<close> together
  with a quadratic drop forces either a large \<open>euXi\<close> (Chebyshev) or a large
  one-step increment (the fourth-moment tail).\<close>

lemma comp_entry_measurable_nf:
  fixes Q :: "('n::finite pairpath) measure"
  assumes S: "0 \<le> S" and u: "0 \<le> u"
  shows "(\<lambda>w :: 'n pairpath.
        (outerp (fst (w (min u S))) - snd (w (min u S))) $ c $ d)
      \<in> borel_measurable (natural_filtration Q 0 (\<lambda>v w. w v) u)"
proof -
  let ?F = "natural_filtration Q 0 (\<lambda>v w :: 'n pairpath. w v) u"
  have ev: "(\<lambda>w :: 'n pairpath. w (min u S)) \<in> borel_measurable ?F"
    unfolding natural_filtration_def
    by (rule measurable_family_vimage_algebra) (use S u in auto)
  have m1: "(\<lambda>w :: 'n pairpath. outerp (fst (w (min u S))))
      \<in> borel_measurable ?F"
    by (rule measurable_compose
        [OF measurable_compose[OF ev pair_fst_borel] outerp_borel])
  have m2: "(\<lambda>w :: 'n pairpath. snd (w (min u S))) \<in> borel_measurable ?F"
    by (rule measurable_compose[OF ev pair_snd_borel])
  have mm: "(\<lambda>w :: 'n pairpath. outerp (fst (w (min u S))) - snd (w (min u S)))
      \<in> borel_measurable ?F"
    by (rule borel_measurable_diff[OF m1 m2])
  have bl: "bounded_linear (\<lambda>M :: real^'n^'n. M $ c $ d)"
    by (rule bounded_linear_compose[OF bounded_linear_vec_nth
        bounded_linear_vec_nth])
  have entm: "(\<lambda>M :: real^'n^'n. M $ c $ d) \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI) (rule linear_continuous_on[OF bl])
  from measurable_compose[OF mm entm] show ?thesis by simp
qed

lemma comp_entry_continuous:
  fixes w :: "'n::finite pairpath"
  assumes w: "w \<in> mspace (path_metric S :: ('n pairpath) metric)"
  shows "continuous_on {0..S}
      (\<lambda>u. (outerp (fst (w (min u S))) - snd (w (min u S))) $ c $ d)"
proof -
  have cw: "continuous_on {0..S} w" by (rule mspace_path_metricD[OF w])
  have cf: "continuous_on {0..S} (\<lambda>u. fst (w u))"
    using cw by (rule continuous_on_fst)
  have cs: "continuous_on {0..S} (\<lambda>u. snd (w u))"
    using cw by (rule continuous_on_snd)
  have c1: "continuous_on {0..S} (\<lambda>u. fst (w u) $ c)"
    using cf by (rule bounded_linear.continuous_on[OF bounded_linear_vec_nth])
  have c2: "continuous_on {0..S} (\<lambda>u. fst (w u) $ d)"
    using cf by (rule bounded_linear.continuous_on[OF bounded_linear_vec_nth])
  have bl: "bounded_linear (\<lambda>M :: real^'n^'n. M $ c $ d)"
    by (rule bounded_linear_compose[OF bounded_linear_vec_nth
        bounded_linear_vec_nth])
  have c3: "continuous_on {0..S} (\<lambda>u. snd (w u) $ c $ d)"
    using cs by (rule bounded_linear.continuous_on[OF bl])
  have cc: "continuous_on {0..S}
      (\<lambda>u. fst (w u) $ c * fst (w u) $ d - snd (w u) $ c $ d)"
    by (intro continuous_on_diff continuous_on_mult c1 c2 c3)
  have "continuous_on {0..S}
        (\<lambda>u. (outerp (fst (w (min u S))) - snd (w (min u S))) $ c $ d)
      = continuous_on {0..S}
        (\<lambda>u. fst (w u) $ c * fst (w u) $ d - snd (w u) $ c $ d)"
    by (rule continuous_on_cong[OF refl]) (simp add: outerp_def)
  then show ?thesis using cc by simp
qed

text \<open>Clause (iv) of (1.7) for the conditional law, by the same assembly as
  clause (iii): the index set of components is now a pair, and
  @{thm [source] martingale_matI} does the reassembly.\<close>

lemma quad_eval_cont:
  fixes \<omega> :: "'n::finite pairpath" and q x :: "real^'n"
    and M :: "real^'n^'n" and c :: real
  assumes wm: "\<omega> \<in> mspace (path_metric c :: ('n pairpath) metric)"
  shows "continuous_on {0..c} (\<lambda>s. q \<bullet> (fst (\<omega> s) - x)
      + (1/2) * ((fst (\<omega> s) - x) \<bullet> (M *v (fst (\<omega> s) - x))))"
proof -
  have wc: "continuous_on {0..c} \<omega>" by (rule mspace_path_metricD[OF wm])
  have c0: "continuous_on UNIV
      (\<lambda>p :: (real^'n) \<times> (real^'n^'n). fst p - x)"
    by (intro continuous_intros)
  have c1: "continuous_on UNIV
      (\<lambda>p :: (real^'n) \<times> (real^'n^'n). M *v (fst p - x))"
    by (rule continuous_on_compose2[OF
        linear_continuous_on[OF matvec_blin] c0]) auto
  have cq: "continuous_on UNIV
      (\<lambda>p :: (real^'n) \<times> (real^'n^'n). q \<bullet> (fst p - x))"
    by (rule continuous_on_compose2[OF
        linear_continuous_on[OF bounded_linear_inner_right] c0]) auto
  have cin: "continuous_on UNIV
      (\<lambda>p :: (real^'n) \<times> (real^'n^'n).
        (fst p - x) \<bullet> (M *v (fst p - x)))"
    by (rule bounded_bilinear.continuous_on[OF bounded_bilinear_inner c0 c1])
  have contf: "continuous_on UNIV
      (\<lambda>p :: (real^'n) \<times> (real^'n^'n).
        q \<bullet> (fst p - x) + (1/2) * ((fst p - x) \<bullet> (M *v (fst p - x))))"
    by (intro continuous_on_add continuous_on_mult
        continuous_on_const cq cin)
  show ?thesis
    by (rule continuous_on_compose2[OF contf wc]) auto
qed

text \<open>\<open>quad_good_upto\<close> with the confinement region and the
  quadratic's centre both free.  Only reachability from below is used,
  so the proof is the same sequence-and-continuity passage.\<close>

lemma quad_good_upto_region:
  fixes \<omega> :: "'n::finite pairpath" and q x :: "real^'n"
    and M :: "real^'n^'n" and c cm t :: real and RO :: "(real^'n) set"
  assumes wm: "\<omega> \<in> mspace (path_metric c :: ('n pairpath) metric)"
    and good: "\<And>t'. 0 < t' \<Longrightarrow> t' \<le> c \<Longrightarrow>
      (\<forall>s\<in>{0..t'}. fst (\<omega> s) \<in> RO) \<Longrightarrow>
      t' * cm / 2 \<le> q \<bullet> (fst (\<omega> t') - x)
        + (1/2) * ((fst (\<omega> t') - x) \<bullet> (M *v (fst (\<omega> t') - x)))"
    and t0: "0 < t" and tc: "t \<le> c"
    and inb: "\<And>s. 0 \<le> s \<Longrightarrow> s < t \<Longrightarrow> fst (\<omega> s) \<in> RO"
  shows "t * cm / 2 \<le> q \<bullet> (fst (\<omega> t) - x)
      + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x)))"
proof -
  define g where "g = (\<lambda>s. q \<bullet> (fst (\<omega> s) - x)
      + (1/2) * ((fst (\<omega> s) - x) \<bullet> (M *v (fst (\<omega> s) - x))))"
  have gc: "continuous_on {0..c} g"
    unfolding g_def by (rule quad_eval_cont[OF wm])
  define tj where "tj = (\<lambda>j. t - t / (2 * real (Suc j)))"
  have tjl: "0 < tj j" for j
  proof -
    have "t / (2 * real (Suc j)) \<le> t / 2"
    proof (rule divide_left_mono)
      show "2 \<le> 2 * real (Suc j)" by simp
      show "0 \<le> t" using t0 by linarith
      show "0 < 2 * real (Suc j) * 2" by simp
    qed
    then show ?thesis unfolding tj_def using t0 by linarith
  qed
  have tju: "tj j < t" for j
  proof -
    have "0 < t / (2 * real (Suc j))" using t0 by simp
    then show ?thesis unfolding tj_def by linarith
  qed
  have tjc: "tj j \<le> c" for j using tju[of j] tc by linarith
  have glow: "tj j * cm / 2 \<le> g (tj j)" for j
    unfolding g_def
  proof (rule good)
    show "0 < tj j" by (rule tjl)
    show "tj j \<le> c" by (rule tjc)
    show "\<forall>s\<in>{0..tj j}. fst (\<omega> s) \<in> RO"
    proof
      fix s assume s: "s \<in> {0..tj j}"
      then have "0 \<le> s" and "s < t" using tju[of j] by auto
      then show "fst (\<omega> s) \<in> RO" by (rule inb)
    qed
  qed
  have tjlim: "tj \<longlonglongrightarrow> t"
  proof -
    have eq: "(\<lambda>j. (t / 2) * inverse (real (Suc j)))
        = (\<lambda>j. t / (2 * real (Suc j)))"
      by (rule ext) (simp add: field_simps)
    have "(\<lambda>j. (t / 2) * inverse (real (Suc j))) \<longlonglongrightarrow> (t / 2) * 0"
      by (intro tendsto_mult tendsto_const LIMSEQ_inverse_real_of_nat)
    then have "(\<lambda>j. t / (2 * real (Suc j))) \<longlonglongrightarrow> 0"
      unfolding eq by simp
    then have "(\<lambda>j. t - t / (2 * real (Suc j))) \<longlonglongrightarrow> t - 0"
      by (intro tendsto_diff tendsto_const)
    then show ?thesis unfolding tj_def by simp
  qed
  have gcomp: "(\<lambda>j. g (tj j)) \<longlonglongrightarrow> g t"
  proof -
    have inS: "\<forall>n. tj n \<in> {0..c}"
      using tjl tjc by (auto intro: less_imp_le)
    have tS: "t \<in> {0..c}" using t0 tc by auto
    have "(g \<circ> tj) \<longlonglongrightarrow> g t"
      using continuous_on_sequentially[THEN iffD1, OF gc] inS tS tjlim
      by blast
    then show ?thesis by (simp add: o_def)
  qed
  have lim1: "(\<lambda>j. tj j * cm / 2) \<longlonglongrightarrow> t * cm / 2"
    by (rule tendsto_divide[OF
        tendsto_mult[OF tjlim tendsto_const] tendsto_const]) simp
  have "t * cm / 2 \<le> g t"
    by (rule LIMSEQ_le[OF lim1 gcomp]) (use glow in blast)
  then show ?thesis unfolding g_def .
qed

subsection \<open>Case 1 for the lower envelope\<close>

text \<open>The touching-point argument at the envelope.  Two things change
  relative to \<open>exit_val_supersol_contradiction_case1\<close>.
  First, the horizon lemma is applied to the envelope, so it is stated
  for an arbitrary touching function with an explicit cap.  Second, the
  value at the touching point need not be attained there, so the
  construction is run at an approximating point \<open>y\<close> supplied by
  \<open>lsc_env_approx\<close>, with the quadratic still centred at
  \<open>x\<close>.  @{thm [source] quad_shift} and @{thm [source] quad_grad_shift}
  make the verified machinery serve that configuration unchanged: the
  gradient field and the kill hypothesis are the same, and the only
  trace of the displacement is the additive constant \<open>\<psi>(y)\<close>, which the
  choice of \<open>y\<close> drives below any prescribed margin.\<close>

lemma quad_good_rat_to_real_region:
  fixes \<omega> :: "'n::finite pairpath" and q x :: "real^'n"
    and M :: "real^'n^'n" and c cm t :: real and RO :: "(real^'n) set"
  assumes wm: "\<omega> \<in> mspace (path_metric c :: ('n pairpath) metric)"
    and rat: "\<And>r. r \<in> \<rat> \<Longrightarrow> 0 < r \<Longrightarrow> r \<le> c \<Longrightarrow>
      (\<forall>s\<in>{0..r}. fst (\<omega> s) \<in> RO) \<Longrightarrow>
      r * cm / 2 \<le> q \<bullet> (fst (\<omega> r) - x)
        + (1/2) * ((fst (\<omega> r) - x) \<bullet> (M *v (fst (\<omega> r) - x)))"
    and t0: "0 < t" and tc: "t \<le> c"
    and inb: "\<And>s. s \<in> {0..t} \<Longrightarrow> fst (\<omega> s) \<in> RO"
  shows "t * cm / 2 \<le> q \<bullet> (fst (\<omega> t) - x)
      + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x)))"
proof -
  define g where "g = (\<lambda>s. q \<bullet> (fst (\<omega> s) - x)
      + (1/2) * ((fst (\<omega> s) - x) \<bullet> (M *v (fst (\<omega> s) - x))))"
  have gc: "continuous_on {0..c} g"
    unfolding g_def by (rule quad_eval_cont[OF wm])
  have exr: "\<exists>r. r \<in> \<rat>
      \<and> max 0 (t - inverse (real (Suc j))) < r \<and> r < t" for j
  proof -
    have "max 0 (t - inverse (real (Suc j))) < t"
      using t0 by simp
    then show ?thesis
      using Rats_dense_in_real[of
          "max 0 (t - inverse (real (Suc j)))" t] by blast
  qed
  have exr': "\<forall>j. \<exists>r. r \<in> \<rat>
      \<and> max 0 (t - inverse (real (Suc j))) < r \<and> r < t"
    using exr by blast
  obtain rj where rjprop: "\<forall>j. rj j \<in> \<rat>
      \<and> max 0 (t - inverse (real (Suc j))) < rj j \<and> rj j < t"
    using choice[OF exr'] by blast
  have rjQ: "rj j \<in> \<rat>" for j using rjprop by blast
  have rjl: "max 0 (t - inverse (real (Suc j))) < rj j" for j
    using rjprop by blast
  have rju: "rj j < t" for j using rjprop by blast
  have rj0: "0 < rj j" for j
  proof -
    have "(0::real) \<le> max 0 (t - inverse (real (Suc j)))" by simp
    then show ?thesis using rjl[of j] by linarith
  qed
  have rjc: "rj j \<le> c" for j using rju[of j] tc by linarith
  have glow: "rj j * cm / 2 \<le> g (rj j)" for j
    unfolding g_def
  proof (rule rat)
    show "rj j \<in> \<rat>" by (rule rjQ)
    show "0 < rj j" by (rule rj0)
    show "rj j \<le> c" by (rule rjc)
    show "\<forall>s\<in>{0..rj j}. fst (\<omega> s) \<in> RO"
    proof
      fix s assume "s \<in> {0..rj j}"
      then have "s \<in> {0..t}" using rju[of j] by auto
      then show "fst (\<omega> s) \<in> RO" by (rule inb)
    qed
  qed
  have rjlim: "rj \<longlonglongrightarrow> t"
  proof (rule tendsto_sandwich[of
      "\<lambda>j. t - inverse (real (Suc j))" rj sequentially "\<lambda>_. t"])
    show "\<forall>\<^sub>F j in sequentially. t - inverse (real (Suc j)) \<le> rj j"
    proof (intro always_eventually allI)
      fix j
      have "t - inverse (real (Suc j))
          \<le> max 0 (t - inverse (real (Suc j)))"
        by (rule max.cobounded2)
      then show "t - inverse (real (Suc j)) \<le> rj j"
        using rjl[of j] by linarith
    qed
    show "\<forall>\<^sub>F j in sequentially. rj j \<le> t"
      by (intro always_eventually allI less_imp_le rju)
    show "(\<lambda>j. t - inverse (real (Suc j))) \<longlonglongrightarrow> t"
      using tendsto_diff[OF tendsto_const
          LIMSEQ_inverse_real_of_nat, of t] by simp
    show "(\<lambda>_. t) \<longlonglongrightarrow> t" by (rule tendsto_const)
  qed
  have gcomp: "(\<lambda>j. g (rj j)) \<longlonglongrightarrow> g t"
  proof -
    have inS: "\<forall>n. rj n \<in> {0..c}"
      using rj0 rjc by (auto intro: less_imp_le)
    have tS: "t \<in> {0..c}" using t0 tc by auto
    have "(g \<circ> rj) \<longlonglongrightarrow> g t"
      using continuous_on_sequentially[THEN iffD1, OF gc] inS tS rjlim
      by blast
    then show ?thesis by (simp add: o_def)
  qed
  have lim1: "(\<lambda>j. rj j * cm / 2) \<longlonglongrightarrow> t * cm / 2"
    by (rule tendsto_divide[OF
        tendsto_mult[OF rjlim tendsto_const] tendsto_const]) simp
  have "t * cm / 2 \<le> g t"
    by (rule LIMSEQ_le[OF lim1 gcomp]) (use glow in blast)
  then show ?thesis unfolding g_def .
qed

lemma quad_good_rat_to_real:
  fixes \<omega> :: "'n::finite pairpath" and q x :: "real^'n"
    and M :: "real^'n^'n" and c cm rb t :: real
  assumes wm: "\<omega> \<in> mspace (path_metric c :: ('n pairpath) metric)"
    and rat: "\<And>r. r \<in> \<rat> \<Longrightarrow> 0 < r \<Longrightarrow> r \<le> c \<Longrightarrow>
      (\<forall>s\<in>{0..r}. fst (\<omega> s) \<in> ball x rb) \<Longrightarrow>
      r * cm / 2 \<le> q \<bullet> (fst (\<omega> r) - x)
        + (1/2) * ((fst (\<omega> r) - x) \<bullet> (M *v (fst (\<omega> r) - x)))"
    and t0: "0 < t" and tc: "t \<le> c"
    and inb: "\<And>s. s \<in> {0..t} \<Longrightarrow> fst (\<omega> s) \<in> ball x rb"
  shows "t * cm / 2 \<le> q \<bullet> (fst (\<omega> t) - x)
      + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x)))"
proof -
  define g where "g = (\<lambda>s. q \<bullet> (fst (\<omega> s) - x)
      + (1/2) * ((fst (\<omega> s) - x) \<bullet> (M *v (fst (\<omega> s) - x))))"
  have gc: "continuous_on {0..c} g"
    unfolding g_def by (rule quad_eval_cont[OF wm])
  have exr: "\<exists>r. r \<in> \<rat>
      \<and> max 0 (t - inverse (real (Suc j))) < r \<and> r < t" for j
  proof -
    have "max 0 (t - inverse (real (Suc j))) < t"
      using t0 by simp
    then show ?thesis
      using Rats_dense_in_real[of
          "max 0 (t - inverse (real (Suc j)))" t] by blast
  qed
  have exr': "\<forall>j. \<exists>r. r \<in> \<rat>
      \<and> max 0 (t - inverse (real (Suc j))) < r \<and> r < t"
    using exr by blast
  obtain rj where rjprop: "\<forall>j. rj j \<in> \<rat>
      \<and> max 0 (t - inverse (real (Suc j))) < rj j \<and> rj j < t"
    using choice[OF exr'] by blast
  have rjQ: "rj j \<in> \<rat>" for j using rjprop by blast
  have rjl: "max 0 (t - inverse (real (Suc j))) < rj j" for j
    using rjprop by blast
  have rju: "rj j < t" for j using rjprop by blast
  have rj0: "0 < rj j" for j
  proof -
    have "(0::real) \<le> max 0 (t - inverse (real (Suc j)))" by simp
    then show ?thesis using rjl[of j] by linarith
  qed
  have rjc: "rj j \<le> c" for j using rju[of j] tc by linarith
  have glow: "rj j * cm / 2 \<le> g (rj j)" for j
    unfolding g_def
  proof (rule rat)
    show "rj j \<in> \<rat>" by (rule rjQ)
    show "0 < rj j" by (rule rj0)
    show "rj j \<le> c" by (rule rjc)
    show "\<forall>s\<in>{0..rj j}. fst (\<omega> s) \<in> ball x rb"
    proof
      fix s assume "s \<in> {0..rj j}"
      then have "s \<in> {0..t}" using rju[of j] by auto
      then show "fst (\<omega> s) \<in> ball x rb" by (rule inb)
    qed
  qed
  have rjlim: "rj \<longlonglongrightarrow> t"
  proof (rule tendsto_sandwich[of
      "\<lambda>j. t - inverse (real (Suc j))" rj sequentially "\<lambda>_. t"])
    show "\<forall>\<^sub>F j in sequentially. t - inverse (real (Suc j)) \<le> rj j"
    proof (intro always_eventually allI)
      fix j
      have "t - inverse (real (Suc j))
          \<le> max 0 (t - inverse (real (Suc j)))"
        by (rule max.cobounded2)
      then show "t - inverse (real (Suc j)) \<le> rj j"
        using rjl[of j] by linarith
    qed
    show "\<forall>\<^sub>F j in sequentially. rj j \<le> t"
      by (intro always_eventually allI less_imp_le rju)
    show "(\<lambda>j. t - inverse (real (Suc j))) \<longlonglongrightarrow> t"
      using tendsto_diff[OF tendsto_const
          LIMSEQ_inverse_real_of_nat, of t] by simp
    show "(\<lambda>_. t) \<longlonglongrightarrow> t" by (rule tendsto_const)
  qed
  have gcomp: "(\<lambda>j. g (rj j)) \<longlonglongrightarrow> g t"
  proof -
    have inS: "\<forall>n. rj n \<in> {0..c}"
      using rj0 rjc by (auto intro: less_imp_le)
    have tS: "t \<in> {0..c}" using t0 tc by auto
    have "(g \<circ> rj) \<longlonglongrightarrow> g t"
      using continuous_on_sequentially[THEN iffD1, OF gc] inS tS rjlim
      by blast
    then show ?thesis by (simp add: o_def)
  qed
  have lim1: "(\<lambda>j. rj j * cm / 2) \<longlonglongrightarrow> t * cm / 2"
    by (rule tendsto_divide[OF
        tendsto_mult[OF rjlim tendsto_const] tendsto_const]) simp
  have "t * cm / 2 \<le> g t"
    by (rule LIMSEQ_le[OF lim1 gcomp]) (use glow in blast)
  then show ?thesis unfolding g_def .
qed

lemma quad_good_upto:
  fixes \<omega> :: "'n::finite pairpath" and q x :: "real^'n"
    and M :: "real^'n^'n" and c cm rb t :: real
  assumes wm: "\<omega> \<in> mspace (path_metric c :: ('n pairpath) metric)"
    and good: "\<And>t'. 0 < t' \<Longrightarrow> t' \<le> c \<Longrightarrow>
      (\<forall>s\<in>{0..t'}. fst (\<omega> s) \<in> ball x rb) \<Longrightarrow>
      t' * cm / 2 \<le> q \<bullet> (fst (\<omega> t') - x)
        + (1/2) * ((fst (\<omega> t') - x) \<bullet> (M *v (fst (\<omega> t') - x)))"
    and t0: "0 < t" and tc: "t \<le> c"
    and inb: "\<And>s. 0 \<le> s \<Longrightarrow> s < t \<Longrightarrow> fst (\<omega> s) \<in> ball x rb"
  shows "t * cm / 2 \<le> q \<bullet> (fst (\<omega> t) - x)
      + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x)))"
proof -
  define g where "g = (\<lambda>s. q \<bullet> (fst (\<omega> s) - x)
      + (1/2) * ((fst (\<omega> s) - x) \<bullet> (M *v (fst (\<omega> s) - x))))"
  have gc: "continuous_on {0..c} g"
    unfolding g_def by (rule quad_eval_cont[OF wm])
  define tj where "tj = (\<lambda>j. t - t / (2 * real (Suc j)))"
  have tjl: "0 < tj j" for j
  proof -
    have "t / (2 * real (Suc j)) \<le> t / 2"
    proof (rule divide_left_mono)
      show "2 \<le> 2 * real (Suc j)" by simp
      show "0 \<le> t" using t0 by linarith
      show "0 < 2 * real (Suc j) * 2" by simp
    qed
    then show ?thesis unfolding tj_def using t0 by linarith
  qed
  have tju: "tj j < t" for j
  proof -
    have "0 < t / (2 * real (Suc j))" using t0 by simp
    then show ?thesis unfolding tj_def by linarith
  qed
  have tjc: "tj j \<le> c" for j using tju[of j] tc by linarith
  have glow: "tj j * cm / 2 \<le> g (tj j)" for j
    unfolding g_def
  proof (rule good)
    show "0 < tj j" by (rule tjl)
    show "tj j \<le> c" by (rule tjc)
    show "\<forall>s\<in>{0..tj j}. fst (\<omega> s) \<in> ball x rb"
    proof
      fix s assume s: "s \<in> {0..tj j}"
      then have s0: "0 \<le> s" and st: "s < t" using tju[of j] by auto
      show "fst (\<omega> s) \<in> ball x rb" by (rule inb[OF s0 st])
    qed
  qed
  have tjlim: "tj \<longlonglongrightarrow> t"
  proof -
    have eq: "(\<lambda>j. (t / 2) * inverse (real (Suc j)))
        = (\<lambda>j. t / (2 * real (Suc j)))"
      by (rule ext) (simp add: field_simps)
    have "(\<lambda>j. (t / 2) * inverse (real (Suc j))) \<longlonglongrightarrow> (t / 2) * 0"
      by (intro tendsto_mult tendsto_const LIMSEQ_inverse_real_of_nat)
    then have "(\<lambda>j. t / (2 * real (Suc j))) \<longlonglongrightarrow> 0"
      unfolding eq by simp
    then have "(\<lambda>j. t - t / (2 * real (Suc j))) \<longlonglongrightarrow> t - 0"
      by (intro tendsto_diff tendsto_const)
    then show ?thesis unfolding tj_def by simp
  qed
  have gcomp: "(\<lambda>j. g (tj j)) \<longlonglongrightarrow> g t"
  proof -
    have inS: "\<forall>n. tj n \<in> {0..c}"
      using tjl tjc by (auto intro: less_imp_le)
    have tS: "t \<in> {0..c}" using t0 tc by auto
    have "(g \<circ> tj) \<longlonglongrightarrow> g t"
      using continuous_on_sequentially[THEN iffD1, OF gc] inS tS tjlim
      by blast
    then show ?thesis by (simp add: o_def)
  qed
  have lim1: "(\<lambda>j. tj j * cm / 2) \<longlonglongrightarrow> t * cm / 2"
    by (rule tendsto_divide[OF
        tendsto_mult[OF tjlim tendsto_const] tendsto_const]) simp
  have "t * cm / 2 \<le> g t"
    by (rule LIMSEQ_le[OF lim1 gcomp]) (use glow in blast)
  then show ?thesis unfolding g_def .
qed


section \<open>Laws with a constrained covariation\<close>

text \<open>
  The object a stochastic-control argument in the martingale-problem
  formulation actually works with: the set of laws \<open>Q\<close> of a pair path
  \<open>(X, Y)\<close> on \<open>C([0,T])\<close> such that \<open>(X\<^sub>0, Y\<^sub>0) = (x, 0)\<close>, every difference
  quotient of \<open>Y\<close> lies in a fixed set \<open>S\<close> of matrices, \<open>X\<close> is a martingale
  for the pair's own filtration, and \<open>X X\<^sup>T - Y\<close> is one too -- so that \<open>Y\<close>
  is the covariation of \<open>X\<close> and \<open>S\<close> constrains its density.

  Only the third clause mentions \<open>S\<close>, and the results below say which
  properties of \<open>S\<close> each consequence needs: a norm bound gives Lipschitz
  paths for \<open>Y\<close>, and a bound on the diagonal entries gives the monotone
  increments a compensator argument reads.  \<open>S\<close> itself is arbitrary.
\<close>

definition covariation_class ::
  "(real^'n::finite^'n) set \<Rightarrow> real \<Rightarrow> real^'n
     \<Rightarrow> (('n pairpath) measure) set"
  where
  "covariation_class S T x = {Q.
     prob_space Q \<and>
     sets Q = sets (path_borel T :: ('n pairpath) measure) \<and>
     (AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0) \<and>
     (AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> S) \<and>
     martingale Q
       (natural_filtration Q 0 (\<lambda>t \<omega>. \<omega> t)) 0
       (\<lambda>t \<omega>. fst (\<omega> (min t T))) \<and>
     martingale Q
       (natural_filtration Q 0 (\<lambda>t \<omega>. \<omega> t)) 0
       (\<lambda>t \<omega>. outerp (fst (\<omega> (min t T))) - snd (\<omega> (min t T)))}"

text \<open>The six clauses, projected out.\<close>

lemma covariation_class_prob:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes "Q \<in> covariation_class S T x" shows "prob_space Q"
  using assms unfolding covariation_class_def by blast

lemma covariation_class_sets:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes "Q \<in> covariation_class S T x"
  shows "sets Q = sets (path_borel T :: ('n pairpath) measure)"
  using assms unfolding covariation_class_def by blast

lemma covariation_class_start:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes "Q \<in> covariation_class S T x"
  shows "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
  using assms unfolding covariation_class_def by blast

lemma covariation_class_diffquot:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes "Q \<in> covariation_class S T x"
  shows "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> S"
  using assms unfolding covariation_class_def by blast

lemma covariation_class_martingale_fst:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes "Q \<in> covariation_class S T x"
  shows "martingale Q (natural_filtration Q 0 (\<lambda>t \<omega>. \<omega> t)) 0
      (\<lambda>t \<omega>. fst (\<omega> (min t T)))"
  using assms unfolding covariation_class_def by blast

lemma covariation_class_martingale_compensated:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes "Q \<in> covariation_class S T x"
  shows "martingale Q (natural_filtration Q 0 (\<lambda>t \<omega>. \<omega> t)) 0
      (\<lambda>t \<omega>. outerp (fst (\<omega> (min t T))) - snd (\<omega> (min t T)))"
  using assms unfolding covariation_class_def by blast

lemma covariation_classI:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes "prob_space Q"
    and "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    and "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> S"
    and "martingale Q (natural_filtration Q 0 (\<lambda>t \<omega>. \<omega> t)) 0
        (\<lambda>t \<omega>. fst (\<omega> (min t T)))"
    and "martingale Q (natural_filtration Q 0 (\<lambda>t \<omega>. \<omega> t)) 0
        (\<lambda>t \<omega>. outerp (fst (\<omega> (min t T))) - snd (\<omega> (min t T)))"
  shows "Q \<in> covariation_class S T x"
  using assms unfolding covariation_class_def by blast

text \<open>Monotonicity in the constraint set: enlarging \<open>S\<close> enlarges the class.
  This is the only structural fact that needs nothing of \<open>S\<close> at all.\<close>

lemma covariation_class_mono:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes Q: "Q \<in> covariation_class S T x" and SS: "S \<subseteq> S'"
  shows "Q \<in> covariation_class S' T x"
proof (rule covariation_classI)
  show "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> S'"
    using covariation_class_diffquot[OF Q] by eventually_elim (use SS in blast)
qed (rule covariation_class_prob[OF Q], rule covariation_class_sets[OF Q],
     rule covariation_class_start[OF Q],
     rule covariation_class_martingale_fst[OF Q],
     rule covariation_class_martingale_compensated[OF Q])

text \<open>A norm bound on \<open>S\<close> makes the covariation path Lipschitz, at the same
  constant, and hence bounded on the horizon.\<close>

theorem covariation_class_lipschitz_ae:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes T: "0 \<le> T" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and Q: "Q \<in> covariation_class S T x"
  shows "AE \<omega> in Q. B-lipschitz_on {0..T} (\<lambda>t. snd (\<omega> t))"
proof -
  have dq: "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> S"
    by (rule covariation_class_diffquot[OF Q])
  show ?thesis
  proof (rule AE_mp[OF dq], rule AE_I2, intro impI)
    fix \<omega> :: "'n pairpath"
    assume q: "\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> S"
    show "B-lipschitz_on {0..T} (\<lambda>t. snd (\<omega> t))"
    proof (rule diffquot_lipschitz[OF B0])
      fix a :: "real^'n^'n" assume "a \<in> S" then show "norm a \<le> B" by (rule B)
    next
      fix s t :: real assume "0 \<le> s" "s < t" "t \<le> T"
      then show "(1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> S"
        using q by blast
    qed
  qed
qed

theorem covariation_class_Y_bounded_ae:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes T: "0 \<le> T" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and Q: "Q \<in> covariation_class S T x"
  shows "AE \<omega> in Q. \<forall>t\<in>{0..T}. norm (snd (\<omega> t)) \<le> B * T"
proof -
  have z0: "(0::real) \<in> {0..T}" using T by simp
  have lip: "AE \<omega> in Q. B-lipschitz_on {0..T} (\<lambda>t. snd (\<omega> t))"
    by (rule covariation_class_lipschitz_ae[OF T B0 B Q])
  have st: "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    by (rule covariation_class_start[OF Q])
  from lip st show ?thesis
  proof eventually_elim
    case (elim \<omega>)
    then have lp: "B-lipschitz_on {0..T} (\<lambda>t. snd (\<omega> t))"
      and z: "snd (\<omega> 0) = 0" by blast+
    show ?case
    proof (intro ballI)
      fix t :: real assume t: "t \<in> {0..T}"
      have "norm (snd (\<omega> t)) = dist (snd (\<omega> t)) (snd (\<omega> 0))"
        using z by (simp add: dist_norm)
      also have "\<dots> \<le> B * dist t 0" by (rule lipschitz_onD[OF lp t z0])
      also have "\<dots> = B * t" using t by (simp add: dist_real_def)
      also have "\<dots> \<le> B * T" using t B0 by (intro mult_left_mono) auto
      finally show "norm (snd (\<omega> t)) \<le> B * T" .
    qed
  qed
qed

text \<open>A two-sided bound on the diagonal entries of \<open>S\<close> makes each diagonal
  entry of the covariation nondecreasing, at rate at most \<open>B\<close>.\<close>

theorem covariation_class_Y_diag_increment:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes B0: "0 \<le> B"
    and D: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> 0 \<le> a $ i $ i \<and> a $ i $ i \<le> B"
    and Q: "Q \<in> covariation_class S T x"
  shows "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s \<le> t \<longrightarrow> t \<le> T \<longrightarrow>
      0 \<le> snd (\<omega> t) $ i $ i - snd (\<omega> s) $ i $ i
      \<and> snd (\<omega> t) $ i $ i - snd (\<omega> s) $ i $ i \<le> B * (t - s)"
proof -
  have dq: "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> S"
    by (rule covariation_class_diffquot[OF Q])
  from dq show ?thesis
  proof (rule eventually_mono)
    fix \<omega> :: "'n pairpath"
    assume h: "\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> S"
    show "\<forall>s t. 0 \<le> s \<longrightarrow> s \<le> t \<longrightarrow> t \<le> T \<longrightarrow>
        0 \<le> snd (\<omega> t) $ i $ i - snd (\<omega> s) $ i $ i
        \<and> snd (\<omega> t) $ i $ i - snd (\<omega> s) $ i $ i \<le> B * (t - s)"
    proof (intro allI impI)
      fix s t :: real
      assume s: "0 \<le> s" and st: "s \<le> t" and tT: "t \<le> T"
      show "0 \<le> snd (\<omega> t) $ i $ i - snd (\<omega> s) $ i $ i
          \<and> snd (\<omega> t) $ i $ i - snd (\<omega> s) $ i $ i \<le> B * (t - s)"
      proof (cases "s = t")
        case True
        then show ?thesis using B0 by simp
      next
        case False
        then have lt: "s < t" using st by simp
        have d0: "0 < t - s" using lt by simp
        have mem: "(1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> S"
          using h s lt tT by blast
        have ent: "((1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s))) $ i $ i
            = (snd (\<omega> t) $ i $ i - snd (\<omega> s) $ i $ i) / (t - s)"
          by simp
        have nn: "0 \<le> (snd (\<omega> t) $ i $ i - snd (\<omega> s) $ i $ i) / (t - s)"
          using D[OF mem] ent by simp
        have ub: "(snd (\<omega> t) $ i $ i - snd (\<omega> s) $ i $ i) / (t - s) \<le> B"
          using D[OF mem] ent by simp
        have p1: "0 \<le> ((snd (\<omega> t) $ i $ i - snd (\<omega> s) $ i $ i) / (t - s))
            * (t - s)"
          using nn d0 by (intro mult_nonneg_nonneg) auto
        have p2: "((snd (\<omega> t) $ i $ i - snd (\<omega> s) $ i $ i) / (t - s))
            * (t - s) \<le> B * (t - s)"
          using ub d0 by (intro mult_right_mono) auto
        show ?thesis using p1 p2 d0 by simp
      qed
    qed
  qed
qed

lemma covariation_class_eval_measurable:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes Q: "Q \<in> covariation_class S T x" and t: "t \<in> {0..T}"
  shows "(\<lambda>\<omega>. \<omega> t) \<in> borel_measurable Q"
proof -
  have "(\<lambda>\<omega> :: 'n pairpath. \<omega> t) \<in> (path_borel T :: ('n pairpath) measure) \<rightarrow>\<^sub>M borel"
    using continuous_map_measurable[OF continuous_map_path_eval[OF t]]
    by (simp add: borel_of_euclidean)
  then show ?thesis
    using measurable_cong_sets[OF covariation_class_sets[OF Q] refl] by blast
qed

lemma covariation_class_Y_entry_measurable:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes Q: "Q \<in> covariation_class S T x" and t: "t \<in> {0..T}"
  shows "(\<lambda>\<omega>. snd (\<omega> t) $ i $ j) \<in> borel_measurable Q"
proof (rule measurable_compose[OF covariation_class_eval_measurable[OF Q t]])
  have s: "(snd :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n^'n)
      \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  \<comment> \<open>\<^verbatim>\<open>borel_measurable_nth\<close> is only the REAL-valued instance
      \<open>real^'n \<Rightarrow> real\<close>; the matrix row map needs the linear-continuity
      route.\<close>
  have n1: "(\<lambda>v :: real^'n^'n. v $ i) \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI)
      (rule linear_continuous_on[OF bounded_linear_vec_nth])
  have n2: "(\<lambda>v :: real^'n. v $ j) \<in> borel_measurable borel"
    by (rule borel_measurable_nth)
  show "(\<lambda>p :: (real^'n) \<times> (real^'n^'n). snd p $ i $ j)
      \<in> borel_measurable borel"
    by (rule measurable_compose[OF measurable_compose[OF s n1] n2])
qed

lemma covariation_class_Y_entry_bound_ae:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes B0: "0 \<le> B" and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B" and T: "0 \<le> T"
    and Q: "Q \<in> covariation_class S T x" and t: "t \<in> {0..T}"
  shows "AE \<omega> in Q. norm (snd (\<omega> t) $ i $ j) \<le> B * T"
proof -
  have "AE \<omega> in Q. \<forall>u\<in>{0..T}. norm (snd (\<omega> u)) \<le> B * T"
    by (rule covariation_class_Y_bounded_ae[OF T B0 B Q])
  then show ?thesis
  proof (rule eventually_mono)
    fix \<omega> :: "'n pairpath"
    assume "\<forall>u\<in>{0..T}. norm (snd (\<omega> u)) \<le> B * T"
    then have b: "norm (snd (\<omega> t)) \<le> B * T" using t by blast
    have "norm (snd (\<omega> t) $ i $ j) \<le> norm (snd (\<omega> t) $ i)"
      by (rule Finite_Cartesian_Product.norm_nth_le)
    also have "\<dots> \<le> norm (snd (\<omega> t))"
      by (rule Finite_Cartesian_Product.norm_nth_le)
    finally show "norm (snd (\<omega> t) $ i $ j) \<le> B * T"
      using b by simp
  qed
qed

lemma covariation_class_Y_entry_integrable:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes B0: "0 \<le> B" and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B" and T: "0 \<le> T"
    and Q: "Q \<in> covariation_class S T x" and t: "t \<in> {0..T}"
  shows "integrable Q (\<lambda>\<omega>. snd (\<omega> t) $ i $ j)"
proof -
  interpret P: prob_space Q by (rule covariation_class_prob[OF Q])
  show ?thesis
    by (rule P.integrable_const_bound
        [OF covariation_class_Y_entry_bound_ae[OF B0 B T Q t]
            covariation_class_Y_entry_measurable[OF Q t]])
qed

lemma covariation_class_compensated_martingale:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes Q: "Q \<in> covariation_class S T x"
  shows "martingale Q (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)) 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T)))"
  using Q unfolding covariation_class_def by blast

lemma covariation_class_compensated_integrable:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes Q: "Q \<in> covariation_class S T x" and t: "t \<in> {0..T}"
  shows "integrable Q (\<lambda>\<omega>. outerp (fst (\<omega> t)) - snd (\<omega> t))"
proof -
  interpret MG: martingale Q "natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)" 0
      "\<lambda>u \<omega>. outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T))"
    by (rule covariation_class_compensated_martingale[OF Q])
  have "integrable Q (\<lambda>\<omega>. outerp (fst (\<omega> (min t T))) - snd (\<omega> (min t T)))"
    using t by (intro MG.integrable) simp
  then show ?thesis using t by simp
qed

lemma covariation_class_compensated_entry_integrable:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes Q: "Q \<in> covariation_class S T x" and t: "t \<in> {0..T}"
  shows "integrable Q (\<lambda>\<omega>. (outerp (fst (\<omega> t)) - snd (\<omega> t)) $ i $ j)"
  by (rule integrable_bounded_linear[OF bounded_linear_vec_nth,
        OF integrable_bounded_linear[OF bounded_linear_vec_nth
          covariation_class_compensated_integrable[OF Q t]]])

text \<open>Squaring the coordinate is the diagonal entry of \<open>outerp\<close>, so the
  split of \<open>(X\<^sub>t $ i)\<^sup>2\<close> into the compensated part plus \<open>Y\<close> is an
  identity of functions, not an inequality.\<close>

text \<open>Squaring the coordinate is the diagonal entry of \<open>outerp\<close>, so the
  split of \<open>(X\<^sub>t $ i)\<^sup>2\<close> into the compensated part plus \<open>Y\<close> is an
  identity of functions, not an inequality.\<close>


theorem covariation_class_sq_integrable:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes B0: "0 \<le> B" and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B" and T: "0 \<le> T"
    and Q: "Q \<in> covariation_class S T x" and t: "t \<in> {0..T}"
  shows "integrable Q (\<lambda>\<omega>. (fst (\<omega> t) $ i)\<^sup>2)"
proof -
  have t0: "0 \<le> t" using t by simp
  have eq: "(\<lambda>\<omega>. (fst (\<omega> t) $ i)\<^sup>2)
      = (\<lambda>\<omega>. (outerp (fst (\<omega> t)) - snd (\<omega> t)) $ i $ i + snd (\<omega> t) $ i $ i)"
    by (rule ext) (rule sq_coord_split)
  show ?thesis
    unfolding eq
    by (rule Bochner_Integration.integrable_add
        [OF covariation_class_compensated_entry_integrable[OF Q t]
            covariation_class_Y_entry_integrable[OF B0 B T Q t]])
qed

subsection \<open>The uniform \<open>L\<^sup>2\<close> bound on the class\<close>

text \<open>The uniform bound the weak-limit machinery needs, from a martingale's
  constant mean: \<open>E[outerp X\<^sub>t - Y\<^sub>t] = outerp x\<close>, whose diagonal entry
  is \<open>(x $ i)\<^sup>2 - E[Y\<^sub>t $ i $ i]\<close>. Since \<open>Y\<close> is bounded by \<open>n\<sqdot>L\<sqdot>T\<close>,
  the second moments are bounded uniformly over the class --- the hypothesis
  of \<open>unif_integrable_of_L2_bound\<close>.\<close>

text \<open>\<open>integral_of_bounded_linear\<close>, \<open>set_integral_of_bounded_linear\<close>,
  \<open>martingale_bounded_linear_image\<close>, \<open>martingale_vec_nth\<close> and
  \<open>martingale_mat_nth\<close> live in
  @{theory Continuous_Time_Martingales.Martingale_Algebra}.\<close>

text \<open>\<open>integral_of_bounded_linear\<close>, \<open>set_integral_of_bounded_linear\<close>,
  \<open>martingale_bounded_linear_image\<close>, \<open>martingale_vec_nth\<close> and
  \<open>martingale_mat_nth\<close> live in
  @{theory Continuous_Time_Martingales.Martingale_Algebra}.\<close>

theorem covariation_class_compensated_mean:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes Q: "Q \<in> covariation_class S T x" and t: "t \<in> {0..T}"
  shows "(\<integral>\<omega>. outerp (fst (\<omega> t)) - snd (\<omega> t) \<partial>Q) = outerp x"
proof -
  interpret P: prob_space Q by (rule covariation_class_prob[OF Q])
  interpret MG: martingale Q "natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)" 0
      "\<lambda>u \<omega>. outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T))"
    by (rule covariation_class_compensated_martingale[OF Q])
  have t0: "0 \<le> t" and tT: "t \<le> T" using t by simp_all
  have z: "(0::real) \<in> {0..T}" using t by simp
  have i0: "integrable Q (\<lambda>\<omega>. outerp (fst (\<omega> 0)) - snd (\<omega> 0))"
    by (rule covariation_class_compensated_integrable[OF Q z])
  have it: "integrable Q (\<lambda>\<omega>. outerp (fst (\<omega> t)) - snd (\<omega> t))"
    by (rule covariation_class_compensated_integrable[OF Q t])
  \<comment> \<open>the whole space is in the filtration at time \<open>0\<close>, so the martingale's
      set-integral identity there IS constancy of the mean.\<close>
  have top: "space Q \<in> sets (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u) 0)"
    using sets.top[of "natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u) 0"]
    by simp
  have const: "(\<integral>\<omega>. outerp (fst (\<omega> 0)) - snd (\<omega> 0) \<partial>Q)
      = (\<integral>\<omega>. outerp (fst (\<omega> t)) - snd (\<omega> t) \<partial>Q)"
    using MG.set_integral_eq[OF top order.refl t0] t0 tT
    by (simp add: set_integral_space[OF i0] set_integral_space[OF it])
  have start: "(\<integral>\<omega>. outerp (fst (\<omega> 0)) - snd (\<omega> 0) \<partial>Q) = outerp x"
  proof -
    have ae: "AE \<omega> in Q. outerp (fst (\<omega> 0)) - snd (\<omega> 0) = outerp x"
    proof -
      have "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
        using Q unfolding covariation_class_def by blast
      then show ?thesis by (rule eventually_mono) simp
    qed
    have "(\<integral>\<omega>. outerp (fst (\<omega> 0)) - snd (\<omega> 0) \<partial>Q) = (\<integral>\<omega>. outerp x \<partial>Q)"
      by (rule integral_cong_AE[OF borel_measurable_integrable[OF i0] _ ae])
        measurable
    then show ?thesis by (simp add: P.prob_space)
  qed
  from const start show ?thesis by simp
qed

theorem covariation_class_sq_mean_le:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes B0: "0 \<le> B" and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B" and T: "0 \<le> T"
    and Q: "Q \<in> covariation_class S T x" and t: "t \<in> {0..T}"
  shows "(\<integral>\<omega>. (fst (\<omega> t) $ i)\<^sup>2 \<partial>Q) \<le> (x $ i)\<^sup>2 + B * T"
proof -
  interpret P: prob_space Q by (rule covariation_class_prob[OF Q])
  have t0: "0 \<le> t" using t by simp
  have iA: "integrable Q (\<lambda>\<omega>. (outerp (fst (\<omega> t)) - snd (\<omega> t)) $ i $ i)"
    by (rule covariation_class_compensated_entry_integrable[OF Q t])
  have iB: "integrable Q (\<lambda>\<omega>. snd (\<omega> t) $ i $ i)"
    by (rule covariation_class_Y_entry_integrable[OF B0 B T Q t])
  have eq: "(\<lambda>\<omega>. (fst (\<omega> t) $ i)\<^sup>2)
      = (\<lambda>\<omega>. (outerp (fst (\<omega> t)) - snd (\<omega> t)) $ i $ i + snd (\<omega> t) $ i $ i)"
    by (rule ext) (rule sq_coord_split)
  have split: "(\<integral>\<omega>. (fst (\<omega> t) $ i)\<^sup>2 \<partial>Q)
      = (\<integral>\<omega>. (outerp (fst (\<omega> t)) - snd (\<omega> t)) $ i $ i \<partial>Q)
        + (\<integral>\<omega>. snd (\<omega> t) $ i $ i \<partial>Q)"
    unfolding eq by (rule Bochner_Integration.integral_add[OF iA iB])
  \<comment> \<open>the compensated part: pull the two \<open>$\<close> projections, both bounded
      linear, out through the integral, then apply the mean identity.\<close>
  have partA: "(\<integral>\<omega>. (outerp (fst (\<omega> t)) - snd (\<omega> t)) $ i $ i \<partial>Q)
      = (x $ i)\<^sup>2"
  proof -
    have "(\<integral>\<omega>. (outerp (fst (\<omega> t)) - snd (\<omega> t)) $ i $ i \<partial>Q)
        = (\<integral>\<omega>. (outerp (fst (\<omega> t)) - snd (\<omega> t)) $ i \<partial>Q) $ i"
      by (rule integral_of_bounded_linear[OF bounded_linear_vec_nth]
          , rule integrable_bounded_linear[OF bounded_linear_vec_nth])
        (rule covariation_class_compensated_integrable[OF Q t])
    also have "(\<integral>\<omega>. (outerp (fst (\<omega> t)) - snd (\<omega> t)) $ i \<partial>Q)
        = (\<integral>\<omega>. outerp (fst (\<omega> t)) - snd (\<omega> t) \<partial>Q) $ i"
      by (rule integral_of_bounded_linear[OF bounded_linear_vec_nth
            covariation_class_compensated_integrable[OF Q t]])
    also have "(\<integral>\<omega>. outerp (fst (\<omega> t)) - snd (\<omega> t) \<partial>Q) = outerp x"
      by (rule covariation_class_compensated_mean[OF Q t])
    finally show ?thesis by (simp add: outerp_def power2_eq_square)
  qed
  have partB: "(\<integral>\<omega>. snd (\<omega> t) $ i $ i \<partial>Q) \<le> B * T"
  proof -
    have "(\<integral>\<omega>. snd (\<omega> t) $ i $ i \<partial>Q) \<le> (\<integral>\<omega>. B * T \<partial>Q)"
    proof (rule integral_mono_AE[OF iB P.integrable_const])
      show "AE \<omega> in Q. snd (\<omega> t) $ i $ i \<le> B * T"
      proof (rule eventually_mono[OF covariation_class_Y_entry_bound_ae
              [OF B0 B T Q t, of i i]])
        fix \<omega> :: "'n pairpath"
        assume "norm (snd (\<omega> t) $ i $ i) \<le> B * T"
        then show "snd (\<omega> t) $ i $ i \<le> B * T"
          using abs_le_D1[of "snd (\<omega> t) $ i $ i" "B * T"] by simp
      qed
    qed
    then show ?thesis by (simp add: P.prob_space)
  qed
  from split partA partB show ?thesis by simp
qed

section \<open>Pair tightness from the two component moduli\<close>

text \<open>\<open>lipschitz_imp_holder_bound\<close> lives in @{theory Continuous_Path_Spaces.Holder_Interpolation}.\<close>


text \<open>The value of the minimum-exit-time problem over such a class: the
  largest almost-sure lower bound on the exit time of \<open>K\<close>, optimised over
  the laws.  \<open>K\<close> and \<open>S\<close> are both parameters; nothing here knows what they
  are.\<close>

definition covariation_val ::
  "(real^'n::finite^'n) set \<Rightarrow> real \<Rightarrow> (real^'n) set \<Rightarrow> real^'n \<Rightarrow> ennreal"
  where
  "covariation_val S T K x =
     Sup ((\<lambda>Q. ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))))
       ` covariation_class S T x)"

lemma covariation_val_mono_class:
  assumes "S \<subseteq> S'"
  shows "covariation_val S T K x \<le> covariation_val S' T K x"
  unfolding covariation_val_def
  by (rule Sup_subset_mono) (use assms covariation_class_mono in blast)

(*<*)
end
(*>*)
