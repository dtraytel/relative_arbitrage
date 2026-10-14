section \<open>The pair path space\<close>

(*<*)
theory Pair_Path_Space
  imports
    "Continuous_Path_Spaces.Adapted_Quadratic_Variation"
    "Continuous_Path_Spaces.Path_Exit_Times" "Continuous_Path_Spaces.Path_Tightness"
    "Disintegration.Disintegration" "Continuous_Path_Spaces.Semicontinuous_Selection"
    "Continuous_Time_Martingales.Integrability_Criteria"
    "Symmetric_Matrix_Spectra.Householder_Rotation"
    "Symmetric_Matrix_Spectra.Symmetric_Spectral"
begin

(*>*)

text \<open>The path space this development works on carries a pair: the state
  and its covariation, \<open>real \<Rightarrow> (real^'n) \<times> (real^'n^'n)\<close>.  This theory fixes
  that type and collects what is true of paths, and of laws of paths, before
  any constraint on the covariation is imposed -- measurability of the
  coordinates, continuity of evaluation, and martingale clauses for a
  general law.

  A fact that never looks inside the pair is stated for paths with values
  in any Polish Banach space \<open>'p\<close>, here and in the theories that follow;
  the pair is the instance \<open>'p = 'a \<times> 'b\<close>.  Only the facts that read a
  component (the shift \<open>pshift\<close> of the first component, \<open>pfst\<close>, exit
  times of the first component, path stopping times, the covariation
  constraint) are stated at a product.\<close>

text \<open>The state and its covariation, carried as one path.\<close>

type_synonym 'n pairpath = "real \<Rightarrow> (real^'n) \<times> (real^'n^'n)"

subsection \<open>The components of a pair path\<close>

text \<open>An identity \<open>F (X\<^sub>t) = c\<^sub>0 + t c\<^sub>n\<close> for a continuous functional \<open>F\<close>
  of the first component, known at every time up to which the path stays in
  a region \<open>RO\<close>, extends to the endpoint of a half-open stay \<open>[0, e)\<close>:
  both sides are continuous, so the identity passes to the limit from below.\<close>

lemma radial_sq_upto_gen:
  fixes \<omega> :: "(real \<Rightarrow> 'a::{polish_space,banach} \<times> 'b::{polish_space,banach})" and TT e c0 cn :: real
    and RO :: "('a) set" and F :: "'a \<Rightarrow> real"
  assumes wm: "\<omega> \<in> mspace (path_metric TT :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    and Fc: "continuous_on UNIV F"
    and grow: "\<And>t. 0 < t \<Longrightarrow> t \<le> TT \<Longrightarrow>
      (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> RO) \<Longrightarrow> F (fst (\<omega> t)) = c0 + t * cn"
    and e0: "0 < e" and eT: "e \<le> TT"
    and inside: "\<And>s. 0 \<le> s \<Longrightarrow> s < e \<Longrightarrow> fst (\<omega> s) \<in> RO"
  shows "F (fst (\<omega> e)) = c0 + e * cn"
proof -
  have gc: "continuous_on {0..TT} (\<lambda>s. F (fst (\<omega> s)))"
    by (rule continuous_on_compose2[OF Fc continuous_on_fst[OF
          mspace_path_metricD[OF wm]]]) auto
  have lc: "continuous_on {0..TT} (\<lambda>s. c0 + s * cn)"
    by (intro continuous_intros)
  have eq: "F (fst (\<omega> s)) = c0 + s * cn" if "s \<in> {0<..<e}" for s
    using that eT by (intro grow) (auto intro: inside)
  have cl: "e \<in> closure {0<..<e}" using e0 by simp
  have "F (fst (\<omega> e)) \<le> c0 + e * cn"
    by (rule le_from_below[OF lc gc eT order_refl cl]) (simp add: eq)
  moreover have "c0 + e * cn \<le> F (fst (\<omega> e))"
    by (rule le_from_below[OF gc lc eT order_refl cl]) (simp add: eq)
  ultimately show ?thesis by linarith
qed

text \<open>Each coordinate of the state is continuous along a pair path.\<close>

lemma path_coord_cont_on:
  fixes \<omega> :: "'n::finite pairpath"
  assumes w: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
  shows "continuous_on {0..T} (\<lambda>t. fst (\<omega> t) $ i)"
proof -
  have c: "continuous_on {0..T} \<omega>" by (rule mspace_path_metricD[OF w])
  have c2: "continuous_on UNIV
      (\<lambda>p :: (real^'n) \<times> (real^'n^'n). fst p $ i)"
    by (intro continuous_intros)
  show ?thesis by (rule continuous_on_compose2[OF c2 c]) simp
qed

text \<open>The two components at a time.\<close>

abbreviation pairX :: "real \<Rightarrow> (real \<Rightarrow> 'a \<times> 'b) \<Rightarrow> 'a"
  where "pairX t \<omega> \<equiv> fst (\<omega> t)"


abbreviation pairY :: "real \<Rightarrow> (real \<Rightarrow> 'a \<times> 'b) \<Rightarrow> 'b"
  where "pairY t \<omega> \<equiv> snd (\<omega> t)"

subsection \<open>Laws on the capped path space\<close>

text \<open>A law on the path space has the paths as its points.\<close>

lemma space_of_path_sets:
  fixes Q :: "(real \<Rightarrow> 'p::{polish_space,banach}) measure"
  assumes "sets Q = sets (path_borel T :: (real \<Rightarrow> 'p) measure)"
  shows "space Q = mspace (path_metric T :: (real \<Rightarrow> 'p) metric)"
  using sets_eq_imp_space_eq[OF assms] by (simp add: space_borel_of)

text \<open>Restricting a path to \<open>{0..s}\<close> is measurable from the natural
  filtration at \<open>s\<close> into the path space of horizon \<open>s\<close>; hence so is every
  Borel test of the restricted path, a test of the past.\<close>

lemma restrict_measurable_natural_filtration:
  fixes Q :: "(real \<Rightarrow> 'p::{polish_space,banach}) measure"
  assumes setsQ: "sets Q = sets (path_borel T :: (real \<Rightarrow> 'p) measure)"
    and s: "0 \<le> s" and sT: "s \<le> T"
  shows "(\<lambda>\<omega>. restrict \<omega> {0..s})
      \<in> natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u) s
        \<rightarrow>\<^sub>M (path_borel s :: (real \<Rightarrow> 'p) measure)"
proof -
  let ?F = "natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u) s"
  have spF: "space ?F = mspace (path_metric T :: (real \<Rightarrow> 'p) metric)"
    by (simp add: space_of_path_sets[OF setsQ])
  have evm: "(\<lambda>\<omega> :: (real \<Rightarrow> 'p). \<omega> u) \<in> borel_measurable ?F"
    if u: "u \<in> {0..s}" for u
    unfolding natural_filtration_def
    by (rule measurable_family_vimage_algebra) (use u in auto)
  have cont: "continuous_on {0..s} (\<lambda>u. \<omega> u)"
    if w: "\<omega> \<in> space ?F" for \<omega> :: "(real \<Rightarrow> 'p)"
  proof -
    have "\<omega> \<in> mspace (path_metric T :: (real \<Rightarrow> 'p) metric)"
      using w spF by simp
    from mspace_path_metricD[OF this] show ?thesis
      by (rule continuous_on_subset) (use sT s in auto)
  qed
  show ?thesis by (rule pathify_measurable[OF s evm cont])
qed

lemma past_test_measurable_natural_filtration:
  fixes Q :: "(real \<Rightarrow> 'p::{polish_space,banach}) measure" and h :: "(real \<Rightarrow> 'p) \<Rightarrow> real"
  assumes setsQ: "sets Q = sets (path_borel T :: (real \<Rightarrow> 'p) measure)"
    and s: "0 \<le> s" and sT: "s \<le> T"
    and h: "h \<in> borel_measurable (path_borel s :: (real \<Rightarrow> 'p) measure)"
  shows "(\<lambda>\<omega>. h (restrict \<omega> {0..s}))
      \<in> borel_measurable (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u) s)"
  by (rule measurable_compose
      [OF restrict_measurable_natural_filtration[OF setsQ s sT] h])

subsection \<open>Glueing two continuous paths\<close>

text \<open>Running \<open>\<omega>\<close> up to time \<open>r\<close> and continuing with the increments of
  \<open>\<omega>'\<close> gives a continuous path, on the half-line and on a capped horizon.\<close>

lemma continuous_on_iglue:
  fixes \<omega> \<omega>' :: "(real \<Rightarrow> 'p::real_normed_vector)"
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

lemma continuous_on_pglue:
  fixes \<omega> \<omega>' :: "(real \<Rightarrow> 'p::real_normed_vector)"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and c1: "continuous_on {0..r} \<omega>"
    and c2: "continuous_on {0..T - r} \<omega>'"
  shows "continuous_on {0..T}
      (\<lambda>t. if t \<le> r then \<omega> t else \<omega> r + (\<omega>' (t - r) - \<omega>' 0))"
proof -
  let ?w = "\<lambda>t. \<omega>' (min t (T - r))"
  have "continuous_on {0..} ?w"
    by (rule continuous_on_compose2[OF c2 continuous_on_min[OF continuous_on_id
          continuous_on_const]]) (use rT in auto)
  then have "continuous_on {0..}
      (\<lambda>t. if t \<le> r then \<omega> t else \<omega> r + (?w (t - r) - ?w 0))"
    by (rule continuous_on_iglue[OF r c1])
  then have "continuous_on {0..T}
      (\<lambda>t. if t \<le> r then \<omega> t else \<omega> r + (?w (t - r) - ?w 0))"
    by (rule continuous_on_subset) auto
  then show ?thesis by (rule continuous_on_eq) (use r rT in \<open>auto simp: min_def\<close>)
qed

subsection \<open>Difference quotients and second moments\<close>

text \<open>For fixed times \<open>s\<close> and \<open>t\<close>, the difference quotient of the covariation
  is a continuous function of the path.  So for a closed set \<open>S\<close> of
  matrices the paths whose quotient lies in \<open>S\<close> form a closed set, and the
  closed-set half of the portmanteau theorem (\<open>weak_conv_closed_full_measure\<close>)
  passes full mass of that set to a weak limit, with no Skorokhod
  representation.\<close>

lemma continuous_map_diffquot:
  fixes s t :: real
  assumes s: "s \<in> {0..T}" and t: "t \<in> {0..T}"
  shows "continuous_map (mtopology_of (path_metric T :: ('n::finite pairpath) metric))
      euclidean (\<lambda>\<omega>. (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)))"
proof -
  have "continuous_map (mtopology_of (path_metric T :: ('n pairpath) metric))
      euclidean (\<lambda>\<omega>. \<omega> t)"
    by (rule continuous_map_path_eval[OF t])
  moreover have "continuous_map (mtopology_of (path_metric T :: ('n pairpath) metric))
      euclidean (\<lambda>\<omega>. \<omega> s)"
    by (rule continuous_map_path_eval[OF s])
  moreover have sndc:
    "continuous_map euclidean euclidean
       (snd :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n^'n)"
    by (simp add: continuous_on_snd)
  ultimately have "continuous_map
      (mtopology_of (path_metric T :: ('n pairpath) metric)) euclidean
      (\<lambda>\<omega>. snd (\<omega> t) - snd (\<omega> s))"
    by (intro continuous_map_diff)
      (auto intro: continuous_map_compose[OF _ sndc, unfolded o_def])
  moreover have scl: "continuous_map euclidean euclidean
      (\<lambda>v :: real^'n^'n. (1 / (t - s)) *\<^sub>R v)"
    by (simp add:
        continuous_on_scaleR)
  ultimately have "continuous_map
      (mtopology_of (path_metric T :: ('n pairpath) metric)) euclidean
      ((\<lambda>v :: real^'n^'n. (1 / (t - s)) *\<^sub>R v)
        \<circ> (\<lambda>\<omega>. snd (\<omega> t) - snd (\<omega> s)))"
    by (intro continuous_map_compose)
  then show ?thesis by (simp add: o_def)
qed


text \<open>A second-moment bound on a coordinate, in nonnegative-integral form.\<close>

lemma pair_law_coord_sq_nn_bound:
  fixes N :: "('n::finite pairpath) measure"
  assumes setsN: "sets N = sets (path_borel T :: ('n pairpath) measure)"
    and u: "u \<in> {0..T}"
    and int: "integrable N (\<lambda>\<omega>. (fst (\<omega> u) $ i)\<^sup>2)"
    and le: "(\<integral>\<omega>. (fst (\<omega> u) $ i)\<^sup>2 \<partial>N) \<le> C"
  shows "(\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> u) $ i)\<^sup>2) \<partial>N) \<le> ennreal C"
proof -
  have "(\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> u) $ i)\<^sup>2) \<partial>N)
      = ennreal (\<integral>\<omega>. (fst (\<omega> u) $ i)\<^sup>2 \<partial>N)"
    by (rule nn_integral_eq_integral[OF int]) simp
  also have "\<dots> \<le> ennreal C" using le by (rule ennreal_leI)
  finally show ?thesis .
qed

text \<open>The algebra of the compensated clause at a difference of points: the
  outer product of \<open>a - b\<close> minus the difference of the covariations is the
  compensated outer product at \<open>a\<close>, minus the two cross terms, plus a
  remainder in \<open>b\<close> alone.\<close>

lemma outerp_diff_compensated:
  fixes a b :: "real^'n::finite" and Ya Yb :: "real^'n^'n"
  shows "outerp (a - b) - (Ya - Yb)
      = (outerp a - Ya) - ((\<chi> i j. a $ i * b $ j) + (\<chi> i j. b $ i * a $ j))
        + (outerp b + Yb)"
  by (simp add: outerp_diff)

subsection \<open>The exit time of a process and of its law\<close>

text \<open>The shifted exit-time functional \<open>vshift\<close> speaks about laws on the
  path space; \<open>path_law\<close> bridges to a process with continuous paths, and
  the essential infimum of the exit time is the same on both sides.\<close>

theorem vshift_path_law:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> 'b::{polish_space,banach}" and y :: 'b
  assumes T: "0 \<le> T" and A: "open A"
    and Xm: "\<And>t. t \<in> {0..T} \<Longrightarrow> X t \<in> borel_measurable M"
    and cont: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> continuous_on {0..T} (\<lambda>t. X t \<omega>)"
  shows "vshift T A y (path_law M X T)
       = enn2real (ess_inf_time M (etime T A (\<lambda>s \<omega>'. y + X s \<omega>')))"
proof -
  have pm: "(\<lambda>\<omega>. restrict (\<lambda>t. X t \<omega>) {0..T})
      \<in> M \<rightarrow>\<^sub>M (path_borel T :: (real \<Rightarrow> 'b) measure)"
    by (rule pathify_measurable[OF T Xm cont])
  have meas: "{\<omega> \<in> space (path_borel T :: (real \<Rightarrow> 'b) measure).
        c \<le> ennreal (etime T A (\<lambda>s w. y + w s) \<omega>)}
      \<in> sets (path_borel T :: (real \<Rightarrow> 'b) measure)"
    for c :: ennreal
    using borel_of_closed[OF etime_shift_superlevel_closed[OF T A, of c y]]
    by (simp add: space_borel_of)
  have "ess_inf_time (path_law M X T) (etime T A (\<lambda>s w. y + w s))
      = ess_inf_time M
          (\<lambda>\<omega>. etime T A (\<lambda>s w. y + w s) (restrict (\<lambda>t. X t \<omega>) {0..T}))"
    unfolding path_law_def by (rule ess_inf_time_distr[OF pm meas])
  also have "\<dots> = ess_inf_time M (etime T A (\<lambda>s \<omega>'. y + X s \<omega>'))"
    by (simp add: etime_shift_of_restrict)
  finally show ?thesis unfolding vshift_def by simp
qed

(*<*)
end
(*>*)
