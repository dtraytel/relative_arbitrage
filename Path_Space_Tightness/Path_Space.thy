section \<open>The path space \<open>C({0..T}, 'b)\<close> as a Polish metric space\<close>

(*<*)
theory Path_Space
  imports "Levy_Prokhorov_Metric.Prokhorov_Theorem"
    "Standard_Borel_Spaces.Set_Based_Metric_Space"
    Equicontinuity
begin

(*>*)

text \<open>
  The space the martingale laws of Lemma 2.2 of arXiv:2512.17702 live on:
  HOL-Analysis' set-based \<open>cfunspace\<close> (bounded continuous maps with the sup
  metric) over the compact interval \<open>{0..T}\<close>, valued in a Polish type.
  Completeness is \<open>Metric_space.mcomplete_cfunspace\<close> and separability
  \<open>Metric_space.separable_space_cfunspace\<close> (AFP Standard\_Borel\_Spaces);
  with compactness and metrizability of the domain, these are the
  hypotheses of the AFP's \<open>Prokhorov_theorem_LP\<close>, converting tightness of
  the Lemma 2.2 laws into relative compactness in the L\'evy-Prokhorov
  metric on this space.
\<close>
definition path_metric :: "real \<Rightarrow> (real \<Rightarrow> 'b::polish_space) metric" where
  "path_metric T = cfunspace (top_of_set {0..T::real}) (euclidean_metric :: 'b metric)"

lemma mcomplete_path_metric:
  "mcomplete_of (path_metric T :: (real \<Rightarrow> 'b::polish_space) metric)"
proof -
  have "Met_TC.mcomplete TYPE('b)" by (simp add: complete_UNIV)
  hence "mcomplete_of (cfunspace (top_of_set {0..T}) (Met_TC.Self :: 'b metric))"
    by (rule Met_TC.mcomplete_cfunspace)
  thus ?thesis
    by (simp add: path_metric_def Met_TC.Self_def euclidean_metric_def)
qed

lemma metrizable_Icc: "metrizable_space (top_of_set ({0..T} :: real set))"
  by (simp add: metrizable_space_subtopology metrizable_space_euclidean)

lemma compact_space_Icc: "compact_space (top_of_set ({0..T} :: real set))"
  by (intro compact_space_subtopology) simp

lemma separable_path_metric:
  "separable_space (mtopology_of (path_metric T :: (real \<Rightarrow> 'b::polish_space) metric))"
proof -
  have "separable_space (mtopology_of
      (cfunspace (top_of_set {0..T}) (Met_TC.Self :: 'b metric)))"
    using Met_TC.Metric_space_axioms Met_TC.separable_space_iff_second_countable
    by (auto intro!: Metric_space.separable_space_cfunspace
        [OF _ _ _ metrizable_Icc compact_space_Icc])
  thus ?thesis
    by (simp add: path_metric_def Met_TC.Self_def euclidean_metric_def)
qed

text \<open>The forms that the L\'evy-Prokhorov development consumes.\<close>

theorem path_metric_polish:
  "Metric_space.mcomplete (mspace (path_metric T :: (real \<Rightarrow> 'b::polish_space) metric))
      (mdist (path_metric T :: (real \<Rightarrow> 'b) metric))"
  "separable_space (Metric_space.mtopology
      (mspace (path_metric T :: (real \<Rightarrow> 'b::polish_space) metric))
      (mdist (path_metric T :: (real \<Rightarrow> 'b) metric)))"
  using mcomplete_path_metric[of T] separable_path_metric[of T]
  by (simp_all add: mcomplete_of_def mtopology_of_def)

subsection \<open>H\"older balls are compact in the path space\<close>

text \<open>
  The Arzel\`a--Ascoli input for tightness: the set of paths starting at a fixed
  point with a uniform H\"older bound is sequentially compact in the sup metric.
  The subsequence extraction is the type-class \<open>holder_family_subsequence\<close>
  (@{theory Path_Space_Tightness.Equicontinuity}); this theorem transports it into the set-based
  framework via \<open>compactin_sequentially\<close> and \<open>cfunspace_mdist_le\<close>.
\<close>

lemma mspace_path_metricI:
  fixes L :: "real \<Rightarrow> 'b::polish_space"
  assumes L: "continuous_on {0..T} L"
  shows "restrict L {0..T} \<in> mspace (path_metric T)"
proof -
  have c: "continuous_on {0..T} (restrict L {0..T})"
    by (rule continuous_on_cong[OF refl, THEN iffD2, OF _ L]) simp
  have im: "restrict L {0..T} ` {0..T} = L ` {0..T}"
    by (intro image_cong) simp_all
  have b: "bounded (restrict L {0..T} ` {0..T})"
    unfolding im
    by (intro compact_imp_bounded compact_continuous_image L) simp
  show ?thesis
    unfolding path_metric_def mspace_cfunspace
    using c b by auto
qed

text \<open>The converse direction: a point of the path space \<^emph>\<open>is\<close> a continuous
  function on \<open>{0..T}\<close>, so the countable-witness reduction
  \<open>Exit_Time.etime_less_iff_qtimes_open\<close> applies to it.\<close>

lemma mspace_path_metricD:
  fixes f :: "real \<Rightarrow> 'b::polish_space"
  assumes f: "f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric)"
  shows "continuous_on {0..T} f"
proof -
  have "continuous_map (top_of_set {0..T})
      (mtopology_of (euclidean_metric :: 'b metric)) f"
    using f unfolding path_metric_def mspace_cfunspace by simp
  hence "continuous_map (top_of_set {0..T}) euclidean f" by simp
  thus ?thesis by simp
qed

theorem compactin_path_holder_ball:
  fixes x :: "'b::{polish_space, real_normed_vector, heine_borel}"
    and T c ga :: real
  assumes T: "0 \<le> T" and ga: "0 < ga" and c: "0 \<le> c"
  shows "compactin (mtopology_of (path_metric T))
      {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
         f 0 = x \<and> (\<forall>s\<in>{0..T}. \<forall>t\<in>{0..T}. norm (f t - f s) \<le> c * \<bar>t - s\<bar> powr ga)}"
    (is "compactin _ ?S")
proof -
  interpret PM: Metric_space
    "mspace (path_metric T :: (real \<Rightarrow> 'b) metric)"
    "mdist (path_metric T :: (real \<Rightarrow> 'b) metric)"
    by (rule Metric_space_mspace_mdist)
  have mt: "mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric) = PM.mtopology"
    by (simp add: mtopology_of_def)
  have T0mem: "(0::real) \<in> {0..T}" using T by simp
  have ne: "{0..T} \<noteq> {}" using T by simp
  show ?thesis
    unfolding mt PM.compactin_sequentially
  proof (intro conjI allI impI)
    show "?S \<subseteq> mspace (path_metric T)" by auto
  next
    fix \<sigma> :: "nat \<Rightarrow> real \<Rightarrow> 'b"
    assume r\<sigma>: "range \<sigma> \<subseteq> ?S"
    have mem: "\<sigma> m \<in> mspace (path_metric T)" for m
      using r\<sigma> by blast
    have s0: "\<sigma> m 0 = x" for m
      using r\<sigma> by blast
    have hol: "norm (\<sigma> m t - \<sigma> m s) \<le> c * \<bar>t - s\<bar> powr ga"
      if "s \<in> {0..T}" "t \<in> {0..T}" for m s t
      using r\<sigma> that by blast
    show "\<exists>l r. l \<in> ?S \<and> strict_mono r
        \<and> limitin PM.mtopology (\<sigma> \<circ> r) l sequentially"
    proof (rule holder_family_subsequence[OF T ga c s0 hol])
      fix L and k :: "nat \<Rightarrow> nat"
      assume k: "strict_mono k"
        and Lc: "continuous_on {0..T} L" and L0: "L 0 = x"
        and Lh: "\<And>s t. s \<in> {0..T} \<Longrightarrow> t \<in> {0..T}
            \<Longrightarrow> norm (L t - L s) \<le> c * \<bar>t - s\<bar> powr ga"
        and conv: "\<And>e. 0 < e \<Longrightarrow> \<exists>N. \<forall>m\<ge>N. \<forall>t\<in>{0..T}. norm (\<sigma> (k m) t - L t) < e"
      let ?L = "restrict L {0..T}"
    have Lmem: "?L \<in> mspace (path_metric T)" by (rule mspace_path_metricI[OF Lc])
    have LS: "?L \<in> ?S"
    proof -
      have "?L 0 = x" using T0mem L0 by simp
      moreover have "norm (?L t - ?L s) \<le> c * \<bar>t - s\<bar> powr ga"
        if "s \<in> {0..T}" "t \<in> {0..T}" for s t
        using Lh[OF that] that by simp
      ultimately show ?thesis using Lmem by auto
    qed
    have lim: "limitin PM.mtopology (\<sigma> \<circ> k) ?L sequentially"
      unfolding PM.limit_metric_sequentially
    proof (intro conjI allI impI)
      show "?L \<in> mspace (path_metric T)" by (rule Lmem)
      fix \<epsilon> :: real assume e: "0 < \<epsilon>"
      then obtain N where N: "\<forall>m\<ge>N. \<forall>t\<in>{0..T}. norm (\<sigma> (k m) t - L t) < \<epsilon>/2"
        using conv[of "\<epsilon>/2"] by auto
      show "\<exists>N. \<forall>n\<ge>N. (\<sigma> \<circ> k) n \<in> mspace (path_metric T)
          \<and> mdist (path_metric T) ((\<sigma> \<circ> k) n) ?L < \<epsilon>"
      proof (intro exI[of _ N] allI impI conjI)
        fix n assume nN: "N \<le> n"
        show "(\<sigma> \<circ> k) n \<in> mspace (path_metric T)" using mem by simp
        have "mdist (path_metric T) (\<sigma> (k n)) ?L \<le> \<epsilon>/2"
          unfolding path_metric_def
        proof (subst cfunspace_mdist_le)
          show "\<sigma> (k n) \<in> mspace (cfunspace (top_of_set {0..T})
              (euclidean_metric :: 'b metric))"
            using mem[of "k n"] by (simp add: path_metric_def)
          show "?L \<in> mspace (cfunspace (top_of_set {0..T})
              (euclidean_metric :: 'b metric))"
            using Lmem by (simp add: path_metric_def)
          show "topspace (top_of_set ({0..T}::real set)) \<noteq> {}"
            using ne by simp
          show "\<forall>t\<in>topspace (top_of_set ({0..T}::real set)).
              mdist (euclidean_metric :: 'b metric) (\<sigma> (k n) t) (?L t) \<le> \<epsilon>/2"
          proof
            fix t assume "t \<in> topspace (top_of_set ({0..T}::real set))"
            hence t: "t \<in> {0..T}" by simp
            have "dist (\<sigma> (k n) t) (?L t) = norm (\<sigma> (k n) t - L t)"
              using t by (simp add: dist_norm)
            also have "\<dots> \<le> \<epsilon>/2"
              using N nN t by (intro less_imp_le) blast
            finally show "mdist (euclidean_metric :: 'b metric)
                (\<sigma> (k n) t) (?L t) \<le> \<epsilon>/2" by simp
          qed
        qed
        also have "\<epsilon>/2 < \<epsilon>" using e by simp
        finally show "mdist (path_metric T) ((\<sigma> \<circ> k) n) ?L < \<epsilon>" by simp
      qed
    qed
      show "\<exists>l r. l \<in> ?S \<and> strict_mono r
          \<and> limitin PM.mtopology (\<sigma> \<circ> r) l sequentially"
        using LS k lim by blast
    qed
  qed
qed

subsection \<open>Measurability of the path map\<close>

text \<open>
  The process-to-path map \<open>\<omega> \<mapsto> restrict (\<lambda>t. X t \<omega>) {0..T}\<close> is measurable
  into the Borel \<open>\<sigma>\<close>-algebra of the path space.  By separability the Borel
  algebra is generated by the countable family of balls around a countable
  dense set (\<open>generated_by_countable_balls\<close> and
  \<open>borel_of_second_countable'\<close>), and the sup-distance to a fixed continuous
  path is determined by its values at rational times, so ball preimages are
  countable intersections and unions of one-time-point constraints.
\<close>

lemma Icc_rats_dense:
  fixes T t :: real
  assumes T: "0 \<le> T" and t: "t \<in> {0..T}"
  shows "t \<in> closure ({0..T} \<inter> \<rat>)"
proof (cases "t < T")
  case True
  show ?thesis
  proof (rule closure_approachable[THEN iffD2], intro allI impI)
    fix e :: real assume e: "0 < e"
    have "t < min T (t + e)" using True e by simp
    then obtain q where q: "q \<in> \<rat>" "t < q" "q < min T (t + e)"
      using Rats_dense_in_real by blast
    have "q \<in> {0..T} \<inter> \<rat>" using q t by auto
    moreover have "dist q t < e" using q by (simp add: dist_real_def)
    ultimately show "\<exists>y\<in>{0..T} \<inter> \<rat>. dist y t < e" by blast
  qed
next
  case False
  hence tT: "t = T" using t by simp
  show ?thesis
  proof (cases "T = 0")
    case True
    have "t \<in> {0..T} \<inter> \<rat>" using tT True by simp
    thus ?thesis by (rule subsetD[OF closure_subset])
  next
    case F0: False
    hence T0: "0 < T" using T by simp
    show ?thesis
    proof (rule closure_approachable[THEN iffD2], intro allI impI)
      fix e :: real assume e: "0 < e"
      have "max 0 (T - e) < T" using T0 e by simp
      then obtain q where q: "q \<in> \<rat>" "max 0 (T - e) < q" "q < T"
        using Rats_dense_in_real by blast
      have "q \<in> {0..T} \<inter> \<rat>" using q by auto
      moreover have "dist q t < e" using q tT by (simp add: dist_real_def)
      ultimately show "\<exists>y\<in>{0..T} \<inter> \<rat>. dist y t < e" by blast
    qed
  qed
qed

lemma le_on_Icc_of_rats:
  fixes h :: "real \<Rightarrow> real"
  assumes T: "0 \<le> T" and cont: "continuous_on {0..T} h"
    and le: "\<And>t. t \<in> {0..T} \<inter> \<rat> \<Longrightarrow> h t \<le> q"
    and t: "t \<in> {0..T}"
  shows "h t \<le> q"
proof -
  have cl: "closure ({0..T} \<inter> \<rat>) \<subseteq> {0..T}"
    by (intro closure_minimal) auto
  have contc: "continuous_on (closure ({0..T} \<inter> \<rat>)) h"
    by (rule continuous_on_subset[OF cont cl])
  show ?thesis
    by (rule continuous_le_on_closure[OF contc Icc_rats_dense[OF T t] le])
qed

lemma mspace_path_metric_continuous:
  fixes g :: "real \<Rightarrow> 'b::polish_space"
  assumes "g \<in> mspace (path_metric T)"
  shows "continuous_on {0..T} g"
  using assms unfolding path_metric_def mspace_cfunspace by auto

lemma path_mdist_le_iff:
  fixes g h :: "real \<Rightarrow> 'b::polish_space"
  assumes T: "0 \<le> T"
    and g: "g \<in> mspace (path_metric T)" and h: "h \<in> mspace (path_metric T)"
  shows "mdist (path_metric T) g h \<le> q \<longleftrightarrow> (\<forall>t\<in>{0..T} \<inter> \<rat>. dist (g t) (h t) \<le> q)"
proof -
  have ne: "topspace (top_of_set ({0..T}::real set)) \<noteq> {}" using T by simp
  have gc: "g \<in> mspace (cfunspace (top_of_set {0..T})
      (euclidean_metric :: 'b metric))"
    using g by (simp add: path_metric_def)
  have hc: "h \<in> mspace (cfunspace (top_of_set {0..T})
      (euclidean_metric :: 'b metric))"
    using h by (simp add: path_metric_def)
  have iff1: "mdist (path_metric T) g h \<le> q
      \<longleftrightarrow> (\<forall>t\<in>{0..T}. dist (g t) (h t) \<le> q)"
    unfolding path_metric_def
    by (subst cfunspace_mdist_le[OF gc hc ne]) simp
  show ?thesis
  proof
    assume "mdist (path_metric T) g h \<le> q"
    thus "\<forall>t\<in>{0..T} \<inter> \<rat>. dist (g t) (h t) \<le> q"
      unfolding iff1 by blast
  next
    assume r: "\<forall>t\<in>{0..T} \<inter> \<rat>. dist (g t) (h t) \<le> q"
    have cd: "continuous_on {0..T} (\<lambda>t. dist (g t) (h t))"
      by (intro continuous_on_dist mspace_path_metric_continuous[OF g]
          mspace_path_metric_continuous[OF h])
    have "dist (g t) (h t) \<le> q" if "t \<in> {0..T}" for t
      by (rule le_on_Icc_of_rats[OF T cd _ that]) (use r in blast)
    thus "mdist (path_metric T) g h \<le> q" unfolding iff1 by blast
  qed
qed

theorem pathify_measurable:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> 'b::polish_space"
  assumes T: "0 \<le> T"
    and Xm: "\<And>t. t \<in> {0..T} \<Longrightarrow> X t \<in> borel_measurable M"
    and cont: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> continuous_on {0..T} (\<lambda>t. X t \<omega>)"
  shows "(\<lambda>\<omega>. restrict (\<lambda>t. X t \<omega>) {0..T})
      \<in> M \<rightarrow>\<^sub>M borel_of (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))"
proof -
  interpret PM: Metric_space
    "mspace (path_metric T :: (real \<Rightarrow> 'b) metric)"
    "mdist (path_metric T :: (real \<Rightarrow> 'b) metric)"
    by (rule Metric_space_mspace_mdist)
  have mt: "mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric) = PM.mtopology"
    by (simp add: mtopology_of_def)
  let ?pf = "\<lambda>\<omega>. restrict (\<lambda>t. X t \<omega>) {0..T}"
  have pfin: "?pf \<omega> \<in> mspace (path_metric T)" if "\<omega> \<in> space M" for \<omega>
    by (rule mspace_path_metricI[OF cont[OF that]])
  have sep: "separable_space PM.mtopology"
    using separable_path_metric[of T] by (simp add: mtopology_of_def)
  obtain D where Dc: "countable D" and Dd: "dense_in PM.mtopology D"
    using sep separable_space_def2 by blast
  have gen: "PM.mtopology = topology_generated_by
      {PM.mball y (1 / real n) | y n. y \<in> D}"
    by (rule PM.generated_by_countable_balls[OF Dc Dd])
  have sc: "second_countable PM.mtopology"
    by (rule PM.separable_space_imp_second_countable[OF sep])
  have sb: "subbase_in PM.mtopology {PM.mball y (1 / real n) | y n. y \<in> D}"
    unfolding subbase_in_def by (rule gen)
  have B: "borel_of PM.mtopology
      = sigma (mspace (path_metric T)) {PM.mball y (1 / real n) | y n. y \<in> D}"
    using borel_of_second_countable'[OF sc sb] by simp
  have tset: "{\<omega> \<in> space M. dist (y t) (X t \<omega>) \<le> q} \<in> sets M"
    if t: "t \<in> {0..T}" for y :: "real \<Rightarrow> 'b" and t q
  proof -
    note m[measurable] = Xm[OF t]
    show ?thesis by measurable
  qed
  have leq_set: "{\<omega> \<in> space M. mdist (path_metric T) y (?pf \<omega>) \<le> q} \<in> sets M"
    if y: "y \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric)" for y q
  proof -
    have iff: "mdist (path_metric T) y (?pf \<omega>) \<le> q
        \<longleftrightarrow> (\<forall>t\<in>{0..T} \<inter> \<rat>. dist (y t) (X t \<omega>) \<le> q)"
      if w: "\<omega> \<in> space M" for \<omega>
    proof -
      have "mdist (path_metric T) y (?pf \<omega>) \<le> q
          \<longleftrightarrow> (\<forall>t\<in>{0..T} \<inter> \<rat>. dist (y t) (?pf \<omega> t) \<le> q)"
        by (rule path_mdist_le_iff[OF T y pfin[OF w]])
      also have "\<dots> \<longleftrightarrow> (\<forall>t\<in>{0..T} \<inter> \<rat>. dist (y t) (X t \<omega>) \<le> q)"
        by (intro ball_cong refl) simp
      finally show ?thesis .
    qed
    have zero: "(0::real) \<in> {0..T} \<inter> \<rat>" using T by simp
    have eq: "{\<omega> \<in> space M. mdist (path_metric T) y (?pf \<omega>) \<le> q}
        = (\<Inter>t \<in> {0..T} \<inter> \<rat>. {\<omega> \<in> space M. dist (y t) (X t \<omega>) \<le> q})"
    proof (intro subset_antisym subsetI)
      fix \<omega> assume "\<omega> \<in> {\<omega> \<in> space M. mdist (path_metric T) y (?pf \<omega>) \<le> q}"
      hence w: "\<omega> \<in> space M" and le: "mdist (path_metric T) y (?pf \<omega>) \<le> q"
        by auto
      show "\<omega> \<in> (\<Inter>t \<in> {0..T} \<inter> \<rat>. {\<omega> \<in> space M. dist (y t) (X t \<omega>) \<le> q})"
        using iff[OF w] le w by auto
    next
      fix \<omega>
      assume A: "\<omega> \<in> (\<Inter>t \<in> {0..T} \<inter> \<rat>. {\<omega> \<in> space M. dist (y t) (X t \<omega>) \<le> q})"
      have w: "\<omega> \<in> space M" using A zero by auto
      have "\<forall>t\<in>{0..T} \<inter> \<rat>. dist (y t) (X t \<omega>) \<le> q" using A by auto
      thus "\<omega> \<in> {\<omega> \<in> space M. mdist (path_metric T) y (?pf \<omega>) \<le> q}"
        using iff[OF w] w by auto
    qed
    have cnt: "countable ({0..T} \<inter> \<rat>)"
      by (intro countable_Int2 countable_rat)
    show ?thesis unfolding eq
    proof (rule sets.countable_INT'[OF cnt])
      show "{0..T} \<inter> \<rat> \<noteq> {}" using zero by blast
      show "(\<lambda>t. {\<omega> \<in> space M. dist (y t) (X t \<omega>) \<le> q}) ` ({0..T} \<inter> \<rat>)
          \<subseteq> sets M"
        by (intro image_subsetI tset) simp
    qed
  qed
  have ball_pre: "?pf -` PM.mball y (1 / real n) \<inter> space M \<in> sets M"
    if yD: "y \<in> D" for y n
  proof -
    have yM: "y \<in> mspace (path_metric T)"
      using dense_in_subset[OF Dd] yD by auto
    have eq: "?pf -` PM.mball y (1 / real n) \<inter> space M
        = (\<Union>q \<in> \<rat> \<inter> {q'. q' < 1 / real n}.
            {\<omega> \<in> space M. mdist (path_metric T) y (?pf \<omega>) \<le> q})"
    proof (intro subset_antisym subsetI)
      fix \<omega> assume "\<omega> \<in> ?pf -` PM.mball y (1 / real n) \<inter> space M"
      hence w: "\<omega> \<in> space M"
        and lt: "mdist (path_metric T) y (?pf \<omega>) < 1 / real n" by auto
      obtain q where q: "q \<in> \<rat>" "mdist (path_metric T) y (?pf \<omega>) < q"
        "q < 1 / real n"
        using Rats_dense_in_real[OF lt] by blast
      show "\<omega> \<in> (\<Union>q \<in> \<rat> \<inter> {q'. q' < 1 / real n}.
          {\<omega> \<in> space M. mdist (path_metric T) y (?pf \<omega>) \<le> q})"
        using w q by (intro UN_I[of q]) auto
    next
      fix \<omega> assume "\<omega> \<in> (\<Union>q \<in> \<rat> \<inter> {q'. q' < 1 / real n}.
          {\<omega> \<in> space M. mdist (path_metric T) y (?pf \<omega>) \<le> q})"
      then obtain q where q: "q < 1 / real n" "\<omega> \<in> space M"
        "mdist (path_metric T) y (?pf \<omega>) \<le> q" by auto
      have "mdist (path_metric T) y (?pf \<omega>) < 1 / real n" using q by linarith
      thus "\<omega> \<in> ?pf -` PM.mball y (1 / real n) \<inter> space M"
        using q pfin[OF q(2)] yM by auto
    qed
    have cnt: "countable (\<rat> \<inter> {q'. q' < 1 / real n})"
      by (intro countable_Int1 countable_rat)
    show ?thesis unfolding eq
    proof (rule sets.countable_UN''[OF cnt])
      show "\<And>q'. q' \<in> \<rat> \<inter> {q'. q' < 1 / real n} \<Longrightarrow>
          {\<omega> \<in> space M. mdist (path_metric T) y (?pf \<omega>) \<le> q'} \<in> sets M"
        by (rule leq_set[OF yM])
    qed
  qed
  show ?thesis
    unfolding mt B
  proof (rule measurable_measure_of)
    show "{PM.mball y (1 / real n) | y n. y \<in> D}
        \<subseteq> Pow (mspace (path_metric T))" by auto
    show "?pf \<in> space M \<rightarrow> mspace (path_metric T)"
      by (intro funcsetI pfin)
    fix A assume "A \<in> {PM.mball y (1 / real n) | y n. y \<in> D}"
    then obtain y n where A: "A = PM.mball y (1 / real n)" and yD: "y \<in> D"
      by blast
    show "?pf -` A \<inter> space M \<in> sets M"
      unfolding A by (rule ball_pre[OF yD])
  qed
qed

subsection \<open>The law of the path\<close>

text \<open>
  The pushforward of a process with continuous paths along the path map: the
  object the sets \<open>\<P>\<^sub>x\<close> of Lemma 2.2 consist of.
\<close>

definition path_law ::
  "'a measure \<Rightarrow> (real \<Rightarrow> 'a \<Rightarrow> 'b::polish_space) \<Rightarrow> real \<Rightarrow> (real \<Rightarrow> 'b) measure"
  where
  "path_law M X T =
     distr M (borel_of (mtopology_of (path_metric T)))
       (\<lambda>\<omega>. restrict (\<lambda>t. X t \<omega>) {0..T})"

lemma sets_path_law[simp]:
  "sets (path_law M X T)
     = sets (borel_of (mtopology_of (path_metric T :: (real \<Rightarrow> 'b::polish_space) metric)))"
  unfolding path_law_def by simp

lemma prob_space_path_law:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> 'b::polish_space"
  assumes P: "prob_space M" and T: "0 \<le> T"
    and Xm: "\<And>t. t \<in> {0..T} \<Longrightarrow> X t \<in> borel_measurable M"
    and cont: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> continuous_on {0..T} (\<lambda>t. X t \<omega>)"
  shows "prob_space (path_law M X T)"
  unfolding path_law_def
  by (rule prob_space.prob_space_distr[OF P pathify_measurable[OF T Xm cont]])

subsection \<open>Consistency of the path laws across horizons\<close>

text \<open>
  The restriction map \<open>C({0..m'}) \<rightarrow> C({0..m})\<close> is 1-Lipschitz, hence
  continuous, hence Borel; and it intertwines the path laws:
  \<open>path_law M X m\<close> is the pushforward of \<open>path_law M X m'\<close>.  This is the
  projective-family consistency that \<open>HOL-Probability.Projective_Limit\<close>
  needs.
\<close>

lemma path_mdist_le_iff_all:
  fixes g h :: "real \<Rightarrow> 'b::polish_space"
  assumes T: "0 \<le> T"
    and g: "g \<in> mspace (path_metric T)" and h: "h \<in> mspace (path_metric T)"
  shows "mdist (path_metric T) g h \<le> q \<longleftrightarrow> (\<forall>t\<in>{0..T}. dist (g t) (h t) \<le> q)"
proof -
  have ne: "topspace (top_of_set ({0..T}::real set)) \<noteq> {}" using T by simp
  have gc: "g \<in> mspace (cfunspace (top_of_set {0..T})
      (euclidean_metric :: 'b metric))"
    using g by (simp add: path_metric_def)
  have hc: "h \<in> mspace (cfunspace (top_of_set {0..T})
      (euclidean_metric :: 'b metric))"
    using h by (simp add: path_metric_def)
  show ?thesis
    unfolding path_metric_def
    by (subst cfunspace_mdist_le[OF gc hc ne]) simp
qed

lemma restrict_mspace_path_metric:
  fixes f :: "real \<Rightarrow> 'b::polish_space"
  assumes m0: "0 \<le> m" and mm: "m \<le> m'"
    and f: "f \<in> mspace (path_metric m')"
  shows "restrict f {0..m} \<in> mspace (path_metric m)"
proof -
  have "continuous_on {0..m'} f" by (rule mspace_path_metric_continuous[OF f])
  hence "continuous_on {0..m} f"
    by (rule continuous_on_subset) (use mm in auto)
  thus ?thesis by (rule mspace_path_metricI)
qed

lemma Lipschitz_restrict_path_metric:
  fixes m m' :: real
  assumes m0: "0 \<le> m" and mm: "m \<le> m'"
  shows "Lipschitz_continuous_map
      (path_metric m' :: (real \<Rightarrow> 'b::polish_space) metric)
      (path_metric m) (\<lambda>f. restrict f {0..m})"
  unfolding Lipschitz_continuous_map_def
proof (intro conjI)
  show "(\<lambda>f. restrict f {0..m})
      \<in> mspace (path_metric m' :: (real \<Rightarrow> 'b) metric)
        \<rightarrow> mspace (path_metric m :: (real \<Rightarrow> 'b) metric)"
    by (intro funcsetI restrict_mspace_path_metric[OF m0 mm])
  have m'0: "0 \<le> m'" using m0 mm by linarith
  have key: "mdist (path_metric m) (restrict f {0..m}) (restrict g {0..m})
      \<le> 1 * mdist (path_metric m') f g"
    if f: "f \<in> mspace (path_metric m' :: (real \<Rightarrow> 'b) metric)"
      and g: "g \<in> mspace (path_metric m')" for f g
  proof -
    have rf: "restrict f {0..m} \<in> mspace (path_metric m :: (real \<Rightarrow> 'b) metric)"
      by (rule restrict_mspace_path_metric[OF m0 mm f])
    have rg: "restrict g {0..m} \<in> mspace (path_metric m :: (real \<Rightarrow> 'b) metric)"
      by (rule restrict_mspace_path_metric[OF m0 mm g])
    have le: "mdist (path_metric m') f g \<le> mdist (path_metric m') f g" by simp
    have pw: "\<forall>t\<in>{0..m'}. dist (f t) (g t) \<le> mdist (path_metric m') f g"
      using le path_mdist_le_iff_all[OF m'0 f g] by blast
    have pwr: "dist (restrict f {0..m} t) (restrict g {0..m} t)
        \<le> mdist (path_metric m') f g" if t: "t \<in> {0..m}" for t
    proof -
      have t': "t \<in> {0..m'}" using t mm by auto
      show ?thesis using bspec[OF pw t'] t by simp
    qed
    have "mdist (path_metric m) (restrict f {0..m}) (restrict g {0..m})
        \<le> mdist (path_metric m') f g"
      using path_mdist_le_iff_all[OF m0 rf rg] pwr by blast
    thus ?thesis by simp
  qed
  show "\<exists>B. \<forall>f\<in>mspace (path_metric m' :: (real \<Rightarrow> 'b) metric).
      \<forall>g\<in>mspace (path_metric m').
        mdist (path_metric m) (restrict f {0..m}) (restrict g {0..m})
          \<le> B * mdist (path_metric m') f g"
    by (intro exI[of _ 1] ballI key)
qed

lemma restrict_measurable_path_borel:
  fixes m m' :: real
  assumes m0: "0 \<le> m" and mm: "m \<le> m'"
  shows "(\<lambda>f. restrict f {0..m})
      \<in> borel_of (mtopology_of (path_metric m' :: (real \<Rightarrow> 'b::polish_space) metric))
        \<rightarrow>\<^sub>M borel_of (mtopology_of (path_metric m :: (real \<Rightarrow> 'b) metric))"
  by (intro continuous_map_measurable Lipschitz_continuous_imp_continuous_map
        Lipschitz_restrict_path_metric[OF m0 mm])

theorem path_law_restrict:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> 'b::polish_space"
  assumes m0: "0 \<le> m" and mm: "m \<le> m'"
    and Xm: "\<And>t. t \<in> {0..m'} \<Longrightarrow> X t \<in> borel_measurable M"
    and cont: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> continuous_on {0..m'} (\<lambda>t. X t \<omega>)"
  shows "distr (path_law M X m')
           (borel_of (mtopology_of (path_metric m :: (real \<Rightarrow> 'b) metric)))
           (\<lambda>f. restrict f {0..m})
       = path_law M X m"
proof -
  have m'0: "0 \<le> m'" using m0 mm by linarith
  have pfm: "(\<lambda>\<omega>. restrict (\<lambda>t. X t \<omega>) {0..m'})
      \<in> M \<rightarrow>\<^sub>M borel_of (mtopology_of (path_metric m' :: (real \<Rightarrow> 'b) metric))"
    by (rule pathify_measurable[OF m'0 Xm cont])
  have rm: "(\<lambda>f. restrict f {0..m})
      \<in> borel_of (mtopology_of (path_metric m' :: (real \<Rightarrow> 'b) metric))
        \<rightarrow>\<^sub>M borel_of (mtopology_of (path_metric m :: (real \<Rightarrow> 'b) metric))"
    by (rule restrict_measurable_path_borel[OF m0 mm])
  have comp: "((\<lambda>f. restrict f {0..m}) \<circ> (\<lambda>\<omega>. restrict (\<lambda>t. X t \<omega>) {0..m'}))
      = (\<lambda>\<omega>. restrict (\<lambda>t. X t \<omega>) {0..m})"
  proof (rule ext)
    fix \<omega>
    show "((\<lambda>f. restrict f {0..m}) \<circ> (\<lambda>\<omega>. restrict (\<lambda>t. X t \<omega>) {0..m'})) \<omega>
        = restrict (\<lambda>t. X t \<omega>) {0..m}"
      using mm by (auto simp: restrict_def fun_eq_iff o_def)
  qed
  have "distr (path_law M X m')
           (borel_of (mtopology_of (path_metric m :: (real \<Rightarrow> 'b) metric)))
           (\<lambda>f. restrict f {0..m})
      = distr M (borel_of (mtopology_of (path_metric m :: (real \<Rightarrow> 'b) metric)))
          ((\<lambda>f. restrict f {0..m}) \<circ> (\<lambda>\<omega>. restrict (\<lambda>t. X t \<omega>) {0..m'}))"
    unfolding path_law_def by (rule distr_distr[OF rm pfm])
  also have "\<dots> = path_law M X m"
    unfolding comp path_law_def by (rule refl)
  finally show ?thesis .
qed

subsection \<open>The continuous-mapping theorem for weak convergence\<close>

text \<open>
  Pushforward along a continuous map preserves weak convergence --- absent from
  the AFP's L\'evy-Prokhorov development, proved here from
  \<open>weak_conv_on_def\<close>: bounded continuous test functions compose with the map,
  and \<open>integral_distr\<close> transfers the integrals. Used with the restriction
  map to prove the horizon-consistency of weak limits of path laws.
\<close>

lemma weak_conv_on_pushforward:
  fixes r :: "'b \<Rightarrow> 'c" and Ni :: "'i \<Rightarrow> 'b measure"
  assumes r: "continuous_map X Y r"
    and wc: "weak_conv_on Ni N F X"
  shows "weak_conv_on (\<lambda>i. distr (Ni i) (borel_of Y) r)
      (distr N (borel_of Y) r) F Y"
proof -
  have rm: "r \<in> borel_of X \<rightarrow>\<^sub>M borel_of Y"
    by (rule continuous_map_measurable[OF r])
  have sN: "sets N = sets (borel_of X)"
    and fN: "finite_measure N"
    and ev: "\<forall>\<^sub>F i in F. sets (Ni i) = sets (borel_of X) \<and> finite_measure (Ni i)"
    using wc[unfolded weak_conv_on_def] by blast+
  have int: "((\<lambda>i. \<integral>x. f x \<partial>(Ni i)) \<longlongrightarrow> (\<integral>x. f x \<partial>N)) F"
    if "continuous_map X euclideanreal f" "\<exists>B. \<forall>x\<in>topspace X. \<bar>f x\<bar> \<le> B" for f
    using wc[unfolded weak_conv_on_def] that by blast
  have rmN: "r \<in> N \<rightarrow>\<^sub>M borel_of Y"
    using rm measurable_cong_sets[OF sN refl] by blast
  show ?thesis
    unfolding weak_conv_on_def
  proof (intro conjI allI impI)
    show "\<forall>\<^sub>F i in F. sets (distr (Ni i) (borel_of Y) r) = sets (borel_of Y)
        \<and> finite_measure (distr (Ni i) (borel_of Y) r)"
    proof (rule eventually_mono[OF ev])
      fix i assume A: "sets (Ni i) = sets (borel_of X) \<and> finite_measure (Ni i)"
      have rmi: "r \<in> Ni i \<rightarrow>\<^sub>M borel_of Y"
        using rm measurable_cong_sets[of "Ni i" "borel_of X" "borel_of Y" "borel_of Y"] A
        by blast
      show "sets (distr (Ni i) (borel_of Y) r) = sets (borel_of Y)
          \<and> finite_measure (distr (Ni i) (borel_of Y) r)"
        using A by (auto intro: finite_measure.finite_measure_distr[OF _ rmi])
    qed
    show "sets (distr N (borel_of Y) r) = sets (borel_of Y)" by simp
    show "finite_measure (distr N (borel_of Y) r)"
      by (rule finite_measure.finite_measure_distr[OF fN rmN])
    fix f :: "'c \<Rightarrow> real"
    assume f: "continuous_map Y euclideanreal f"
      and bd: "\<exists>B. \<forall>x\<in>topspace Y. \<bar>f x\<bar> \<le> B"
    have fm: "f \<in> borel_measurable (borel_of Y)"
      using continuous_map_measurable[OF f] by (simp add: borel_of_euclidean)
    have fr: "continuous_map X euclideanreal (f \<circ> r)"
      by (rule continuous_map_compose[OF r f])
    have bdr: "\<exists>B. \<forall>x\<in>topspace X. \<bar>(f \<circ> r) x\<bar> \<le> B"
    proof -
      from bd obtain B where B: "\<forall>x\<in>topspace Y. \<bar>f x\<bar> \<le> B" by blast
      have "r ` topspace X \<subseteq> topspace Y"
        by (rule continuous_map_image_subset_topspace[OF r])
      thus ?thesis using B by (intro exI[of _ B]) auto
    qed
    have lim: "((\<lambda>i. \<integral>x. (f \<circ> r) x \<partial>(Ni i)) \<longlongrightarrow> (\<integral>x. (f \<circ> r) x \<partial>N)) F"
      by (rule int[OF fr bdr])
    have eqN: "(\<integral>x. f x \<partial>(distr N (borel_of Y) r)) = (\<integral>x. (f \<circ> r) x \<partial>N)"
      by (subst integral_distr[OF rmN fm]) (simp add: o_def)
    have ev2: "\<forall>\<^sub>F i in F. (\<integral>x. f x \<partial>(distr (Ni i) (borel_of Y) r))
        = (\<integral>x. (f \<circ> r) x \<partial>(Ni i))"
    proof (rule eventually_mono[OF ev])
      fix i assume A: "sets (Ni i) = sets (borel_of X) \<and> finite_measure (Ni i)"
      have rmi: "r \<in> Ni i \<rightarrow>\<^sub>M borel_of Y"
        using rm measurable_cong_sets[of "Ni i" "borel_of X" "borel_of Y" "borel_of Y"] A
        by blast
      show "(\<integral>x. f x \<partial>(distr (Ni i) (borel_of Y) r)) = (\<integral>x. (f \<circ> r) x \<partial>(Ni i))"
        by (subst integral_distr[OF rmi fm]) (simp add: o_def)
    qed
    show "((\<lambda>i. \<integral>x. f x \<partial>(distr (Ni i) (borel_of Y) r))
        \<longlongrightarrow> (\<integral>x. f x \<partial>(distr N (borel_of Y) r))) F"
      unfolding eqN using tendsto_cong[OF ev2] lim by blast
  qed
qed

subsection \<open>Evaluation maps and moment bounds under weak limits\<close>

text \<open>
  Evaluation at a time point is 1-Lipschitz on the path space, hence
  continuous --- so coordinate moments are (unbounded, nonnegative, continuous)
  test functions. The Fatou-type lemma below transfers uniform moment bounds
  to weak limits by truncation: the truncated integrands are bounded
  continuous, so their integrals converge, and monotone convergence recovers
  the untruncated bound. This is how the Eq. (2.7) package passes to the
  limit laws of Lemma 2.2.
\<close>

lemma Lipschitz_path_eval:
  fixes t T :: real
  assumes t: "t \<in> {0..T}"
  shows "Lipschitz_continuous_map
      (path_metric T :: (real \<Rightarrow> 'b::polish_space) metric)
      euclidean_metric (\<lambda>f. f t)"
  unfolding Lipschitz_continuous_map_def
proof (intro conjI)
  show "(\<lambda>f. f t) \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric)
      \<rightarrow> mspace (euclidean_metric :: 'b metric)"
    by (intro funcsetI) simp
  have T0: "0 \<le> T" using t by auto
  have key: "mdist euclidean_metric (f t) (g t) \<le> 1 * mdist (path_metric T) f g"
    if f: "f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric)"
      and g: "g \<in> mspace (path_metric T)" for f g
  proof -
    have le: "mdist (path_metric T) f g \<le> mdist (path_metric T) f g" by simp
    have "dist (f t) (g t) \<le> mdist (path_metric T) f g"
      using le path_mdist_le_iff_all[OF T0 f g] t by blast
    thus ?thesis by simp
  qed
  show "\<exists>B. \<forall>f\<in>mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
      \<forall>g\<in>mspace (path_metric T).
        mdist euclidean_metric (f t) (g t) \<le> B * mdist (path_metric T) f g"
    by (intro exI[of _ 1] ballI key)
qed

lemma continuous_map_path_eval:
  fixes t T :: real
  assumes t: "t \<in> {0..T}"
  shows "continuous_map (mtopology_of (path_metric T :: (real \<Rightarrow> 'b::polish_space) metric))
      euclidean (\<lambda>f. f t)"
  using Lipschitz_continuous_imp_continuous_map[OF Lipschitz_path_eval[OF t]]
  by simp

text \<open>The exit time is upper semicontinuous because "has already entered
  \<open>A\<close> strictly before \<open>c\<close>" is an open condition on the path: witnessed at a
  single time \<open>r\<close>, with evaluation at a fixed time continuous
  (\<open>continuous_map_path_eval\<close>), so an open \<open>A\<close> pulls back to an open set of
  paths, and the union over admissible witness times \<open>r\<close> stays open.
  Stated here, purely about the path topology, because
  \<open>Exit_Time.etime_less_iff\<close> -- identifying this set with
  \<open>{f. etime T A (\<lambda>s w. w s) f < c}\<close> when \<open>\<not> T < c\<close> -- lives on a
  different import branch.\<close>

lemma open_hit_strictly_before:
  fixes T c :: real and A :: "'b::polish_space set"
  assumes A: "open A"
  shows "openin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))
      {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
         \<exists>r. 0 \<le> r \<and> r \<le> T \<and> r < c \<and> f r \<in> A}"
proof -
  have eq: "{f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
        \<exists>r. 0 \<le> r \<and> r \<le> T \<and> r < c \<and> f r \<in> A}
      = (\<Union>r \<in> {r. 0 \<le> r \<and> r \<le> T \<and> r < c}.
           {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric). f r \<in> A})"
    by blast
  have op: "openin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))
      {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric). f r \<in> A}"
    if r: "r \<in> {r. 0 \<le> r \<and> r \<le> T \<and> r < c}" for r
  proof -
    have rT: "r \<in> {0..T}" using r by simp
    have cm: "continuous_map
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)) euclidean (\<lambda>f. f r)"
      by (rule continuous_map_path_eval[OF rT])
    have "openin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))
        {f \<in> topspace (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)).
           f r \<in> A}"
      by (rule openin_continuous_map_preimage[OF cm]) (use A in simp)
    then show ?thesis by simp
  qed
  show ?thesis unfolding eq
    by (rule openin_Union) (use op in blast)
qed

text \<open>The brick the proof above used inline, now stated on its own:
  evaluation at a fixed admissible time is continuous, so an open target
  pulls back to an open set of paths.\<close>

lemma open_eval_preimage:
  fixes T r :: real and U :: "'b::polish_space set"
  assumes rT: "r \<in> {0..T}" and U: "open U"
  shows "openin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))
      {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric). f r \<in> U}"
proof -
  have cm: "continuous_map
      (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)) euclidean (\<lambda>f. f r)"
    by (rule continuous_map_path_eval[OF rT])
  have "openin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))
      {f \<in> topspace (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)).
         f r \<in> U}"
    by (rule openin_continuous_map_preimage[OF cm]) (use U in simp)
  thus ?thesis by simp
qed

lemma weak_conv_on_nn_integral_le:
  fixes f :: "'b \<Rightarrow> real" and Ni :: "nat \<Rightarrow> 'b measure"
  assumes wc: "weak_conv_on Ni N sequentially X"
    and f: "continuous_map X euclideanreal f"
    and nn: "\<And>y. y \<in> topspace X \<Longrightarrow> 0 \<le> f y"
    and B0: "0 \<le> B"
    and bnd: "\<And>i. (\<integral>\<^sup>+x. ennreal (f x) \<partial>(Ni i)) \<le> ennreal B"
  shows "(\<integral>\<^sup>+x. ennreal (f x) \<partial>N) \<le> ennreal B"
proof -
  have sN: "sets N = sets (borel_of X)"
    and fN: "finite_measure N"
    and ev: "\<forall>\<^sub>F i in sequentially. sets (Ni i) = sets (borel_of X)
        \<and> finite_measure (Ni i)"
    using wc[unfolded weak_conv_on_def] by blast+
  have int: "((\<lambda>i. \<integral>x. g x \<partial>(Ni i)) \<longlongrightarrow> (\<integral>x. g x \<partial>N)) sequentially"
    if "continuous_map X euclideanreal g" "\<exists>B. \<forall>x\<in>topspace X. \<bar>g x\<bar> \<le> B" for g
    using wc[unfolded weak_conv_on_def] that by blast
  have spN: "space N = topspace X"
    using sets_eq_imp_space_eq[OF sN] by (simp add: space_borel_of)
  have fmN: "f \<in> borel_measurable N"
    using continuous_map_measurable[OF f]
      measurable_cong_sets[OF sN[symmetric] refl]
    by (auto simp: borel_of_euclidean)
  define fK where "fK = (\<lambda>K::nat. \<lambda>x. min (f x) (real K))"
  have fKc: "continuous_map X euclideanreal (fK K)" for K
    unfolding fK_def by (intro continuous_map_real_min f) simp
  have fKb: "\<exists>B. \<forall>x\<in>topspace X. \<bar>fK K x\<bar> \<le> B" for K
  proof -
    have "\<bar>fK K x\<bar> \<le> real K" if "x \<in> topspace X" for x
      unfolding fK_def using nn[OF that] by simp
    thus ?thesis by blast
  qed
  have fK_le: "fK K x \<le> fK (Suc K) x" for K x
    unfolding fK_def by (simp add: min_def)
  have limK: "((\<lambda>i. \<integral>x. fK K x \<partial>(Ni i)) \<longlongrightarrow> (\<integral>x. fK K x \<partial>N)) sequentially" for K
    by (rule int[OF fKc fKb])
  have bndK: "(\<integral>x. fK K x \<partial>(Ni i)) \<le> B"
    if A: "sets (Ni i) = sets (borel_of X)" "finite_measure (Ni i)" for K i
  proof -
    interpret Nii: finite_measure "Ni i" by (rule A(2))
    have spi: "space (Ni i) = topspace X"
      using sets_eq_imp_space_eq[OF A(1)] by (simp add: space_borel_of)
    have fmi: "fK K \<in> borel_measurable (Ni i)"
      using continuous_map_measurable[OF fKc[of K]]
        measurable_cong_sets[OF A(1)[symmetric] refl]
      by (auto simp: borel_of_euclidean)
    have fKbd: "\<And>x. x \<in> space (Ni i) \<Longrightarrow> \<bar>fK K x\<bar> \<le> real K"
      unfolding fK_def spi using nn by auto
    have intg: "integrable (Ni i) (fK K)"
      by (rule Nii.integrable_const_bound[OF _ fmi]) (use fKbd in auto)
    have ae: "AE x in Ni i. 0 \<le> fK K x"
      by (rule AE_I2) (auto simp: fK_def spi intro: nn)
    have "ennreal (\<integral>x. fK K x \<partial>(Ni i)) = (\<integral>\<^sup>+x. ennreal (fK K x) \<partial>(Ni i))"
      by (rule nn_integral_eq_integral[symmetric, OF intg ae])
    also have "\<dots> \<le> (\<integral>\<^sup>+x. ennreal (f x) \<partial>(Ni i))"
      by (intro nn_integral_mono ennreal_leI) (simp add: fK_def)
    also have "\<dots> \<le> ennreal B" by (rule bnd)
    finally show ?thesis
      using B0 by simp
  qed
  have bndKN: "(\<integral>x. fK K x \<partial>N) \<le> B" for K
  proof -
    from ev obtain n0 where n0: "\<And>i. n0 \<le> i \<Longrightarrow>
        sets (Ni i) = sets (borel_of X) \<and> finite_measure (Ni i)"
      by (auto simp: eventually_sequentially)
    have evB: "\<forall>\<^sub>F i in sequentially. (\<integral>x. fK K x \<partial>(Ni i)) \<le> B"
      by (rule eventually_sequentiallyI[of n0]) (use n0 bndK in blast)
    show ?thesis
      by (rule tendsto_upperbound[OF limK evB trivial_limit_sequentially])
  qed
  interpret N: finite_measure N by (rule fN)
  have fKm: "fK K \<in> borel_measurable N" for K
    unfolding fK_def by (intro borel_measurable_min fmN) simp
  have intgN: "integrable N (fK K)" for K
  proof -
    have "\<And>x. x \<in> space N \<Longrightarrow> \<bar>fK K x\<bar> \<le> real K"
      unfolding fK_def spN using nn by auto
    thus ?thesis
      by (intro N.integrable_const_bound[OF _ fKm]) auto
  qed
  have aeN: "AE x in N. 0 \<le> fK K x" for K
    by (rule AE_I2) (auto simp: fK_def spN intro: nn)
  have eqK: "(\<integral>\<^sup>+x. ennreal (fK K x) \<partial>N) = ennreal (\<integral>x. fK K x \<partial>N)" for K
    by (rule nn_integral_eq_integral[OF intgN aeN])
  have inc: "incseq (\<lambda>K x. ennreal (fK K x))"
    by (intro incseq_SucI le_funI ennreal_leI fK_le)
  have ptSUP: "(\<Squnion>K. ennreal (fK K x)) = ennreal (f x)" for x
  proof -
    have rlim: "(\<lambda>K. min (f x) (real K)) \<longlonglongrightarrow> f x"
    proof -
      obtain K0 :: nat where K0: "f x \<le> real K0" using real_arch_simple by blast
      have "min (f x) (real K) = f x" if "K0 \<le> K" for K
        using K0 that by (auto simp: min_def)
      thus ?thesis
        by (intro tendsto_eventually) (auto simp: eventually_sequentially)
    qed
    have elim: "(\<lambda>K. ennreal (fK K x)) \<longlonglongrightarrow> ennreal (f x)"
      unfolding fK_def by (intro tendsto_ennrealI rlim)
    have inc1: "incseq (\<lambda>K. ennreal (fK K x))"
      by (intro incseq_SucI ennreal_leI fK_le)
    have "(\<lambda>K. ennreal (fK K x)) \<longlonglongrightarrow> (\<Squnion>K. ennreal (fK K x))"
      by (rule LIMSEQ_SUP[OF inc1])
    from tendsto_unique[OF trivial_limit_sequentially this elim]
    show ?thesis .
  qed
  have "(\<integral>\<^sup>+x. ennreal (f x) \<partial>N) = (\<integral>\<^sup>+x. (\<Squnion>K. ennreal (fK K x)) \<partial>N)"
    by (rule nn_integral_cong) (simp add: ptSUP)
  also have "\<dots> = (\<Squnion>K. \<integral>\<^sup>+x. ennreal (fK K x) \<partial>N)"
    by (rule nn_integral_monotone_convergence_SUP[OF inc])
       (use fKm in measurable)
  also have "\<dots> \<le> ennreal B"
    unfolding eqK by (intro SUP_least ennreal_leI bndKN)
  finally show ?thesis .
qed

text \<open>A weak limit of probability measures is a probability measure: test
  against the constant function 1.\<close>

lemma weak_conv_on_prob_space:
  fixes Ni :: "nat \<Rightarrow> 'b measure"
  assumes wc: "weak_conv_on Ni N sequentially X"
    and P: "\<And>i. prob_space (Ni i)"
  shows "prob_space N"
proof -
  have fN: "finite_measure N"
    using wc[unfolded weak_conv_on_def] by blast
  have int: "((\<lambda>i. \<integral>x. g x \<partial>(Ni i)) \<longlongrightarrow> (\<integral>x. g x \<partial>N)) sequentially"
    if "continuous_map X euclideanreal g" "\<exists>B. \<forall>x\<in>topspace X. \<bar>g x\<bar> \<le> B" for g
    using wc[unfolded weak_conv_on_def] that by blast
  have c1: "continuous_map X euclideanreal (\<lambda>_. 1::real)" by simp
  have b1: "\<exists>B. \<forall>x\<in>topspace X. \<bar>1::real\<bar> \<le> B" by (intro exI[of _ 1]) simp
  have lim1: "((\<lambda>i. \<integral>x. (1::real) \<partial>(Ni i)) \<longlongrightarrow> (\<integral>x. (1::real) \<partial>N)) sequentially"
    by (rule int[OF c1 b1])
  have ci: "(\<integral>x. (1::real) \<partial>(Ni i)) = 1" for i
    using prob_space.prob_space[OF P] by simp
  have "((\<lambda>i. 1::real) \<longlongrightarrow> (\<integral>x. (1::real) \<partial>N)) sequentially"
    using lim1 unfolding ci .
  hence e1: "(\<integral>x. (1::real) \<partial>N) = 1"
    using LIMSEQ_unique tendsto_const by blast
  have "measure N (space N) = 1"
    using e1 by simp
  thus ?thesis
    by (intro prob_spaceI)
       (simp add: finite_measure.emeasure_eq_measure[OF fN])
qed

subsection \<open>Portmanteau: a closed set of full measure survives the weak limit\<close>

text \<open>The closed-set half of the Portmanteau theorem, in the shape needed
  here.  The AFP proves the general statement as \<open>mweak_conv2\<close>, inside the
  \<open>mweak_conv_fin\<close> locale, whose parameters \<open>weak_conv_on_def\<close> supplies.

  Only the \<open>measure = 1\<close> instance is needed: for the usc argument for
  \<open>P \<mapsto> P-essinf \<tau>\<^sub>K\<close>, the superlevel set \<open>{\<tau>\<^sub>K \<ge> c}\<close> is closed since
  \<open>\<tau>\<^sub>K\<close> is upper semicontinuous, and \<open>c \<le> P-essinf \<tau>\<^sub>K\<close> is by definition
  \<open>P {\<tau>\<^sub>K \<ge> c} = 1\<close> -- \<open>Value_Function_Market.ess_inf_time_ge_iff_measure\<close> states
  this with \<open>measure\<close> rather than \<open>AE\<close> for precisely this junction.\<close>

lemma weak_conv_closed_full_measure:
  fixes m :: "'a metric" and Ni :: "nat \<Rightarrow> 'a measure"
  assumes wc: "weak_conv_on Ni N sequentially (mtopology_of m)"
    and clA: "closedin (mtopology_of m) A"
    and one: "\<And>i. measure (Ni i) A = 1"
    and pN: "prob_space N"
  shows "measure N A = 1"
proof -
  interpret PM: Metric_space "mspace m" "mdist m"
    by (rule Metric_space_mspace_mdist)
  interpret PN: prob_space N by (rule pN)
  have top: "PM.mtopology = mtopology_of m"
    by (simp add: mtopology_of_def)
  have sN: "sets N = sets (borel_of (mtopology_of m))"
    and ev: "\<forall>\<^sub>F i in sequentially.
        sets (Ni i) = sets (borel_of (mtopology_of m)) \<and> finite_measure (Ni i)"
    using wc[unfolded weak_conv_on_def] by blast+
  have int: "((\<lambda>i. \<integral>x. g x \<partial>(Ni i))
        \<longlongrightarrow> (\<integral>x. g x \<partial>N)) sequentially"
    if "continuous_map (mtopology_of m) euclideanreal g"
       "\<exists>B. \<forall>x \<in> topspace (mtopology_of m). \<bar>g x\<bar> \<le> B" for g
    using wc[unfolded weak_conv_on_def] that by blast
  interpret MW: mweak_conv_fin "mspace m" "mdist m" Ni N sequentially
  proof
    show "\<forall>\<^sub>F i in sequentially.
        sets (Ni i) = sets (borel_of PM.mtopology)"
      using ev unfolding top by (simp add: eventually_mono)
    show "sets N = sets (borel_of PM.mtopology)" using sN unfolding top by simp
    show "\<forall>\<^sub>F i in sequentially. finite_measure (Ni i)"
      using ev by (simp add: eventually_mono)
  qed
  have key: "Limsup sequentially (\<lambda>x. ereal (measure (Ni x) A))
      \<le> ereal (measure N A)"
  proof (rule MW.mweak_conv2)
    fix g :: "'a \<Rightarrow> real"
    assume u: "uniformly_continuous_map PM.Self euclidean_metric g"
      and b: "\<exists>B. \<forall>x \<in> mspace m. \<bar>g x\<bar> \<le> B"
    have cg: "continuous_map (mtopology_of m) euclideanreal g"
      using uniformly_continuous_imp_continuous_map[OF u]
      by (simp add: mtopology_of_def)
    show "((\<lambda>i. \<integral>x. g x \<partial>(Ni i))
        \<longlongrightarrow> (\<integral>x. g x \<partial>N)) sequentially"
      by (rule int[OF cg]) (use b in simp)
  next
    show "closedin PM.mtopology A" using clA unfolding top by simp
  qed
  have "Limsup sequentially (\<lambda>x. ereal (measure (Ni x) A)) = ereal 1"
    by (simp add: one Limsup_const)
  hence "(1::real) \<le> measure N A" using key by simp
  moreover have "measure N A \<le> 1" by (rule PN.prob_le_1)
  ultimately show ?thesis by linarith
qed

subsection \<open>Portmanteau, open sets: positive mass survives a weak perturbation\<close>

text \<open>The mirror of \<open>weak_conv_closed_full_measure\<close>, for open sets: here the
  limit measure is known to charge \<open>G\<close>, and the nearby measures inherit it
  -- exactly what Berge's \<open>box\<close> hypothesis wants, a neighbourhood of \<open>P\<close>
  on which the strict inequality persists, needing the open-set half of
  Portmanteau rather than the closed-set half.

  The AFP's \<open>mweak_conv3\<close> asks for the closed-set half plus convergence of
  the total mass. The first comes from \<open>mweak_conv2\<close> in the same locale;
  the second is trivial since every measure in sight is a probability
  measure. The \<open>sets\<close> equation is assumed at every index rather than
  eventually, since the total-mass step needs \<open>space (Ni i) = mspace m\<close>
  with no exceptions.\<close>

lemma weak_conv_open_positive_eventually:
  fixes m :: "'a metric" and Ni :: "nat \<Rightarrow> 'a measure"
  assumes wc: "weak_conv_on Ni N sequentially (mtopology_of m)"
    and G: "openin (mtopology_of m) G"
    and pos: "0 < measure N G"
    and si: "\<And>i. sets (Ni i) = sets (borel_of (mtopology_of m))"
    and pi: "\<And>i. prob_space (Ni i)" and pN: "prob_space N"
  shows "eventually (\<lambda>i. 0 < measure (Ni i) G) sequentially"
proof -
  interpret PM: Metric_space "mspace m" "mdist m"
    by (rule Metric_space_mspace_mdist)
  interpret PN: prob_space N by (rule pN)
  have top: "PM.mtopology = mtopology_of m"
    by (simp add: mtopology_of_def)
  have sN: "sets N = sets (borel_of (mtopology_of m))"
    using wc[unfolded weak_conv_on_def] by blast
  have int: "((\<lambda>i. \<integral>x. g x \<partial>(Ni i))
        \<longlongrightarrow> (\<integral>x. g x \<partial>N)) sequentially"
    if "continuous_map (mtopology_of m) euclideanreal g"
       "\<exists>B. \<forall>x \<in> topspace (mtopology_of m). \<bar>g x\<bar> \<le> B" for g
    using wc[unfolded weak_conv_on_def] that by blast
  interpret MW: mweak_conv_fin "mspace m" "mdist m" Ni N sequentially
  proof
    show "\<forall>\<^sub>F i in sequentially.
        sets (Ni i) = sets (borel_of PM.mtopology)"
      using si unfolding top by simp
    show "sets N = sets (borel_of PM.mtopology)" using sN unfolding top by simp
    show "\<forall>\<^sub>F i in sequentially. finite_measure (Ni i)"
      using pi by (simp add: prob_space.finite_measure)
  qed
  have closed_half: "Limsup sequentially (\<lambda>n. ereal (measure (Ni n) A))
      \<le> ereal (measure N A)" if clA: "closedin PM.mtopology A" for A
  proof (rule MW.mweak_conv2)
    fix g :: "'a \<Rightarrow> real"
    assume u: "uniformly_continuous_map PM.Self euclidean_metric g"
      and b: "\<exists>B. \<forall>x \<in> mspace m. \<bar>g x\<bar> \<le> B"
    have cg: "continuous_map (mtopology_of m) euclideanreal g"
      using uniformly_continuous_imp_continuous_map[OF u]
      by (simp add: mtopology_of_def)
    show "((\<lambda>i. \<integral>x. g x \<partial>(Ni i))
        \<longlongrightarrow> (\<integral>x. g x \<partial>N)) sequentially"
      by (rule int[OF cg]) (use b in simp)
  next
    show "closedin PM.mtopology A" by (rule clA)
  qed
  have spi: "space (Ni i) = mspace m" for i
    using sets_eq_imp_space_eq[OF si[of i]] by (simp add: space_borel_of)
  have massi: "measure (Ni i) (mspace m) = 1" for i
    using prob_space.prob_space[OF pi[of i]] unfolding spi[of i] .
  have massN: "measure N (mspace m) = 1"
    using PN.prob_space
      sets_eq_imp_space_eq[OF sN] by (simp add: space_borel_of)
  have mass: "((\<lambda>n. measure (Ni n) (mspace m))
      \<longlongrightarrow> measure N (mspace m)) sequentially"
    unfolding massN by (simp add: massi)
  have lim_ge: "ereal (measure N G)
      \<le> Liminf sequentially (\<lambda>n. ereal (measure (Ni n) G))"
    using MW.mweak_conv3[OF closed_half mass] G unfolding top by simp
  have posE: "ereal 0 < ereal (measure N G)" using pos by simp
  have "ereal 0 < Liminf sequentially (\<lambda>n. ereal (measure (Ni n) G))"
    using posE lim_ge by (rule order_less_le_trans)
  from less_LiminfD[OF this] show ?thesis by simp
qed

text \<open>The hypothesis that makes \<open>Equicontinuity.box_of_sequential\<close>
  usable on the space of laws: the weak topology over the path space is
  metrizable, by the L\'evy--Prokhorov theorem.  Both inputs are already
  here: the path space is a metric space by construction and separable by
  \<open>path_metric_polish\<close>.\<close>

lemma metrizable_weak_conv_path_topology:
  "metrizable_space (weak_conv_topology
      (mtopology_of (path_metric T :: (real \<Rightarrow> 'b::polish_space) metric)))"
proof (rule metrizable_weak_conv_topology)
  show "metrizable_space
      (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))"
    unfolding mtopology_of_def
    by (rule Metric_space.metrizable_space_mtopology[OF Metric_space_mspace_mdist])
  show "separable_space
      (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))"
    unfolding mtopology_of_def by (rule path_metric_polish(2))
qed


(*<*)
end
(*>*)
