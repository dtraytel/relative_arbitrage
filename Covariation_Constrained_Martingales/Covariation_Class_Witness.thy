section \<open>Concrete pair processes, and nonemptiness of the class\<close>

(*<*)
theory Covariation_Class_Witness
  imports
    Covariation_Class_Shift "Wiener_Measure.Continuous_Brownian_Motion"
begin

(*>*)

subsection \<open>Laws of concrete pair processes\<close>

text \<open>The compensated outer product of the continuous Brownian state is a
  matrix martingale, assembled entrywise by \<open>martingale_matI\<close> from the
  compensated coordinate products \<open>martingale_bm_prod\<close>, transferred to the
  continuous modification by \<open>martingale_cbmX_fun\<close>.\<close>

theorem martingale_cbm_outerp:
  fixes x0 :: "real^'n::finite"
  shows "martingale (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (natural_filtration bm_paths 0 (cbmX x0)) 0
      (\<lambda>t \<omega>. outerp (cbmX x0 t \<omega>) - t *\<^sub>R mat 1)"
proof (rule martingale_matI)
  fix i j :: 'n
  show "martingale bm_paths (natural_filtration bm_paths 0 (cbmX x0)) 0
      (\<lambda>t \<omega>. (outerp (cbmX x0 t \<omega>) - t *\<^sub>R mat 1) $ i $ j)"
    using martingale_cbmX_fun[where f = "\<lambda>t y. y $ i * y $ j - t * mat 1 $ i $ j",
        OF martingale_bm_prod]
    by (simp add: outerp_def)
qed

subsection \<open>The class is nonempty\<close>

text \<open>The witness: Brownian motion started at \<open>0\<close> and pushed through a
  constant matrix \<open>\<sigma>\<close>, paired with the deterministic covariation
  \<open>Y\<^sub>t = t \<sqdot> \<sigma> \<sigma>\<^sup>T\<close>, capped at the horizon.  It is a member of
  \<open>covariation_class S\<close> for every closed \<open>S\<close> that contains \<open>\<sigma> \<sigma>\<^sup>T\<close>; the
  Euler scheme of the supersolution half is built from it, and plain
  Brownian motion is the case \<open>\<sigma> = I\<close>.\<close>

definition sbmpair ::
  "real^'n::finite^'n \<Rightarrow> real \<Rightarrow> ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> 'n pairpath"
  where "sbmpair S T \<omega> = restrict
    (\<lambda>t. (S *v cbmX 0 t \<omega>, t *\<^sub>R (S ** transpose S))) {0..T}"

lemma sbmpair_apply:
  "t \<in> {0..T} \<Longrightarrow> sbmpair S T \<omega> t
     = (S *v cbmX 0 t \<omega>, t *\<^sub>R (S ** transpose S))"
  by (simp add: sbmpair_def)

lemma continuous_on_sbmpair_path:
  fixes \<omega> :: "'n::finite \<Rightarrow> real \<Rightarrow> real" and S :: "real^'n^'n"
  shows "continuous_on {0..T}
      (\<lambda>t. (S *v cbmX (0 :: real^'n) t \<omega>, t *\<^sub>R (S ** transpose S)))"
proof (intro continuous_on_Pair)
  have c1: "continuous_on {0..T} (\<lambda>t. cbmX (0 :: real^'n) t \<omega>)"
    by (rule continuous_on_subset[OF cbmX_cont]) auto
  show "continuous_on {0..T} (\<lambda>t. S *v cbmX (0 :: real^'n) t \<omega>)"
    by (rule continuous_on_compose2[OF linear_continuous_on[OF matrix_vector_mul_bounded_linear]
          c1]) auto
  show "continuous_on {0..T} (\<lambda>t. t *\<^sub>R (S ** transpose S))"
    by (rule linear_continuous_on[OF bounded_linear_scaleR_left])
qed

lemma sbmpair_measurable:
  assumes T: "0 \<le> T"
  shows "(sbmpair S T :: ('n::finite \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> 'n pairpath)
      \<in> bm_paths \<rightarrow>\<^sub>M (path_borel T :: ('n pairpath) measure)"
proof -
  have "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. restrict
          (\<lambda>t. (S *v cbmX (0 :: real^'n) t \<omega>,
                t *\<^sub>R (S ** transpose S))) {0..T})
      \<in> bm_paths \<rightarrow>\<^sub>M (path_borel T :: ('n pairpath) measure)"
  proof (rule pathify_measurable[OF T])
    fix t :: real assume "t \<in> {0..T}"
    have c: "(\<lambda>v :: real^'n. (S *v v, t *\<^sub>R (S ** transpose S)))
        \<in> borel_measurable borel"
      by (intro borel_measurable_continuous_onI continuous_on_Pair
          continuous_on_const
          continuous_on_compose2[OF linear_continuous_on[OF matrix_vector_mul_bounded_linear]
            continuous_on_id])
        auto
    show "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real.
          (S *v cbmX (0 :: real^'n) t \<omega>, t *\<^sub>R (S ** transpose S)))
        \<in> borel_measurable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)"
      by (rule measurable_compose[OF measurable_cbmX c])
  next
    fix \<omega> :: "'n \<Rightarrow> real \<Rightarrow> real"
    show "continuous_on {0..T}
        (\<lambda>t. (S *v cbmX (0 :: real^'n) t \<omega>, t *\<^sub>R (S ** transpose S)))"
      by (rule continuous_on_sbmpair_path)
  qed
  moreover have "(sbmpair S T :: ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> 'n pairpath)
      = (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. restrict
          (\<lambda>t. (S *v cbmX (0 :: real^'n) t \<omega>,
                t *\<^sub>R (S ** transpose S))) {0..T})"
    by (rule ext) (simp add: sbmpair_def)
  ultimately show ?thesis by simp
qed

lemma prob_space_sbmpair_law:
  assumes T: "0 \<le> T"
  shows "prob_space (process_law T (sbmpair S T)
      (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure))"
  unfolding process_law_def
  by (rule BMP.prob_space_distr[OF sbmpair_measurable[OF T]])

lemma sbmpair_law_start:
  assumes T: "0 \<le> T"
  shows "AE \<omega> in process_law T (sbmpair S T)
      (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure).
        fst (\<omega> 0) = (0 :: real^'n) \<and> snd (\<omega> 0) = 0"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  have phim: "sbmpair S T \<in> ?M \<rightarrow>\<^sub>M ?B" by (rule sbmpair_measurable[OF T])
  have mset: "{\<omega> \<in> space ?B. fst (\<omega> 0) = (0 :: real^'n) \<and> snd (\<omega> 0) = 0}
      \<in> sets ?B"
    by (rule start_set_sets[OF refl])
  have iff: "(AE \<omega> in process_law T (sbmpair S T) ?M.
        fst (\<omega> 0) = (0 :: real^'n) \<and> snd (\<omega> 0) = 0)
      = (AE \<omega> in ?M. fst (sbmpair S T \<omega> 0) = (0 :: real^'n)
          \<and> snd (sbmpair S T \<omega> 0) = 0)"
    unfolding process_law_def by (rule AE_distr_iff[OF phim mset])
  have z: "(0::real) \<in> {0..T}" using T by simp
  have "AE \<omega> in ?M. cbmX (0 :: real^'n) 0 \<omega> = bmX 0 0 \<omega>"
    by (intro cbmX_ae_eq) simp
  moreover have "AE \<omega> in ?M. bmX (0 :: real^'n) 0 \<omega> = 0"
    by (rule bmX_start)
  ultimately have "AE \<omega> in ?M. fst (sbmpair S T \<omega> 0) = (0 :: real^'n)
      \<and> snd (sbmpair S T \<omega> 0) = 0"
    by eventually_elim (simp add: sbmpair_apply[OF z])
  then show ?thesis unfolding iff .
qed

lemma sbmpair_law_diffquot:
  assumes T: "0 \<le> T" and S: "closed S"
    and SST: "\<sigma> ** transpose \<sigma> \<in> S"
  shows "AE \<omega> in process_law T (sbmpair \<sigma> T)
      (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure).
        \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
          (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> S"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?Q = "process_law T (sbmpair \<sigma> T) ?M"
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  have phim: "sbmpair \<sigma> T \<in> ?M \<rightarrow>\<^sub>M ?B" by (rule sbmpair_measurable[OF T])
  have spQ: "space ?Q = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_process_law)
  have one: "AE \<omega> in ?Q.
      (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> S"
    if pq: "p \<in> {0..T}" "q \<in> {0..T}" "p < q" for p q :: real
  proof -
    have mm: "{\<omega> \<in> space ?B.
        (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> S}
        \<in> sets ?B"
      using borel_of_closed[OF closedin_diffquot_constraint[OF pq(1) pq(2) S]]
      by (simp add: space_borel_of)
    have iff: "(AE \<omega> in ?Q.
          (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> S)
        = (AE \<omega> in ?M. (1 / (q - p))
            *\<^sub>R (snd (sbmpair \<sigma> T \<omega> q) - snd (sbmpair \<sigma> T \<omega> p))
            \<in> S)"
      unfolding process_law_def by (rule AE_distr_iff[OF phim mm])
    have "AE \<omega> in ?M. (1 / (q - p))
        *\<^sub>R (snd (sbmpair \<sigma> T \<omega> q) - snd (sbmpair \<sigma> T \<omega> p))
        \<in> S"
    proof (intro AE_I2)
      fix \<omega> :: "'n \<Rightarrow> real \<Rightarrow> real"
      have "(1 / (q - p))
          *\<^sub>R (snd (sbmpair \<sigma> T \<omega> q) - snd (sbmpair \<sigma> T \<omega> p))
          = (1 / (q - p)) *\<^sub>R ((q - p) *\<^sub>R (\<sigma> ** transpose \<sigma>))"
        using pq by (simp add: sbmpair_apply scaleR_left_diff_distrib)
      also have "\<dots> = \<sigma> ** transpose \<sigma>"
        using pq(3) by simp
      finally show "(1 / (q - p))
          *\<^sub>R (snd (sbmpair \<sigma> T \<omega> q) - snd (sbmpair \<sigma> T \<omega> p))
          \<in> S"
        using SST by simp
    qed
    then show ?thesis unfolding iff .
  qed
  have rat: "AE \<omega> in ?Q. \<forall>p\<in>(\<rat>::real set). \<forall>q\<in>(\<rat>::real set).
      0 \<le> p \<longrightarrow> p < q \<longrightarrow> q \<le> T \<longrightarrow>
      (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> S"
  proof (rule AE_ball_countable'[OF _ countable_rat])
    fix p :: real assume "p \<in> \<rat>"
    show "AE \<omega> in ?Q. \<forall>q\<in>(\<rat>::real set). 0 \<le> p \<longrightarrow> p < q \<longrightarrow> q \<le> T \<longrightarrow>
        (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> S"
    proof (rule AE_ball_countable'[OF _ countable_rat])
      fix q :: real assume "q \<in> \<rat>"
      show "AE \<omega> in ?Q. 0 \<le> p \<longrightarrow> p < q \<longrightarrow> q \<le> T \<longrightarrow>
          (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> S"
      proof (cases "0 \<le> p \<and> p < q \<and> q \<le> T")
        case True
        then have "p \<in> {0..T}" "q \<in> {0..T}" "p < q" by auto
        from one[OF this] show ?thesis by (rule eventually_mono) simp
      next
        case False
        then show ?thesis by auto
      qed
    qed
  qed
  from rat AE_space show ?thesis
  proof eventually_elim
    case (elim \<omega>)
    then have R: "\<And>p q :: real. p \<in> \<rat> \<Longrightarrow> q \<in> \<rat> \<Longrightarrow> 0 \<le> p \<Longrightarrow> p < q
        \<Longrightarrow> q \<le> T
        \<Longrightarrow> (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> S"
      and W: "\<omega> \<in> space ?Q" by blast+
    have mw: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using W spQ by simp
    have cont: "continuous_on {0..T} (\<lambda>u. snd (\<omega> u))"
      using mspace_path_metricD[OF mw] by (intro continuous_intros)
    show ?case
    proof (intro allI impI)
      fix u v :: real
      assume uv: "0 \<le> u" "u < v" "v \<le> T"
      show "(1 / (v - u)) *\<^sub>R (snd (\<omega> v) - snd (\<omega> u)) \<in> S"
        by (rule diffquot_all_of_rational
            [OF S cont _ uv(1) uv(2) uv(3)]) (rule R)
    qed
  qed
qed

lemma sbmpair_adapted:
  fixes r u :: real
  assumes r: "0 \<le> r" and ru: "r \<le> u"
  shows "(\<lambda>\<omega> :: 'n::finite \<Rightarrow> real \<Rightarrow> real. sbmpair S T \<omega> r)
      \<in> borel_measurable
      (natural_filtration (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0
        (cbmX (0 :: real^'n)) u)"
proof (cases "r \<in> {0..T}")
  case True
  let ?F = "natural_filtration (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0
      (cbmX (0 :: real^'n))"
  interpret MC: martingale "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure" ?F 0
      "cbmX (0 :: real^'n)"
    by (rule martingale_cbmX)
  have cr: "cbmX (0 :: real^'n) r \<in> borel_measurable (?F r)"
    by (rule MC.adapted[OF r])
  have cu: "cbmX (0 :: real^'n) r \<in> borel_measurable (?F u)"
    using MC.borel_measurable_mono[OF r ru] cr by blast
  have c: "(\<lambda>v :: real^'n. (S *v v, r *\<^sub>R (S ** transpose S)))
      \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_on_Pair
        continuous_on_const
        continuous_on_compose2[OF linear_continuous_on[OF matrix_vector_mul_bounded_linear]
          continuous_on_id])
      auto
  have "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real.
        (S *v cbmX (0 :: real^'n) r \<omega>, r *\<^sub>R (S ** transpose S)))
      \<in> borel_measurable (?F u)"
    by (rule measurable_compose[OF cu c])
  then show ?thesis using True by (simp add: sbmpair_apply)
next
  case False
  then have "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. sbmpair S T \<omega> r) = (\<lambda>\<omega>. undefined)"
    by (auto simp: sbmpair_def)
  then show ?thesis by simp
qed

theorem sbmpair_law_X_martingale:
  assumes T: "0 \<le> T"
  shows "martingale (process_law T (sbmpair S T)
        (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure))
      (natural_filtration (process_law T (sbmpair S T) bm_paths) 0
        (\<lambda>v \<omega>. \<omega> v)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u T)) :: real^'n)"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?Q = "process_law T (sbmpair S T) ?M"
  let ?F = "natural_filtration ?M 0 (cbmX (0 :: real^'n))"
  let ?G = "natural_filtration ?Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  have Zm: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min u T))) \<in> borel_measurable (?G u)"
    if u: "0 \<le> u" for u
  proof -
    have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u T)) \<in> ?G u \<rightarrow>\<^sub>M borel"
      by (rule natural_filtration_eval) (use u T in auto)
    show ?thesis by (rule measurable_compose[OF ev pair_fst_borel])
  qed
  have mg: "martingale ?M ?F 0 (\<lambda>u \<omega>. fst (sbmpair S T \<omega> (min u T)))"
  proof (rule martingale_cong_ge[OF martingale_bounded_linear_image
        [OF matrix_vector_mul_bounded_linear martingale_stopped_const[OF T martingale_cbmX]]])
    fix u :: real assume u: "0 \<le> u"
    have mI: "min u T \<in> {0..T}" using u T by simp
    show "(\<lambda>\<omega>. S *v cbmX (0 :: real^'n) (min u T) \<omega>)
        = (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. fst (sbmpair S T \<omega> (min u T)))"
      by (rule ext) (simp add: sbmpair_apply[OF mI])
  qed
  show ?thesis
    by (rule martingale_process_law[OF prob_space_bm_paths
        sbmpair_measurable[OF T] sbmpair_adapted Zm mg])
qed

theorem sbmpair_law_comp_martingale:
  assumes T: "0 \<le> T"
  shows "martingale (process_law T (sbmpair S T)
        (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure))
      (natural_filtration (process_law T (sbmpair S T) bm_paths) 0
        (\<lambda>v \<omega>. \<omega> v)) 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (min u T)) :: real^'n) - snd (\<omega> (min u T)))"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?Q = "process_law T (sbmpair S T) ?M"
  let ?F = "natural_filtration ?M 0 (cbmX (0 :: real^'n))"
  let ?G = "natural_filtration ?Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  have Zm: "(\<lambda>\<omega> :: 'n pairpath.
        outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T)))
      \<in> borel_measurable (?G u)" if u: "0 \<le> u" for u
  proof -
    have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u T)) \<in> ?G u \<rightarrow>\<^sub>M borel"
      by (rule natural_filtration_eval) (use u T in auto)
    show ?thesis by (rule measurable_compose[OF ev compensated_map_borel])
  qed
  have mg: "martingale ?M ?F 0
      (\<lambda>u \<omega>. outerp (fst (sbmpair S T \<omega> (min u T)))
        - snd (sbmpair S T \<omega> (min u T)))"
  proof (rule martingale_cong_ge[OF martingale_bounded_linear_image
        [OF matmul_sandwich_blin
          martingale_stopped_const[OF T martingale_cbm_outerp]]])
    fix u :: real assume u: "0 \<le> u"
    have mI: "min u T \<in> {0..T}" using u T by simp
    show "(\<lambda>\<omega>. S ** (outerp (cbmX (0 :: real^'n) (min u T) \<omega>)
                - (min u T) *\<^sub>R mat 1) ** transpose S)
        = (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real.
          outerp (fst (sbmpair S T \<omega> (min u T)))
            - snd (sbmpair S T \<omega> (min u T)))"
    proof (rule ext)
      fix \<omega> :: "'n \<Rightarrow> real \<Rightarrow> real"
      have "S ** (outerp (cbmX (0 :: real^'n) (min u T) \<omega>)
            - (min u T) *\<^sub>R mat 1) ** transpose S
          = S ** outerp (cbmX (0 :: real^'n) (min u T) \<omega>) ** transpose S
            - S ** ((min u T) *\<^sub>R mat 1) ** transpose S"
        by (simp add: matrix_matrix_mult_def vec_eq_iff
            sum_subtractf algebra_simps)
      also have "\<dots> = outerp (S *v cbmX (0 :: real^'n) (min u T) \<omega>)
          - (min u T) *\<^sub>R (S ** transpose S)"
        by (simp add: outerp_matvec_image sandwich_mat1)
      finally show "S ** (outerp (cbmX (0 :: real^'n) (min u T) \<omega>)
                - (min u T) *\<^sub>R mat 1) ** transpose S
          = outerp (fst (sbmpair S T \<omega> (min u T)))
            - snd (sbmpair S T \<omega> (min u T))"
        by (simp add: sbmpair_apply[OF mI])
    qed
  qed
  show ?thesis
    by (rule martingale_process_law[OF prob_space_bm_paths
        sbmpair_measurable[OF T] sbmpair_adapted Zm mg])
qed

text \<open>In the membership of the witness the martingale clauses are
  bounded-linear images of the Brownian ones
  (@{thm [source] martingale_bounded_linear_image}) and the covariation
  clause is deterministic, so the only hypothesis on \<open>S\<close> is that it is
  closed and contains \<open>\<sigma> \<sigma>\<^sup>T\<close>; an arbitrary start comes free from
  @{thm [source] covariation_class_pshift}.\<close>

theorem sbmpair_law_in_covariation_class:
  assumes T: "0 \<le> T" and S: "closed S"
    and SST: "\<sigma> ** transpose \<sigma> \<in> S"
  shows "process_law T (sbmpair \<sigma> T)
      (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure)
    \<in> covariation_class S T (0 :: real^'n)"
  by (rule covariation_classI[OF prob_space_sbmpair_law[OF T] _ sbmpair_law_start[OF T]
        sbmpair_law_diffquot[OF T S SST] sbmpair_law_X_martingale[OF T]
        sbmpair_law_comp_martingale[OF T]]) simp

corollary sbmpair_pshift_law_in_covariation_class:
  assumes T: "0 \<le> T" and S: "closed S"
    and SST: "\<sigma> ** transpose \<sigma> \<in> S"
  shows "pshift_law T v (process_law T (sbmpair \<sigma> T)
      (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure))
    \<in> covariation_class S T (v :: real^'n)"
  using covariation_class_pshift[OF T sbmpair_law_in_covariation_class[OF T S SST], of v]
  by simp

subsubsection \<open>The witness is a member, so the class is nonempty\<close>

definition bmpair :: "real \<Rightarrow> ('n::finite \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> 'n pairpath"
  where "bmpair T \<omega> = restrict (\<lambda>t. (cbmX 0 t \<omega>, t *\<^sub>R mat 1)) {0..T}"

lemma bmpair_eq_sbmpair: "bmpair T = sbmpair (mat 1) T"
  by (rule ext) (simp add: bmpair_def sbmpair_def)

theorem bmpair_law_in_covariation_class:
  assumes T: "0 \<le> T" and S: "closed S" and I: "mat 1 \<in> S"
  shows "process_law T (bmpair T)
      (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure)
    \<in> covariation_class S T (0 :: real^'n)"
  unfolding bmpair_eq_sbmpair
  by (rule sbmpair_law_in_covariation_class[OF T S]) (use I in simp)

text \<open>So the class is nonempty as soon as \<open>S\<close> contains one covariation
  rate \<open>\<sigma> \<sigma>\<^sup>T\<close>: Brownian motion pushed through \<open>\<sigma>\<close> is a member.\<close>

corollary covariation_class_nonempty:
  fixes \<sigma> :: "real^'n::finite^'n"
  assumes T: "0 \<le> T" and S: "closed S"
    and SST: "\<sigma> ** transpose \<sigma> \<in> S"
  shows "covariation_class S T (x :: real^'n) \<noteq> {}"
  using sbmpair_pshift_law_in_covariation_class[OF T S SST, of x] by blast

subsection \<open>Bounds on the value\<close>

text \<open>Lower bounds for the value: every member of the class bounds it
  from below by its essential infimum, so an almost-sure lower bound on one
  member's exit time is a lower bound for the value.\<close>

lemma covariation_val_ge_ess_inf:
  assumes "Q \<in> covariation_class S T x"
  shows "ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))) \<le> covariation_val S T K x"
  unfolding covariation_val_def using assms by (intro Sup_upper imageI)

lemma covariation_val_ge_of_AE:
  assumes Q: "Q \<in> covariation_class S T x"
    and ae: "AE \<omega> in Q. c \<le> pexit T K (\<lambda>t. fst (\<omega> t))"
  shows "ennreal c \<le> covariation_val S T K x"
proof -
  have "ennreal c \<le> ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))"
    unfolding ess_inf_time_def
    by (intro Sup_upper CollectI) (use ae in \<open>auto elim: eventually_mono intro: ennreal_leI\<close>)
  then show ?thesis using covariation_val_ge_ess_inf[OF Q] by (rule order_trans)
qed

text \<open>The exit functional is capped at the horizon,
  so the value is bounded by it outright, for any constraint set.  The sharp
  bound on a ball, which also gives the value \<open>0\<close> on its boundary, needs the class-level
  expected-exit-time estimate below.\<close>

theorem covariation_val_le_T:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
  assumes T: "0 \<le> T"
  shows "covariation_val S T K x \<le> ennreal T"
  unfolding covariation_val_def
proof (rule Sup_least)
  fix c :: ennreal
  assume "c \<in> (\<lambda>Q. ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))))
      ` covariation_class S T x"
  then obtain Q :: "('n pairpath) measure"
    where Q: "Q \<in> covariation_class S T x"
      and c: "c = ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))" by blast
  show "c \<le> ennreal T"
    unfolding c
    by (rule ess_inf_time_le_const[OF covariation_class_prob[OF Q]])
      (simp add: pexit_def etime_le_T[OF T])
qed

text \<open>A lower bound \<open>\<theta>\<close> on the trace over the constraint set makes
  \<open>|X|\<^sup>2\<close> a submartingale with rate at least \<open>\<theta>\<close>, which gives an
  exit-time estimate at the class level.\<close>

theorem covariation_class_trace_rate:
  fixes Q :: "('n::finite pairpath) measure"
  assumes th: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> \<theta> \<le> trace a"
    and Q: "Q \<in> covariation_class S T x"
  shows "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
      \<theta> * (t - s)
        \<le> trace (snd (\<omega> t)) - trace (snd (\<omega> s))"
proof -
  have dq: "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> S"
    by (rule covariation_class_diffquot[OF Q])
  show ?thesis
  proof (rule eventually_mono[OF dq])
    fix \<omega> :: "'n pairpath"
    assume q: "\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> S"
    show "\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        \<theta> * (t - s)
          \<le> trace (snd (\<omega> t)) - trace (snd (\<omega> s))"
    proof (intro allI impI)
      fix s t :: real
      assume s: "0 \<le> s" and st: "s < t" and tT: "t \<le> T"
      have mem: "(1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> S"
        using q s st tT by blast
      have "\<theta>
          \<le> trace ((1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)))"
        by (rule th[OF mem])
      also have "\<dots> = (trace (snd (\<omega> t)) - trace (snd (\<omega> s))) / (t - s)"
        by (simp add: trace_scaleR trace_sub)
      finally show "\<theta> * (t - s)
          \<le> trace (snd (\<omega> t)) - trace (snd (\<omega> s))"
        using st by (simp add: pos_le_divide_eq)
    qed
  qed
qed

lemma covariation_class_norm_sq_integrable:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and Q: "Q \<in> covariation_class S T x" and t: "t \<in> {0..T}"
  shows "integrable Q (\<lambda>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t))"
proof -
  have "integrable Q (\<lambda>\<omega> :: 'n pairpath. \<Sum>i\<in>UNIV. (fst (\<omega> t) $ i)\<^sup>2)"
    by (intro Bochner_Integration.integrable_sum
        covariation_class_sq_integrable[OF B0 B T Q t])
  then show ?thesis by (simp add: inner_vec_def power2_eq_square)
qed

text \<open>The class-level form of the exit-time estimate: the expected squared
  norm grows at rate at least \<open>\<theta>\<close>, using the compensated clause only at
  the fixed time \<open>t\<close> --- no stopping, no optional sampling.\<close>

theorem covariation_class_sq_norm_mean_ge:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and th: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> \<theta> \<le> trace a"
    and Q: "Q \<in> covariation_class S T x" and t: "t \<in> {0..T}"
  shows "x \<bullet> x + \<theta> * t
      \<le> (\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q)"
proof -
  interpret P: prob_space Q by (rule covariation_class_prob[OF Q])
  have t0: "0 \<le> t" and tT: "t \<le> T" using t by auto
  have ci: "integrable Q (\<lambda>\<omega>. outerp (fst (\<omega> t)) - snd (\<omega> t))"
    by (rule covariation_class_compensated_integrable[OF Q t])
  have ti: "integrable Q (\<lambda>\<omega>. trace (outerp (fst (\<omega> t)) - snd (\<omega> t)))"
    by (rule integrable_bounded_linear[OF bounded_linear_trace ci])
  have ni: "integrable Q (\<lambda>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t))"
    by (rule covariation_class_norm_sq_integrable[OF T B0 B Q t])
  have mean: "(\<integral>\<omega>. trace (outerp (fst (\<omega> t)) - snd (\<omega> t)) \<partial>Q) = x \<bullet> x"
  proof -
    have "(\<integral>\<omega>. trace (outerp (fst (\<omega> t)) - snd (\<omega> t)) \<partial>Q)
        = trace (\<integral>\<omega>. outerp (fst (\<omega> t)) - snd (\<omega> t) \<partial>Q)"
      by (rule integral_bounded_linear[OF bounded_linear_trace ci])
    also have "\<dots> = trace (outerp x)"
      by (simp add: covariation_class_compensated_mean[OF Q t])
    finally show ?thesis by (simp add: trace_outerp)
  qed
  have st: "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    by (rule covariation_class_start[OF Q])
  have tr: "AE \<omega> in Q. \<forall>s t'. 0 \<le> s \<longrightarrow> s < t' \<longrightarrow> t' \<le> T \<longrightarrow>
      \<theta> * (t' - s)
        \<le> trace (snd (\<omega> t')) - trace (snd (\<omega> s))"
    by (rule covariation_class_trace_rate[OF th Q])
  have rate: "AE \<omega> in Q. \<theta> * t \<le> trace (snd (\<omega> t))"
    using st tr
  proof eventually_elim
    case (elim \<omega>)
    show ?case
    proof (cases "t = 0")
      case True
      then show ?thesis using elim by (simp add: trace_def)
    next
      case False
      with t0 have pos: "0 < t" by simp
      have "\<theta> * (t - 0)
          \<le> trace (snd (\<omega> t)) - trace (snd (\<omega> 0))"
        using elim pos tT by blast
      then show ?thesis using elim by (simp add: trace_def)
    qed
  qed
  have ptw: "AE \<omega> in Q. trace (outerp (fst (\<omega> t)) - snd (\<omega> t))
      + \<theta> * t \<le> fst (\<omega> t) \<bullet> fst (\<omega> t)"
    using rate by eventually_elim (simp add: trace_sub trace_outerp)
  have "(\<integral>\<omega>. trace (outerp (fst (\<omega> t)) - snd (\<omega> t)) \<partial>Q)
      + \<theta> * t
      = (\<integral>\<omega>. trace (outerp (fst (\<omega> t)) - snd (\<omega> t))
            + \<theta> * t \<partial>Q)"
    using ti by (simp add: P.prob_space)
  also have "\<dots> \<le> (\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q)"
    by (rule integral_mono_AE) (use ti ni ptw in auto)
  finally show ?thesis unfolding mean .
qed

text \<open>The ball bound: if the target set fits inside a ball
  of radius \<open>r\<close>, then \<open>v(x) \<le> (r\<^sup>2 - |x|\<^sup>2) / \<theta>\<close>, independent of the
  horizon \<open>T\<close> --- the quantitative form of the horizon bound, and why the horizon
  cap is eventually invisible.  It is usually derived from It\<open>\<^bold>o\<close>'s formula; here it
  follows from \<open>covariation_class_sq_norm_mean_ge\<close>, the estimate at
  a fixed time, with no stochastic calculus.\<close>

theorem covariation_val_le_ball_bound:
  fixes r :: real and x :: "real^'n::finite" and K :: "(real^'n) set"
  assumes T: "0 \<le> T" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and th0: "0 < \<theta>" and th: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> \<theta> \<le> trace a"
    and KB: "K \<subseteq> cball 0 r"
  shows "covariation_val S T K x \<le> ennreal ((r * r - x \<bullet> x) / \<theta>)"
proof -
  define V where "V = (r * r - x \<bullet> x) / \<theta>"
  have main: "covariation_val S T K x \<le> ennreal V"
    unfolding covariation_val_def
  proof (rule Sup_least)
    fix e :: ennreal
    assume "e \<in> (\<lambda>Q. ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))))
        ` covariation_class S T x"
    then obtain Q :: "('n pairpath) measure"
      where Q: "Q \<in> covariation_class S T x"
        and e: "e = ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))" by blast
    interpret P: prob_space Q by (rule covariation_class_prob[OF Q])
    show "e \<le> ennreal V"
    proof (rule ccontr)
      assume "\<not> e \<le> ennreal V"
      then have gt: "ennreal V < e" by simp
      have ele: "e \<le> ennreal T"
        unfolding e
        by (rule ess_inf_time_le_const[OF P.prob_space_axioms])
          (simp add: pexit_def etime_le_T[OF T])
      have efin: "e < \<top>"
        using ele ennreal_less_top by (rule order_le_less_trans)
      define c where "c = enn2real e"
      have ec: "e = ennreal c" unfolding c_def using efin by simp
      have c0: "0 \<le> c" unfolding c_def by simp
      have cT: "c \<le> T" using ele T unfolding ec by simp
      define m where "m = max V 0"
      have m0: "0 \<le> m" and mB: "V \<le> m" unfolding m_def by auto
      have mc: "m < c"
      proof (cases "0 \<le> V")
        case True
        then have "V < c" using gt unfolding ec by (simp add: ennreal_less_iff)
        then show ?thesis using True unfolding m_def by simp
      next
        case False
        then have z: "ennreal V = 0" by (simp add: ennreal_neg)
        have "0 < c"
        proof (rule ccontr)
          assume "\<not> 0 < c"
          then have "ennreal c = 0" by (simp add: ennreal_neg)
          with gt z show False unfolding ec by simp
        qed
        then show ?thesis using False unfolding m_def by simp
      qed
      define t where "t = (m + c) / 2"
      have t0: "0 < t" unfolding t_def using m0 mc by simp
      have tc: "t < c" unfolding t_def using mc by simp
      have Bt: "V < t" unfolding t_def using mB mc by simp
      have tT: "t \<le> T" using tc cT by simp
      have tI: "t \<in> {0..T}" using t0 tT by simp
      have ae1: "AE \<omega> in Q. e \<le> ennreal (pexit T K (\<lambda>s. fst (\<omega> s)))"
        unfolding e by (rule ess_inf_time_AE)
      have ae2: "AE \<omega> in Q. fst (\<omega> t) \<bullet> fst (\<omega> t) \<le> r * r"
      proof (rule eventually_mono[OF ae1])
        fix \<omega> :: "'n pairpath"
        assume "e \<le> ennreal (pexit T K (\<lambda>s. fst (\<omega> s)))"
        then have "ennreal c \<le> ennreal (pexit T K (\<lambda>s. fst (\<omega> s)))"
          using ec by simp
        moreover have nn: "0 \<le> pexit T K (\<lambda>s. fst (\<omega> s))"
          unfolding pexit_def by (rule etime_nonneg[OF T])
        ultimately have ct: "c \<le> pexit T K (\<lambda>s. fst (\<omega> s))" by simp
        have inK: "fst (\<omega> t) \<in> K"
        proof (rule ccontr)
          assume notin: "fst (\<omega> t) \<notin> K"
          have "pexit T K (\<lambda>s. fst (\<omega> s)) \<le> t"
            unfolding pexit_def
            by (rule etime_le_of_mem[OF T less_imp_le[OF t0] tT])
              (use notin in simp)
          with ct tc show False by simp
        qed
        have "norm (fst (\<omega> t)) \<le> r" using inK KB by (auto simp: dist_norm)
        then have "(norm (fst (\<omega> t)))\<^sup>2 \<le> r\<^sup>2"
          by (rule power_mono) simp
        then show "fst (\<omega> t) \<bullet> fst (\<omega> t) \<le> r * r"
          by (simp add: power2_norm_eq_inner[symmetric] power2_eq_square)
      qed
      have ni: "integrable Q (\<lambda>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t))"
        by (rule covariation_class_norm_sq_integrable[OF T B0 B Q tI])
      have lo: "x \<bullet> x + \<theta> * t
          \<le> (\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q)"
        by (rule covariation_class_sq_norm_mean_ge[OF T B0 B th Q tI])
      have hi: "(\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q) \<le> r * r"
      proof -
        have "(\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q) \<le> (\<integral>\<omega>. r * r \<partial>Q)"
          by (rule integral_mono_AE) (use ni ae2 in auto)
        also have "\<dots> = r * r" by (simp add: P.prob_space)
        finally show ?thesis .
      qed
      from lo hi have "\<theta> * t \<le> r * r - x \<bullet> x" by simp
      then have "t \<le> V" unfolding V_def
        using th0 by (simp add: pos_le_divide_eq mult.commute)
      with Bt show False by simp
    qed
  qed
  from main show ?thesis unfolding V_def .
qed

text \<open>On the boundary of the ball: a member starting on the boundary
  \<open>|x| = r\<close> has exit value \<open>0\<close>, the case \<open>x \<bullet> x = r\<^sup>2\<close> of the
  bound above.\<close>

theorem covariation_val_boundary_zero:
  fixes r :: real and x :: "real^'n::finite"
  assumes T: "0 < T" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and th0: "0 < \<theta>" and th: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> \<theta> \<le> trace a"
    and x: "norm x = r"
  shows "covariation_val S T (cball 0 r) x = 0"
proof -
  have "x \<bullet> x = r * r"
    using x by (simp add: power2_norm_eq_inner[symmetric] power2_eq_square)
  then show ?thesis using T
    covariation_val_le_ball_bound[OF _ B0 B th0 th order_refl, where r = r and x = x] by simp
qed

(*<*)
end
(*>*)
