section \<open>The Euler scheme, its weak limit, and the exact quadratic lower bound\<close>

(*<*)
theory Value_Function_Euler_Construction
  imports
    "Lower_Semicontinuous.Lower_Semicontinuous" Dynamic_Programming_Pasting
    "Second_Order_Viscosity_Analysis.Doubling_Of_Variables"
begin

(*>*)

section \<open>The supersolution half: a rotating covariance field\<close>

text \<open>The supersolution inequality is an essential-infimum statement, so it
  needs pathwise control.  The paper (\<open>\<section>\<close>3.2, Case 1) gets it from a
  covariance field that annihilates the gradient of the test function along
  the path, so that no stochastic integral appears: its columns are
  \<open>S\<^sub>i \<nabla>\<phi>(y)\<close> with \<open>S\<^sub>i\<close> skew-symmetric.  The field used here annihilates the
  gradient for the same reason, but is built differently --- it is the
  feasible witness conjugated by the rotation carrying the frozen gradient to
  the current one.  Conjugation does not move the spectrum, so no eigenvalue
  margin is needed anywhere and the construction runs at \<open>L = 1\<close> as well; see
  the subsection \<open>Exact rotations\<close> below.

  Either way the field is fed to an Euler scheme glued by
  @{thm [source] exit_class_kglue_law'} and passed to a weak limit.  This
  section builds the algebra first: the trace pairing for sums of column
  outer products, the constant-volatility Gaussian member the Euler kernels
  are made of, and the limit itself.\<close>

subsection \<open>A crude operator bound for matrices\<close>

text \<open>\<open>sum_sq_le_sq_sum\<close> lives in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


text \<open>\<open>matvec_norm_le\<close> lives in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


subsection \<open>The trace pairing for sums of column outer products\<close>


definition sbmpair ::
  "real^'n::finite^'n \<Rightarrow> real \<Rightarrow> ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> 'n pairpath"
  where "sbmpair S T \<omega> = restrict
    (\<lambda>t. (S *v cbmX 0 t \<omega>, t *\<^sub>R (S ** transpose S))) {0..T}"

lemma sbmpair_apply:
  "t \<in> {0..T} \<Longrightarrow> sbmpair S T \<omega> t
     = (S *v cbmX 0 t \<omega>, t *\<^sub>R (S ** transpose S))"
  by (simp add: sbmpair_def)

text \<open>\<open>matvec_blin\<close>, \<open>matmul_sandwich_blin\<close> live in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


lemma continuous_on_sbmpair_path:
  fixes \<omega> :: "'n::finite \<Rightarrow> real \<Rightarrow> real" and S :: "real^'n^'n"
  shows "continuous_on {0..T}
      (\<lambda>t. (S *v cbmX (0 :: real^'n) t \<omega>, t *\<^sub>R (S ** transpose S)))"
proof (intro continuous_on_Pair)
  have c1: "continuous_on {0..T} (\<lambda>t. cbmX (0 :: real^'n) t \<omega>)"
    by (rule continuous_on_subset[OF cbmX_cont]) auto
  show "continuous_on {0..T} (\<lambda>t. S *v cbmX (0 :: real^'n) t \<omega>)"
    by (rule continuous_on_compose2[OF linear_continuous_on[OF matvec_blin]
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
          continuous_on_compose2[OF linear_continuous_on[OF matvec_blin]
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
  shows "prob_space (pair_law_of T (sbmpair S T)
      (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure))"
  unfolding pair_law_of_def
  by (rule BMP.prob_space_distr[OF sbmpair_measurable[OF T]])

lemma sbmpair_law_start:
  assumes T: "0 \<le> T"
  shows "AE \<omega> in pair_law_of T (sbmpair S T)
      (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure).
        fst (\<omega> 0) = (0 :: real^'n) \<and> snd (\<omega> 0) = 0"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  have phim: "sbmpair S T \<in> ?M \<rightarrow>\<^sub>M ?B" by (rule sbmpair_measurable[OF T])
  have mset: "{\<omega> \<in> space ?B. fst (\<omega> 0) = (0 :: real^'n) \<and> snd (\<omega> 0) = 0}
      \<in> sets ?B"
    by (rule start_set_sets[OF refl])
  have iff: "(AE \<omega> in pair_law_of T (sbmpair S T) ?M.
        fst (\<omega> 0) = (0 :: real^'n) \<and> snd (\<omega> 0) = 0)
      = (AE \<omega> in ?M. fst (sbmpair S T \<omega> 0) = (0 :: real^'n)
          \<and> snd (sbmpair S T \<omega> 0) = 0)"
    unfolding pair_law_of_def by (rule AE_distr_iff[OF phim mset])
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
  assumes T: "0 \<le> T"
    and SST: "S ** transpose S \<in> sconstraint k L"
  shows "AE \<omega> in pair_law_of T (sbmpair S T)
      (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure).
        \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
          (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?Q = "pair_law_of T (sbmpair S T) ?M"
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  have phim: "sbmpair S T \<in> ?M \<rightarrow>\<^sub>M ?B" by (rule sbmpair_measurable[OF T])
  have spQ: "space ?Q = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_pair_law_of)
  have one: "AE \<omega> in ?Q.
      (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
    if pq: "p \<in> {0..T}" "q \<in> {0..T}" "p < q" for p q :: real
  proof -
    have mm: "{\<omega> \<in> space ?B.
        (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L}
        \<in> sets ?B"
      using borel_of_closed[OF closedin_diffquot_constraint[OF pq(1) pq(2)]]
      by (simp add: space_borel_of)
    have iff: "(AE \<omega> in ?Q.
          (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L)
        = (AE \<omega> in ?M. (1 / (q - p))
            *\<^sub>R (snd (sbmpair S T \<omega> q) - snd (sbmpair S T \<omega> p))
            \<in> sconstraint k L)"
      unfolding pair_law_of_def by (rule AE_distr_iff[OF phim mm])
    have "AE \<omega> in ?M. (1 / (q - p))
        *\<^sub>R (snd (sbmpair S T \<omega> q) - snd (sbmpair S T \<omega> p))
        \<in> sconstraint k L"
    proof (intro AE_I2)
      fix \<omega> :: "'n \<Rightarrow> real \<Rightarrow> real"
      have "(1 / (q - p))
          *\<^sub>R (snd (sbmpair S T \<omega> q) - snd (sbmpair S T \<omega> p))
          = (1 / (q - p)) *\<^sub>R ((q - p) *\<^sub>R (S ** transpose S))"
        using pq by (simp add: sbmpair_apply scaleR_left_diff_distrib)
      also have "\<dots> = S ** transpose S"
        using pq(3) by simp
      finally show "(1 / (q - p))
          *\<^sub>R (snd (sbmpair S T \<omega> q) - snd (sbmpair S T \<omega> p))
          \<in> sconstraint k L"
        using SST by simp
    qed
    then show ?thesis unfolding iff .
  qed
  have rat: "AE \<omega> in ?Q. \<forall>p\<in>(\<rat>::real set). \<forall>q\<in>(\<rat>::real set).
      0 \<le> p \<longrightarrow> p < q \<longrightarrow> q \<le> T \<longrightarrow>
      (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
  proof (rule AE_ball_countable'[OF _ countable_rat])
    fix p :: real assume "p \<in> \<rat>"
    show "AE \<omega> in ?Q. \<forall>q\<in>(\<rat>::real set). 0 \<le> p \<longrightarrow> p < q \<longrightarrow> q \<le> T \<longrightarrow>
        (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
    proof (rule AE_ball_countable'[OF _ countable_rat])
      fix q :: real assume "q \<in> \<rat>"
      show "AE \<omega> in ?Q. 0 \<le> p \<longrightarrow> p < q \<longrightarrow> q \<le> T \<longrightarrow>
          (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
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
        \<Longrightarrow> (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
      and W: "\<omega> \<in> space ?Q" by blast+
    have mw: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using W spQ by simp
    have cont: "continuous_on {0..T} (\<lambda>u. snd (\<omega> u))"
      using mspace_path_metricD[OF mw] by (intro continuous_intros)
    show ?case
    proof (intro allI impI)
      fix u v :: real
      assume uv: "0 \<le> u" "u < v" "v \<le> T"
      show "(1 / (v - u)) *\<^sub>R (snd (\<omega> v) - snd (\<omega> u)) \<in> sconstraint k L"
        by (rule diffquot_all_of_rational
            [OF closed_sconstraint cont _ uv(1) uv(2) uv(3)]) (rule R)
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
        continuous_on_compose2[OF linear_continuous_on[OF matvec_blin]
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
  shows "martingale (pair_law_of T (sbmpair S T)
        (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure))
      (natural_filtration (pair_law_of T (sbmpair S T) bm_paths) 0
        (\<lambda>v \<omega>. \<omega> v)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u T)) :: real^'n)"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?Q = "pair_law_of T (sbmpair S T) ?M"
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
        [OF matvec_blin martingale_stopped_const[OF T martingale_cbmX]]])
    fix u :: real assume u: "0 \<le> u"
    have mI: "min u T \<in> {0..T}" using u T by simp
    show "(\<lambda>\<omega>. S *v cbmX (0 :: real^'n) (min u T) \<omega>)
        = (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. fst (sbmpair S T \<omega> (min u T)))"
      by (rule ext) (simp add: sbmpair_apply[OF mI])
  qed
  show ?thesis
    by (rule martingale_pair_law[OF prob_space_bm_paths
        sbmpair_measurable[OF T] sbmpair_adapted Zm mg])
qed

theorem sbmpair_law_comp_martingale:
  assumes T: "0 \<le> T"
  shows "martingale (pair_law_of T (sbmpair S T)
        (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure))
      (natural_filtration (pair_law_of T (sbmpair S T) bm_paths) 0
        (\<lambda>v \<omega>. \<omega> v)) 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (min u T)) :: real^'n) - snd (\<omega> (min u T)))"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?Q = "pair_law_of T (sbmpair S T) ?M"
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
    by (rule martingale_pair_law[OF prob_space_bm_paths
        sbmpair_measurable[OF T] sbmpair_adapted Zm mg])
qed

theorem sbmpair_law_in_paper_pair_class:
  assumes T: "0 \<le> T" and L: "1 \<le> L"
    and SST: "S ** transpose S \<in> sconstraint k L"
  shows "pair_law_of T (sbmpair S T)
      (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure)
    \<in> exit_class k L T (0 :: real^'n)"
  unfolding exit_class_def
proof (intro CollectI conjI)
  show "prob_space (pair_law_of T (sbmpair S T)
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))"
    by (rule prob_space_sbmpair_law[OF T])
  show "sets (pair_law_of T (sbmpair S T)
        (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      = sets (path_borel T :: ('n pairpath) measure)"
    by simp
  show "AE \<omega> in pair_law_of T (sbmpair S T)
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
        fst (\<omega> 0) = (0 :: real^'n) \<and> snd (\<omega> 0) = 0"
    by (rule sbmpair_law_start[OF T])
  show "AE \<omega> in pair_law_of T (sbmpair S T)
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
        \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
          (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
    by (rule sbmpair_law_diffquot[OF T SST])
  show "martingale (pair_law_of T (sbmpair S T)
        (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      (natural_filtration (pair_law_of T (sbmpair S T) bm_paths) 0
        (\<lambda>t \<omega>. \<omega> t)) 0
      (\<lambda>t \<omega>. fst (\<omega> (min t T)) :: real^'n)"
    by (rule sbmpair_law_X_martingale[OF T])
  show "martingale (pair_law_of T (sbmpair S T)
        (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      (natural_filtration (pair_law_of T (sbmpair S T) bm_paths) 0
        (\<lambda>t \<omega>. \<omega> t)) 0
      (\<lambda>t \<omega>. outerp (fst (\<omega> (min t T)) :: real^'n) - snd (\<omega> (min t T)))"
    by (rule sbmpair_law_comp_martingale[OF T])
qed

corollary sbmpair_pshift_law_in_paper_pair_class:
  assumes T: "0 \<le> T" and L: "1 \<le> L"
    and SST: "S ** transpose S \<in> sconstraint k L"
  shows "pshift_law T v (pair_law_of T (sbmpair S T)
      (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure))
    \<in> exit_class k L T (v :: real^'n)"
proof -
  have "pshift_law T v (pair_law_of T (sbmpair S T)
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
    \<in> exit_class k L T (v + 0)"
    by (rule exit_class_pshift[OF T
          sbmpair_law_in_paper_pair_class[OF T L SST]])
  then show ?thesis by simp
qed

subsection \<open>Writing the field as a square: columns into a matrix\<close>

text \<open>\<open>sbmpair\<close> wants a volatility matrix \<open>S\<close> with \<open>S S\<^sup>T\<close> equal to the
  field value; the field is a sum of column outer products, so \<open>S\<close> is the
  matrix whose columns are those columns, indexed through any enumeration
  of the eigenbasis.\<close>


lemma sbmpair_in_mspace:
  fixes \<omega> :: "'n::finite \<Rightarrow> real \<Rightarrow> real" and S :: "real^'n^'n"
  shows "sbmpair S T \<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
  unfolding sbmpair_def
  by (rule mspace_path_metricI[OF continuous_on_sbmpair_path])

lemma sbmpair_pathwise_tendsto:
  fixes Sm :: "nat \<Rightarrow> real^'n::finite^'n" and S :: "real^'n^'n"
    and \<omega> :: "'n \<Rightarrow> real \<Rightarrow> real"
  assumes T: "0 \<le> T" and Sc: "Sm \<longlonglongrightarrow> S"
  shows "limitin (mtopology_of (path_metric T :: ('n pairpath) metric))
      (\<lambda>m. sbmpair (Sm m) T \<omega>) (sbmpair S T \<omega>) sequentially"
proof -
  let ?PM = "path_metric T :: ('n pairpath) metric"
  interpret PM: Metric_space "mspace ?PM" "mdist ?PM"
    by (rule Metric_space_mspace_mdist)
  have msp: "sbmpair S' T \<omega> \<in> mspace ?PM" for S' :: "real^'n^'n"
    by (rule sbmpair_in_mspace)
  have cW: "continuous_on {0..T} (\<lambda>t. cbmX (0 :: real^'n) t \<omega>)"
    by (rule continuous_on_subset[OF cbmX_cont]) auto
  have "bounded ((\<lambda>t. cbmX (0 :: real^'n) t \<omega>) ` {0..T})"
    by (intro compact_imp_bounded compact_continuous_image cW) simp
  then obtain BW where BW: "\<And>t. t \<in> {0..T}
      \<Longrightarrow> norm (cbmX (0 :: real^'n) t \<omega>) \<le> BW"
    unfolding bounded_iff by blast
  have BW0: "0 \<le> BW"
  proof -
    have z: "(0::real) \<in> {0..T}" using T by simp
    show ?thesis
      using BW[OF z] norm_ge_zero[of "cbmX (0 :: real^'n) 0 \<omega>"] by linarith
  qed
  define cs where "cs = (\<lambda>m. \<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>(Sm m - S) $ i $ j\<bar>)"
  define ds where "ds = (\<lambda>m. norm (Sm m ** transpose (Sm m)
      - S ** transpose S))"
  define D where "D = (\<lambda>m. cs m * BW + T * ds m)"
  have cs_nn: "0 \<le> cs m" for m
    unfolding cs_def by (intro sum_nonneg) simp_all
  have ds_nn: "0 \<le> ds m" for m unfolding ds_def by simp
  have cs0: "cs \<longlonglongrightarrow> 0"
  proof -
    have ent: "(\<lambda>m. \<bar>(Sm m - S) $ i $ j\<bar>) \<longlonglongrightarrow> 0" for i j
    proof -
      have "(\<lambda>m. Sm m - S) \<longlonglongrightarrow> S - S"
        by (intro tendsto_diff Sc tendsto_const)
      then have "(\<lambda>m. (Sm m - S) $ i $ j) \<longlonglongrightarrow> (S - S) $ i $ j"
        by (intro tendsto_vec_nth)
      then have "(\<lambda>m. (Sm m - S) $ i $ j) \<longlonglongrightarrow> 0" by simp
      then show ?thesis using tendsto_rabs_zero by blast
    qed
    have "(\<lambda>m. \<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>(Sm m - S) $ i $ j\<bar>)
        \<longlonglongrightarrow> (\<Sum>i\<in>(UNIV :: 'n set). \<Sum>j\<in>(UNIV :: 'n set). (0::real))"
      by (intro tendsto_sum ent)
    then show ?thesis unfolding cs_def by simp
  qed
  have ds0: "ds \<longlonglongrightarrow> 0"
  proof -
    have h: "(\<lambda>m. Sm m ** transpose (Sm m)) \<longlonglongrightarrow> S ** transpose S"
    proof (intro vec_tendstoI)
      fix i j
      have e: "\<And>A :: real^'n^'n. (A ** transpose A) $ i $ j
          = (\<Sum>l\<in>UNIV. A $ i $ l * A $ j $ l)"
        by (simp add: matrix_matrix_mult_def transpose_def)
      have "(\<lambda>m. \<Sum>l\<in>UNIV. Sm m $ i $ l * Sm m $ j $ l)
          \<longlonglongrightarrow> (\<Sum>l\<in>UNIV. S $ i $ l * S $ j $ l)"
        by (intro tendsto_sum tendsto_mult tendsto_vec_nth Sc)
      then show "(\<lambda>m. (Sm m ** transpose (Sm m)) $ i $ j)
          \<longlonglongrightarrow> (S ** transpose S) $ i $ j"
        unfolding e .
    qed
    have "(\<lambda>m. Sm m ** transpose (Sm m) - S ** transpose S)
        \<longlonglongrightarrow> S ** transpose S - S ** transpose S"
      by (intro tendsto_diff h tendsto_const)
    then have "(\<lambda>m. Sm m ** transpose (Sm m) - S ** transpose S)
        \<longlonglongrightarrow> 0" by simp
    then show ?thesis unfolding ds_def
      using tendsto_norm_zero by blast
  qed
  have D0: "D \<longlonglongrightarrow> 0"
  proof -
    have "D \<longlonglongrightarrow> 0 * BW + T * 0"
      unfolding D_def by (intro tendsto_add tendsto_mult tendsto_const cs0 ds0)
    then show ?thesis by simp
  qed
  have mbound: "mdist ?PM (sbmpair (Sm m) T \<omega>) (sbmpair S T \<omega>) \<le> D m" for m
  proof (rule path_mdist_le_iff_all[OF T msp msp, THEN iffD2], rule ballI)
    fix t assume t: "t \<in> {0..T}"
    have fst_b: "dist (Sm m *v cbmX (0 :: real^'n) t \<omega>)
        (S *v cbmX (0 :: real^'n) t \<omega>) \<le> cs m * BW"
    proof -
      have "dist (Sm m *v cbmX (0 :: real^'n) t \<omega>)
          (S *v cbmX (0 :: real^'n) t \<omega>)
          = norm ((Sm m - S) *v cbmX (0 :: real^'n) t \<omega>)"
        by (simp add: dist_norm matrix_vector_mult_diff_rdistrib)
      also have "\<dots> \<le> cs m * norm (cbmX (0 :: real^'n) t \<omega>)"
        unfolding cs_def by (rule matvec_norm_le)
      also have "\<dots> \<le> cs m * BW"
        using BW[OF t] cs_nn by (intro mult_left_mono)
      finally show ?thesis .
    qed
    have snd_b: "dist (t *\<^sub>R (Sm m ** transpose (Sm m)))
        (t *\<^sub>R (S ** transpose S)) \<le> T * ds m"
    proof -
      have "dist (t *\<^sub>R (Sm m ** transpose (Sm m)))
          (t *\<^sub>R (S ** transpose S))
          = \<bar>t\<bar> * ds m"
        unfolding ds_def
        by (simp add: dist_norm scaleR_diff_right[symmetric])
      also have "\<dots> \<le> T * ds m"
        using t ds_nn by (intro mult_right_mono) auto
      finally show ?thesis .
    qed
    have "dist (sbmpair (Sm m) T \<omega> t) (sbmpair S T \<omega> t)
        = dist (Sm m *v cbmX (0 :: real^'n) t \<omega>,
            t *\<^sub>R (Sm m ** transpose (Sm m)))
          (S *v cbmX (0 :: real^'n) t \<omega>, t *\<^sub>R (S ** transpose S))"
      by (simp add: sbmpair_apply[OF t])
    also have "\<dots> \<le> dist (Sm m *v cbmX (0 :: real^'n) t \<omega>)
          (S *v cbmX (0 :: real^'n) t \<omega>)
        + dist (t *\<^sub>R (Sm m ** transpose (Sm m)))
            (t *\<^sub>R (S ** transpose S))"
      by (rule dist_pair_le)
    also have "\<dots> \<le> cs m * BW + T * ds m"
      using fst_b snd_b by linarith
    finally show "dist (sbmpair (Sm m) T \<omega> t) (sbmpair S T \<omega> t) \<le> D m"
      unfolding D_def .
  qed
  show ?thesis
    unfolding mtopology_of_def
  proof (rule PM.limitin_metric[THEN iffD2], intro conjI allI impI)
    show "sbmpair S T \<omega> \<in> mspace ?PM" by (rule msp)
    fix \<epsilon> :: real assume e: "0 < \<epsilon>"
    from LIMSEQ_D[OF D0 e] obtain M0
      where M0': "\<And>m. M0 \<le> m \<Longrightarrow> norm (D m - 0) < \<epsilon>" by blast
    have M0: "\<And>m. M0 \<le> m \<Longrightarrow> norm (D m) < \<epsilon>" using M0' by simp
    show "\<forall>\<^sub>F m in sequentially. sbmpair (Sm m) T \<omega> \<in> mspace ?PM
        \<and> mdist ?PM (sbmpair (Sm m) T \<omega>) (sbmpair S T \<omega>) < \<epsilon>"
    proof (intro eventually_sequentiallyI[of M0] conjI)
      fix m assume m: "M0 \<le> m"
      show "sbmpair (Sm m) T \<omega> \<in> mspace ?PM" by (rule msp)
      have "mdist ?PM (sbmpair (Sm m) T \<omega>) (sbmpair S T \<omega>) \<le> D m"
        by (rule mbound)
      also have "\<dots> \<le> norm (D m)" by simp
      also have "\<dots> < \<epsilon>" by (rule M0[OF m])
      finally show "mdist ?PM (sbmpair (Sm m) T \<omega>) (sbmpair S T \<omega>) < \<epsilon>" .
    qed
  qed
qed

theorem sbm_law_weak_conv:
  fixes Sm :: "nat \<Rightarrow> real^'n::finite^'n" and S :: "real^'n^'n"
  assumes T: "0 \<le> T" and Sc: "Sm \<longlonglongrightarrow> S"
  shows "weak_conv_on
      (\<lambda>m. pair_law_of T (sbmpair (Sm m) T)
        (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      (pair_law_of T (sbmpair S T) bm_paths)
      sequentially (mtopology_of (path_metric T :: ('n pairpath) metric))"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?X = "mtopology_of (path_metric T :: ('n pairpath) metric)"
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?S = "mspace (path_metric T :: ('n pairpath) metric)"
  let ?law = "\<lambda>S'. pair_law_of T (sbmpair S' T) ?M"
  have fmS: "finite_measure (?law S')" for S' :: "real^'n^'n"
    using prob_space_sbmpair_law[OF T, where S = S']
    by (simp add: prob_space.emeasure_space_1 finite_measureI)
  have MWfin: "mweak_conv_fin ?S
      (mdist (path_metric T :: ('n pairpath) metric))
      (\<lambda>m. ?law (Sm m)) (?law S) sequentially"
    unfolding mweak_conv_fin_def mweak_conv_fin_axioms_def
    using fmS by (simp add: mtopology_of_def)
  interpret MW: mweak_conv_fin ?S
      "mdist (path_metric T :: ('n pairpath) metric)"
      "\<lambda>m. ?law (Sm m)" "?law S" sequentially
    by (rule MWfin)
  show ?thesis
    unfolding mtopology_of_def
  proof (rule MW.mweak_conv_eq1[THEN iffD2], intro allI impI)
    fix f :: "'n pairpath \<Rightarrow> real"
    assume uc: "uniformly_continuous_map MW.Self euclidean_metric f"
    assume bnd: "\<exists>B. \<forall>x \<in> ?S. \<bar>f x\<bar> \<le> B"
    from bnd obtain B where B: "\<And>x. x \<in> ?S \<Longrightarrow> \<bar>f x\<bar> \<le> B" by blast
    have cf: "continuous_map ?X euclideanreal f"
      using uniformly_continuous_imp_continuous_map[OF uc]
      by (simp add: mtopology_of_def)
    have fm: "f \<in> borel_measurable ?B"
      using continuous_map_measurable[OF cf] by (simp add: borel_of_euclidean)
    have distr_int: "(\<integral>\<omega>. f \<omega> \<partial>(?law S')) = (\<integral>\<omega>. f (sbmpair S' T \<omega>) \<partial>?M)"
      for S' :: "real^'n^'n"
      unfolding pair_law_of_def
      by (rule integral_distr[OF sbmpair_measurable[OF T] fm])
    have ptw: "(\<lambda>m. f (sbmpair (Sm m) T \<omega>)) \<longlonglongrightarrow> f (sbmpair S T \<omega>)"
      for \<omega> :: "'n \<Rightarrow> real \<Rightarrow> real"
    proof -
      have "limitin euclideanreal
          (f \<circ> (\<lambda>m. sbmpair (Sm m) T \<omega>))
          (f (sbmpair S T \<omega>)) sequentially"
        by (rule continuous_map_limit[OF cf
              sbmpair_pathwise_tendsto[OF T Sc]])
      then show ?thesis by (simp add: o_def)
    qed
    have meas: "(\<lambda>\<omega>. f (sbmpair S' T \<omega>)) \<in> borel_measurable ?M"
      for S' :: "real^'n^'n"
      by (rule measurable_compose[OF sbmpair_measurable[OF T] fm])
    have bd: "AE \<omega> in ?M. norm (f (sbmpair S' T \<omega>)) \<le> \<bar>B\<bar>"
      for S' :: "real^'n^'n"
    proof (intro AE_I2)
      fix \<omega> :: "'n \<Rightarrow> real \<Rightarrow> real"
      have "\<bar>f (sbmpair S' T \<omega>)\<bar> \<le> B"
        by (rule B[OF sbmpair_in_mspace])
      then show "norm (f (sbmpair S' T \<omega>)) \<le> \<bar>B\<bar>" by simp
    qed
    interpret BMPP: prob_space ?M by (rule prob_space_bm_paths)
    have ibd: "integrable ?M (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<bar>B\<bar>)"
      by simp
    have "(\<lambda>m. \<integral>\<omega>. f (sbmpair (Sm m) T \<omega>) \<partial>?M)
        \<longlonglongrightarrow> (\<integral>\<omega>. f (sbmpair S T \<omega>) \<partial>?M)"
      by (rule integral_dominated_convergence[OF meas meas ibd _ bd])
        (simp add: ptw)
    then show "(\<lambda>m. \<integral>\<omega>. f \<omega> \<partial>(?law (Sm m)))
        \<longlonglongrightarrow> (\<integral>\<omega>. f \<omega> \<partial>(?law S))"
      unfolding distr_int .
  qed
qed

subsection \<open>The Euler kernel: measurability package\<close>

text \<open>A continuous matrix field with admissible squares induces, through
  the Gaussian member, a kernel with exactly the three measurability
  properties @{thm [source] exit_class_kglue_law'} consumes.
  Sequential continuity in the LP metric comes from
  @{thm [source] sbm_law_weak_conv}; it upgrades to topological continuity
  by the closed-preimage criterion (both sides are metric), and the
  prob-algebra form follows by the same bridge as
  @{thm [source] exit_val_measurable_selector_kernel'}.\<close>

theorem sbm_kernel_package:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n" and T' :: real
  assumes T: "0 < T'" and L: "1 \<le> L"
    and SFc: "continuous_on UNIV SF"
    and SFs: "\<And>z. SF z ** transpose (SF z) \<in> sconstraint k L"
  shows "(\<lambda>z. pair_law_of T' (sbmpair (SF z) T')
        (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      \<in> borel \<rightarrow>\<^sub>M prob_algebra (path_borel T' :: ('n pairpath) measure)"
    and "(\<lambda>z. pair_law_of T' (sbmpair (SF z) T')
        (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      \<in> borel \<rightarrow>\<^sub>M borel_of (Metric_space.mtopology
        (exit_class k L T' (0::real^'n))
        (Levy_Prokhorov.LPm (mspace (path_metric T' :: ('n pairpath) metric))
          (mdist (path_metric T' :: ('n pairpath) metric))))"
    and "\<And>z. pair_law_of T' (sbmpair (SF z) T')
        (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      \<in> exit_class k L T' (0 :: real^'n)"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?X = "mtopology_of (path_metric T' :: ('n pairpath) metric)"
  let ?B = "(path_borel T' :: ('n pairpath) measure)"
  let ?W = "weak_conv_topology
      (mtopology_of (path_metric T' :: ('n pairpath) metric))"
  let ?C = "exit_class k L T' (0::real^'n)"
  let ?dd = "Levy_Prokhorov.LPm
      (mspace (path_metric T' :: ('n pairpath) metric))
      (mdist (path_metric T' :: ('n pairpath) metric))"
  let ?P = "{N :: ('n pairpath) measure. prob_space N
      \<and> sets N = sets (path_borel T' :: ('n pairpath) measure)}"
  define KK where "KK = (\<lambda>z. pair_law_of T' (sbmpair (SF z) T') ?M)"
  have T0': "0 \<le> T'" using T by simp
  have L0: "0 \<le> L" using L by simp
  interpret MC: Metric_space ?C ?dd
    by (rule exit_class_compact_metric_space(1)[OF T L0])
  have Ctop: "MC.mtopology = subtopology ?W ?C"
    by (rule exit_class_compact_metric_space(2)[OF T L0])
  show KC: "\<And>z. pair_law_of T' (sbmpair (SF z) T') ?M
      \<in> exit_class k L T' (0 :: real^'n)"
    by (rule sbmpair_law_in_paper_pair_class[OF T0' L SFs])
  have KCk: "KK z \<in> ?C" for z unfolding KK_def by (rule KC)
  have seq: "limitin MC.mtopology (\<lambda>m. KK (zm m)) (KK z) sequentially"
    if zc: "zm \<longlonglongrightarrow> z" for zm and z :: "real^'n"
  proof -
    have SFzc: "(\<lambda>m. SF (zm m)) \<longlonglongrightarrow> SF z"
    proof (rule isCont_tendsto_compose[OF _ zc])
      show "isCont SF z"
        using SFc continuous_on_eq_continuous_at[of UNIV SF] by simp
    qed
    have wc: "limitin ?W (\<lambda>m. KK (zm m)) (KK z) sequentially"
      unfolding KK_def by (rule sbm_law_weak_conv[OF T0' SFzc])
    show ?thesis
      unfolding Ctop limitin_subtopology
      by (intro conjI wc KCk always_eventually allI)
  qed
  have cont: "continuous_map (euclidean :: (real^'n) topology)
      MC.mtopology KK"
    unfolding continuous_map_closedin
  proof (intro conjI allI impI)
    show "KK \<in> topspace (euclidean :: (real^'n) topology)
        \<rightarrow> topspace MC.mtopology"
      using KCk by auto
    fix C' assume cl: "closedin MC.mtopology C'"
    have "closed {z. KK z \<in> C'}"
    proof (rule closed_sequential_limits[THEN iffD2], intro allI impI)
      fix zm and z :: "real^'n"
      assume h: "(\<forall>m. zm m \<in> {z. KK z \<in> C'}) \<and> zm \<longlonglongrightarrow> z"
      have lim: "limitin MC.mtopology (\<lambda>m. KK (zm m)) (KK z) sequentially"
        using h by (intro seq) blast
      have ev: "eventually (\<lambda>m. KK (zm m) \<in> C') sequentially"
        using h by (intro always_eventually) blast
      have "KK z \<in> C'"
        by (rule limitin_closedin[OF lim cl ev]) simp
      then show "z \<in> {z. KK z \<in> C'}" by blast
    qed
    then show "closedin (euclidean :: (real^'n) topology)
        {x \<in> topspace euclidean. KK x \<in> C'}"
      unfolding closed_closedin[symmetric] by simp
  qed
  show "(\<lambda>z. pair_law_of T' (sbmpair (SF z) T') ?M)
      \<in> borel \<rightarrow>\<^sub>M borel_of (Metric_space.mtopology ?C ?dd)"
    using continuous_map_measurable[OF cont]
    by (simp add: borel_of_euclidean KK_def)
  have contW: "continuous_map (euclidean :: (real^'n) topology) ?W KK"
    using cont unfolding Ctop continuous_map_in_subtopology by blast
  have SmB: "KK \<in> borel \<rightarrow>\<^sub>M borel_of ?W"
    using continuous_map_measurable[OF contW]
    by (simp add: borel_of_euclidean)
  have SP: "KK z \<in> ?P" for z
    using exit_class_prob[OF KCk] exit_class_sets[OF KCk]
    by simp
  have polish: "Polish_space
      (mtopology_of (path_metric T' :: ('n pairpath) metric))"
    by (rule Polish_space_path_metric)
  have setsPA: "sets (borel_of (subtopology ?W ?P)) = sets (prob_algebra ?B)"
    by (rule weak_conv_topology_eq_prob_algebra[OF polish])
  have r1: "KK \<in> borel \<rightarrow>\<^sub>M restrict_space (borel_of ?W) ?P"
    by (rule measurable_restrict_space2[OF _ SmB]) (use SP in auto)
  have r2: "KK \<in> borel \<rightarrow>\<^sub>M borel_of (subtopology ?W ?P)"
    using r1 by (simp add: borel_of_subtopology)
  show "(\<lambda>z. pair_law_of T' (sbmpair (SF z) T') ?M)
      \<in> borel \<rightarrow>\<^sub>M prob_algebra ?B"
    using r2 measurable_cong_sets[OF refl setsPA] unfolding KK_def by blast
qed

subsection \<open>The Euler process\<close>

text \<open>Freeze the field at the left endpoint of each step and glue with
  @{thm [source] exit_class_kglue_law'}: stage \<open>j\<close> is a member on
  the horizon \<open>(j+1)h\<close>, and membership is plain induction --- the
  continuation kernel is centred (\<open>pglue\<close> recenters), so it is exactly
  @{thm [source] sbm_kernel_package} composed with the endpoint map.\<close>

fun eulerp ::
  "(real^'n::finite \<Rightarrow> real^'n^'n) \<Rightarrow> real^'n \<Rightarrow> real \<Rightarrow> nat
     \<Rightarrow> ('n pairpath) measure"
  where
    "eulerp SF x h 0 = pshift_law h x
        (pair_law_of h (sbmpair (SF x) h) bm_paths)"
  | "eulerp SF x h (Suc j) = kglue_law' (real (Suc j) * h)
        (real (Suc (Suc j)) * h)
        (\<lambda>\<omega>. pair_law_of h (sbmpair (SF (fst (\<omega> (real (Suc j) * h)))) h)
             bm_paths)
        (eulerp SF x h j)"

theorem eulerp_in_class:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n" and x :: "real^'n"
  assumes h0: "0 < h" and L1: "1 \<le> L"
    and SFc: "continuous_on UNIV SF"
    and SFs: "\<And>z. SF z ** transpose (SF z) \<in> sconstraint k L"
  shows "eulerp SF x h j \<in> exit_class k L (real (Suc j) * h) x"
proof (induction j)
  case 0
  have "pshift_law h x (pair_law_of h (sbmpair (SF x) h)
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      \<in> exit_class k L h x"
    by (rule sbmpair_pshift_law_in_paper_pair_class)
      (use h0 L1 SFs in simp_all)
  then show ?case by simp
next
  case (Suc j)
  define r where "r = real (Suc j) * h"
  define T' where "T' = real (Suc (Suc j)) * h"
  have hT: "T' - r = h" unfolding r_def T'_def by (simp add: field_simps)
  have r0: "0 \<le> r" unfolding r_def using h0 by simp
  have rT: "r < T'" unfolding r_def T'_def using h0 by simp
  have T0: "0 < T'" unfolding T'_def using h0 by simp
  have Q: "eulerp SF x h j \<in> exit_class k L r x"
    using Suc unfolding r_def .
  have setsQ: "sets (eulerp SF x h j) = sets (path_borel r :: ('n pairpath) measure)"
    by (rule exit_class_sets[OF Q])
  have hpos: "0 < (h :: real)" by (rule h0)
  note pack = sbm_kernel_package[OF hpos L1 SFc SFs]
  have eQ: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> r))
      \<in> borel_measurable (eulerp SF x h j)"
    by (rule measurable_compose[OF pair_law_eval_measurable[OF setsQ] pair_fst_borel])
  have eF: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> r))
      \<in> natural_filtration (eulerp SF x h j) 0 (\<lambda>v \<omega>. \<omega> v) r \<rightarrow>\<^sub>M borel"
    by (rule measurable_compose[OF natural_filtration_eval[OF r0 order_refl] pair_fst_borel])
  have Kp: "(\<lambda>\<omega> :: 'n pairpath.
      pair_law_of h (sbmpair (SF (fst (\<omega> r))) h) bm_paths)
      \<in> eulerp SF x h j \<rightarrow>\<^sub>M prob_algebra ((path_borel (T' - r) :: ('n pairpath) measure))"
    unfolding hT by (rule measurable_compose[OF eQ pack(1)])
  have Kb: "(\<lambda>\<omega> :: 'n pairpath.
      pair_law_of h (sbmpair (SF (fst (\<omega> r))) h) bm_paths)
      \<in> natural_filtration (eulerp SF x h j) 0 (\<lambda>v \<omega>. \<omega> v) r
      \<rightarrow>\<^sub>M borel_of (Metric_space.mtopology
          (exit_class k L (T' - r) (0::real^'n))
          (Levy_Prokhorov.LPm
            (mspace (path_metric (T' - r) :: ('n pairpath) metric))
            (mdist (path_metric (T' - r) :: ('n pairpath) metric))))"
    unfolding hT by (rule measurable_compose[OF eF pack(2)])
  have Kc: "pair_law_of h (sbmpair (SF (fst (\<omega> r))) h) bm_paths
      \<in> exit_class k L (T' - r) 0" for \<omega> :: "'n pairpath"
    unfolding hT by (rule pack(3))
  have "kglue_law' r T'
      (\<lambda>\<omega>. pair_law_of h (sbmpair (SF (fst (\<omega> r))) h) bm_paths)
      (eulerp SF x h j) \<in> exit_class k L T' x"
  proof (rule exit_class_kglue_law')
    show "0 \<le> r" by (rule r0)
    show "r < T'" by (rule rT)
    show "1 \<le> L" by (rule L1)
    show "0 < T'" by (rule T0)
    show "eulerp SF x h j \<in> exit_class k L r x" by (rule Q)
    show "(\<lambda>\<omega> :: 'n pairpath.
        pair_law_of h (sbmpair (SF (fst (\<omega> r))) h) bm_paths)
        \<in> eulerp SF x h j \<rightarrow>\<^sub>M prob_algebra ((path_borel (T' - r) :: ('n pairpath) measure))"
      by (rule Kp)
    show "(\<lambda>\<omega> :: 'n pairpath.
        pair_law_of h (sbmpair (SF (fst (\<omega> r))) h) bm_paths)
        \<in> natural_filtration (eulerp SF x h j) 0 (\<lambda>v \<omega>. \<omega> v) r
        \<rightarrow>\<^sub>M borel_of (Metric_space.mtopology
            (exit_class k L (T' - r) (0::real^'n))
            (Levy_Prokhorov.LPm
              (mspace (path_metric (T' - r) :: ('n pairpath) metric))
              (mdist (path_metric (T' - r) :: ('n pairpath) metric))))"
      by (rule Kb)
    show "\<And>\<omega> :: 'n pairpath.
        pair_law_of h (sbmpair (SF (fst (\<omega> r))) h) bm_paths
        \<in> exit_class k L (T' - r) 0"
      by (rule Kc)
  qed
  then show ?case unfolding r_def T'_def by simp
qed

subsection \<open>Step moments of the Gaussian member\<close>

text \<open>\<open>bounded_linear_trace_mult_left\<close> lives in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


lemma sconstraint_diag_le:
  fixes a :: "real^'n::finite^'n"
  assumes a: "a \<in> sconstraint k L"
  shows "a $ i $ i \<le> L"
proof -
  have ub: "eigen_ub a L"
    using a unfolding sconstraint_def by blast
  have gen: "\<And>u :: real^'n. u \<bullet> (a *v u) \<le> L * (u \<bullet> u)"
    using ub unfolding eigen_ub_def by blast
  have inst: "axis i 1 \<bullet> (a *v axis i 1)
      \<le> L * ((axis i 1 :: real^'n) \<bullet> axis i 1)"
    using gen by blast
  have e1: "axis i 1 \<bullet> (a *v axis i 1) = a $ i $ i"
    using axis1_inner[of i "a *v axis i 1"] matvec_axis1[of a i i] by simp
  have e2: "(axis i 1 :: real^'n) \<bullet> axis i 1 = 1"
    by (rule axis1_self)
  show ?thesis using inst unfolding e1 e2 by simp
qed

lemma sbm_entry_bound:
  fixes S :: "real^'n::finite^'n"
  assumes SST: "S ** transpose S \<in> sconstraint k L"
  shows "\<bar>S $ i $ j\<bar> \<le> sqrt L"
proof -
  have diag: "(S ** transpose S) $ i $ i = (\<Sum>l\<in>UNIV. (S $ i $ l)\<^sup>2)"
    by (simp add: matrix_matrix_mult_def transpose_def power2_eq_square)
  have "(S $ i $ j)\<^sup>2 \<le> (\<Sum>l\<in>UNIV. (S $ i $ l)\<^sup>2)"
    by (rule member_le_sum) simp_all
  also have "\<dots> \<le> L"
    using sconstraint_diag_le[OF SST, of i] diag by simp
  finally have "(S $ i $ j)\<^sup>2 \<le> L" .
  then have "sqrt ((S $ i $ j)\<^sup>2) \<le> sqrt L"
    by (rule real_sqrt_le_mono)
  then show ?thesis by simp
qed

lemma bm_coordinate_pow4:
  assumes h0: "0 < h"
  shows bm_coordinate_pow4_integrable:
    "integrable (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>\<omega>. (\<omega> i h) ^ 4)"
    and bm_coordinate_pow4_integral:
    "(\<integral>\<omega>. (\<omega> i h) ^ 4 \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      = 3 * h\<^sup>2"
proof -
  have h0': "(0::real) \<le> h" using h0 by simp
  have m: "(\<lambda>\<omega>. \<omega> i h) \<in> (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      \<rightarrow>\<^sub>M (borel :: real measure)"
    using h0' by (intro measurable_bm_coordinate) simp
  have p4: "(\<lambda>y :: real. y ^ 4) \<in> borel_measurable borel"
    by measurable
  have hb: "has_bochner_integral (gauss_measure h) (\<lambda>x. x ^ (2 * 2))
      (fact (2 * 2) / (2 ^ 2 * fact 2) * h ^ 2)"
    by (rule gauss_measure_moment_even[OF h0])
  have c3: "(fact (2 * 2) / (2 ^ 2 * fact 2) :: real) = 3"
    by (simp add: fact_numeral)
  have hb4: "has_bochner_integral (gauss_measure h) (\<lambda>x. x ^ 4) (3 * h\<^sup>2)"
    using hb by (simp add: c3 fact_numeral)
  have ig: "integrable (gauss_measure h) (\<lambda>x. x ^ 4)"
    and vg: "(\<integral>x. x ^ 4 \<partial>gauss_measure h) = 3 * h\<^sup>2"
    using hb4 by (auto intro: integrable.intros
        simp: has_bochner_integral_integral_eq)
  have d: "distr (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) borel
      (\<lambda>\<omega>. \<omega> i h) = gauss_measure h"
    by (rule bm_coordinate_distr[OF h0'])
  have "integrable (distr (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) borel
      (\<lambda>\<omega>. \<omega> i h)) (\<lambda>y. y ^ 4)"
    unfolding d by (rule ig)
  then show "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>\<omega>. (\<omega> i h) ^ 4)"
    by (subst (asm) integrable_distr_eq[OF m p4])
  have "(\<integral>\<omega>. (\<omega> i h) ^ 4 \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      = (\<integral>y. y ^ 4 \<partial>(distr (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
          borel (\<lambda>\<omega>. \<omega> i h)))"
    by (rule integral_distr[OF m p4, symmetric])
  also have "\<dots> = 3 * h\<^sup>2" unfolding d by (rule vg)
  finally show "(\<integral>\<omega>. (\<omega> i h) ^ 4
      \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)) = 3 * h\<^sup>2" .
qed

lemma bm_R2_moment:
  assumes h0: "0 < h"
  shows bm_R2_integrable:
    "integrable (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>\<omega>. (\<Sum>i\<in>UNIV. (\<omega> i h)\<^sup>2)\<^sup>2)"
    and bm_R2_integral:
    "(\<integral>\<omega>. (\<Sum>i\<in>UNIV. (\<omega> i h)\<^sup>2)\<^sup>2
        \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      \<le> 3 * (real CARD('n))\<^sup>2 * h\<^sup>2"
proof -
  have h0': "(0::real) \<le> h" using h0 by simp
  have m: "\<And>i. (\<lambda>\<omega>. \<omega> i h)
      \<in> (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      \<rightarrow>\<^sub>M (borel :: real measure)"
    using h0' by (intro measurable_bm_coordinate) simp
  have i4: "\<And>i. integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>\<omega>. (\<omega> i h) ^ 4)"
    by (rule bm_coordinate_pow4_integrable[OF h0])
  have prod_int: "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>\<omega>. (\<omega> i h)\<^sup>2 * (\<omega> j h)\<^sup>2)" for i j
  proof (rule Bochner_Integration.integrable_bound
      [where f = "\<lambda>\<omega>. (\<omega> i h) ^ 4 / 2 + (\<omega> j h) ^ 4 / 2"])
    show "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
        (\<lambda>\<omega>. (\<omega> i h) ^ 4 / 2 + (\<omega> j h) ^ 4 / 2)"
      using i4 by auto
    show "(\<lambda>\<omega>. (\<omega> i h)\<^sup>2 * (\<omega> j h)\<^sup>2)
        \<in> borel_measurable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)"
      using m by measurable
    show "AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
        norm ((\<omega> i h)\<^sup>2 * (\<omega> j h)\<^sup>2)
          \<le> norm ((\<omega> i h) ^ 4 / 2 + (\<omega> j h) ^ 4 / 2)"
    proof (intro AE_I2)
      fix \<omega> :: "'n \<Rightarrow> real \<Rightarrow> real"
      have "(\<omega> i h)\<^sup>2 * (\<omega> j h)\<^sup>2 \<le> (\<omega> i h) ^ 4 / 2 + (\<omega> j h) ^ 4 / 2"
        by (rule prod_sq_le_half_pow4)
      moreover have "0 \<le> (\<omega> i h)\<^sup>2 * (\<omega> j h)\<^sup>2" by simp
      moreover have "0 \<le> (\<omega> i h) ^ 4 / 2 + (\<omega> j h) ^ 4 / 2"
        by (intro add_nonneg_nonneg) simp_all
      ultimately show "norm ((\<omega> i h)\<^sup>2 * (\<omega> j h)\<^sup>2)
          \<le> norm ((\<omega> i h) ^ 4 / 2 + (\<omega> j h) ^ 4 / 2)" by simp
    qed
  qed
  have expand: "(\<Sum>i\<in>UNIV. (\<omega> i h)\<^sup>2)\<^sup>2
      = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. (\<omega> i h)\<^sup>2 * (\<omega> j h)\<^sup>2)"
    for \<omega> :: "'n \<Rightarrow> real \<Rightarrow> real"
    by (simp add: power2_eq_square sum_product)
  show int: "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>\<omega>. (\<Sum>i\<in>UNIV. (\<omega> i h)\<^sup>2)\<^sup>2)"
    unfolding expand by (intro Bochner_Integration.integrable_sum prod_int)
  have per: "(\<integral>\<omega>. (\<omega> i h)\<^sup>2 * (\<omega> j h)\<^sup>2
      \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)) \<le> 3 * h\<^sup>2" for i j
  proof -
    have "(\<integral>\<omega>. (\<omega> i h)\<^sup>2 * (\<omega> j h)\<^sup>2
        \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
        \<le> (\<integral>\<omega>. (\<omega> i h) ^ 4 / 2 + (\<omega> j h) ^ 4 / 2
            \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))"
    proof (rule integral_mono_AE)
      show "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
          (\<lambda>\<omega>. (\<omega> i h)\<^sup>2 * (\<omega> j h)\<^sup>2)" by (rule prod_int)
      show "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
          (\<lambda>\<omega>. (\<omega> i h) ^ 4 / 2 + (\<omega> j h) ^ 4 / 2)"
        using i4 by auto
      show "AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
          (\<omega> i h)\<^sup>2 * (\<omega> j h)\<^sup>2
            \<le> (\<omega> i h) ^ 4 / 2 + (\<omega> j h) ^ 4 / 2"
        by (intro AE_I2 prod_sq_le_half_pow4)
    qed
    also have "\<dots> = 3 * h\<^sup>2 / 2 + 3 * h\<^sup>2 / 2"
      using i4 by (simp add: bm_coordinate_pow4_integral[OF h0])
    finally show ?thesis by simp
  qed
  have "(\<integral>\<omega>. (\<Sum>i\<in>UNIV. (\<omega> i h)\<^sup>2)\<^sup>2
      \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      = (\<Sum>i\<in>UNIV. (\<integral>\<omega>. (\<Sum>j\<in>UNIV. (\<omega> i h)\<^sup>2 * (\<omega> j h)\<^sup>2)
          \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)))"
    unfolding expand
    by (rule Bochner_Integration.integral_sum)
      (intro Bochner_Integration.integrable_sum prod_int)
  also have "\<dots> = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. (\<integral>\<omega>. (\<omega> i h)\<^sup>2 * (\<omega> j h)\<^sup>2
      \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)))"
    by (intro sum.cong refl Bochner_Integration.integral_sum prod_int)
  also have "\<dots> \<le> (\<Sum>i\<in>(UNIV :: 'n set). \<Sum>j\<in>(UNIV :: 'n set). 3 * h\<^sup>2)"
    by (intro sum_mono per)
  also have "\<dots> = 3 * (real CARD('n))\<^sup>2 * h\<^sup>2"
    by (simp add: power2_eq_square)
  finally show "(\<integral>\<omega>. (\<Sum>i\<in>UNIV. (\<omega> i h)\<^sup>2)\<^sup>2
      \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      \<le> 3 * (real CARD('n))\<^sup>2 * h\<^sup>2" .
qed

subsection \<open>The step increment: mean zero\<close>

theorem sbm_xi_mean0:
  fixes S :: "real^'n::finite^'n" and M :: "real^'n^'n" and h :: real
  assumes h0: "0 < h" and L1: "1 \<le> L"
    and SST: "S ** transpose S \<in> sconstraint k L"
  shows sbm_xi_integrable:
    "integrable (pair_law_of h (sbmpair S h)
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      (\<lambda>\<omega>'. trace (M ** (outerp (fst (\<omega>' h) - fst (\<omega>' 0))
        - h *\<^sub>R (S ** transpose S))))"
    and sbm_xi_mean:
    "(\<integral>\<omega>'. trace (M ** (outerp (fst (\<omega>' h) - fst (\<omega>' 0))
        - h *\<^sub>R (S ** transpose S)))
      \<partial>(pair_law_of h (sbmpair S h)
          (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))) = 0"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?\<mu> = "pair_law_of h (sbmpair S h) ?M"
  let ?B = "(path_borel h :: ('n pairpath) measure)"
  let ?\<xi> = "\<lambda>\<omega>' :: 'n pairpath. trace (M ** (outerp
      (fst (\<omega>' h) - fst (\<omega>' 0)) - h *\<^sub>R (S ** transpose S)))"
  let ?g = "\<lambda>\<omega>' :: 'n pairpath. trace (M ** (outerp
      (fst (\<omega>' h)) - snd (\<omega>' h)))"
  have h0': "(0::real) \<le> h" using h0 by simp
  have hI: "h \<in> {0..h}" using h0' by simp
  have mem: "?\<mu> \<in> exit_class k L h (0 :: real^'n)"
    by (rule sbmpair_law_in_paper_pair_class[OF h0' L1 SST])
  have sets\<mu>: "sets ?\<mu> = sets ?B" by simp
  have evh: "(\<lambda>\<omega>' :: 'n pairpath. \<omega>' h) \<in> ?B \<rightarrow>\<^sub>M borel"
    by (rule pair_law_eval_measurable[OF refl])
  have ev0: "(\<lambda>\<omega>' :: 'n pairpath. \<omega>' 0) \<in> ?B \<rightarrow>\<^sub>M borel"
    by (rule pair_law_eval_measurable[OF refl])
  have pairm: "(\<lambda>\<omega>' :: 'n pairpath. (\<omega>' h, \<omega>' 0)) \<in> ?B \<rightarrow>\<^sub>M borel"
    using evh ev0 by (simp add: borel_prod[symmetric])
  have contxi: "(\<lambda>p :: ((real^'n) \<times> (real^'n^'n))
        \<times> ((real^'n) \<times> (real^'n^'n)).
      trace (M ** (outerp (fst (fst p) - fst (snd p))
        - h *\<^sub>R (S ** transpose S)))) \<in> borel_measurable borel"
  proof (intro borel_measurable_continuous_onI)
    have e: "(\<lambda>p :: ((real^'n) \<times> (real^'n^'n))
          \<times> ((real^'n) \<times> (real^'n^'n)).
        trace (M ** (outerp (fst (fst p) - fst (snd p))
          - h *\<^sub>R (S ** transpose S))))
        = (\<lambda>p. \<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. M $ i $ j
            * ((fst (fst p) $ j - fst (snd p) $ j)
                * (fst (fst p) $ i - fst (snd p) $ i)
              - h * (S ** transpose S) $ j $ i))"
      by (rule ext)
        (simp add: trace_def matrix_matrix_mult_def outerp_def
          sum_distrib_left algebra_simps
          sum_subtractf)
    show "continuous_on UNIV (\<lambda>p :: ((real^'n) \<times> (real^'n^'n))
          \<times> ((real^'n) \<times> (real^'n^'n)).
        trace (M ** (outerp (fst (fst p) - fst (snd p))
          - h *\<^sub>R (S ** transpose S))))"
      unfolding e by (intro continuous_intros)
  qed
  have ximeas: "?\<xi> \<in> borel_measurable ?B"
    using measurable_compose[OF pairm contxi] by (simp add: o_def)
  have ximeas\<mu>: "?\<xi> \<in> borel_measurable ?\<mu>"
    using ximeas measurable_cong_sets[OF sets\<mu>[symmetric] refl] by blast
  have contg: "(\<lambda>q :: (real^'n) \<times> (real^'n^'n).
      trace (M ** (outerp (fst q) - snd q))) \<in> borel_measurable borel"
  proof (intro borel_measurable_continuous_onI)
    have e: "(\<lambda>q :: (real^'n) \<times> (real^'n^'n).
        trace (M ** (outerp (fst q) - snd q)))
        = (\<lambda>q. \<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. M $ i $ j
            * (fst q $ j * fst q $ i - snd q $ j $ i))"
      by (rule ext)
        (simp add: trace_def matrix_matrix_mult_def outerp_def
          sum_distrib_left algebra_simps
          sum_subtractf)
    show "continuous_on UNIV (\<lambda>q :: (real^'n) \<times> (real^'n^'n).
        trace (M ** (outerp (fst q) - snd q)))"
      unfolding e by (intro continuous_intros)
  qed
  have gmeas: "?g \<in> borel_measurable ?B"
    using measurable_compose[OF evh contg] by (simp add: o_def)
  have gmeas\<mu>: "?g \<in> borel_measurable ?\<mu>"
    using gmeas measurable_cong_sets[OF sets\<mu>[symmetric] refl] by blast
  have start: "AE \<omega>' in ?\<mu>. fst (\<omega>' 0) = (0 :: real^'n) \<and> snd (\<omega>' 0) = 0"
    using mem unfolding exit_class_def by blast
  have snddet: "AE \<omega>' in ?\<mu>. snd (\<omega>' h) = h *\<^sub>R (S ** transpose S)"
  proof -
    have phim: "sbmpair S h \<in> ?M \<rightarrow>\<^sub>M ?B"
      by (rule sbmpair_measurable[OF h0'])
    have sndm: "(\<lambda>\<omega>' :: 'n pairpath. snd (\<omega>' h)) \<in> ?B \<rightarrow>\<^sub>M borel"
      using evh by (simp add: borel_prod[symmetric])
    have mset: "{\<omega>' \<in> space ?B. snd (\<omega>' h) = h *\<^sub>R (S ** transpose S)}
        \<in> sets ?B"
    proof -
      have "{\<omega>' \<in> space ?B. snd (\<omega>' h) = h *\<^sub>R (S ** transpose S)}
          = (\<lambda>\<omega>' :: 'n pairpath. snd (\<omega>' h))
            -` {h *\<^sub>R (S ** transpose S)} \<inter> space ?B"
        by auto
      then show ?thesis using measurable_sets[OF sndm] by simp
    qed
    have iff: "(AE \<omega>' in ?\<mu>. snd (\<omega>' h) = h *\<^sub>R (S ** transpose S))
        = (AE \<omega> in ?M. snd (sbmpair S h \<omega> h) = h *\<^sub>R (S ** transpose S))"
      unfolding pair_law_of_def by (rule AE_distr_iff[OF phim mset])
    have "AE \<omega> in ?M. snd (sbmpair S h \<omega> h) = h *\<^sub>R (S ** transpose S)"
      by (intro AE_I2) (simp add: sbmpair_apply[OF hI])
    then show ?thesis unfolding iff .
  qed
  have aeq: "AE \<omega>' in ?\<mu>. ?\<xi> \<omega>' = ?g \<omega>'"
    using start snddet by eventually_elim simp
  have int_inner: "integrable ?\<mu>
      (\<lambda>\<omega>'. outerp (fst (\<omega>' h)) - snd (\<omega>' h))"
    by (rule exit_class_compensated_integrable[OF mem hI])
  have intg: "integrable ?\<mu> ?g"
    by (rule integrable_bounded_linear[OF bounded_linear_trace_mult_left int_inner])
  show "integrable ?\<mu> ?\<xi>"
    by (rule integrable_cong_AE[THEN iffD2, OF ximeas\<mu> gmeas\<mu> aeq intg])
  have op0: "outerp (0 :: real^'n) = 0"
    by (simp add: outerp_def vec_eq_iff zero_vec_def)
  have "(\<integral>\<omega>'. ?\<xi> \<omega>' \<partial>?\<mu>) = (\<integral>\<omega>'. ?g \<omega>' \<partial>?\<mu>)"
    by (rule integral_cong_AE[OF ximeas\<mu> gmeas\<mu> aeq])
  also have "\<dots> = trace (M ** (\<integral>\<omega>'. outerp (fst (\<omega>' h)) - snd (\<omega>' h)
      \<partial>?\<mu>))"
    by (rule integral_bounded_linear[OF bounded_linear_trace_mult_left int_inner])
  also have "\<dots> = trace (M ** outerp (0 :: real^'n))"
    by (simp add: exit_class_compensated_mean[OF mem hI])
  also have "\<dots> = 0"
    unfolding op0 by (rule trace_mult_zero_right)
  finally show "(\<integral>\<omega>'. ?\<xi> \<omega>' \<partial>?\<mu>) = 0" .
qed

subsection \<open>The step increment: variance of order \<open>h\<^sup>2\<close>\<close>

text \<open>\<open>diff_sq_le_double\<close> is \<open>sq_diff_le\<close> from
  @{theory Continuous_Time_Martingales.Quadratic_Variation}.\<close>

theorem sbm_xi_sq_bound:
  fixes S :: "real^'n::finite^'n" and M :: "real^'n^'n" and h :: real
  defines "Cmm \<equiv> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>)"
  defines "Cs \<equiv> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>S $ i $ j\<bar>)"
  defines "n' \<equiv> real (CARD('n))"
  assumes h0: "0 < h" and L1: "1 \<le> L"
    and SST: "S ** transpose S \<in> sconstraint k L"
  shows sbm_xi_sq_integrable:
    "integrable (pair_law_of h (sbmpair S h)
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      (\<lambda>\<omega>'. (trace (M ** (outerp (fst (\<omega>' h) - fst (\<omega>' 0))
        - h *\<^sub>R (S ** transpose S))))\<^sup>2)"
    and sbm_xi_sq_integral:
    "(\<integral>\<omega>'. (trace (M ** (outerp (fst (\<omega>' h) - fst (\<omega>' 0))
        - h *\<^sub>R (S ** transpose S))))\<^sup>2
      \<partial>(pair_law_of h (sbmpair S h)
          (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)))
      \<le> (6 * (Cmm * Cs\<^sup>2)\<^sup>2 * n'\<^sup>2 + 2 * (n'\<^sup>2 * Cmm * L)\<^sup>2) * h\<^sup>2"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?\<mu> = "pair_law_of h (sbmpair S h) ?M"
  let ?B = "(path_borel h :: ('n pairpath) measure)"
  let ?\<xi> = "\<lambda>\<omega>' :: 'n pairpath. trace (M ** (outerp
      (fst (\<omega>' h) - fst (\<omega>' 0)) - h *\<^sub>R (S ** transpose S)))"
  let ?V = "\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. (\<chi> i. \<omega> i h) :: real^'n"
  let ?R = "\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. (\<Sum>i\<in>UNIV. (\<omega> i h)\<^sup>2)"
  define b where "b = trace (M ** (S ** transpose S))"
  define CA where "CA = 2 * (Cmm * Cs\<^sup>2)\<^sup>2"
  define CB where "CB = 2 * (n'\<^sup>2 * Cmm * L)\<^sup>2"
  have h0': "(0::real) \<le> h" using h0 by simp
  have hI: "h \<in> {0..h}" using h0' by simp
  have z0: "(0::real) \<in> {0..h}" using h0' by simp
  have L0: "0 \<le> L" using L1 by simp
  have Cmm0: "0 \<le> Cmm" unfolding Cmm_def by (intro sum_nonneg) simp_all
  have Cs0: "0 \<le> Cs" unfolding Cs_def by (intro sum_nonneg) simp_all
  have CA0: "0 \<le> CA" unfolding CA_def by simp
  have CB0: "0 \<le> CB" unfolding CB_def by simp
  interpret BMPP: prob_space ?M by (rule prob_space_bm_paths)
  \<comment> \<open>measurability of the squared increment functional\<close>
  have sets\<mu>: "sets ?\<mu> = sets ?B" by simp
  have xim\<mu>: "?\<xi> \<in> borel_measurable ?\<mu>"
    by (rule borel_measurable_integrable[OF sbm_xi_integrable[OF h0 L1 SST]])
  have ximeas: "?\<xi> \<in> borel_measurable ?B"
    using xim\<mu> measurable_cong_sets[OF sets\<mu> refl] by blast
  have xi2meas: "(\<lambda>\<omega>'. (?\<xi> \<omega>')\<^sup>2) \<in> borel_measurable ?B"
    by (intro borel_measurable_power ximeas)
  have phim: "sbmpair S h \<in> ?M \<rightarrow>\<^sub>M ?B"
    by (rule sbmpair_measurable[OF h0'])
  have xi2measM: "(\<lambda>\<omega>. (?\<xi> (sbmpair S h \<omega>))\<^sup>2) \<in> borel_measurable ?M"
    using measurable_compose[OF phim xi2meas] by (simp add: o_def)
  \<comment> \<open>the increment is the matrix image of the coordinate vector, a.e.\<close>
  have aeV: "AE \<omega> in ?M.
      fst (sbmpair S h \<omega> h) - fst (sbmpair S h \<omega> 0) = S *v ?V \<omega>"
  proof -
    have a1: "AE \<omega> in ?M. cbmX (0 :: real^'n) h \<omega> = bmX 0 h \<omega>"
      by (intro cbmX_ae_eq) (use h0' in simp)
    have a2: "AE \<omega> in ?M. cbmX (0 :: real^'n) 0 \<omega> = bmX 0 0 \<omega>"
      by (intro cbmX_ae_eq) simp
    have a3: "AE \<omega> in ?M. bmX (0 :: real^'n) 0 \<omega> = 0"
      by (rule bmX_start)
    show ?thesis
      using a1 a2 a3
    proof eventually_elim
      case (elim \<omega>)
      have "fst (sbmpair S h \<omega> h) - fst (sbmpair S h \<omega> 0)
          = S *v cbmX (0 :: real^'n) h \<omega> - S *v cbmX (0 :: real^'n) 0 \<omega>"
        by (simp add: sbmpair_apply[OF hI] sbmpair_apply[OF z0])
      also have "\<dots> = S *v (cbmX (0 :: real^'n) h \<omega>
          - cbmX (0 :: real^'n) 0 \<omega>)"
        by (simp add: matrix_vector_mult_diff_distrib)
      also have "\<dots> = S *v bmX (0 :: real^'n) h \<omega>"
        using elim by simp
      also have "\<dots> = S *v ?V \<omega>"
        by (simp add: bmX_def)
      finally show ?case .
    qed
  qed
  \<comment> \<open>uniform pointwise bounds\<close>
  have qb: "\<bar>(S *v v) \<bullet> (M *v (S *v v))\<bar> \<le> Cmm * Cs\<^sup>2 * (v \<bullet> v)"
    for v :: "real^'n"
  proof -
    have "\<bar>(S *v v) \<bullet> (M *v (S *v v))\<bar>
        \<le> norm (S *v v) * norm (M *v (S *v v))"
      by (rule Cauchy_Schwarz_ineq2)
    also have "\<dots> \<le> norm (S *v v) * (Cmm * norm (S *v v))"
      unfolding Cmm_def
      by (intro mult_left_mono matvec_norm_le) simp
    also have "\<dots> = Cmm * (norm (S *v v))\<^sup>2"
      by (simp add: power2_eq_square algebra_simps)
    also have "\<dots> \<le> Cmm * (Cs * norm v)\<^sup>2"
      unfolding Cs_def
      by (intro mult_left_mono power_mono matvec_norm_le)
        (simp_all add: Cmm_def[symmetric] Cmm0)
    also have "\<dots> = Cmm * Cs\<^sup>2 * (v \<bullet> v)"
      by (simp add: power2_norm_eq_inner algebra_simps)
    finally show ?thesis .
  qed
  have bb: "\<bar>b\<bar> \<le> n'\<^sup>2 * Cmm * L"
  proof -
    define col where "col = (\<lambda>j. (\<chi> i. S $ i $ j) :: real^'n)"
    have Se: "S = (\<chi> i j. col j $ i)"
      unfolding col_def by (simp add: vec_eq_iff)
    have deco: "S ** transpose S = (\<Sum>j\<in>UNIV. outerp (col j))"
      using Se cols_mult_transpose by blast
    have beq: "b = (\<Sum>j\<in>UNIV. col j \<bullet> (M *v col j))"
      unfolding b_def deco by (simp add: trace_mult_outerp_sum)
    have per: "\<bar>col j \<bullet> (M *v col j)\<bar> \<le> Cmm * (n' * L)" for j
    proof -
      have "\<bar>col j \<bullet> (M *v col j)\<bar> \<le> norm (col j) * norm (M *v col j)"
        by (rule Cauchy_Schwarz_ineq2)
      also have "\<dots> \<le> norm (col j) * (Cmm * norm (col j))"
        unfolding Cmm_def by (intro mult_left_mono matvec_norm_le) simp
      also have "\<dots> = Cmm * (norm (col j))\<^sup>2"
        by (simp add: power2_eq_square algebra_simps)
      also have "\<dots> \<le> Cmm * (n' * L)"
      proof (intro mult_left_mono Cmm0)
        have "(norm (col j))\<^sup>2 = (\<Sum>i\<in>UNIV. (S $ i $ j)\<^sup>2)"
          unfolding col_def
          by (simp add: power2_norm_eq_inner inner_vec_def
              power2_eq_square[of "S $ _ $ _"])
        also have "\<dots> \<le> (\<Sum>i\<in>(UNIV :: 'n set). L)"
        proof (rule sum_mono)
          fix i :: 'n
          have "(S $ i $ j)\<^sup>2 = \<bar>S $ i $ j\<bar>\<^sup>2" by simp
          also have "\<dots> \<le> (sqrt L)\<^sup>2"
            using sbm_entry_bound[OF SST, of i j]
            by (intro power_mono) simp_all
          also have "\<dots> = L" using L0 by simp
          finally show "(S $ i $ j)\<^sup>2 \<le> L" .
        qed
        also have "\<dots> = n' * L" unfolding n'_def by simp
        finally show "(norm (col j))\<^sup>2 \<le> n' * L" .
      qed
      finally show ?thesis .
    qed
    have "\<bar>b\<bar> \<le> (\<Sum>j\<in>UNIV. \<bar>col j \<bullet> (M *v col j)\<bar>)"
      unfolding beq by (rule sum_abs)
    also have "\<dots> \<le> (\<Sum>j\<in>(UNIV :: 'n set). Cmm * (n' * L))"
      by (intro sum_mono per)
    also have "\<dots> = n' * (Cmm * (n' * L))" unfolding n'_def by simp
    also have "\<dots> = n'\<^sup>2 * Cmm * L"
      by (simp add: power2_eq_square algebra_simps)
    finally show ?thesis .
  qed
  have Vsq: "?V \<omega> \<bullet> ?V \<omega> = ?R \<omega>" for \<omega> :: "'n \<Rightarrow> real \<Rightarrow> real"
    by (simp add: inner_vec_def power2_eq_square)
  \<comment> \<open>the pointwise domination\<close>
  have ptw: "AE \<omega> in ?M. (?\<xi> (sbmpair S h \<omega>))\<^sup>2
      \<le> CA * (?R \<omega>)\<^sup>2 + CB * h\<^sup>2"
    using aeV
  proof eventually_elim
    case (elim \<omega>)
    have xieq: "?\<xi> (sbmpair S h \<omega>)
        = (S *v ?V \<omega>) \<bullet> (M *v (S *v ?V \<omega>)) - h * b"
    proof -
      have "?\<xi> (sbmpair S h \<omega>) = trace (M ** (outerp (S *v ?V \<omega>)
          - h *\<^sub>R (S ** transpose S)))"
        using elim by simp
      also have "\<dots> = trace (M ** outerp (S *v ?V \<omega>))
          - trace (M ** (h *\<^sub>R (S ** transpose S)))"
        by (simp add: trace_mult_diff)
      also have "trace (M ** (h *\<^sub>R (S ** transpose S))) = h * b"
        unfolding b_def by (simp add: matmul_scaleR_right trace_scaleR)
      also have "trace (M ** outerp (S *v ?V \<omega>))
          = (S *v ?V \<omega>) \<bullet> (M *v (S *v ?V \<omega>))"
        by (rule trace_mult_outerp)
      finally show ?thesis by simp
    qed
    have step1: "(?\<xi> (sbmpair S h \<omega>))\<^sup>2
        \<le> 2 * ((S *v ?V \<omega>) \<bullet> (M *v (S *v ?V \<omega>)))\<^sup>2 + 2 * (h * b)\<^sup>2"
      unfolding xieq by (rule sq_diff_le)
    have step2: "((S *v ?V \<omega>) \<bullet> (M *v (S *v ?V \<omega>)))\<^sup>2
        \<le> (Cmm * Cs\<^sup>2)\<^sup>2 * (?R \<omega>)\<^sup>2"
    proof -
      have nnq: "0 \<le> Cmm * Cs\<^sup>2 * (?V \<omega> \<bullet> ?V \<omega>)"
        using Cmm0 Cs0 by (intro mult_nonneg_nonneg) simp_all
      have "((S *v ?V \<omega>) \<bullet> (M *v (S *v ?V \<omega>)))\<^sup>2
          = \<bar>(S *v ?V \<omega>) \<bullet> (M *v (S *v ?V \<omega>))\<bar>\<^sup>2" by simp
      also have "\<dots> \<le> (Cmm * Cs\<^sup>2 * (?V \<omega> \<bullet> ?V \<omega>))\<^sup>2"
        using qb[of "?V \<omega>"] nnq by (intro power_mono) simp_all
      also have "\<dots> = (Cmm * Cs\<^sup>2)\<^sup>2 * (?R \<omega>)\<^sup>2"
        unfolding Vsq by (simp add: power_mult_distrib)
      finally show ?thesis .
    qed
    have step3: "(h * b)\<^sup>2 \<le> (n'\<^sup>2 * Cmm * L)\<^sup>2 * h\<^sup>2"
    proof -
      have nb: "0 \<le> n'\<^sup>2 * Cmm * L"
        using Cmm0 L0 by (intro mult_nonneg_nonneg) simp_all
      have "(h * b)\<^sup>2 = h\<^sup>2 * \<bar>b\<bar>\<^sup>2"
        by (simp add: power_mult_distrib)
      also have "\<dots> \<le> h\<^sup>2 * (n'\<^sup>2 * Cmm * L)\<^sup>2"
        using bb nb by (intro mult_left_mono power_mono) simp_all
      finally show ?thesis by (simp add: algebra_simps)
    qed
    show ?case using step1 step2 step3
      unfolding CA_def CB_def by linarith
  qed
  \<comment> \<open>integrability of the dominating function and of the square\<close>
  have Rint: "integrable ?M (\<lambda>\<omega>. (?R \<omega>)\<^sup>2)"
    by (rule bm_R2_integrable[OF h0])
  have domint: "integrable ?M (\<lambda>\<omega>. CA * (?R \<omega>)\<^sup>2 + CB * h\<^sup>2)"
    by (intro Bochner_Integration.integrable_add integrable_cmult Rint
        BMP.integrable_const)
  have int2M: "integrable ?M (\<lambda>\<omega>. (?\<xi> (sbmpair S h \<omega>))\<^sup>2)"
  proof (rule Bochner_Integration.integrable_bound[OF domint xi2measM])
    show "AE \<omega> in ?M. norm ((?\<xi> (sbmpair S h \<omega>))\<^sup>2)
        \<le> norm (CA * (?R \<omega>)\<^sup>2 + CB * h\<^sup>2)"
      using ptw
    proof eventually_elim
      case (elim \<omega>)
      have "0 \<le> CA * (?R \<omega>)\<^sup>2 + CB * h\<^sup>2"
        using CA0 CB0 by (intro add_nonneg_nonneg mult_nonneg_nonneg)
          simp_all
      then show ?case using elim by simp
    qed
  qed
  show "integrable ?\<mu> (\<lambda>\<omega>'. (?\<xi> \<omega>')\<^sup>2)"
    unfolding pair_law_of_def
    by (subst integrable_distr_eq[OF phim xi2meas]) (rule int2M)
  \<comment> \<open>the integral bound\<close>
  have "(\<integral>\<omega>'. (?\<xi> \<omega>')\<^sup>2 \<partial>?\<mu>) = (\<integral>\<omega>. (?\<xi> (sbmpair S h \<omega>))\<^sup>2 \<partial>?M)"
    unfolding pair_law_of_def by (rule integral_distr[OF phim xi2meas])
  also have "\<dots> \<le> (\<integral>\<omega>. CA * (?R \<omega>)\<^sup>2 + CB * h\<^sup>2 \<partial>?M)"
    by (rule integral_mono_AE[OF int2M domint ptw])
  also have "\<dots> = CA * (\<integral>\<omega>. (?R \<omega>)\<^sup>2 \<partial>?M) + CB * h\<^sup>2"
  proof -
    have ic: "integrable ?M (\<lambda>\<omega>. CA * (?R \<omega>)\<^sup>2)"
      by (rule integrable_cmult[OF Rint])
    have icc: "integrable ?M (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. CB * h\<^sup>2)"
      by simp
    have "(\<integral>\<omega>. CA * (?R \<omega>)\<^sup>2 + CB * h\<^sup>2 \<partial>?M)
        = (\<integral>\<omega>. CA * (?R \<omega>)\<^sup>2 \<partial>?M) + (\<integral>\<omega>. CB * h\<^sup>2 \<partial>?M)"
      by (rule Bochner_Integration.integral_add[OF ic icc])
    also have "(\<integral>\<omega>. CA * (?R \<omega>)\<^sup>2 \<partial>?M) = CA * (\<integral>\<omega>. (?R \<omega>)\<^sup>2 \<partial>?M)"
      by (rule integral_cmult[OF Rint])
    also have "(\<integral>\<omega>. CB * h\<^sup>2 \<partial>?M) = measure ?M (space ?M) *\<^sub>R (CB * h\<^sup>2)"
      by (rule lebesgue_integral_const)
    finally show ?thesis
      by (simp add: BMP.prob_space)
  qed
  also have "\<dots> \<le> CA * (3 * n'\<^sup>2 * h\<^sup>2) + CB * h\<^sup>2"
  proof -
    have "(\<integral>\<omega>. (?R \<omega>)\<^sup>2 \<partial>?M) \<le> 3 * (real CARD('n))\<^sup>2 * h\<^sup>2"
      by (rule bm_R2_integral[OF h0])
    then show ?thesis
      using CA0 unfolding n'_def by (intro add_right_mono mult_left_mono)
  qed
  also have "\<dots> = (6 * (Cmm * Cs\<^sup>2)\<^sup>2 * n'\<^sup>2 + 2 * (n'\<^sup>2 * Cmm * L)\<^sup>2) * h\<^sup>2"
    unfolding CA_def CB_def by (simp add: algebra_simps)
  finally show "(\<integral>\<omega>'. (?\<xi> \<omega>')\<^sup>2 \<partial>?\<mu>)
      \<le> (6 * (Cmm * Cs\<^sup>2)\<^sup>2 * n'\<^sup>2 + 2 * (n'\<^sup>2 * Cmm * L)\<^sup>2) * h\<^sup>2" .
qed

subsection \<open>A volatility-uniform variance constant\<close>

definition xiC :: "real^'n::finite^'n \<Rightarrow> real \<Rightarrow> real" where
  "xiC M L = (let n' = real (CARD('n));
      Cmm = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>)
    in 6 * (Cmm * (n'\<^sup>2 * sqrt L)\<^sup>2)\<^sup>2 * n'\<^sup>2 + 2 * (n'\<^sup>2 * Cmm * L)\<^sup>2)"

lemma xiC_nonneg: "0 \<le> xiC M L"
proof -
  have "0 \<le> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>)"
    by (intro sum_nonneg) simp_all
  then show ?thesis
    unfolding xiC_def Let_def
    by (intro add_nonneg_nonneg mult_nonneg_nonneg zero_le_power2) simp_all
qed

corollary sbm_xi_sq_bound_uniform:
  fixes S :: "real^'n::finite^'n" and M :: "real^'n^'n" and h :: real
  assumes h0: "0 < h" and L1: "1 \<le> L"
    and SST: "S ** transpose S \<in> sconstraint k L"
  shows "(\<integral>\<omega>'. (trace (M ** (outerp (fst (\<omega>' h) - fst (\<omega>' 0))
        - h *\<^sub>R (S ** transpose S))))\<^sup>2
      \<partial>(pair_law_of h (sbmpair S h)
          (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)))
      \<le> xiC M L * h\<^sup>2"
proof -
  define Cmm where "Cmm = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>)"
  define Cs where "Cs = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>S $ i $ j\<bar>)"
  define n' where "n' = real (CARD('n))"
  have Cmm0: "0 \<le> Cmm" unfolding Cmm_def by (intro sum_nonneg) simp_all
  have Cs0: "0 \<le> Cs" unfolding Cs_def by (intro sum_nonneg) simp_all
  have Csle: "Cs \<le> n'\<^sup>2 * sqrt L"
  proof -
    have "Cs \<le> (\<Sum>i\<in>(UNIV :: 'n set). \<Sum>j\<in>(UNIV :: 'n set). sqrt L)"
      unfolding Cs_def by (intro sum_mono sbm_entry_bound[OF SST])
    also have "\<dots> = n'\<^sup>2 * sqrt L"
      unfolding n'_def by (simp add: power2_eq_square mult_ac)
    finally show ?thesis .
  qed
  have base: "(\<integral>\<omega>'. (trace (M ** (outerp (fst (\<omega>' h) - fst (\<omega>' 0))
        - h *\<^sub>R (S ** transpose S))))\<^sup>2
      \<partial>(pair_law_of h (sbmpair S h)
          (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)))
      \<le> (6 * (Cmm * Cs\<^sup>2)\<^sup>2 * n'\<^sup>2 + 2 * (n'\<^sup>2 * Cmm * L)\<^sup>2) * h\<^sup>2"
    unfolding Cmm_def Cs_def n'_def by (rule sbm_xi_sq_bound[OF h0 L1 SST])
  have mono1: "Cmm * Cs\<^sup>2 \<le> Cmm * (n'\<^sup>2 * sqrt L)\<^sup>2"
    by (intro mult_left_mono power_mono Csle Cs0 Cmm0)
  have mono2: "(Cmm * Cs\<^sup>2)\<^sup>2 \<le> (Cmm * (n'\<^sup>2 * sqrt L)\<^sup>2)\<^sup>2"
    by (intro power_mono mono1 mult_nonneg_nonneg Cmm0) simp_all
  have mono3: "6 * (Cmm * Cs\<^sup>2)\<^sup>2 * n'\<^sup>2 \<le> 6 * (Cmm * (n'\<^sup>2 * sqrt L)\<^sup>2)\<^sup>2 * n'\<^sup>2"
    by (intro mult_right_mono mult_left_mono mono2) simp_all
  have xiCe: "xiC M L = 6 * (Cmm * (n'\<^sup>2 * sqrt L)\<^sup>2)\<^sup>2 * n'\<^sup>2
      + 2 * (n'\<^sup>2 * Cmm * L)\<^sup>2"
    unfolding xiC_def Let_def Cmm_def n'_def by (rule refl)
  have tot: "6 * (Cmm * Cs\<^sup>2)\<^sup>2 * n'\<^sup>2 + 2 * (n'\<^sup>2 * Cmm * L)\<^sup>2 \<le> xiC M L"
    unfolding xiCe using mono3 by linarith
  have h2: "(0::real) \<le> h\<^sup>2" by simp
  from base mult_right_mono[OF tot h2] show ?thesis by linarith
qed

subsection \<open>The compensated grid functional of the Euler process\<close>

definition euXi :: "(real^'n::finite \<Rightarrow> real^'n^'n) \<Rightarrow> real^'n^'n \<Rightarrow> real
    \<Rightarrow> nat \<Rightarrow> 'n pairpath \<Rightarrow> real" where
  "euXi SF M h m \<omega> = (\<Sum>j<m. trace (M ** (outerp
      (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h)))
      - h *\<^sub>R (SF (fst (\<omega> (real j * h)))
          ** transpose (SF (fst (\<omega> (real j * h))))))))"


lemma euXi_measurable:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n" and M :: "real^'n^'n"
    and h :: real
  assumes SFc: "continuous_on UNIV SF"
  shows "euXi SF M h m \<in> borel_measurable
      (path_borel T :: ('n pairpath) measure)"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  have tm: "(\<lambda>\<omega> :: 'n pairpath. trace (M ** (outerp
      (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h)))
      - h *\<^sub>R (SF (fst (\<omega> (real j * h)))
          ** transpose (SF (fst (\<omega> (real j * h))))))))
      \<in> borel_measurable ?B" for j
  proof -
    have evu: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (real (Suc j) * h)) \<in> ?B \<rightarrow>\<^sub>M borel"
      by (rule pair_law_eval_measurable[OF refl])
    have evv: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (real j * h)) \<in> ?B \<rightarrow>\<^sub>M borel"
      by (rule pair_law_eval_measurable[OF refl])
    have pairm: "(\<lambda>\<omega> :: 'n pairpath.
        (\<omega> (real (Suc j) * h), \<omega> (real j * h))) \<in> ?B \<rightarrow>\<^sub>M borel"
      using evu evv by (simp add: borel_prod[symmetric])
    have cm: "(\<lambda>ab :: ((real^'n) \<times> (real^'n^'n))
          \<times> ((real^'n) \<times> (real^'n^'n)).
        trace (M ** (outerp (fst (fst ab) - fst (snd ab))
          - h *\<^sub>R (SF (fst (snd ab)) ** transpose (SF (fst (snd ab)))))))
        \<in> borel_measurable borel"
      by (rule borel_measurable_continuous_onI[OF euXi_term_cont[OF SFc]])
    show ?thesis using measurable_compose[OF pairm cm] by simp
  qed
  show ?thesis unfolding euXi_def by (intro borel_measurable_sum tm)
qed

lemma euXi_pglue_split:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n" and M :: "real^'n^'n"
    and \<omega> \<omega>' :: "'n pairpath" and h :: real
  assumes h0: "0 \<le> h"
  shows "euXi SF M h (Suc (Suc N)) (pglue (real (Suc N) * h)
        (real (Suc (Suc N)) * h) \<omega> \<omega>')
      = euXi SF M h (Suc N) \<omega>
        + trace (M ** (outerp (fst (\<omega>' h) - fst (\<omega>' 0))
            - h *\<^sub>R (SF (fst (\<omega> (real (Suc N) * h)))
                ** transpose (SF (fst (\<omega> (real (Suc N) * h)))))))"
proof -
  let ?r = "real (Suc N) * h"
  let ?T = "real (Suc (Suc N)) * h"
  let ?g = "pglue ?r ?T \<omega> \<omega>'"
  have mem: "real j * h \<in> {0..?T}" if le: "j \<le> Suc (Suc N)" for j
  proof -
    have a: "0 \<le> real j * h"
      by (intro mult_nonneg_nonneg h0) simp_all
    have b: "real j * h \<le> ?T"
      using le h0 by (intro mult_right_mono) simp_all
    show ?thesis using a b by simp
  qed
  have prefl: "?g (real j * h) = \<omega> (real j * h)" if j: "j \<le> Suc N" for j
  proof (rule pglue_le)
    show "real j * h \<in> {0..?T}" using j by (intro mem) simp
    show "real j * h \<le> ?r" using j h0 by (intro mult_right_mono) simp_all
  qed
  have rleT: "?r \<le> ?T" using h0 by (intro mult_right_mono) simp_all
  have Tmem: "?T \<in> {0..?T}" by (rule mem) simp
  have gT: "?g ?T = \<omega> ?r + (\<omega>' (?T - ?r) - \<omega>' 0)"
    by (rule pglue_ge[OF Tmem rleT])
  have gr: "?g ?r = \<omega> ?r" by (rule prefl) simp
  have Tr: "?T - ?r = h" by (simp add: algebra_simps)
  have head: "fst (?g ?T) - fst (?g ?r) = fst (\<omega>' h) - fst (\<omega>' 0)"
    unfolding gT gr Tr by simp
  have "euXi SF M h (Suc (Suc N)) ?g
      = (\<Sum>j<Suc N. trace (M ** (outerp
          (fst (?g (real (Suc j) * h)) - fst (?g (real j * h)))
          - h *\<^sub>R (SF (fst (?g (real j * h)))
              ** transpose (SF (fst (?g (real j * h))))))))
        + trace (M ** (outerp
          (fst (?g (real (Suc (Suc N)) * h)) - fst (?g (real (Suc N) * h)))
          - h *\<^sub>R (SF (fst (?g (real (Suc N) * h)))
              ** transpose (SF (fst (?g (real (Suc N) * h)))))))"
    unfolding euXi_def by (subst sum.lessThan_Suc) (simp add: add.commute)
  also have "(\<Sum>j<Suc N. trace (M ** (outerp
        (fst (?g (real (Suc j) * h)) - fst (?g (real j * h)))
        - h *\<^sub>R (SF (fst (?g (real j * h)))
            ** transpose (SF (fst (?g (real j * h))))))))
      = euXi SF M h (Suc N) \<omega>"
    unfolding euXi_def
  proof (rule sum.cong[OF refl])
    fix j assume "j \<in> {..<Suc N}"
    then have j1: "Suc j \<le> Suc N" and j2: "j \<le> Suc N" by auto
    show "trace (M ** (outerp
        (fst (?g (real (Suc j) * h)) - fst (?g (real j * h)))
        - h *\<^sub>R (SF (fst (?g (real j * h)))
            ** transpose (SF (fst (?g (real j * h)))))))
      = trace (M ** (outerp
        (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h)))
        - h *\<^sub>R (SF (fst (\<omega> (real j * h)))
            ** transpose (SF (fst (\<omega> (real j * h)))))))"
      by (simp only: prefl[OF j1] prefl[OF j2])
  qed
  also have "trace (M ** (outerp
        (fst (?g (real (Suc (Suc N)) * h)) - fst (?g (real (Suc N) * h)))
        - h *\<^sub>R (SF (fst (?g (real (Suc N) * h)))
            ** transpose (SF (fst (?g (real (Suc N) * h)))))))
      = trace (M ** (outerp (fst (\<omega>' h) - fst (\<omega>' 0))
          - h *\<^sub>R (SF (fst (\<omega> ?r)) ** transpose (SF (fst (\<omega> ?r))))))"
  proof -
    have "fst (?g ?T) - fst (?g ?r) = fst (\<omega>' h) - fst (\<omega>' 0)"
      by (rule head)
    moreover have "fst (?g ?r) = fst (\<omega> ?r)" unfolding gr by (rule refl)
    ultimately show ?thesis by simp
  qed
  finally show ?thesis .
qed

subsection \<open>The second moment of the grid functional grows linearly\<close>

theorem eulerp_Xi_sq_bound:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n" and M :: "real^'n^'n"
    and x :: "real^'n" and h :: real
  assumes h0: "0 < h" and L1: "1 \<le> L"
    and SFc: "continuous_on UNIV SF"
    and SFs: "\<And>z. SF z ** transpose (SF z) \<in> sconstraint k L"
  shows "integrable (eulerp SF x h N) (\<lambda>\<omega>. (euXi SF M h (Suc N) \<omega>)\<^sup>2)
      \<and> (\<integral>\<omega>. (euXi SF M h (Suc N) \<omega>)\<^sup>2 \<partial>(eulerp SF x h N))
        \<le> real (Suc N) * xiC M L * h\<^sup>2"
proof (induction N)
  case 0
  have h0': "(0::real) \<le> h" using h0 by simp
  let ?\<mu>0 = "pair_law_of h (sbmpair (SF x) h)
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)"
  let ?Bh = "(path_borel h :: ('n pairpath) measure)"
  note SFsx = SFs[of x]
  have E0: "eulerp SF x h 0 = pshift_law h x ?\<mu>0" by simp
  have sets\<mu>: "sets ?\<mu>0 = sets ?Bh" by simp
  have shm: "pshift h x \<in> ?\<mu>0 \<rightarrow>\<^sub>M ?Bh"
    using pshift_measurable[OF h0'] measurable_cong_sets[OF sets\<mu> refl]
    by blast
  have Gm2: "(\<lambda>\<omega>. (euXi SF M h (Suc 0) \<omega>)\<^sup>2) \<in> borel_measurable ?Bh"
    by (intro borel_measurable_power euXi_measurable[OF SFc])
  have st: "AE \<omega> in ?\<mu>0. fst (\<omega> 0) = (0 :: real^'n)"
    using sbmpair_law_start[OF h0', of "SF x"]
    by (rule eventually_mono) simp
  have cong: "AE \<omega> in ?\<mu>0. (euXi SF M h (Suc 0) (pshift h x \<omega>))\<^sup>2
      = (trace (M ** (outerp (fst (\<omega> h) - fst (\<omega> 0))
          - h *\<^sub>R (SF x ** transpose (SF x)))))\<^sup>2"
    using st
  proof eventually_elim
    case (elim \<omega>)
    have m1: "h \<in> {0..h}" using h0' by simp
    have m2: "(0::real) \<in> {0..h}" using h0' by simp
    have "euXi SF M h (Suc 0) (pshift h x \<omega>)
        = trace (M ** (outerp
            (fst (pshift h x \<omega> h) - fst (pshift h x \<omega> 0))
            - h *\<^sub>R (SF (fst (pshift h x \<omega> 0))
                ** transpose (SF (fst (pshift h x \<omega> 0))))))"
      unfolding euXi_def by simp
    also have "\<dots> = trace (M ** (outerp (fst (\<omega> h) - fst (\<omega> 0))
        - h *\<^sub>R (SF (x + fst (\<omega> 0)) ** transpose (SF (x + fst (\<omega> 0))))))"
      by (simp add: pshift_fst[OF m1] pshift_fst[OF m2])
    also have "\<dots> = trace (M ** (outerp (fst (\<omega> h) - fst (\<omega> 0))
        - h *\<^sub>R (SF x ** transpose (SF x))))"
      using elim by simp
    finally show ?case by simp
  qed
  have measL: "(\<lambda>\<omega>. (euXi SF M h (Suc 0) (pshift h x \<omega>))\<^sup>2)
      \<in> borel_measurable ?\<mu>0"
    by (rule measurable_compose[OF shm Gm2])
  have measR: "(\<lambda>\<omega>. (trace (M ** (outerp (fst (\<omega> h) - fst (\<omega> 0))
      - h *\<^sub>R (SF x ** transpose (SF x)))))\<^sup>2) \<in> borel_measurable ?\<mu>0"
    by (intro borel_measurable_power
        borel_measurable_integrable[OF sbm_xi_integrable[OF h0 L1 SFsx]])
  have iB: "integrable (eulerp SF x h 0) (\<lambda>\<omega>. (euXi SF M h (Suc 0) \<omega>)\<^sup>2)"
  proof -
    have "integrable ?\<mu>0 (\<lambda>\<omega>. (euXi SF M h (Suc 0) (pshift h x \<omega>))\<^sup>2)"
      using integrable_cong_AE[OF measL measR cong]
        sbm_xi_sq_integrable[OF h0 L1 SFsx] by blast
    then show ?thesis
      unfolding E0 pshift_law_def
      using integrable_distr_eq[OF shm Gm2] by blast
  qed
  have bB: "(\<integral>\<omega>. (euXi SF M h (Suc 0) \<omega>)\<^sup>2 \<partial>(eulerp SF x h 0))
      \<le> real (Suc 0) * xiC M L * h\<^sup>2"
  proof -
    have "(\<integral>\<omega>. (euXi SF M h (Suc 0) \<omega>)\<^sup>2 \<partial>(eulerp SF x h 0))
        = (\<integral>\<omega>. (euXi SF M h (Suc 0) (pshift h x \<omega>))\<^sup>2 \<partial>?\<mu>0)"
      unfolding E0 pshift_law_def by (rule integral_distr[OF shm Gm2])
    also have "\<dots> = (\<integral>\<omega>. (trace (M ** (outerp (fst (\<omega> h) - fst (\<omega> 0))
        - h *\<^sub>R (SF x ** transpose (SF x)))))\<^sup>2 \<partial>?\<mu>0)"
      by (rule integral_cong_AE[OF measL measR cong])
    also have "\<dots> \<le> xiC M L * h\<^sup>2"
      by (rule sbm_xi_sq_bound_uniform[OF h0 L1 SFsx])
    finally show ?thesis by simp
  qed
  show ?case using iB bB by blast
next
  case (Suc N)
  have h0': "(0::real) \<le> h" using h0 by simp
  define r where "r = real (Suc N) * h"
  define T' where "T' = real (Suc (Suc N)) * h"
  let ?Q = "eulerp SF x h N"
  let ?Br = "(path_borel r :: ('n pairpath) measure)"
  let ?Bt = "(path_borel T' :: ('n pairpath) measure)"
  let ?MR = "(path_borel (T' - r) :: ('n pairpath) measure)"
  let ?K = "\<lambda>\<omega> :: 'n pairpath.
      pair_law_of h (sbmpair (SF (fst (\<omega> r))) h) bm_paths"
  let ?A = "euXi SF M h (Suc N)"
  let ?xi = "\<lambda>\<omega> \<omega>' :: 'n pairpath. trace (M ** (outerp
      (fst (\<omega>' h) - fst (\<omega>' 0))
      - h *\<^sub>R (SF (fst (\<omega> r)) ** transpose (SF (fst (\<omega> r))))))"
  have hT: "T' - r = h" unfolding r_def T'_def by (simp add: algebra_simps)
  have r0: "0 \<le> r" unfolding r_def using h0' by simp
  have rleT: "r \<le> T'" unfolding r_def T'_def
    using h0' by (intro mult_right_mono) simp_all
  have Qc: "?Q \<in> exit_class k L r x"
    unfolding r_def by (rule eulerp_in_class[OF h0 L1 SFc SFs])
  interpret PQ: prob_space ?Q by (rule exit_class_prob[OF Qc])
  have setsQ: "sets ?Q = sets ?Br" by (rule exit_class_sets[OF Qc])
  have ne: "space ?Q \<noteq> {}" by (rule PQ.not_empty)
  note pack = sbm_kernel_package[OF h0 L1 SFc SFs]
  have eQ: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> r)) \<in> borel_measurable ?Q"
    by (rule measurable_compose[OF pair_law_eval_measurable[OF setsQ] pair_fst_borel])
  have Kp: "?K \<in> ?Q \<rightarrow>\<^sub>M prob_algebra ?MR"
    unfolding hT by (rule measurable_compose[OF eQ pack(1)])
  have Ee: "eulerp SF x h (Suc N) = kglue_law' r T' ?K ?Q"
    by (simp add: r_def T'_def)
  have phim: "(\<lambda>p. pglue r T' (fst p) (snd p))
      \<in> ksemi ?Q ?MR ?K \<rightarrow>\<^sub>M ?Bt"
    by (rule kglue_law'_measurable[OF r0 rleT setsQ Kp ne])
  have sksemi: "sets (ksemi ?Q ?MR ?K) = sets (?Q \<Otimes>\<^sub>M ?MR)"
    by (rule sets_ksemi[OF Kp ne])
  have Em: "euXi SF M h (Suc (Suc N)) \<in> borel_measurable ?Bt"
    by (rule euXi_measurable[OF SFc])
  have Gmsq: "(\<lambda>\<omega>. (euXi SF M h (Suc (Suc N)) \<omega>)\<^sup>2)
      \<in> borel_measurable ?Bt"
    by (intro borel_measurable_power Em)
  have Gm2e: "(\<lambda>\<omega>. ennreal ((euXi SF M h (Suc (Suc N)) \<omega>)\<^sup>2))
      \<in> borel_measurable ?Bt"
    using Gmsq by measurable
  have Gm2e': "(\<lambda>\<omega>. ennreal ((euXi SF M h (Suc (Suc N)) \<omega>)\<^sup>2))
      \<in> borel_measurable (distr (ksemi ?Q ?MR ?K) ?Bt
        (\<lambda>p. pglue r T' (fst p) (snd p)))"
    using Gm2e measurable_cong_sets[OF sets_distr refl] by blast
  have Fsplit: "(euXi SF M h (Suc (Suc N)) (pglue r T' (fst p) (snd p)))\<^sup>2
      = (?A (fst p) + ?xi (fst p) (snd p))\<^sup>2"
    for p :: "'n pairpath \<times> 'n pairpath"
    unfolding r_def T'_def by (simp only: euXi_pglue_split[OF h0'])
  have Feq: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath.
        (euXi SF M h (Suc (Suc N)) (pglue r T' (fst p) (snd p)))\<^sup>2)
      = (\<lambda>p. (?A (fst p) + ?xi (fst p) (snd p))\<^sup>2)"
    by (rule ext) (rule Fsplit)
  have Fm0: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath.
        (euXi SF M h (Suc (Suc N)) (pglue r T' (fst p) (snd p)))\<^sup>2)
      \<in> borel_measurable (ksemi ?Q ?MR ?K)"
    by (intro borel_measurable_power measurable_compose[OF phim Em])
  have Fsq: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath.
        (?A (fst p) + ?xi (fst p) (snd p))\<^sup>2)
      \<in> borel_measurable (?Q \<Otimes>\<^sub>M ?MR)"
    using Fm0 unfolding Feq
    using measurable_cong_sets[OF sksemi refl] by blast
  have Fme: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath.
        ennreal ((?A (fst p) + ?xi (fst p) (snd p))\<^sup>2))
      \<in> borel_measurable (?Q \<Otimes>\<^sub>M ?MR)"
    using Fsq by measurable
  \<comment> \<open>the inner conditional bound, valid for every prefix path\<close>
  have inner: "(\<integral>\<^sup>+\<omega>'. ennreal ((?A \<omega> + ?xi \<omega> \<omega>')\<^sup>2) \<partial>(?K \<omega>))
      \<le> ennreal ((?A \<omega>)\<^sup>2 + xiC M L * h\<^sup>2)" for \<omega> :: "'n pairpath"
  proof -
    note SSTw = SFs[of "fst (\<omega> r)"]
    note i1 = sbm_xi_integrable[OF h0 L1 SSTw]
    note i2 = sbm_xi_sq_integrable[OF h0 L1 SSTw]
    note m0 = sbm_xi_mean[OF h0 L1 SSTw]
    note v1 = sbm_xi_sq_bound_uniform[OF h0 L1 SSTw, where M = M]
    interpret KP: prob_space "?K \<omega>"
      by (rule prob_space_sbmpair_law[OF h0'])
    have exl: "(\<lambda>\<omega>'. (?A \<omega> + ?xi \<omega> \<omega>')\<^sup>2)
        = (\<lambda>\<omega>'. (?A \<omega>)\<^sup>2
            + ((2 * ?A \<omega>) * ?xi \<omega> \<omega>' + (?xi \<omega> \<omega>')\<^sup>2))"
      by (rule ext) (simp add: power2_sum algebra_simps)
    have iconst: "integrable (?K \<omega>) (\<lambda>\<omega>'. (?A \<omega>)\<^sup>2)"
      by (rule KP.integrable_const)
    have ia: "integrable (?K \<omega>) (\<lambda>\<omega>'. (2 * ?A \<omega>) * ?xi \<omega> \<omega>')"
      by (rule integrable_cmult[OF i1])
    have ib: "integrable (?K \<omega>)
        (\<lambda>\<omega>'. (2 * ?A \<omega>) * ?xi \<omega> \<omega>' + (?xi \<omega> \<omega>')\<^sup>2)"
      by (rule Bochner_Integration.integrable_add[OF ia i2])
    have icc: "integrable (?K \<omega>) (\<lambda>\<omega>'. (?A \<omega> + ?xi \<omega> \<omega>')\<^sup>2)"
      unfolding exl by (rule Bochner_Integration.integrable_add[OF iconst ib])
    have c1: "(\<integral>\<omega>'. (?A \<omega>)\<^sup>2 \<partial>(?K \<omega>)) = (?A \<omega>)\<^sup>2"
      using lebesgue_integral_const[of "?K \<omega>" "(?A \<omega>)\<^sup>2"] KP.prob_space
      by simp
    have c2: "(\<integral>\<omega>'. (2 * ?A \<omega>) * ?xi \<omega> \<omega>' + (?xi \<omega> \<omega>')\<^sup>2 \<partial>(?K \<omega>))
        = (2 * ?A \<omega>) * (\<integral>\<omega>'. ?xi \<omega> \<omega>' \<partial>(?K \<omega>))
          + (\<integral>\<omega>'. (?xi \<omega> \<omega>')\<^sup>2 \<partial>(?K \<omega>))"
      by (simp add: Bochner_Integration.integral_add[OF ia i2]
          integral_cmult[OF i1])
    have split: "(\<integral>\<omega>'. (?A \<omega> + ?xi \<omega> \<omega>')\<^sup>2 \<partial>(?K \<omega>))
        = (\<integral>\<omega>'. (?A \<omega>)\<^sup>2 \<partial>(?K \<omega>))
          + (\<integral>\<omega>'. (2 * ?A \<omega>) * ?xi \<omega> \<omega>' + (?xi \<omega> \<omega>')\<^sup>2 \<partial>(?K \<omega>))"
      unfolding exl
      by (rule Bochner_Integration.integral_add[OF iconst ib])
    have Eval: "(\<integral>\<omega>'. (?A \<omega> + ?xi \<omega> \<omega>')\<^sup>2 \<partial>(?K \<omega>))
        \<le> (?A \<omega>)\<^sup>2 + xiC M L * h\<^sup>2"
    proof -
      have "(\<integral>\<omega>'. (?A \<omega> + ?xi \<omega> \<omega>')\<^sup>2 \<partial>(?K \<omega>))
          = (?A \<omega>)\<^sup>2 + (\<integral>\<omega>'. (?xi \<omega> \<omega>')\<^sup>2 \<partial>(?K \<omega>))"
        using split c1 c2 m0 by simp
      then show ?thesis using v1 by linarith
    qed
    have nn: "AE \<omega>' in ?K \<omega>. 0 \<le> (?A \<omega> + ?xi \<omega> \<omega>')\<^sup>2" by simp
    have "(\<integral>\<^sup>+\<omega>'. ennreal ((?A \<omega> + ?xi \<omega> \<omega>')\<^sup>2) \<partial>(?K \<omega>))
        = ennreal (\<integral>\<omega>'. (?A \<omega> + ?xi \<omega> \<omega>')\<^sup>2 \<partial>(?K \<omega>))"
      by (rule nn_integral_eq_integral[OF icc nn])
    also have "\<dots> \<le> ennreal ((?A \<omega>)\<^sup>2 + xiC M L * h\<^sup>2)"
      by (intro ennreal_leI Eval)
    finally show ?thesis .
  qed
  \<comment> \<open>the outer bound through the induction hypothesis\<close>
  have IHi: "integrable ?Q (\<lambda>\<omega>. (?A \<omega>)\<^sup>2)"
    and IHb: "(\<integral>\<omega>. (?A \<omega>)\<^sup>2 \<partial>?Q) \<le> real (Suc N) * xiC M L * h\<^sup>2"
    using Suc.IH by blast+
  have iQc: "integrable ?Q (\<lambda>\<omega>. (?A \<omega>)\<^sup>2 + xiC M L * h\<^sup>2)"
    by (intro Bochner_Integration.integrable_add IHi PQ.integrable_const)
  have nnQ: "AE \<omega> in ?Q. 0 \<le> (?A \<omega>)\<^sup>2 + xiC M L * h\<^sup>2"
    by (intro always_eventually allI add_nonneg_nonneg
        mult_nonneg_nonneg xiC_nonneg) simp_all
  have step2: "(\<integral>\<^sup>+\<omega>. ennreal ((?A \<omega>)\<^sup>2 + xiC M L * h\<^sup>2) \<partial>?Q)
      = ennreal ((\<integral>\<omega>. (?A \<omega>)\<^sup>2 \<partial>?Q) + xiC M L * h\<^sup>2)"
  proof -
    have "(\<integral>\<^sup>+\<omega>. ennreal ((?A \<omega>)\<^sup>2 + xiC M L * h\<^sup>2) \<partial>?Q)
        = ennreal (\<integral>\<omega>. (?A \<omega>)\<^sup>2 + xiC M L * h\<^sup>2 \<partial>?Q)"
      by (rule nn_integral_eq_integral[OF iQc nnQ])
    also have "(\<integral>\<omega>. (?A \<omega>)\<^sup>2 + xiC M L * h\<^sup>2 \<partial>?Q)
        = (\<integral>\<omega>. (?A \<omega>)\<^sup>2 \<partial>?Q) + (\<integral>\<omega>. xiC M L * h\<^sup>2 \<partial>?Q)"
      by (rule Bochner_Integration.integral_add[OF IHi PQ.integrable_const])
    also have "(\<integral>\<omega>. xiC M L * h\<^sup>2 \<partial>?Q)
        = measure ?Q (space ?Q) *\<^sub>R (xiC M L * h\<^sup>2)"
      by (rule lebesgue_integral_const)
    finally show ?thesis by (simp add: PQ.prob_space)
  qed
  have main: "(\<integral>\<^sup>+\<omega>. ennreal ((euXi SF M h (Suc (Suc N)) \<omega>)\<^sup>2)
      \<partial>(eulerp SF x h (Suc N)))
      \<le> ennreal (real (Suc (Suc N)) * xiC M L * h\<^sup>2)"
  proof -
    have kd: "kglue_law' r T' ?K ?Q = distr (ksemi ?Q ?MR ?K) ?Bt
        (\<lambda>p. pglue r T' (fst p) (snd p))"
      unfolding kglue_law'_def pair_law_of_def by (rule refl)
    have "(\<integral>\<^sup>+\<omega>. ennreal ((euXi SF M h (Suc (Suc N)) \<omega>)\<^sup>2)
        \<partial>(eulerp SF x h (Suc N)))
        = (\<integral>\<^sup>+p. ennreal ((euXi SF M h (Suc (Suc N))
            (pglue r T' (fst p) (snd p)))\<^sup>2) \<partial>(ksemi ?Q ?MR ?K))"
      unfolding Ee kd by (rule nn_integral_distr[OF phim Gm2e'])
    also have "\<dots> = (\<integral>\<^sup>+p. ennreal ((?A (fst p)
        + ?xi (fst p) (snd p))\<^sup>2) \<partial>(ksemi ?Q ?MR ?K))"
      by (rule nn_integral_cong) (simp only: Fsplit)
    also have "\<dots> = (\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+\<omega>'. ennreal ((?A (fst (\<omega>, \<omega>'))
        + ?xi (fst (\<omega>, \<omega>')) (snd (\<omega>, \<omega>')))\<^sup>2) \<partial>(?K \<omega>)) \<partial>?Q)"
      by (rule nn_integral_ksemi[OF Kp Fme])
    also have "\<dots> = (\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+\<omega>'. ennreal ((?A \<omega> + ?xi \<omega> \<omega>')\<^sup>2)
        \<partial>(?K \<omega>)) \<partial>?Q)"
      by simp
    also have "\<dots> \<le> (\<integral>\<^sup>+\<omega>. ennreal ((?A \<omega>)\<^sup>2 + xiC M L * h\<^sup>2) \<partial>?Q)"
      by (rule nn_integral_mono) (rule inner)
    also have "\<dots> = ennreal ((\<integral>\<omega>. (?A \<omega>)\<^sup>2 \<partial>?Q) + xiC M L * h\<^sup>2)"
      by (rule step2)
    also have "\<dots> \<le> ennreal (real (Suc N) * xiC M L * h\<^sup>2
        + xiC M L * h\<^sup>2)"
      by (intro ennreal_leI add_right_mono IHb)
    also have "\<dots> = ennreal (real (Suc (Suc N)) * xiC M L * h\<^sup>2)"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have setsE: "sets (eulerp SF x h (Suc N)) = sets ?Bt"
    unfolding Ee by simp
  have Gme: "(\<lambda>\<omega>. (euXi SF M h (Suc (Suc N)) \<omega>)\<^sup>2)
      \<in> borel_measurable (eulerp SF x h (Suc N))"
    using Gmsq measurable_cong_sets[OF setsE refl] by blast
  have nnG: "AE \<omega> in eulerp SF x h (Suc N).
      0 \<le> (euXi SF M h (Suc (Suc N)) \<omega>)\<^sup>2" by simp
  have intS: "integrable (eulerp SF x h (Suc N))
      (\<lambda>\<omega>. (euXi SF M h (Suc (Suc N)) \<omega>)\<^sup>2)"
  proof (rule integrableI_nonneg[OF Gme nnG])
    have "ennreal (real (Suc (Suc N)) * xiC M L * h\<^sup>2) < \<infinity>" by simp
    with main show "(\<integral>\<^sup>+\<omega>. ennreal ((euXi SF M h (Suc (Suc N)) \<omega>)\<^sup>2)
        \<partial>(eulerp SF x h (Suc N))) < \<infinity>"
      by (rule le_less_trans)
  qed
  have c0: "0 \<le> real (Suc (Suc N)) * xiC M L * h\<^sup>2"
    by (intro mult_nonneg_nonneg xiC_nonneg) simp_all
  have bndS: "(\<integral>\<omega>. (euXi SF M h (Suc (Suc N)) \<omega>)\<^sup>2
      \<partial>(eulerp SF x h (Suc N)))
      \<le> real (Suc (Suc N)) * xiC M L * h\<^sup>2"
  proof -
    have "ennreal (\<integral>\<omega>. (euXi SF M h (Suc (Suc N)) \<omega>)\<^sup>2
        \<partial>(eulerp SF x h (Suc N)))
        = (\<integral>\<^sup>+\<omega>. ennreal ((euXi SF M h (Suc (Suc N)) \<omega>)\<^sup>2)
          \<partial>(eulerp SF x h (Suc N)))"
      by (rule nn_integral_eq_integral[OF intS nnG, symmetric])
    also have "\<dots> \<le> ennreal (real (Suc (Suc N)) * xiC M L * h\<^sup>2)"
      by (rule main)
    finally show ?thesis using c0 by simp
  qed
  show ?case using intS bndS by blast
qed

subsection \<open>The increments are almost surely orthogonal to a killed field\<close>

lemma sbm_orth_increment:
  fixes S :: "real^'n::finite^'n" and w :: "real^'n"
  assumes h0: "0 \<le> h" and orth: "transpose S *v w = 0"
  shows "AE \<omega>' in pair_law_of h (sbmpair S h)
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
    w \<bullet> (fst (\<omega>' h) - fst (\<omega>' 0)) = 0"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?B = "(path_borel h :: ('n pairpath) measure)"
  have phim: "sbmpair S h \<in> ?M \<rightarrow>\<^sub>M ?B" by (rule sbmpair_measurable[OF h0])
  have evh: "(\<lambda>\<omega>' :: 'n pairpath. \<omega>' h) \<in> ?B \<rightarrow>\<^sub>M borel"
    by (rule pair_law_eval_measurable[OF refl])
  have ev0: "(\<lambda>\<omega>' :: 'n pairpath. \<omega>' 0) \<in> ?B \<rightarrow>\<^sub>M borel"
    by (rule pair_law_eval_measurable[OF refl])
  have pairm: "(\<lambda>\<omega>' :: 'n pairpath. (\<omega>' h, \<omega>' 0)) \<in> ?B \<rightarrow>\<^sub>M borel"
    using evh ev0 by (simp add: borel_prod[symmetric])
  have contf: "(\<lambda>ab :: ((real^'n) \<times> (real^'n^'n))
        \<times> ((real^'n) \<times> (real^'n^'n)).
      w \<bullet> (fst (fst ab) - fst (snd ab))) \<in> borel_measurable borel"
  proof (intro borel_measurable_continuous_onI)
    have p1: "continuous_on UNIV (\<lambda>ab :: ((real^'n) \<times> (real^'n^'n))
        \<times> ((real^'n) \<times> (real^'n^'n)). fst (fst ab))"
      by (intro continuous_on_fst continuous_on_id)
    have p2: "continuous_on UNIV (\<lambda>ab :: ((real^'n) \<times> (real^'n^'n))
        \<times> ((real^'n) \<times> (real^'n^'n)). fst (snd ab))"
      by (intro continuous_on_fst continuous_on_snd continuous_on_id)
    show "continuous_on UNIV (\<lambda>ab :: ((real^'n) \<times> (real^'n^'n))
        \<times> ((real^'n) \<times> (real^'n^'n)).
        w \<bullet> (fst (fst ab) - fst (snd ab)))"
      by (intro continuous_intros p1 p2)
  qed
  have fm: "(\<lambda>\<omega>' :: 'n pairpath. w \<bullet> (fst (\<omega>' h) - fst (\<omega>' 0)))
      \<in> borel_measurable ?B"
    using measurable_compose[OF pairm contf] by simp
  have mset: "{\<omega>' \<in> space ?B. w \<bullet> (fst (\<omega>' h) - fst (\<omega>' 0)) = 0}
      \<in> sets ?B"
  proof -
    have "{\<omega>' \<in> space ?B. w \<bullet> (fst (\<omega>' h) - fst (\<omega>' 0)) = 0}
        = (\<lambda>\<omega>' :: 'n pairpath. w \<bullet> (fst (\<omega>' h) - fst (\<omega>' 0)))
          -` {0} \<inter> space ?B"
      by auto
    then show ?thesis using measurable_sets[OF fm] by simp
  qed
  have ptw: "w \<bullet> (fst (sbmpair S h \<omega> h) - fst (sbmpair S h \<omega> 0)) = 0"
    for \<omega> :: "'n \<Rightarrow> real \<Rightarrow> real"
  proof -
    have hI: "h \<in> {0..h}" and zI: "(0::real) \<in> {0..h}"
      using h0 by simp_all
    have "fst (sbmpair S h \<omega> h) - fst (sbmpair S h \<omega> 0)
        = S *v (cbmX (0::real^'n) h \<omega> - cbmX (0::real^'n) 0 \<omega>)"
      by (simp add: sbmpair_apply[OF hI] sbmpair_apply[OF zI]
          matrix_vector_mult_diff_distrib)
    then have "w \<bullet> (fst (sbmpair S h \<omega> h) - fst (sbmpair S h \<omega> 0))
        = (transpose S *v w)
          \<bullet> (cbmX (0::real^'n) h \<omega> - cbmX (0::real^'n) 0 \<omega>)"
      by (simp add: inner_transpose_matrix)
    then show ?thesis using orth by simp
  qed
  show ?thesis
    unfolding pair_law_of_def
    by (subst AE_distr_iff[OF phim mset]) (simp add: ptw)
qed


subsection \<open>Partial grid sums: peel, moment bound, Chebyshev\<close>

lemma euXi_pglue_prefix:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n" and M :: "real^'n^'n"
    and \<omega> \<omega>' :: "'n pairpath" and h :: real
  assumes h0: "0 \<le> h" and m: "m \<le> Suc N"
  shows "euXi SF M h m (pglue (real (Suc N) * h)
      (real (Suc (Suc N)) * h) \<omega> \<omega>') = euXi SF M h m \<omega>"
proof -
  let ?r = "real (Suc N) * h"
  let ?T = "real (Suc (Suc N)) * h"
  have prefl: "pglue ?r ?T \<omega> \<omega>' (real j * h) = \<omega> (real j * h)"
    if j: "j \<le> Suc N" for j
  proof (rule pglue_le)
    have a: "0 \<le> real j * h"
      by (intro mult_nonneg_nonneg h0) simp_all
    have b: "real j * h \<le> ?T"
      using j h0 by (intro mult_right_mono) simp_all
    show "real j * h \<in> {0..?T}" using a b by simp
    show "real j * h \<le> ?r" using j h0 by (intro mult_right_mono) simp_all
  qed
  show ?thesis unfolding euXi_def
  proof (rule sum.cong[OF refl])
    fix j assume "j \<in> {..<m}"
    then have j1: "Suc j \<le> Suc N" and j2: "j \<le> Suc N" using m by auto
    show "trace (M ** (outerp
        (fst (pglue ?r ?T \<omega> \<omega>' (real (Suc j) * h))
          - fst (pglue ?r ?T \<omega> \<omega>' (real j * h)))
        - h *\<^sub>R (SF (fst (pglue ?r ?T \<omega> \<omega>' (real j * h)))
            ** transpose (SF (fst (pglue ?r ?T \<omega> \<omega>' (real j * h)))))))
      = trace (M ** (outerp
        (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h)))
        - h *\<^sub>R (SF (fst (\<omega> (real j * h)))
            ** transpose (SF (fst (\<omega> (real j * h)))))))"
      by (simp only: prefl[OF j1] prefl[OF j2])
  qed
qed

theorem eulerp_Xi_sq_bound_le:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n" and M :: "real^'n^'n"
    and x :: "real^'n" and h :: real
  assumes h0: "0 < h" and L1: "1 \<le> L"
    and SFc: "continuous_on UNIV SF"
    and SFs: "\<And>z. SF z ** transpose (SF z) \<in> sconstraint k L"
    and m: "m \<le> Suc N"
  shows "integrable (eulerp SF x h N) (\<lambda>\<omega>. (euXi SF M h m \<omega>)\<^sup>2)
      \<and> (\<integral>\<omega>. (euXi SF M h m \<omega>)\<^sup>2 \<partial>(eulerp SF x h N))
        \<le> real m * xiC M L * h\<^sup>2"
  using m
proof (induction N)
  case 0
  then consider (z) "m = 0" | (o) "m = Suc 0" by linarith
  then show ?case
  proof cases
    case z
    have e: "(\<lambda>\<omega> :: 'n pairpath. (euXi SF M h m \<omega>)\<^sup>2) = (\<lambda>\<omega>. 0)"
      by (rule ext) (simp add: z euXi_def)
    show ?thesis unfolding e by (simp add: z)
  next
    case o
    show ?thesis unfolding o
      by (rule eulerp_Xi_sq_bound[OF h0 L1 SFc SFs])
  qed
next
  case (Suc N)
  show ?case
  proof (cases "m = Suc (Suc N)")
    case True
    show ?thesis unfolding True
      by (rule eulerp_Xi_sq_bound[OF h0 L1 SFc SFs])
  next
    case False
    with Suc.prems have mle: "m \<le> Suc N" by simp
    have IHi: "integrable (eulerp SF x h N) (\<lambda>\<omega>. (euXi SF M h m \<omega>)\<^sup>2)"
      and IHb: "(\<integral>\<omega>. (euXi SF M h m \<omega>)\<^sup>2 \<partial>(eulerp SF x h N))
        \<le> real m * xiC M L * h\<^sup>2"
      using Suc.IH[OF mle] by blast+
    have h0': "(0::real) \<le> h" using h0 by simp
    define r where "r = real (Suc N) * h"
    define T' where "T' = real (Suc (Suc N)) * h"
    let ?Q = "eulerp SF x h N"
    let ?Br = "(path_borel r :: ('n pairpath) measure)"
    let ?Bt = "(path_borel T' :: ('n pairpath) measure)"
    let ?MR = "(path_borel (T' - r) :: ('n pairpath) measure)"
    let ?K = "\<lambda>\<omega> :: 'n pairpath.
        pair_law_of h (sbmpair (SF (fst (\<omega> r))) h) bm_paths"
    have hT: "T' - r = h" unfolding r_def T'_def by (simp add: algebra_simps)
    have r0: "0 \<le> r" unfolding r_def using h0' by simp
    have rleT: "r \<le> T'" unfolding r_def T'_def
      using h0' by (intro mult_right_mono) simp_all
    have Qc: "?Q \<in> exit_class k L r x"
      unfolding r_def by (rule eulerp_in_class[OF h0 L1 SFc SFs])
    interpret PQ: prob_space ?Q by (rule exit_class_prob[OF Qc])
    have setsQ: "sets ?Q = sets ?Br" by (rule exit_class_sets[OF Qc])
    have ne: "space ?Q \<noteq> {}" by (rule PQ.not_empty)
    note pack = sbm_kernel_package[OF h0 L1 SFc SFs]
    have eQ: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> r)) \<in> borel_measurable ?Q"
      by (rule measurable_compose[OF pair_law_eval_measurable[OF setsQ] pair_fst_borel])
    have Kp: "?K \<in> ?Q \<rightarrow>\<^sub>M prob_algebra ?MR"
      unfolding hT by (rule measurable_compose[OF eQ pack(1)])
    have Ee: "eulerp SF x h (Suc N) = kglue_law' r T' ?K ?Q"
      by (simp add: r_def T'_def)
    have phim: "(\<lambda>p. pglue r T' (fst p) (snd p))
        \<in> ksemi ?Q ?MR ?K \<rightarrow>\<^sub>M ?Bt"
      by (rule kglue_law'_measurable[OF r0 rleT setsQ Kp ne])
    have Gmsq: "(\<lambda>\<omega>. (euXi SF M h m \<omega>)\<^sup>2) \<in> borel_measurable ?Bt"
      by (intro borel_measurable_power euXi_measurable[OF SFc])
    have Gm2e: "(\<lambda>\<omega>. ennreal ((euXi SF M h m \<omega>)\<^sup>2))
        \<in> borel_measurable ?Bt"
      using Gmsq by measurable
    have Gm2e': "(\<lambda>\<omega>. ennreal ((euXi SF M h m \<omega>)\<^sup>2))
        \<in> borel_measurable (distr (ksemi ?Q ?MR ?K) ?Bt
          (\<lambda>p. pglue r T' (fst p) (snd p)))"
      using Gm2e measurable_cong_sets[OF sets_distr refl] by blast
    have euQ: "euXi SF M h m \<in> borel_measurable ?Q"
      using euXi_measurable[OF SFc]
        measurable_cong_sets[OF setsQ refl] by blast
    have Fme: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath.
          ennreal ((euXi SF M h m (fst p))\<^sup>2))
        \<in> borel_measurable (?Q \<Otimes>\<^sub>M ?MR)"
      using measurable_compose[OF measurable_fst euQ] by measurable
    have Fsplit: "(euXi SF M h m (pglue r T' (fst p) (snd p)))\<^sup>2
        = (euXi SF M h m (fst p))\<^sup>2"
      for p :: "'n pairpath \<times> 'n pairpath"
      unfolding r_def T'_def
      by (simp only: euXi_pglue_prefix[OF h0' mle])
    have kd: "kglue_law' r T' ?K ?Q = distr (ksemi ?Q ?MR ?K) ?Bt
        (\<lambda>p. pglue r T' (fst p) (snd p))"
      unfolding kglue_law'_def pair_law_of_def by (rule refl)
    have KP1: "emeasure (pair_law_of h (sbmpair (SF (fst (\<omega> r))) h)
        bm_paths) (space (pair_law_of h (sbmpair (SF (fst (\<omega> r))) h)
          bm_paths)) = 1" for \<omega> :: "'n pairpath"
      by (rule prob_space.emeasure_space_1[OF prob_space_sbmpair_law[OF h0']])
    have nnA: "(\<integral>\<^sup>+\<omega>. ennreal ((euXi SF M h m \<omega>)\<^sup>2)
        \<partial>(eulerp SF x h (Suc N)))
        = (\<integral>\<^sup>+\<omega>. ennreal ((euXi SF M h m \<omega>)\<^sup>2) \<partial>?Q)"
    proof -
      have "(\<integral>\<^sup>+\<omega>. ennreal ((euXi SF M h m \<omega>)\<^sup>2)
          \<partial>(eulerp SF x h (Suc N)))
          = (\<integral>\<^sup>+p. ennreal ((euXi SF M h m
              (pglue r T' (fst p) (snd p)))\<^sup>2) \<partial>(ksemi ?Q ?MR ?K))"
        unfolding Ee kd by (rule nn_integral_distr[OF phim Gm2e'])
      also have "\<dots> = (\<integral>\<^sup>+p. ennreal ((euXi SF M h m (fst p))\<^sup>2)
          \<partial>(ksemi ?Q ?MR ?K))"
        by (rule nn_integral_cong) (simp only: Fsplit)
      also have "\<dots> = (\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+\<omega>'. ennreal
          ((euXi SF M h m (fst (\<omega>, \<omega>')))\<^sup>2) \<partial>(?K \<omega>)) \<partial>?Q)"
        by (rule nn_integral_ksemi[OF Kp Fme])
      also have "\<dots> = (\<integral>\<^sup>+\<omega>. ennreal ((euXi SF M h m \<omega>)\<^sup>2) \<partial>?Q)"
        by (simp add: KP1)
      finally show ?thesis .
    qed
    have nnQfin: "(\<integral>\<^sup>+\<omega>. ennreal ((euXi SF M h m \<omega>)\<^sup>2) \<partial>?Q)
        = ennreal (\<integral>\<omega>. (euXi SF M h m \<omega>)\<^sup>2 \<partial>?Q)"
      by (rule nn_integral_eq_integral[OF IHi]) simp
    have setsE: "sets (eulerp SF x h (Suc N)) = sets ?Bt"
      unfolding Ee by simp
    have Gme: "(\<lambda>\<omega>. (euXi SF M h m \<omega>)\<^sup>2)
        \<in> borel_measurable (eulerp SF x h (Suc N))"
      using Gmsq measurable_cong_sets[OF setsE refl] by blast
    have nnG: "AE \<omega> in eulerp SF x h (Suc N).
        0 \<le> (euXi SF M h m \<omega>)\<^sup>2" by simp
    have intS: "integrable (eulerp SF x h (Suc N))
        (\<lambda>\<omega>. (euXi SF M h m \<omega>)\<^sup>2)"
    proof (rule integrableI_nonneg[OF Gme nnG])
      have "ennreal (\<integral>\<omega>. (euXi SF M h m \<omega>)\<^sup>2 \<partial>?Q) < \<infinity>" by simp
      then show "(\<integral>\<^sup>+\<omega>. ennreal ((euXi SF M h m \<omega>)\<^sup>2)
          \<partial>(eulerp SF x h (Suc N))) < \<infinity>"
        unfolding nnA nnQfin .
    qed
    have c0: "0 \<le> real m * xiC M L * h\<^sup>2"
      by (intro mult_nonneg_nonneg xiC_nonneg) simp_all
    have bndS: "(\<integral>\<omega>. (euXi SF M h m \<omega>)\<^sup>2 \<partial>(eulerp SF x h (Suc N)))
        \<le> real m * xiC M L * h\<^sup>2"
    proof -
      have "ennreal (\<integral>\<omega>. (euXi SF M h m \<omega>)\<^sup>2
          \<partial>(eulerp SF x h (Suc N)))
          = (\<integral>\<^sup>+\<omega>. ennreal ((euXi SF M h m \<omega>)\<^sup>2)
            \<partial>(eulerp SF x h (Suc N)))"
        by (rule nn_integral_eq_integral[OF intS nnG, symmetric])
      also have "\<dots> = ennreal (\<integral>\<omega>. (euXi SF M h m \<omega>)\<^sup>2 \<partial>?Q)"
        unfolding nnA nnQfin by (rule refl)
      also have "\<dots> \<le> ennreal (real m * xiC M L * h\<^sup>2)"
        by (intro ennreal_leI IHb)
      finally show ?thesis using c0 by simp
    qed
    show ?thesis using intS bndS by blast
  qed
qed

corollary eulerp_Xi_chebyshev:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n" and M :: "real^'n^'n"
    and x :: "real^'n" and h \<beta> :: real
  assumes h0: "0 < h" and L1: "1 \<le> L"
    and SFc: "continuous_on UNIV SF"
    and SFs: "\<And>z. SF z ** transpose (SF z) \<in> sconstraint k L"
    and m: "m \<le> Suc N" and b: "0 < \<beta>"
  shows "measure (eulerp SF x h N) {\<omega> \<in> space (eulerp SF x h N).
      \<beta> \<le> \<bar>euXi SF M h m \<omega>\<bar>}
    \<le> real m * xiC M L * h\<^sup>2 / \<beta>\<^sup>2"
proof -
  let ?P = "eulerp SF x h N"
  have int: "integrable ?P (\<lambda>\<omega>. (euXi SF M h m \<omega>)\<^sup>2)"
    and bnd: "(\<integral>\<omega>. (euXi SF M h m \<omega>)\<^sup>2 \<partial>?P)
      \<le> real m * xiC M L * h\<^sup>2"
    using eulerp_Xi_sq_bound_le[OF h0 L1 SFc SFs m] by blast+
  have seteq: "{\<omega> \<in> space ?P. \<beta>\<^sup>2 \<le> (euXi SF M h m \<omega>)\<^sup>2}
      = {\<omega> \<in> space ?P. \<beta> \<le> \<bar>euXi SF M h m \<omega>\<bar>}"
  proof -
    have iff: "\<beta>\<^sup>2 \<le> y\<^sup>2 \<longleftrightarrow> \<beta> \<le> \<bar>y\<bar>" for y :: real
    proof
      assume "\<beta>\<^sup>2 \<le> y\<^sup>2"
      then have "\<beta>\<^sup>2 \<le> \<bar>y\<bar>\<^sup>2" by simp
      then show "\<beta> \<le> \<bar>y\<bar>" by (rule power2_le_imp_le) simp
    next
      assume a: "\<beta> \<le> \<bar>y\<bar>"
      have "\<beta>\<^sup>2 \<le> \<bar>y\<bar>\<^sup>2"
        using a b by (intro power_mono) simp_all
      then show "\<beta>\<^sup>2 \<le> y\<^sup>2" by simp
    qed
    show ?thesis using iff by auto
  qed
  have b2: "0 < \<beta>\<^sup>2" using b by simp
  have "measure ?P {\<omega> \<in> space ?P. \<beta>\<^sup>2 \<le> (euXi SF M h m \<omega>)\<^sup>2}
      \<le> (\<integral>\<omega>. (euXi SF M h m \<omega>)\<^sup>2 \<partial>?P) / \<beta>\<^sup>2"
  proof (rule integral_Markov_inequality_measure)
    show "integrable ?P (\<lambda>\<omega>. (euXi SF M h m \<omega>)\<^sup>2)" by (rule int)
    show "space ?P \<in> sets ?P" by (rule sets.top)
    show "AE \<omega> in ?P. 0 \<le> (euXi SF M h m \<omega>)\<^sup>2" by simp
    show "0 < \<beta>\<^sup>2" by (rule b2)
  qed
  also have "\<dots> \<le> real m * xiC M L * h\<^sup>2 / \<beta>\<^sup>2"
    using bnd b2 by (intro divide_right_mono) simp_all
  finally show ?thesis using seteq by simp
qed

subsection \<open>The exact quadratic lower bound along the grid\<close>

text \<open>\<open>quad_taylor_step\<close> lives in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


subsection \<open>The weak limit of the Euler laws\<close>

text \<open>The Euler laws at mesh \<open>c / (i + 1)\<close> all live in the compact class
  \<open>exit_class k L c x\<close> (@{thm [source]
  exit_class_compact_metric_space}), so some subsequence converges
  weakly to a class member \<open>P\<close>.  The portmanteau bound --- if the
  measures of an open set converge to \<open>b\<close>, the limit member gives the set
  at most \<open>b\<close>, and dually for closed sets --- applies to the event that a
  path stays inside a region while the quadratic drops below its
  guaranteed growth, whose probability vanishes with the mesh by
  @{thm [source] eulerp_Xi_chebyshev} and \<open>eulerp_quad_lower_region\<close>.

  Staying strictly inside an open set through time \<open>t\<close> is an open
  condition on the path: the image of \<open>{0..t}\<close> is compact, so it sits at
  a positive distance from the complement
  (@{thm [source] separate_compact_closed}), and any path uniformly
  closer than that distance stays inside as well
  (@{thm [source] path_mdist_le_iff_all}).\<close>


theorem exit_class_weak_limit:
  fixes Pseq :: "nat \<Rightarrow> ('n::finite pairpath) measure" and x :: "real^'n"
  assumes T: "0 < T" and L0: "0 \<le> L"
    and mem: "\<And>i. Pseq i \<in> exit_class k L T x"
  shows "\<exists>P \<in> exit_class k L T x.
      (\<forall>U b. openin (mtopology_of
            (path_metric T :: ('n pairpath) metric)) U
          \<longrightarrow> (\<lambda>i. measure (Pseq i) U) \<longlonglongrightarrow> b
          \<longrightarrow> measure P U \<le> b)
      \<and> (\<forall>D b. closedin (mtopology_of
            (path_metric T :: ('n pairpath) metric)) D
          \<longrightarrow> (\<lambda>i. measure (Pseq i) D) \<longlonglongrightarrow> b
          \<longrightarrow> b \<le> measure P D)"
proof -
  let ?pm = "path_metric T :: ('n pairpath) metric"
  let ?C = "exit_class k L T x"
  let ?E = "Levy_Prokhorov.LPm (mspace ?pm) (mdist ?pm)"
  interpret CM: Metric_space ?C ?E
    by (rule exit_class_compact_metric_space(1)[OF T L0])
  have cs: "compact_space CM.mtopology"
    by (rule exit_class_compact_metric_space(3)[OF T L0])
  have rng: "range Pseq \<subseteq> ?C" using mem by auto
  obtain P r where P: "P \<in> ?C" and r: "strict_mono r"
    and liml: "limitin CM.mtopology (Pseq \<circ> r) P sequentially"
    using cs[unfolded CM.compact_space_sequentially] rng by blast
  have Ctop: "CM.mtopology = subtopology
      (weak_conv_topology (mtopology_of ?pm)) ?C"
    by (rule exit_class_compact_metric_space(2)[OF T L0])
  have limW: "limitin (weak_conv_topology (mtopology_of ?pm))
      (Pseq \<circ> r) P sequentially"
    using liml unfolding Ctop limitin_subtopology by blast
  have mwc: "limitin (weak_conv_topology
      (Metric_space.mtopology (mspace ?pm) (mdist ?pm)))
      (Pseq \<circ> r) P sequentially"
    using limW by (simp add: mtopology_of_def)
  have fmi: "finite_measure (Pseq i)" for i
    using exit_class_prob[OF mem, of i]
    by (simp add: prob_space.emeasure_space_1 finite_measureI)
  have fmP: "finite_measure P"
    using exit_class_prob[OF P]
    by (simp add: prob_space.emeasure_space_1 finite_measureI)
  have setsP: "sets P = sets (borel_of
      (Metric_space.mtopology (mspace ?pm) (mdist ?pm)))"
    using exit_class_sets[OF P] by (simp add: mtopology_of_def)
  have ev1: "\<forall>\<^sub>F i in sequentially. sets ((Pseq \<circ> r) i)
      = sets (borel_of (Metric_space.mtopology (mspace ?pm) (mdist ?pm)))"
  proof (intro always_eventually allI)
    fix i show "sets ((Pseq \<circ> r) i)
        = sets (borel_of (Metric_space.mtopology (mspace ?pm) (mdist ?pm)))"
      using exit_class_sets[OF mem, of "r i"]
      by (simp add: mtopology_of_def)
  qed
  have ev2: "\<forall>\<^sub>F i in sequentially. finite_measure ((Pseq \<circ> r) i)"
    by (intro always_eventually allI) (simp add: fmi)
  have MWfin: "mweak_conv_fin (mspace ?pm) (mdist ?pm)
      (Pseq \<circ> r) P sequentially"
    unfolding mweak_conv_fin_def mweak_conv_fin_axioms_def
    using ev1 ev2 fmP setsP by (simp add: mtopology_of_def)
  interpret MW: mweak_conv_fin "mspace ?pm" "mdist ?pm"
      "Pseq \<circ> r" P sequentially
    by (rule MWfin)
  note eq3 = MW.mweak_conv_eq3[THEN iffD1, OF mwc,
      THEN conjunct2, rule_format]
  note eq2 = MW.mweak_conv_eq2[THEN iffD1, OF mwc,
      THEN conjunct2, rule_format]
  have main_open: "measure P U \<le> b"
    if U: "openin (mtopology_of ?pm) U"
      and cb: "(\<lambda>i. measure (Pseq i) U) \<longlonglongrightarrow> b" for U b
  proof -
    have U': "openin (Metric_space.mtopology (mspace ?pm) (mdist ?pm)) U"
      using U by (simp add: mtopology_of_def)
    have sub: "(\<lambda>n. ereal (measure ((Pseq \<circ> r) n) U))
        \<longlonglongrightarrow> ereal b"
      using LIMSEQ_subseq_LIMSEQ[OF cb r] by (simp add: o_def)
    have Linf: "Liminf sequentially
        (\<lambda>n. ereal (measure ((Pseq \<circ> r) n) U)) = ereal b"
      by (rule lim_imp_Liminf[OF _ sub]) simp
    have "ereal (measure P U) \<le> ereal b"
      using eq3[OF U'] Linf by simp
    then show ?thesis by simp
  qed
  have main_closed: "b \<le> measure P D"
    if D: "closedin (mtopology_of ?pm) D"
      and cb: "(\<lambda>i. measure (Pseq i) D) \<longlonglongrightarrow> b" for D b
  proof -
    have D': "closedin (Metric_space.mtopology (mspace ?pm) (mdist ?pm)) D"
      using D by (simp add: mtopology_of_def)
    have sub: "(\<lambda>n. ereal (measure ((Pseq \<circ> r) n) D))
        \<longlonglongrightarrow> ereal b"
      using LIMSEQ_subseq_LIMSEQ[OF cb r] by (simp add: o_def)
    have Lsup: "Limsup sequentially
        (\<lambda>n. ereal (measure ((Pseq \<circ> r) n) D)) = ereal b"
      by (rule lim_imp_Limsup[OF _ sub]) simp
    have "ereal b \<le> ereal (measure P D)"
      using eq2[OF D'] Lsup by simp
    then show ?thesis by simp
  qed
  show ?thesis using P main_open main_closed by blast
qed

text \<open>The Euler laws at mesh \<open>c / (i + 1)\<close>: exactly \<open>i + 1\<close> steps of
  length \<open>c / (i + 1)\<close> land on the horizon \<open>c\<close> on the nose, so
  @{thm [source] eulerp_in_class} puts every member of the sequence in
  the same class and the transfer principle applies verbatim.\<close>

lemma eulerp_seq_in_class:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n" and x :: "real^'n"
  assumes c0: "0 < c" and L1: "1 \<le> L"
    and SFc: "continuous_on UNIV SF"
    and SFs: "\<And>z. SF z ** transpose (SF z) \<in> sconstraint k L"
  shows "eulerp SF x (c / real (Suc i)) i \<in> exit_class k L c x"
proof -
  have h0: "0 < c / real (Suc i)" using c0 by simp
  have "eulerp SF x (c / real (Suc i)) i
      \<in> exit_class k L (real (Suc i) * (c / real (Suc i))) x"
    by (rule eulerp_in_class[OF h0 L1 SFc SFs])
  moreover have "real (Suc i) * (c / real (Suc i)) = c" by simp
  ultimately show ?thesis by simp
qed

theorem eulerp_weak_limit:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n" and x :: "real^'n"
  assumes c0: "0 < c" and L1: "1 \<le> L"
    and SFc: "continuous_on UNIV SF"
    and SFs: "\<And>z. SF z ** transpose (SF z) \<in> sconstraint k L"
  shows "\<exists>P \<in> exit_class k L c x.
      (\<forall>U b. openin (mtopology_of
            (path_metric c :: ('n pairpath) metric)) U
          \<longrightarrow> (\<lambda>i. measure (eulerp SF x (c / real (Suc i)) i) U)
              \<longlonglongrightarrow> b
          \<longrightarrow> measure P U \<le> b)
      \<and> (\<forall>D b. closedin (mtopology_of
            (path_metric c :: ('n pairpath) metric)) D
          \<longrightarrow> (\<lambda>i. measure (eulerp SF x (c / real (Suc i)) i) D)
              \<longlonglongrightarrow> b
          \<longrightarrow> b \<le> measure P D)"
proof -
  have L0: "0 \<le> L" using L1 by linarith
  show ?thesis
    by (rule exit_class_weak_limit[OF c0 L0
        eulerp_seq_in_class[OF c0 L1 SFc SFs]])
qed

subsection \<open>The bad event vanishes with the mesh\<close>

text \<open>The bad event --- the path stays inside a bounded region through
  time \<open>t\<close> yet the quadratic drops below its guaranteed growth --- has
  vanishing probability under the Euler laws
  (\<open>eulerp_bad_event_null_region\<close>).  Three estimates feed the proof:
  the grid functional's Chebyshev bound
  (@{thm [source] eulerp_Xi_chebyshev}), the pathwise lower bound at the
  nearest grid point (\<open>eulerp_quad_lower_region\<close>), and a
  fourth-moment tail for the one-step gap between the grid point and
  \<open>t\<close>, derived below from
  @{thm [source] exit_class_fourth_moment}.\<close>

lemma exit_class_increment_tail:
  fixes Q :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T: "0 < T" and L: "0 \<le> L"
    and Q: "Q \<in> exit_class k L T x"
    and st: "0 \<le> s" and stt: "s \<le> tt" and ttT: "tt \<le> T"
    and l: "0 < l"
  shows "measure Q {\<omega> \<in> space Q.
      l \<le> \<bar>fst (\<omega> tt) $ i - fst (\<omega> s) $ i\<bar>}
    \<le> 8 * L\<^sup>2 * (tt - s)\<^sup>2 / l^4"
proof -
  have setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    by (rule exit_class_sets[OF Q])
  have int4: "integrable Q (\<lambda>\<omega>. (fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4)"
    by (rule exit_class_fourth_moment_integrable[OF T L Q st stt ttT])
  have nn: "AE \<omega> in Q. 0 \<le> (fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4"
    by (simp add: zero_le_fourth)
  have intgl: "(\<integral>\<omega>. (fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4 \<partial>Q)
      \<le> 8 * L\<^sup>2 * (tt - s)\<^sup>2"
  proof -
    have eq: "(\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4) \<partial>Q)
        = ennreal (\<integral>\<omega>. (fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4 \<partial>Q)"
      by (rule nn_integral_eq_integral[OF int4 nn])
    have le: "ennreal (\<integral>\<omega>. (fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4 \<partial>Q)
        \<le> ennreal (8 * L\<^sup>2 * (tt - s)\<^sup>2)"
    proof -
      have f4: "(\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4) \<partial>Q)
          \<le> ennreal (8 * L\<^sup>2 * (tt - s)\<^sup>2)"
        by (rule exit_class_fourth_moment[OF T L setsQ Q st stt ttT])
      show ?thesis using f4 unfolding eq .
    qed
    have y0: "0 \<le> 8 * L\<^sup>2 * (tt - s)\<^sup>2"
      by (auto intro!: mult_nonneg_nonneg)
    show ?thesis using le y0 by simp
  qed
  have seteq: "{\<omega> \<in> space Q. l^4 \<le> (fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4}
      = {\<omega> \<in> space Q. l \<le> \<bar>fst (\<omega> tt) $ i - fst (\<omega> s) $ i\<bar>}"
  proof -
    have iff: "l^4 \<le> y^4 \<longleftrightarrow> l \<le> \<bar>y\<bar>" for y :: real
    proof
      assume "l^4 \<le> y^4"
      then have "l ^ Suc 3 \<le> \<bar>y\<bar> ^ Suc 3"
        by (simp add: power_even_abs eval_nat_numeral)
      then show "l \<le> \<bar>y\<bar>" by (rule power_le_imp_le_base) simp
    next
      assume a: "l \<le> \<bar>y\<bar>"
      then have "l^4 \<le> \<bar>y\<bar>^4" using l by (intro power_mono) simp_all
      then show "l^4 \<le> y^4" by (simp add: power_even_abs)
    qed
    show ?thesis using iff by auto
  qed
  have l4: "0 < l^4" using l by simp
  have "measure Q {\<omega> \<in> space Q.
      l^4 \<le> (fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4}
      \<le> (\<integral>\<omega>. (fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4 \<partial>Q) / l^4"
  proof (rule integral_Markov_inequality_measure)
    show "integrable Q (\<lambda>\<omega>. (fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4)"
      by (rule int4)
    show "space Q \<in> sets Q" by (rule sets.top)
    show "AE \<omega> in Q. 0 \<le> (fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4"
      by (rule nn)
    show "0 < l^4" by (rule l4)
  qed
  also have "\<dots> \<le> 8 * L\<^sup>2 * (tt - s)\<^sup>2 / l^4"
    using intgl l4 by (intro divide_right_mono) simp_all
  finally show ?thesis using seteq by simp
qed

lemma exit_class_increment_tail_norm:
  fixes Q :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T: "0 < T" and L: "0 \<le> L"
    and Q: "Q \<in> exit_class k L T x"
    and st: "0 \<le> s" and stt: "s \<le> tt" and ttT: "tt \<le> T"
    and l: "0 < l"
  shows "measure Q {\<omega> \<in> space Q. l \<le> norm (fst (\<omega> tt) - fst (\<omega> s))}
    \<le> real (CARD('n)) ^ 5 * (8 * L\<^sup>2 * (tt - s)\<^sup>2) / l^4"
proof -
  let ?n = "real (CARD('n))"
  have setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    by (rule exit_class_sets[OF Q])
  interpret PQ: prob_space Q by (rule exit_class_prob[OF Q])
  have cpos: "0 < CARD('n)" by (simp add: card_gt_0_iff)
  have n0: "0 < ?n" using cpos by simp
  define l' where "l' = l / ?n"
  have l'0: "0 < l'" unfolding l'_def using l n0 by simp
  have sI: "s \<in> {0..T}" using st stt ttT by simp
  have tI: "tt \<in> {0..T}" using st stt ttT by simp
  have fmi: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> tt) $ i - fst (\<omega> s) $ i)
      \<in> borel_measurable Q" for i
    by (intro borel_measurable_diff pair_law_coord_measurable[OF setsQ tI]
        pair_law_coord_measurable[OF setsQ sI])
  have Em: "{\<omega> \<in> space Q. l' \<le> \<bar>fst (\<omega> tt) $ i - fst (\<omega> s) $ i\<bar>}
      \<in> sets Q" for i
  proof -
    have am: "(\<lambda>\<omega>. \<bar>fst (\<omega> tt) $ i - fst (\<omega> s) $ i\<bar>)
        \<in> borel_measurable Q"
      by (intro borel_measurable_abs fmi)
    have "{\<omega> \<in> space Q. l' \<le> \<bar>fst (\<omega> tt) $ i - fst (\<omega> s) $ i\<bar>}
        = (\<lambda>\<omega>. \<bar>fst (\<omega> tt) $ i - fst (\<omega> s) $ i\<bar>) -` {l'..} \<inter> space Q"
      by auto
    then show ?thesis
      using measurable_sets[OF am borel_closed[OF closed_atLeast]] by simp
  qed
  have incl: "{\<omega> \<in> space Q. l \<le> norm (fst (\<omega> tt) - fst (\<omega> s))}
      \<subseteq> (\<Union>i\<in>(UNIV :: 'n set).
          {\<omega> \<in> space Q. l' \<le> \<bar>fst (\<omega> tt) $ i - fst (\<omega> s) $ i\<bar>})"
  proof
    fix \<omega> assume w: "\<omega> \<in> {\<omega> \<in> space Q.
        l \<le> norm (fst (\<omega> tt) - fst (\<omega> s))}"
    then have sp: "\<omega> \<in> space Q"
      and ln: "l \<le> norm (fst (\<omega> tt) - fst (\<omega> s))" by auto
    have ex: "\<exists>i. l' \<le> \<bar>fst (\<omega> tt) $ i - fst (\<omega> s) $ i\<bar>"
    proof (rule ccontr)
      assume nc: "\<not> (\<exists>i. l' \<le> \<bar>fst (\<omega> tt) $ i - fst (\<omega> s) $ i\<bar>)"
      then have all: "\<And>i. \<bar>fst (\<omega> tt) $ i - fst (\<omega> s) $ i\<bar> < l'"
        by (auto simp: not_le)
      have "norm (fst (\<omega> tt) - fst (\<omega> s))
          \<le> (\<Sum>i\<in>UNIV. \<bar>(fst (\<omega> tt) - fst (\<omega> s)) $ i\<bar>)"
        by (rule norm_le_l1_cart)
      also have "\<dots> = (\<Sum>i\<in>UNIV. \<bar>fst (\<omega> tt) $ i - fst (\<omega> s) $ i\<bar>)"
        by simp
      also have "\<dots> < (\<Sum>i\<in>(UNIV :: 'n set). l')"
        by (rule sum_strict_mono) (use all in simp_all)
      also have "\<dots> = ?n * l'" by simp
      also have "\<dots> = l" unfolding l'_def using n0 by simp
      finally show False using ln by simp
    qed
    then show "\<omega> \<in> (\<Union>i\<in>(UNIV :: 'n set).
        {\<omega> \<in> space Q. l' \<le> \<bar>fst (\<omega> tt) $ i - fst (\<omega> s) $ i\<bar>})"
      using sp by auto
  qed
  have UNs: "(\<Union>i\<in>(UNIV :: 'n set).
      {\<omega> \<in> space Q. l' \<le> \<bar>fst (\<omega> tt) $ i - fst (\<omega> s) $ i\<bar>}) \<in> sets Q"
    using Em by blast
  have "measure Q {\<omega> \<in> space Q. l \<le> norm (fst (\<omega> tt) - fst (\<omega> s))}
      \<le> measure Q (\<Union>i\<in>(UNIV :: 'n set).
          {\<omega> \<in> space Q. l' \<le> \<bar>fst (\<omega> tt) $ i - fst (\<omega> s) $ i\<bar>})"
    by (rule PQ.finite_measure_mono[OF incl UNs])
  also have "\<dots> \<le> (\<Sum>i\<in>(UNIV :: 'n set). measure Q
      {\<omega> \<in> space Q. l' \<le> \<bar>fst (\<omega> tt) $ i - fst (\<omega> s) $ i\<bar>})"
    by (rule measure_UNION_le) (use Em in simp_all)
  also have "\<dots> \<le> (\<Sum>i\<in>(UNIV :: 'n set). 8 * L\<^sup>2 * (tt - s)\<^sup>2 / l'^4)"
    by (rule sum_mono)
      (rule exit_class_increment_tail[OF T L Q st stt ttT l'0])
  also have "\<dots> = ?n * (8 * L\<^sup>2 * (tt - s)\<^sup>2 / l'^4)" by simp
  also have "\<dots> = ?n ^ 5 * (8 * L\<^sup>2 * (tt - s)\<^sup>2) / l^4"
  proof -
    have l'4: "l'^4 = l^4 / ?n^4"
      unfolding l'_def by (simp add: power_divide)
    have ln0: "l^4 \<noteq> 0" using l by simp
    have nn0: "(?n :: real)^4 \<noteq> 0" using n0 by simp
    have "?n * (8 * L\<^sup>2 * (tt - s)\<^sup>2 / l'^4)
        = ?n * (8 * L\<^sup>2 * (tt - s)\<^sup>2 * ?n^4 / l^4)"
      unfolding l'4 using ln0 nn0 by (simp add: field_simps)
    also have "\<dots> = ?n ^ 5 * (8 * L\<^sup>2 * (tt - s)\<^sup>2) / l^4"
      by (simp add: eval_nat_numeral field_simps)
    finally show ?thesis .
  qed
  finally show ?thesis .
qed

text \<open>The bad event is open when the region is open
  (\<open>open_quad_bad_event_region\<close>): staying inside the region is
  @{thm [source] open_stay_inside} through the first projection, and the
  strict quadratic drop is an open condition on the evaluation at \<open>t\<close>,
  via @{thm [source] open_eval_preimage}.\<close>


(*<*)
end
(*>*)
