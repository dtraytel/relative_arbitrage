section \<open>Concrete pair processes, and nonemptiness of the class\<close>

(*<*)
theory Exit_Class_Witness
  imports
    Exit_Class_Shift "Wiener_Measure.Continuous_Brownian_Motion"
begin

(*>*)

section \<open>Laws of concrete pair processes\<close>

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

section \<open>The paper's class is nonempty\<close>

text \<open>The witness: Brownian motion started at \<open>0\<close> paired with the
  deterministic covariation \<open>Y\<^sub>t = t \<sqdot> I\<close>, capped at the horizon.\<close>

definition bmpair :: "real \<Rightarrow> ('n::finite \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> 'n pairpath"
  where "bmpair T \<omega> = restrict (\<lambda>t. (cbmX 0 t \<omega>, t *\<^sub>R mat 1)) {0..T}"

lemma bmpair_apply:
  "t \<in> {0..T} \<Longrightarrow> bmpair T \<omega> t = (cbmX 0 t \<omega>, t *\<^sub>R mat 1)"
  by (simp add: bmpair_def)

lemma continuous_on_bmpair_path:
  fixes \<omega> :: "'n::finite \<Rightarrow> real \<Rightarrow> real"
  shows "continuous_on {0..T}
      (\<lambda>t. (cbmX (0 :: real^'n) t \<omega>, t *\<^sub>R (mat 1 :: real^'n^'n)))"
proof (intro continuous_on_Pair)
  show "continuous_on {0..T} (\<lambda>t. cbmX (0 :: real^'n) t \<omega>)"
    by (rule continuous_on_subset[OF cbmX_cont]) auto
  show "continuous_on {0..T} (\<lambda>t. t *\<^sub>R (mat 1 :: real^'n^'n))"
    by (rule linear_continuous_on[OF bounded_linear_scaleR_left])
qed

lemma bmpair_measurable:
  assumes T: "0 \<le> T"
  shows "(bmpair T :: ('n::finite \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> 'n pairpath)
      \<in> bm_paths \<rightarrow>\<^sub>M (path_borel T :: ('n pairpath) measure)"
proof -
  \<comment> \<open>the intermediate statement carries FULL type annotations; without them
      the obligations \<open>pathify_measurable\<close> generates elaborate at types the
      component lemmas no longer match.\<close>
  have "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. restrict
          (\<lambda>t. (cbmX (0 :: real^'n) t \<omega>, t *\<^sub>R (mat 1 :: real^'n^'n))) {0..T})
      \<in> bm_paths \<rightarrow>\<^sub>M (path_borel T :: ('n pairpath) measure)"
  proof (rule pathify_measurable[OF T])
    fix t :: real assume "t \<in> {0..T}"
    have c: "(\<lambda>v :: real^'n. (v, t *\<^sub>R (mat 1 :: real^'n^'n)))
        \<in> borel_measurable borel"
      by (intro borel_measurable_continuous_onI continuous_intros)
    show "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real.
          (cbmX (0 :: real^'n) t \<omega>, t *\<^sub>R (mat 1 :: real^'n^'n)))
        \<in> borel_measurable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)"
      by (rule measurable_compose[OF measurable_cbmX c])
  next
    fix \<omega> :: "'n \<Rightarrow> real \<Rightarrow> real"
    show "continuous_on {0..T}
        (\<lambda>t. (cbmX (0 :: real^'n) t \<omega>, t *\<^sub>R (mat 1 :: real^'n^'n)))"
      by (rule continuous_on_bmpair_path)
  qed
  moreover have "(bmpair T :: ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> 'n pairpath)
      = (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. restrict
          (\<lambda>t. (cbmX (0 :: real^'n) t \<omega>, t *\<^sub>R (mat 1 :: real^'n^'n))) {0..T})"
    by (rule ext) (simp add: bmpair_def)
  ultimately show ?thesis by simp
qed

lemma prob_space_bmpair_law:
  assumes T: "0 \<le> T"
  shows "prob_space (pair_law_of T (bmpair T)
      (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure))"
  unfolding pair_law_of_def
  by (rule BMP.prob_space_distr[OF bmpair_measurable[OF T]])

subsection \<open>The two almost-sure clauses for the witness\<close>

lemma bmpair_law_start:
  assumes T: "0 \<le> T"
  shows "AE \<omega> in pair_law_of T (bmpair T)
      (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure).
        fst (\<omega> 0) = (0 :: real^'n) \<and> snd (\<omega> 0) = 0"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  have phim: "bmpair T \<in> ?M \<rightarrow>\<^sub>M ?B" by (rule bmpair_measurable[OF T])
  have mset: "{\<omega> \<in> space ?B. fst (\<omega> 0) = (0 :: real^'n) \<and> snd (\<omega> 0) = 0}
      \<in> sets ?B"
    by (rule start_set_sets[OF refl])
  have iff: "(AE \<omega> in pair_law_of T (bmpair T) ?M.
        fst (\<omega> 0) = (0 :: real^'n) \<and> snd (\<omega> 0) = 0)
      = (AE \<omega> in ?M. fst (bmpair T \<omega> 0) = (0 :: real^'n)
          \<and> snd (bmpair T \<omega> 0) = 0)"
    unfolding pair_law_of_def by (rule AE_distr_iff[OF phim mset])
  have z: "(0::real) \<in> {0..T}" using T by simp
  have "AE \<omega> in ?M. cbmX (0 :: real^'n) 0 \<omega> = bmX 0 0 \<omega>"
    by (intro cbmX_ae_eq) simp
  moreover have "AE \<omega> in ?M. bmX (0 :: real^'n) 0 \<omega> = 0"
    by (rule bmX_start)
  ultimately have "AE \<omega> in ?M. fst (bmpair T \<omega> 0) = (0 :: real^'n)
      \<and> snd (bmpair T \<omega> 0) = 0"
    by eventually_elim (simp add: bmpair_apply[OF z])
  then show ?thesis unfolding iff .
qed

lemma bmpair_law_diffquot:
  assumes T: "0 \<le> T" and L: "1 \<le> L"
  shows "AE \<omega> in pair_law_of T (bmpair T)
      (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure).
        \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
          (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?Q = "pair_law_of T (bmpair T) ?M"
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  have phim: "bmpair T \<in> ?M \<rightarrow>\<^sub>M ?B" by (rule bmpair_measurable[OF T])
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
            *\<^sub>R (snd (bmpair T \<omega> q) - snd (bmpair T \<omega> p)) \<in> sconstraint k L)"
      unfolding pair_law_of_def by (rule AE_distr_iff[OF phim mm])
    have "AE \<omega> in ?M. (1 / (q - p))
        *\<^sub>R (snd (bmpair T \<omega> q) - snd (bmpair T \<omega> p)) \<in> sconstraint k L"
    proof (intro AE_I2)
      fix \<omega> :: "'n \<Rightarrow> real \<Rightarrow> real"
      have "(1 / (q - p)) *\<^sub>R (snd (bmpair T \<omega> q) - snd (bmpair T \<omega> p))
          = (1 / (q - p)) *\<^sub>R ((q - p) *\<^sub>R (mat 1 :: real^'n^'n))"
        using pq by (simp add: bmpair_apply scaleR_left_diff_distrib)
      also have "\<dots> = (mat 1 :: real^'n^'n)"
        using pq(3) by simp
      finally show "(1 / (q - p))
          *\<^sub>R (snd (bmpair T \<omega> q) - snd (bmpair T \<omega> p)) \<in> sconstraint k L"
        using mat_1_in_sconstraint[OF L] by simp
    qed
    then show ?thesis unfolding iff .
  qed
  \<comment> \<open>the rational reduction, exactly as in
      \<open>Exit_Class.exit_class_diffquot_limit\<close>\<close>
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
    then have R: "\<And>p q :: real. p \<in> \<rat> \<Longrightarrow> q \<in> \<rat> \<Longrightarrow> 0 \<le> p \<Longrightarrow> p < q \<Longrightarrow> q \<le> T
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

subsection \<open>The two martingale clauses for the witness\<close>

lemma bmpair_adapted:
  fixes r u :: real
  assumes r: "0 \<le> r" and ru: "r \<le> u"
  shows "(\<lambda>\<omega> :: 'n::finite \<Rightarrow> real \<Rightarrow> real. bmpair T \<omega> r) \<in> borel_measurable
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
  have c: "(\<lambda>v :: real^'n. (v, r *\<^sub>R (mat 1 :: real^'n^'n)))
      \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  have "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real.
        (cbmX (0 :: real^'n) r \<omega>, r *\<^sub>R (mat 1 :: real^'n^'n)))
      \<in> borel_measurable (?F u)"
    by (rule measurable_compose[OF cu c])
  then show ?thesis using True by (simp add: bmpair_apply)
next
  case False
  then have "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. bmpair T \<omega> r) = (\<lambda>\<omega>. undefined)"
    by (auto simp: bmpair_def)
  then show ?thesis by simp
qed

theorem bmpair_law_X_martingale:
  assumes T: "0 \<le> T"
  shows "martingale (pair_law_of T (bmpair T)
        (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure))
      (natural_filtration (pair_law_of T (bmpair T) bm_paths) 0 (\<lambda>v \<omega>. \<omega> v)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u T)) :: real^'n)"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?Q = "pair_law_of T (bmpair T) ?M"
  let ?F = "natural_filtration ?M 0 (cbmX (0 :: real^'n))"
  let ?G = "natural_filtration ?Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  have Zm: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min u T))) \<in> borel_measurable (?G u)"
    if u: "0 \<le> u" for u
  proof -
    have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u T)) \<in> ?G u \<rightarrow>\<^sub>M borel"
      by (rule natural_filtration_eval) (use u T in auto)
    show ?thesis by (rule measurable_compose[OF ev pair_fst_borel])
  qed
  have mg: "martingale ?M ?F 0 (\<lambda>u \<omega>. fst (bmpair T \<omega> (min u T)))"
  proof (rule martingale_cong_ge
      [OF martingale_stopped_const[OF T martingale_cbmX]])
    fix u :: real assume u: "0 \<le> u"
    have mI: "min u T \<in> {0..T}" using u T by simp
    show "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. cbmX (0 :: real^'n) (min u T) \<omega>)
        = (\<lambda>\<omega>. fst (bmpair T \<omega> (min u T)))"
      by (rule ext) (simp add: bmpair_apply[OF mI])
  qed
  show ?thesis
    by (rule martingale_pair_law[OF prob_space_bm_paths
        bmpair_measurable[OF T] bmpair_adapted Zm mg])
qed

theorem bmpair_law_comp_martingale:
  assumes T: "0 \<le> T"
  shows "martingale (pair_law_of T (bmpair T)
        (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure))
      (natural_filtration (pair_law_of T (bmpair T) bm_paths) 0 (\<lambda>v \<omega>. \<omega> v)) 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (min u T)) :: real^'n) - snd (\<omega> (min u T)))"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?Q = "pair_law_of T (bmpair T) ?M"
  let ?F = "natural_filtration ?M 0 (cbmX (0 :: real^'n))"
  let ?G = "natural_filtration ?Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  \<comment> \<open>as in \<open>comp_entry_cont\<close>: rewrite to the ENTRYWISE form first, then
      \<open>continuous_on_vec_lambda\<close> twice.\<close>
  have Zm: "(\<lambda>\<omega> :: 'n pairpath.
        outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T)))
      \<in> borel_measurable (?G u)" if u: "0 \<le> u" for u
  proof -
    have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u T)) \<in> ?G u \<rightarrow>\<^sub>M borel"
      by (rule natural_filtration_eval) (use u T in auto)
    show ?thesis by (rule measurable_compose[OF ev compensated_map_borel])
  qed
  have mg: "martingale ?M ?F 0
      (\<lambda>u \<omega>. outerp (fst (bmpair T \<omega> (min u T))) - snd (bmpair T \<omega> (min u T)))"
  proof (rule martingale_cong_ge
      [OF martingale_stopped_const[OF T martingale_cbm_outerp]])
    fix u :: real assume u: "0 \<le> u"
    have mI: "min u T \<in> {0..T}" using u T by simp
    show "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real.
          outerp (cbmX (0 :: real^'n) (min u T) \<omega>) - (min u T) *\<^sub>R mat 1)
        = (\<lambda>\<omega>. outerp (fst (bmpair T \<omega> (min u T)))
             - snd (bmpair T \<omega> (min u T)))"
      by (rule ext) (simp add: bmpair_apply[OF mI])
  qed
  show ?thesis
    by (rule martingale_pair_law[OF prob_space_bm_paths
        bmpair_measurable[OF T] bmpair_adapted Zm mg])
qed

subsection \<open>The witness is a member, so the class is nonempty\<close>

theorem bmpair_law_in_paper_pair_class:
  assumes T: "0 \<le> T" and L: "1 \<le> L"
  shows "pair_law_of T (bmpair T)
      (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure)
    \<in> exit_class k L T (0 :: real^'n)"
  unfolding exit_class_def
proof (intro CollectI conjI)
  show "prob_space (pair_law_of T (bmpair T)
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))"
    by (rule prob_space_bmpair_law[OF T])
  show "sets (pair_law_of T (bmpair T)
        (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      = sets (path_borel T :: ('n pairpath) measure)"
    by simp
  show "AE \<omega> in pair_law_of T (bmpair T)
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
        fst (\<omega> 0) = (0 :: real^'n) \<and> snd (\<omega> 0) = 0"
    by (rule bmpair_law_start[OF T])
  show "AE \<omega> in pair_law_of T (bmpair T)
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
        \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
          (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
    by (rule bmpair_law_diffquot[OF T L])
  show "martingale (pair_law_of T (bmpair T)
        (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      (natural_filtration (pair_law_of T (bmpair T) bm_paths) 0 (\<lambda>t \<omega>. \<omega> t)) 0
      (\<lambda>t \<omega>. fst (\<omega> (min t T)) :: real^'n)"
    by (rule bmpair_law_X_martingale[OF T])
  show "martingale (pair_law_of T (bmpair T)
        (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      (natural_filtration (pair_law_of T (bmpair T) bm_paths) 0 (\<lambda>t \<omega>. \<omega> t)) 0
      (\<lambda>t \<omega>. outerp (fst (\<omega> (min t T)) :: real^'n) - snd (\<omega> (min t T)))"
    by (rule bmpair_law_comp_martingale[OF T])
qed

corollary exit_class_nonempty:
  assumes T: "0 \<le> T" and L: "1 \<le> L"
  shows "exit_class k L T (0 :: real^'n::finite) \<noteq> {}"
  using bmpair_law_in_paper_pair_class[OF T L] by blast

text \<open>Hence clause (1) of Theorem 1.1 for the paper's value function, under
  no hypothesis beyond the paper's own standing ones: \<open>0 < T\<close>, \<open>1 \<le> L\<close>
  (Eq. (1.5)), and \<open>K\<close> closed.\<close>

corollary exit_val_usc_unconditional:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n" and b :: ennreal
  assumes T: "0 < T" and L: "1 \<le> L" and K: "closed K"
    and lt: "exit_val k L T K x < b"
  shows "eventually (\<lambda>y. exit_val k L T K y < b) (nhds x)"
proof (rule exit_val_usc[OF T _ K _ lt])
  show "0 \<le> L" using L by simp
  show "exit_class k L T (0 :: real^'n) \<noteq> {}"
    using T L by (intro exit_class_nonempty) simp_all
qed

section \<open>Consolidating the clauses onto the paper's value function\<close>

text \<open>Clause (0) for \<open>exit_val\<close>: the exit functional of Eq. (1.6) is capped
  at the horizon, so the value is bounded by it outright.  The sharp bound
  \<open>exit_val \<le> ball_v\<close>, giving also clause (3), needs the class-level
  expected-exit-time estimate below.\<close>

theorem exit_val_le_T:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
  assumes T: "0 \<le> T"
  shows "exit_val k L T K x \<le> ennreal T"
  unfolding exit_val_def
proof (rule Sup_least)
  fix c :: ennreal
  assume "c \<in> (\<lambda>Q. ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))))
      ` exit_class k L T x"
  then obtain Q :: "('n pairpath) measure"
    where Q: "Q \<in> exit_class k L T x"
      and c: "c = ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))" by blast
  show "c \<le> ennreal T"
    unfolding c
    by (rule ess_inf_time_le_const[OF exit_class_prob[OF Q]])
      (simp add: pexit_def etime_le_T[OF T])
qed

text \<open>The trace lower bound carried by the constraint set: the identity is a
  rank-\<open>n\<close> projection, so \<open>Pi_proj a n \<le> trace a\<close>, and the constraint's own
  bound at \<open>m = n\<close> is \<open>n - k\<close>.  This makes \<open>|X|\<^sup>2\<close> a submartingale with rate
  at least \<open>n - k\<close>, giving Lemma 2.1's exit-time estimate at the class
  level.\<close>

lemma sconstraint_trace_ge:
  fixes a :: "real^'n::finite^'n"
  assumes k: "k < CARD('n)" and a: "a \<in> sconstraint k L"
  shows "real (CARD('n) - k) \<le> trace a"
proof -
  have p: "psd a"
    and pi: "\<And>m. k < m \<Longrightarrow> m \<le> CARD('n) \<Longrightarrow> real (m - k) \<le> Pi_proj a m"
    using a unfolding sconstraint_def Pi_constraint_def by auto
  have "real (CARD('n) - k) \<le> Pi_proj a CARD('n)" using k by (intro pi) auto
  also have "\<dots> \<le> trace (a ** mat 1)"
    by (rule Pi_proj_le[OF p]) (simp_all add: is_proj_def trace_I)
  also have "\<dots> = trace a" by simp
  finally show ?thesis .
qed

text \<open>\<open>bounded_linear_trace\<close> lives in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>



theorem exit_class_trace_rate:
  fixes Q :: "('n::finite pairpath) measure"
  assumes k: "k < CARD('n)" and Q: "Q \<in> exit_class k L T x"
  shows "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
      real (CARD('n) - k) * (t - s)
        \<le> trace (snd (\<omega> t)) - trace (snd (\<omega> s))"
proof -
  have dq: "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
    using Q unfolding exit_class_def by blast
  show ?thesis
  proof (rule eventually_mono[OF dq])
    fix \<omega> :: "'n pairpath"
    assume q: "\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
    show "\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        real (CARD('n) - k) * (t - s)
          \<le> trace (snd (\<omega> t)) - trace (snd (\<omega> s))"
    proof (intro allI impI)
      fix s t :: real
      assume s: "0 \<le> s" and st: "s < t" and tT: "t \<le> T"
      have mem: "(1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
        using q s st tT by blast
      have "real (CARD('n) - k)
          \<le> trace ((1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)))"
        by (rule sconstraint_trace_ge[OF k mem])
      also have "\<dots> = (trace (snd (\<omega> t)) - trace (snd (\<omega> s))) / (t - s)"
        by (simp add: trace_scaleR trace_diff_matrix)
      finally show "real (CARD('n) - k) * (t - s)
          \<le> trace (snd (\<omega> t)) - trace (snd (\<omega> s))"
        using st by (simp add: pos_le_divide_eq)
    qed
  qed
qed

lemma exit_class_norm_sq_integrable:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> exit_class k L T x" and t: "t \<in> {0..T}"
  shows "integrable Q (\<lambda>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t))"
proof -
  have "integrable Q (\<lambda>\<omega> :: 'n pairpath. \<Sum>i\<in>UNIV. (fst (\<omega> t) $ i)\<^sup>2)"
    by (intro Bochner_Integration.integrable_sum
        exit_class_sq_integrable[OF T L Q t])
  then show ?thesis by (simp add: inner_vec_def power2_eq_square)
qed

text \<open>The class-level form of Lemma 2.1's estimate: the expected squared
  norm grows at rate at least \<open>n - k\<close>, using the compensated clause only at
  the fixed time \<open>t\<close> --- no stopping, no optional sampling.\<close>

theorem exit_class_sq_norm_mean_ge:
  fixes Q :: "('n::finite pairpath) measure"
  assumes k: "k < CARD('n)" and T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> exit_class k L T x" and t: "t \<in> {0..T}"
  shows "x \<bullet> x + real (CARD('n) - k) * t
      \<le> (\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q)"
proof -
  interpret P: prob_space Q by (rule exit_class_prob[OF Q])
  have t0: "0 \<le> t" and tT: "t \<le> T" using t by auto
  have ci: "integrable Q (\<lambda>\<omega>. outerp (fst (\<omega> t)) - snd (\<omega> t))"
    by (rule exit_class_compensated_integrable[OF Q t])
  have ti: "integrable Q (\<lambda>\<omega>. trace (outerp (fst (\<omega> t)) - snd (\<omega> t)))"
    by (rule integrable_bounded_linear[OF bounded_linear_trace ci])
  have ni: "integrable Q (\<lambda>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t))"
    by (rule exit_class_norm_sq_integrable[OF T L Q t])
  have mean: "(\<integral>\<omega>. trace (outerp (fst (\<omega> t)) - snd (\<omega> t)) \<partial>Q) = x \<bullet> x"
  proof -
    have "(\<integral>\<omega>. trace (outerp (fst (\<omega> t)) - snd (\<omega> t)) \<partial>Q)
        = trace (\<integral>\<omega>. outerp (fst (\<omega> t)) - snd (\<omega> t) \<partial>Q)"
      by (rule integral_bounded_linear[OF bounded_linear_trace ci])
    also have "\<dots> = trace (outerp x)"
      by (simp add: exit_class_compensated_mean[OF Q t])
    finally show ?thesis by (simp add: trace_outerp)
  qed
  have st: "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    using Q unfolding exit_class_def by blast
  have tr: "AE \<omega> in Q. \<forall>s t'. 0 \<le> s \<longrightarrow> s < t' \<longrightarrow> t' \<le> T \<longrightarrow>
      real (CARD('n) - k) * (t' - s)
        \<le> trace (snd (\<omega> t')) - trace (snd (\<omega> s))"
    by (rule exit_class_trace_rate[OF k Q])
  have rate: "AE \<omega> in Q. real (CARD('n) - k) * t \<le> trace (snd (\<omega> t))"
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
      have "real (CARD('n) - k) * (t - 0)
          \<le> trace (snd (\<omega> t)) - trace (snd (\<omega> 0))"
        using elim pos tT by blast
      then show ?thesis using elim by (simp add: trace_def)
    qed
  qed
  have ptw: "AE \<omega> in Q. trace (outerp (fst (\<omega> t)) - snd (\<omega> t))
      + real (CARD('n) - k) * t \<le> fst (\<omega> t) \<bullet> fst (\<omega> t)"
    using rate by eventually_elim (simp add: trace_diff_matrix trace_outerp)
  have "(\<integral>\<omega>. trace (outerp (fst (\<omega> t)) - snd (\<omega> t)) \<partial>Q)
      + real (CARD('n) - k) * t
      = (\<integral>\<omega>. trace (outerp (fst (\<omega> t)) - snd (\<omega> t))
            + real (CARD('n) - k) * t \<partial>Q)"
    using ti by (simp add: P.prob_space)
  also have "\<dots> \<le> (\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q)"
    by (rule integral_mono_AE) (use ti ni ptw in auto)
  finally show ?thesis unfolding mean .
qed

text \<open>Clause (3) on the ball: a member starting on the boundary that kept
  \<open>|X| \<le> r\<close> up to a positive time would have expected squared norm at most
  \<open>r\<^sup>2\<close> at an interior time, but \<open>exit_class_sq_norm_mean_ge\<close> forces
  it to be at least \<open>r\<^sup>2 + (n-k)t > r\<^sup>2\<close>.  So the exit time's essential
  infimum, and hence its supremum, is \<open>0\<close>.\<close>

theorem exit_val_boundary_zero:
  fixes r :: real and x :: "real^'n::finite"
  assumes k: "k < CARD('n)" and T: "0 < T" and L: "0 \<le> L"
    and x: "norm x = r"
  shows "exit_val k L T (cball 0 r) x = 0"
proof -
  have T0: "0 \<le> T" using T by simp
  have r0: "0 \<le> r" using x by (metis norm_ge_zero)
  have "exit_val k L T (cball 0 r) x \<le> 0"
    unfolding exit_val_def
  proof (rule Sup_least)
    fix e :: ennreal
    assume "e \<in> (\<lambda>Q. ess_inf_time Q (\<lambda>\<omega>. pexit T (cball 0 r) (\<lambda>t. fst (\<omega> t))))
        ` exit_class k L T x"
    then obtain Q :: "('n pairpath) measure"
      where Q: "Q \<in> exit_class k L T x"
        and e: "e = ess_inf_time Q
            (\<lambda>\<omega>. pexit T (cball 0 r) (\<lambda>t. fst (\<omega> t)))" by blast
    interpret P: prob_space Q by (rule exit_class_prob[OF Q])
    show "e \<le> 0"
    proof (rule ccontr)
      assume "\<not> e \<le> 0"
      then have epos: "0 < e" by (simp add: zero_less_iff_neq_zero)
      have ele: "e \<le> ennreal T"
        unfolding e
        by (rule ess_inf_time_le_const[OF P.prob_space_axioms])
          (simp add: pexit_def etime_le_T[OF T0])
      have efin: "e < \<top>"
        using ele ennreal_less_top by (rule order_le_less_trans)
      define c where "c = enn2real e"
      have ec: "e = ennreal c" unfolding c_def using efin by simp
      have c0: "0 < c"
      proof (rule ccontr)
        assume "\<not> 0 < c"
        then have "ennreal c = 0" by (simp add: ennreal_neg)
        with ec epos show False by simp
      qed
      define t where "t = min (c/2) (T/2)"
      have t0: "0 < t" unfolding t_def using c0 T by simp
      have tc: "t < c" unfolding t_def using c0 by simp
      have tT: "t \<le> T" unfolding t_def using T by simp
      have tI: "t \<in> {0..T}" using t0 tT by simp
      have ae1: "AE \<omega> in Q. e \<le> ennreal (pexit T (cball 0 r) (\<lambda>s. fst (\<omega> s)))"
        unfolding e by (rule ess_inf_time_AE)
      have ae2: "AE \<omega> in Q. fst (\<omega> t) \<bullet> fst (\<omega> t) \<le> r * r"
      proof (rule eventually_mono[OF ae1])
        fix \<omega> :: "'n pairpath"
        assume "e \<le> ennreal (pexit T (cball 0 r) (\<lambda>s. fst (\<omega> s)))"
        then have "ennreal c \<le> ennreal (pexit T (cball 0 r) (\<lambda>s. fst (\<omega> s)))"
          using ec by simp
        moreover have nn: "0 \<le> pexit T (cball 0 r) (\<lambda>s. fst (\<omega> s))"
          unfolding pexit_def by (rule etime_nonneg[OF T0])
        ultimately have ct: "c \<le> pexit T (cball 0 r) (\<lambda>s. fst (\<omega> s))"
          by simp
        have inK: "fst (\<omega> t) \<in> cball 0 r"
        proof (rule ccontr)
          assume notin: "fst (\<omega> t) \<notin> cball 0 r"
          \<comment> \<open>let the CONCLUSION fix \<open>X\<close>, \<open>A\<close> and \<open>\<omega>\<close>; a pre-instantiated
              membership premise beta-reduces and no longer matches.\<close>
          have "pexit T (cball 0 r) (\<lambda>s. fst (\<omega> s)) \<le> t"
            unfolding pexit_def
            by (rule etime_le_of_mem[OF T0 less_imp_le[OF t0] tT])
              (use notin in simp)
          with ct tc show False by simp
        qed
        have "norm (fst (\<omega> t)) \<le> r" using inK by (simp add: dist_norm)
        then have "(norm (fst (\<omega> t)))\<^sup>2 \<le> r\<^sup>2"
          by (rule power_mono) simp
        then show "fst (\<omega> t) \<bullet> fst (\<omega> t) \<le> r * r"
          by (simp add: power2_norm_eq_inner[symmetric] power2_eq_square)
      qed
      have ni: "integrable Q (\<lambda>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t))"
        by (rule exit_class_norm_sq_integrable[OF T0 L Q tI])
      have lo: "x \<bullet> x + real (CARD('n) - k) * t
          \<le> (\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q)"
        by (rule exit_class_sq_norm_mean_ge[OF k T0 L Q tI])
      have hi: "(\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q) \<le> r * r"
      proof -
        have "(\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q) \<le> (\<integral>\<omega>. r * r \<partial>Q)"
          by (rule integral_mono_AE) (use ni ae2 in auto)
        also have "\<dots> = r * r" by (simp add: P.prob_space)
        finally show ?thesis .
      qed
      have xx: "x \<bullet> x = r * r"
        using x by (simp add: power2_norm_eq_inner[symmetric] power2_eq_square)
      \<comment> \<open>simp normalises \<open>real (CARD('n) - k)\<close> to \<open>real CARD('n) - real k\<close>
          inside \<open>lo\<close>, so state the factor in the SAME form or the atoms
          do not agree.\<close>
      have pos: "0 < (real CARD('n) - real k) * t"
      proof (rule mult_pos_pos)
        show "0 < real CARD('n) - real k" using k by simp
        show "0 < t" by (rule t0)
      qed
      have cast: "real (CARD('n) - k) = real CARD('n) - real k"
        using k by simp
      from lo hi pos show False unfolding xx cast by simp
    qed
  qed
  then show ?thesis by simp
qed

text \<open>Example 3.1, inequality (3.10): if the target set fits inside a ball
  of radius \<open>r\<close>, then \<open>v(x) \<le> (r\<^sup>2 - |x|\<^sup>2) / (n - k)\<close>, independent of the
  horizon \<open>T\<close> --- the quantitative form of clause (0), and why the horizon
  cap is eventually invisible.  \<open>exit_val_boundary_zero\<close> is the case
  \<open>|x| = r\<close>.  The paper derives (3.10) from It\<open>\<^bold>o\<close>'s formula; here it
  follows from \<open>exit_class_sq_norm_mean_ge\<close>, Lemma 2.1's estimate at
  a fixed time, with no stochastic calculus.\<close>

theorem exit_val_le_ball_bound:
  fixes r :: real and x :: "real^'n::finite" and K :: "(real^'n) set"
  assumes k: "k < CARD('n)" and T: "0 \<le> T" and L: "0 \<le> L"
    and KB: "K \<subseteq> cball 0 r"
  shows "exit_val k L T K x
      \<le> ennreal ((r * r - x \<bullet> x) / real (CARD('n) - k))"
proof -
  define B where "B = (r * r - x \<bullet> x) / real (CARD('n) - k)"
  have nk: "0 < real (CARD('n) - k)" using k by simp
  have main: "exit_val k L T K x \<le> ennreal B"
    unfolding exit_val_def
  proof (rule Sup_least)
    fix e :: ennreal
    assume "e \<in> (\<lambda>Q. ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))))
        ` exit_class k L T x"
    then obtain Q :: "('n pairpath) measure"
      where Q: "Q \<in> exit_class k L T x"
        and e: "e = ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))" by blast
    interpret P: prob_space Q by (rule exit_class_prob[OF Q])
    show "e \<le> ennreal B"
    proof (rule ccontr)
      assume "\<not> e \<le> ennreal B"
      then have gt: "ennreal B < e" by simp
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
      define m where "m = max B 0"
      have m0: "0 \<le> m" and mB: "B \<le> m" unfolding m_def by auto
      have mc: "m < c"
      proof (cases "0 \<le> B")
        case True
        then have "B < c" using gt unfolding ec by (simp add: ennreal_less_iff)
        then show ?thesis using True unfolding m_def by simp
      next
        case False
        then have z: "ennreal B = 0" by (simp add: ennreal_neg)
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
      have Bt: "B < t" unfolding t_def using mB mc by simp
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
        by (rule exit_class_norm_sq_integrable[OF T L Q tI])
      have lo: "x \<bullet> x + real (CARD('n) - k) * t
          \<le> (\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q)"
        by (rule exit_class_sq_norm_mean_ge[OF k T L Q tI])
      have hi: "(\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q) \<le> r * r"
      proof -
        have "(\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q) \<le> (\<integral>\<omega>. r * r \<partial>Q)"
          by (rule integral_mono_AE) (use ni ae2 in auto)
        also have "\<dots> = r * r" by (simp add: P.prob_space)
        finally show ?thesis .
      qed
      from lo hi have "real (CARD('n) - k) * t \<le> r * r - x \<bullet> x" by simp
      then have "t \<le> B" unfolding B_def
        using nk by (simp add: pos_le_divide_eq mult.commute)
      with Bt show False by simp
    qed
  qed
  from main show ?thesis unfolding B_def .
qed


(*<*)
end
(*>*)
