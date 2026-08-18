section \<open>Shortening the horizon, concatenation, and Proposition 2.4\<close>

(*<*)
theory Exit_Class_Pasting
  imports Exit_Class_Witness
    "Continuous_Time_Martingales.Integrability_Criteria"
    "Continuous_Path_Spaces.Increment_Moments"
    "Continuous_Time_Martingales.Essential_Infimum"
begin

(*>*)

section \<open>The class is closed under shortening the horizon\<close>

text \<open>The conditioning-free half of the closure the weak DPP needs: a
  member on \<open>[0,T]\<close> restricted to \<open>[0,S]\<close> is a member on \<open>[0,S]\<close>.  Both
  martingale clauses follow from \<open>martingale_pair_law\<close> with the restriction
  as path map, adapted for free since \<open>pcut S \<omega> r = \<omega> r\<close> on \<open>{0..S}\<close>, and
  \<open>martingale_stopped_const\<close> turns the \<open>T\<close>-clause into the \<open>S\<close>-clause.\<close>

definition pcut :: "real \<Rightarrow> 'n::finite pairpath \<Rightarrow> 'n pairpath"
  where "pcut S \<omega> = restrict \<omega> {0..S}"

lemma pcut_apply: "r \<in> {0..S} \<Longrightarrow> pcut S \<omega> r = \<omega> r"
  by (simp add: pcut_def)

lemma pcut_measurable:
  fixes Q :: "('n::finite pairpath) measure"
  assumes S: "0 \<le> S" and ST: "S \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
  shows "pcut S \<in> Q \<rightarrow>\<^sub>M (path_borel S :: ('n pairpath) measure)"
proof -
  have "(\<lambda>f :: 'n pairpath. restrict f {0..S})
      \<in> (path_borel T :: ('n pairpath) measure)
        \<rightarrow>\<^sub>M (path_borel S :: ('n pairpath) measure)"
    by (rule restrict_measurable_path_borel[OF S ST])
  then show ?thesis
    unfolding pcut_def using measurable_cong_sets[OF setsQ refl] by blast
qed

lemma pcut_adapted:
  fixes Q :: "('n::finite pairpath) measure"
  assumes S: "0 \<le> S" and r: "0 \<le> r" and ru: "r \<le> u"
  shows "(\<lambda>\<omega> :: 'n pairpath. pcut S \<omega> r) \<in> borel_measurable
      (natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v) u)"
proof (cases "r \<in> {0..S}")
  case True
  have "(\<lambda>\<omega> :: 'n pairpath. \<omega> r) \<in> natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v) u
      \<rightarrow>\<^sub>M borel"
    unfolding natural_filtration_def
    by (rule measurable_family_vimage_algebra) (use r ru in auto)
  then show ?thesis using True by (simp add: pcut_apply)
next
  case False
  then have "(\<lambda>\<omega> :: 'n pairpath. pcut S \<omega> r) = (\<lambda>\<omega>. undefined)"
    by (auto simp: pcut_def)
  then show ?thesis by simp
qed

text \<open>The rational reduction of the covariation clause, factored out since
  it recurs in every construction of a class member: countably many pairs
  by \<open>AE_ball_countable'\<close>, then \<open>diffquot_all_of_rational\<close> against path
  continuity.\<close>

lemma exit_class_diffquot_of_pairs:
  fixes Q :: "('n::finite pairpath) measure"
  assumes setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and one: "\<And>p q :: real. p \<in> {0..T} \<Longrightarrow> q \<in> {0..T} \<Longrightarrow> p < q \<Longrightarrow>
      AE \<omega> in Q. (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
  shows "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
proof -
  have spQ: "space Q = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsQ])
  have rat: "AE \<omega> in Q. \<forall>p\<in>(\<rat>::real set). \<forall>q\<in>(\<rat>::real set).
      0 \<le> p \<longrightarrow> p < q \<longrightarrow> q \<le> T \<longrightarrow>
      (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
  proof (rule AE_ball_countable'[OF _ countable_rat])
    fix p :: real assume "p \<in> \<rat>"
    show "AE \<omega> in Q. \<forall>q\<in>(\<rat>::real set). 0 \<le> p \<longrightarrow> p < q \<longrightarrow> q \<le> T \<longrightarrow>
        (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
    proof (rule AE_ball_countable'[OF _ countable_rat])
      fix q :: real assume "q \<in> \<rat>"
      show "AE \<omega> in Q. 0 \<le> p \<longrightarrow> p < q \<longrightarrow> q \<le> T \<longrightarrow>
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
      and W: "\<omega> \<in> space Q" by blast+
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

text \<open>A member of the class at horizon \<open>T\<close>, cut back to \<open>[0,S]\<close>, is a
  member at horizon \<open>S\<close>: the \<open>AE\<close> clauses of (1.7) survive because \<open>pcut\<close>
  is the identity on \<open>[0,S]\<close>, the martingale clauses because stopping at
  \<open>S\<close> is harmless (\<open>martingale_stopped_const\<close>) and transports along
  \<open>pcut\<close> (\<open>martingale_pair_law\<close>).\<close>

theorem exit_class_pcut:
  fixes Q :: "('n::finite pairpath) measure"
  assumes S: "0 \<le> S" and ST: "S \<le> T" and Q: "Q \<in> exit_class k L T x"
  shows "pair_law_of S (pcut S) Q \<in> exit_class k L S x"
proof -
  let ?Q = "pair_law_of S (pcut S) Q"
  let ?B = "(path_borel S :: ('n pairpath) measure)"
  let ?F = "natural_filtration Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?G = "natural_filtration ?Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  have setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    by (rule exit_class_sets[OF Q])
  interpret P: prob_space Q by (rule exit_class_prob[OF Q])
  have phim: "pcut S \<in> Q \<rightarrow>\<^sub>M ?B" by (rule pcut_measurable[OF S ST setsQ])
  have prob': "prob_space ?Q"
    unfolding pair_law_of_def by (rule P.prob_space_distr[OF phim])
  have adap: "(\<lambda>\<omega> :: 'n pairpath. pcut S \<omega> r) \<in> borel_measurable (?F u)"
    if "0 \<le> r" "r \<le> u" for r u
    by (rule pcut_adapted[OF S that])
  have mT: "min u S \<le> T" for u
    using min.cobounded2[of u S] ST by linarith

  \<comment> \<open>clause (i): the initial condition\<close>
  have start': "AE \<omega> in ?Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
  proof -
    have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> 0) \<in> borel_measurable ?B"
      by (rule pair_law_eval_measurable[OF refl])
    have mset: "{\<omega> \<in> space ?B. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0} \<in> sets ?B"
    proof -
      have "{\<omega> \<in> space ?B. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0}
          = (\<lambda>\<omega> :: 'n pairpath. \<omega> 0) -` {(x, 0)} \<inter> space ?B"
        by (auto simp: prod_eq_iff)
      then show ?thesis using measurable_sets[OF ev] by simp
    qed
    have iff: "(AE \<omega> in ?Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0)
        = (AE \<omega> in Q. fst (pcut S \<omega> 0) = x \<and> snd (pcut S \<omega> 0) = 0)"
      unfolding pair_law_of_def by (rule AE_distr_iff[OF phim mset])
    have z: "(0::real) \<in> {0..S}" using S by simp
    have "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
      using Q unfolding exit_class_def by blast
    then have "AE \<omega> in Q. fst (pcut S \<omega> 0) = x \<and> snd (pcut S \<omega> 0) = 0"
      by eventually_elim (simp add: pcut_apply[OF z])
    then show ?thesis unfolding iff .
  qed

  \<comment> \<open>clause (ii): the eigenvalue constraint on the covariation\<close>
  have cov': "AE \<omega> in ?Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> S \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
  proof (rule exit_class_diffquot_of_pairs[OF sets_pair_law_of])
    fix p q :: real
    assume pq: "p \<in> {0..S}" "q \<in> {0..S}" "p < q"
    have mm: "{\<omega> \<in> space ?B.
        (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L} \<in> sets ?B"
      using borel_of_closed[OF closedin_diffquot_constraint[OF pq(1) pq(2)]]
      by (simp add: space_borel_of)
    have iff: "(AE \<omega> in ?Q.
          (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L)
        = (AE \<omega> in Q. (1 / (q - p))
            *\<^sub>R (snd (pcut S \<omega> q) - snd (pcut S \<omega> p)) \<in> sconstraint k L)"
      unfolding pair_law_of_def by (rule AE_distr_iff[OF phim mm])
    have "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
      using Q unfolding exit_class_def by blast
    then have "AE \<omega> in Q. (1 / (q - p))
        *\<^sub>R (snd (pcut S \<omega> q) - snd (pcut S \<omega> p)) \<in> sconstraint k L"
    proof eventually_elim
      case (elim \<omega>)
      have "(1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
        using elim pq ST by auto
      then show ?case using pq by (simp add: pcut_apply)
    qed
    then show "AE \<omega> in ?Q.
        (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
      unfolding iff .
  qed

  \<comment> \<open>clause (iii): \<open>X\<close> is a martingale\<close>
  have mgX': "martingale ?Q ?G 0 (\<lambda>u \<omega>. fst (\<omega> (min u S)) :: real^'n)"
  proof (rule martingale_pair_law[OF P.prob_space_axioms phim adap])
    fix u :: real assume u: "0 \<le> u"
    have fstB: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
        \<in> borel_measurable borel"
      by (intro borel_measurable_continuous_onI continuous_intros)
    have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u S)) \<in> ?G u \<rightarrow>\<^sub>M borel"
      unfolding natural_filtration_def
      by (rule measurable_family_vimage_algebra) (use u S in auto)
    show "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min u S))) \<in> borel_measurable (?G u)"
      by (rule measurable_compose[OF ev fstB])
  next
    show "martingale Q ?F 0 (\<lambda>u \<omega>. fst (pcut S \<omega> (min u S)) :: real^'n)"
    proof (rule martingale_cong_ge
        [OF martingale_stopped_const[OF S exit_class_X_martingale[OF Q]]])
      fix u :: real assume u: "0 \<le> u"
      have mI: "min u S \<in> {0..S}" using u S by simp
      have e1: "min (min u S) T = min u S" using mT by (rule min_absorb1)
      show "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min (min u S) T)))
          = (\<lambda>\<omega>. fst (pcut S \<omega> (min u S)) :: real^'n)"
        by (rule ext) (simp add: e1 pcut_apply[OF mI])
    qed
  qed

  \<comment> \<open>clause (iv): the compensated process is a martingale\<close>
  have mgC': "martingale ?Q ?G 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (min u S)) :: real^'n) - snd (\<omega> (min u S)))"
  proof (rule martingale_pair_law[OF P.prob_space_axioms phim adap])
    fix u :: real assume u: "0 \<le> u"
    have e: "(\<lambda>p :: (real^'n) \<times> (real^'n^'n). outerp (fst p) - snd p)
        = (\<lambda>p. \<chi> i j. fst p $ i * fst p $ j - snd p $ i $ j)"
      by (rule ext) (simp add: outerp_def vec_eq_iff)
    have cB: "(\<lambda>p :: (real^'n) \<times> (real^'n^'n). outerp (fst p) - snd p)
        \<in> borel_measurable borel"
      unfolding e
      by (intro borel_measurable_continuous_onI continuous_on_vec_lambda
          continuous_intros)
    have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u S)) \<in> ?G u \<rightarrow>\<^sub>M borel"
      unfolding natural_filtration_def
      by (rule measurable_family_vimage_algebra) (use u S in auto)
    show "(\<lambda>\<omega> :: 'n pairpath. outerp (fst (\<omega> (min u S))) - snd (\<omega> (min u S)))
        \<in> borel_measurable (?G u)"
      by (rule measurable_compose[OF ev cB])
  next
    show "martingale Q ?F 0 (\<lambda>u \<omega>. outerp (fst (pcut S \<omega> (min u S)) :: real^'n)
        - snd (pcut S \<omega> (min u S)))"
    proof (rule martingale_cong_ge[OF martingale_stopped_const
          [OF S exit_class_compensated_martingale[OF Q]]])
      fix u :: real assume u: "0 \<le> u"
      have mI: "min u S \<in> {0..S}" using u S by simp
      have e1: "min (min u S) T = min u S" using mT by (rule min_absorb1)
      show "(\<lambda>\<omega> :: 'n pairpath. outerp (fst (\<omega> (min (min u S) T)))
            - snd (\<omega> (min (min u S) T)))
          = (\<lambda>\<omega>. outerp (fst (pcut S \<omega> (min u S)) :: real^'n)
              - snd (pcut S \<omega> (min u S)))"
        by (rule ext) (simp add: e1 pcut_apply[OF mI])
    qed
  qed

  show ?thesis
    unfolding exit_class_def mem_Collect_eq
    using prob' sets_pair_law_of start' cov' mgX' mgC' by blast
qed

section \<open>Concatenation of pair paths\<close>

text \<open>The other half of the dynamic programming principle needs the class
  closed under pasting: run \<open>\<omega>\<close> to time \<open>r\<close>, then continue with an
  independent path \<open>\<omega>'\<close> re-based at \<open>\<omega> r\<close>.  Both components concatenate
  additively --- \<open>X\<close> because increments do, \<open>Y = \<langle>X\<rangle>\<close> because covariation
  concatenates.  Here \<open>r\<close> is an arbitrary real; a stopping-time glue
  instantiates \<open>r\<close> with \<open>\<theta> \<omega>\<close>.\<close>

definition pglue :: "real \<Rightarrow> real \<Rightarrow> 'n::finite pairpath \<Rightarrow> 'n pairpath
    \<Rightarrow> 'n pairpath"
  where "pglue r T \<omega> \<omega>' =
     restrict (\<lambda>t. if t \<le> r then \<omega> t else \<omega> r + (\<omega>' (t - r) - \<omega>' 0)) {0..T}"

lemma pglue_le: "t \<in> {0..T} \<Longrightarrow> t \<le> r \<Longrightarrow> pglue r T \<omega> \<omega>' t = \<omega> t"
  by (simp add: pglue_def)

lemma pglue_ge:
  "t \<in> {0..T} \<Longrightarrow> r \<le> t \<Longrightarrow> pglue r T \<omega> \<omega>' t = \<omega> r + (\<omega>' (t - r) - \<omega>' 0)"
  by (cases "t = r") (auto simp: pglue_def)

lemma pglue_zero: "0 \<le> r \<Longrightarrow> 0 \<le> T \<Longrightarrow> pglue r T \<omega> \<omega>' 0 = \<omega> 0"
  by (rule pglue_le) auto

lemma continuous_on_pglue:
  fixes \<omega> \<omega>' :: "'n::finite pairpath"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and c1: "continuous_on {0..r} \<omega>"
    and c2: "continuous_on {0..T - r} \<omega>'"
  shows "continuous_on {0..T}
      (\<lambda>t. if t \<le> r then \<omega> t else \<omega> r + (\<omega>' (t - r) - \<omega>' 0))"
proof -
  let ?f = "\<lambda>t. if t \<le> r then \<omega> t else \<omega> r + (\<omega>' (t - r) - \<omega>' 0)"
  have U: "{0..T} = {0..r} \<union> {r..T}" using r rT by auto
  have A: "continuous_on {0..r} ?f"
    by (rule continuous_on_eq[OF c1]) simp
  have B: "continuous_on {r..T} ?f"
  proof (rule continuous_on_eq)
    have "continuous_on {r..T} (\<lambda>t. \<omega>' (t - r))"
      by (rule continuous_on_compose2[OF c2 continuous_on_diff
            [OF continuous_on_id continuous_on_const]]) auto
    then show "continuous_on {r..T} (\<lambda>t. \<omega> r + (\<omega>' (t - r) - \<omega>' 0))"
      by (intro continuous_intros)
  next
    fix t :: real assume "t \<in> {r..T}"
    then show "\<omega> r + (\<omega>' (t - r) - \<omega>' 0) = ?f t" by (cases "t = r") auto
  qed
  show ?thesis unfolding U by (rule continuous_on_closed_Un[OF _ _ A B]) auto
qed

lemma pglue_in_mspace:
  fixes \<omega> \<omega>' :: "'n::finite pairpath"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and w: "\<omega> \<in> mspace (path_metric r :: ('n pairpath) metric)"
    and w': "\<omega>' \<in> mspace (path_metric (T - r) :: ('n pairpath) metric)"
  shows "pglue r T \<omega> \<omega>' \<in> mspace (path_metric T :: ('n pairpath) metric)"
  unfolding pglue_def
  by (rule mspace_path_metricI[OF continuous_on_pglue[OF r rT
        mspace_path_metricD[OF w] mspace_path_metricD[OF w']]])

lemma pglue_measurable:
  fixes Q R :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsQ: "sets Q = sets (path_borel r :: ('n pairpath) measure)"
    and setsR: "sets R = sets ((path_borel (T - r) :: ('n pairpath) measure))"
  shows "(\<lambda>p. pglue r T (fst p) (snd p)) \<in> Q \<Otimes>\<^sub>M R \<rightarrow>\<^sub>M
      (path_borel T :: ('n pairpath) measure)"
proof -
  have T0: "0 \<le> T" using r rT by simp
  have eQ: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. fst p v) \<in> borel_measurable (Q \<Otimes>\<^sub>M R)"
    for v
    by (rule measurable_compose[OF measurable_fst
          pair_law_eval_measurable[OF setsQ]])
  have eR: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. snd p v) \<in> borel_measurable (Q \<Otimes>\<^sub>M R)"
    for v
    by (rule measurable_compose[OF measurable_snd
          pair_law_eval_measurable[OF setsR]])
  have Xm: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath.
        if t \<le> r then fst p t else fst p r + (snd p (t - r) - snd p 0))
      \<in> borel_measurable (Q \<Otimes>\<^sub>M R)" for t
    using eQ eR by simp
  have cont: "continuous_on {0..T} (\<lambda>t. if t \<le> r then fst p t
        else fst p r + (snd p (t - r) - snd p 0))"
    if p: "p \<in> space (Q \<Otimes>\<^sub>M R)" for p :: "'n pairpath \<times> 'n pairpath"
  proof (rule continuous_on_pglue[OF r rT])
    have "fst p \<in> space Q" "snd p \<in> space R"
      using p by (auto simp: space_pair_measure)
    then show "continuous_on {0..r} (fst p)" "continuous_on {0..T - r} (snd p)"
      using space_of_path_sets[OF setsQ] space_of_path_sets[OF setsR]
      by (auto intro: mspace_path_metricD)
  qed
  show ?thesis
    using pathify_measurable[OF T0 Xm cont] unfolding pglue_def by simp
qed

text \<open>The eigenvalue constraint (1.7) survives concatenation: across the
  glue point the difference quotient is a convex combination of one
  quotient from each piece, which is why the constraint set had to be
  convexified (Lemma 2.1, \<open>sconstraint_convex\<close>) --- the unconvexified set
  of (1.4) would not do.\<close>

lemma pglue_diffquot:
  fixes \<omega> \<omega>' :: "'n::finite pairpath"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and A: "\<And>p q :: real. 0 \<le> p \<Longrightarrow> p < q \<Longrightarrow> q \<le> r \<Longrightarrow>
        (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
    and B: "\<And>p q :: real. 0 \<le> p \<Longrightarrow> p < q \<Longrightarrow> q \<le> T - r \<Longrightarrow>
        (1 / (q - p)) *\<^sub>R (snd (\<omega>' q) - snd (\<omega>' p)) \<in> sconstraint k L"
    and s: "0 \<le> s" and st: "s < t" and tT: "t \<le> T"
  shows "(1 / (t - s)) *\<^sub>R
      (snd (pglue r T \<omega> \<omega>' t) - snd (pglue r T \<omega> \<omega>' s)) \<in> sconstraint k L"
proof -
  have sT: "s \<in> {0..T}" and tI: "t \<in> {0..T}" using s st tT by auto
  consider (early) "t \<le> r" | (late) "r \<le> s" | (mid) "s < r" "r < t" by fastforce
  then show ?thesis
  proof cases
    case early
    then have "s \<le> r" using st by simp
    then show ?thesis
      using A[OF s st early] by (simp add: pglue_le[OF sT] pglue_le[OF tI early])
  next
    case late
    then have rt: "r \<le> t" using st by simp
    have "(1 / ((t - r) - (s - r))) *\<^sub>R (snd (\<omega>' (t - r)) - snd (\<omega>' (s - r)))
        \<in> sconstraint k L"
      using B[of "s - r" "t - r"] late st tT by simp
    then show ?thesis
      by (simp add: pglue_ge[OF sT late] pglue_ge[OF tI rt])
  next
    case mid
    let ?a = "(1 / (r - s)) *\<^sub>R (snd (\<omega> r) - snd (\<omega> s))"
    let ?b = "(1 / (t - r)) *\<^sub>R (snd (\<omega>' (t - r)) - snd (\<omega>' 0))"
    have aA: "?a \<in> sconstraint k L" by (rule A[OF s mid(1) order_refl])
    have bB: "?b \<in> sconstraint k L"
      using B[of 0 "t - r"] mid(2) tT by simp
    have pos: "0 < r - s" "0 < t - r" "0 < t - s" using mid st by auto
    have sum1: "(r - s) / (t - s) + (t - r) / (t - s) = 1"
      by (subst add_divide_distrib[symmetric]) (use pos(3) in simp)
    have cc: "((r - s) / (t - s)) *\<^sub>R ?a + ((t - r) / (t - s)) *\<^sub>R ?b
        \<in> sconstraint k L"
      using pos by (intro convexD[OF sconstraint_convex aA bB] sum1) auto
    have e1: "((r - s) / (t - s)) *\<^sub>R ?a
        = (1 / (t - s)) *\<^sub>R (snd (\<omega> r) - snd (\<omega> s))"
      using pos by simp
    have e2: "((t - r) / (t - s)) *\<^sub>R ?b
        = (1 / (t - s)) *\<^sub>R (snd (\<omega>' (t - r)) - snd (\<omega>' 0))"
      using pos by simp
    have "snd (pglue r T \<omega> \<omega>' t) - snd (pglue r T \<omega> \<omega>' s)
        = (snd (\<omega> r) - snd (\<omega> s)) + (snd (\<omega>' (t - r)) - snd (\<omega>' 0))"
      using mid(1) less_imp_le[OF mid(2)]
      by (simp add: pglue_le[OF sT] pglue_ge[OF tI])
    then show ?thesis
      using cc unfolding e1 e2 by (simp add: scaleR_right_distrib)
  qed
qed

subsection \<open>The pasted law\<close>

definition pglue_law :: "real \<Rightarrow> real \<Rightarrow> ('n::finite pairpath) measure
    \<Rightarrow> ('n pairpath) measure \<Rightarrow> ('n pairpath) measure"
  where "pglue_law r T Q R
     = pair_law_of T (\<lambda>p. pglue r T (fst p) (snd p)) (Q \<Otimes>\<^sub>M R)"

lemma sets_pglue_law[simp]:
  "sets (pglue_law r T Q R)
     = sets (path_borel T :: ('n::finite pairpath) measure)"
  unfolding pglue_law_def by (rule sets_pair_law_of)

text \<open>\<open>prob_space_pair_measure\<close> lives in
  @{theory Continuous_Time_Martingales.Martingale_Transfer}.\<close>

lemma prob_space_pglue_law:
  fixes Q R :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and PQ: "prob_space Q" and PR: "prob_space R"
    and setsQ: "sets Q = sets (path_borel r :: ('n pairpath) measure)"
    and setsR: "sets R = sets ((path_borel (T - r) :: ('n pairpath) measure))"
  shows "prob_space (pglue_law r T Q R)"
proof -
  interpret PP: prob_space "Q \<Otimes>\<^sub>M R"
    by (rule prob_space_pair_measure[OF PQ PR])
  show ?thesis
    unfolding pglue_law_def pair_law_of_def
    by (rule PP.prob_space_distr[OF pglue_measurable[OF r rT setsQ setsR]])
qed

text \<open>The transfer principle for almost-sure statements: a property of the
  glued path holds \<open>pglue_law\<close>-a.s. as soon as it follows from one
  \<open>Q\<close>-a.s. property of the first piece and one \<open>R\<close>-a.s. property of the
  second.  Both \<open>AE\<close> clauses of (1.7) are of this shape.\<close>

lemma AE_pglue_law:
  fixes Q R :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and PQ: "prob_space Q" and PR: "prob_space R"
    and setsQ: "sets Q = sets (path_borel r :: ('n pairpath) measure)"
    and setsR: "sets R = sets ((path_borel (T - r) :: ('n pairpath) measure))"
    and mset: "{\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric). P \<omega>}
        \<in> sets (path_borel T :: ('n pairpath) measure)"
    and A: "AE \<omega> in Q. A \<omega>" and B: "AE \<omega>' in R. B \<omega>'"
    and imp: "\<And>\<omega> \<omega>' :: 'n pairpath.
        \<omega> \<in> mspace (path_metric r :: ('n pairpath) metric) \<Longrightarrow>
        \<omega>' \<in> mspace (path_metric (T - r) :: ('n pairpath) metric) \<Longrightarrow>
        A \<omega> \<Longrightarrow> B \<omega>' \<Longrightarrow> P (pglue r T \<omega> \<omega>')"
  shows "AE \<omega> in pglue_law r T Q R. P \<omega>"
proof -
  let ?M = "Q \<Otimes>\<^sub>M R"
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?g = "\<lambda>p :: 'n pairpath \<times> 'n pairpath. pglue r T (fst p) (snd p)"
  interpret PQ: prob_space Q by (rule PQ)
  interpret PR: prob_space R by (rule PR)
  interpret PP: pair_prob_space Q R by unfold_locales
  have phim: "?g \<in> ?M \<rightarrow>\<^sub>M ?B" by (rule pglue_measurable[OF r rT setsQ setsR])
  have mset': "{\<omega> \<in> space ?B. P \<omega>} \<in> sets ?B"
    using mset by (simp add: space_borel_of)
  have iff: "(AE \<omega> in pglue_law r T Q R. P \<omega>) = (AE p in ?M. P (?g p))"
    unfolding pglue_law_def pair_law_of_def by (rule AE_distr_iff[OF phim mset'])
  have evm: "{p \<in> space ?M. P (?g p)} \<in> sets ?M"
  proof -
    have "{p \<in> space ?M. P (?g p)} = ?g -` {\<omega> \<in> space ?B. P \<omega>} \<inter> space ?M"
      using measurable_space[OF phim] by auto
    then show ?thesis using measurable_sets[OF phim mset'] by simp
  qed
  have inner: "AE \<omega> in Q. AE \<omega>' in R. P (?g (\<omega>, \<omega>'))"
  proof -
    have RB: "AE \<omega>' in R. B \<omega>'
        \<and> \<omega>' \<in> mspace (path_metric (T - r) :: ('n pairpath) metric)"
      using B AE_space[of R] space_of_path_sets[OF setsR]
      by (auto intro: eventually_conj)
    have QA: "AE \<omega> in Q. A \<omega>
        \<and> \<omega> \<in> mspace (path_metric r :: ('n pairpath) metric)"
      using A AE_space[of Q] space_of_path_sets[OF setsQ]
      by (auto intro: eventually_conj)
    show ?thesis
    proof (rule eventually_mono[OF QA])
      fix \<omega> :: "'n pairpath"
      assume w: "A \<omega> \<and> \<omega> \<in> mspace (path_metric r :: ('n pairpath) metric)"
      show "AE \<omega>' in R. P (?g (\<omega>, \<omega>'))"
      proof (rule eventually_mono[OF RB])
        fix \<omega>' :: "'n pairpath"
        assume "B \<omega>'
            \<and> \<omega>' \<in> mspace (path_metric (T - r) :: ('n pairpath) metric)"
        with w show "P (?g (\<omega>, \<omega>'))" by (simp add: imp)
      qed
    qed
  qed
  have "AE p in ?M. P (?g p)"
    using PP.AE_pair_measure[OF evm] inner by simp
  then show ?thesis unfolding iff .
qed

lemma pglue_law_start:
  fixes Q R :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and Q: "Q \<in> exit_class k L r x"
    and R: "R \<in> exit_class k L (T - r) 0"
  shows "AE \<omega> in pglue_law r T Q R. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> 0) \<in> borel_measurable ?B"
    by (rule pair_law_eval_measurable[OF refl])
  have mset: "{\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
      fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0} \<in> sets ?B"
  proof -
    have "{\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
        fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0}
        = (\<lambda>\<omega> :: 'n pairpath. \<omega> 0) -` {(x, 0)} \<inter> space ?B"
      by (auto simp: prod_eq_iff space_borel_of)
    then show ?thesis using measurable_sets[OF ev] by simp
  qed
  show ?thesis
  proof (rule AE_pglue_law[OF r rT exit_class_prob[OF Q]
        exit_class_prob[OF R] exit_class_sets[OF Q]
        exit_class_sets[OF R] mset])
    show "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
      using Q unfolding exit_class_def by blast
    show "AE \<omega>' in R. True" by simp
    fix \<omega> \<omega>' :: "'n pairpath"
    assume "\<omega> \<in> mspace (path_metric r :: ('n pairpath) metric)"
      and "\<omega>' \<in> mspace (path_metric (T - r) :: ('n pairpath) metric)"
      and st: "fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0" and "True"
    from st show "fst (pglue r T \<omega> \<omega>' 0) = x \<and> snd (pglue r T \<omega> \<omega>' 0) = 0"
      using r rT by (simp add: pglue_zero)
  qed
qed

lemma pglue_law_diffquot:
  fixes Q R :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and Q: "Q \<in> exit_class k L r x"
    and R: "R \<in> exit_class k L (T - r) 0"
  shows "AE \<omega> in pglue_law r T Q R. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
proof (rule exit_class_diffquot_of_pairs[OF sets_pglue_law])
  fix p q :: real
  assume pq: "p \<in> {0..T}" "q \<in> {0..T}" "p < q"
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  have mset: "{\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
      (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L} \<in> sets ?B"
    by (rule borel_of_closed[OF closedin_diffquot_constraint[OF pq(1) pq(2)]])
  show "AE \<omega> in pglue_law r T Q R.
      (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
  proof (rule AE_pglue_law[OF r rT exit_class_prob[OF Q]
        exit_class_prob[OF R] exit_class_sets[OF Q]
        exit_class_sets[OF R] mset])
    show "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> r \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
      using Q unfolding exit_class_def by blast
    show "AE \<omega>' in R. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T - r \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega>' t) - snd (\<omega>' s)) \<in> sconstraint k L"
      using R unfolding exit_class_def by blast
    fix \<omega> \<omega>' :: "'n pairpath"
    assume "\<omega> \<in> mspace (path_metric r :: ('n pairpath) metric)"
      and "\<omega>' \<in> mspace (path_metric (T - r) :: ('n pairpath) metric)"
      and A: "\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> r \<longrightarrow>
          (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
      and B: "\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T - r \<longrightarrow>
          (1 / (t - s)) *\<^sub>R (snd (\<omega>' t) - snd (\<omega>' s)) \<in> sconstraint k L"
    show "(1 / (q - p)) *\<^sub>R
        (snd (pglue r T \<omega> \<omega>' q) - snd (pglue r T \<omega> \<omega>' p)) \<in> sconstraint k L"
      using pq A B by (intro pglue_diffquot[OF r rT]) auto
  qed
qed

section \<open>The horizon cap does not bind\<close>

text \<open>\<open>exit_val\<close> caps the exit time at \<open>T\<close>, the paper's \<open>v\<close> does not.  Cutting
  a member back to \<open>[0,S]\<close> (\<open>exit_class_pcut\<close>) can only shorten its
  exit time to \<open>min \<tau> S\<close>, so the value at horizon \<open>T\<close> is already visible
  at horizon \<open>S\<close> once \<open>S\<close> exceeds the scale \<open>(r\<^sup>2 - |x|\<^sup>2)/(n-k)\<close> of
  \<open>exit_val_le_ball_bound\<close>.  No pasting is needed here.\<close>

definition pfst :: "real \<Rightarrow> 'n::finite pairpath \<Rightarrow> (real \<Rightarrow> real^'n)"
  where "pfst S \<omega> = restrict (\<lambda>t. fst (\<omega> t)) {0..S}"

lemma pexit_pfst: "pexit S K (pfst S \<omega>) = pexit S K (\<lambda>t. fst (\<omega> t))"
proof -
  have "{r. 0 \<le> r \<and> r \<le> S \<and> pfst S \<omega> r \<in> - K}
      = {r. 0 \<le> r \<and> r \<le> S \<and> fst (\<omega> r) \<in> - K}"
    by (auto simp: pfst_def)
  then show ?thesis unfolding pexit_def etime_def by simp
qed

lemma pfst_measurable:
  fixes N :: "('n::finite pairpath) measure"
  assumes S: "0 \<le> S"
    and setsN: "sets N = sets (path_borel S :: ('n pairpath) measure)"
  shows "pfst S \<in> N \<rightarrow>\<^sub>M (path_borel S :: ((real \<Rightarrow> real^'n)) measure)"
  unfolding pfst_def
proof (rule pathify_measurable[OF S])
  have fstB: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
      \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  fix t :: real assume "t \<in> {0..S}"
  show "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> t)) \<in> borel_measurable N"
    by (rule measurable_compose[OF pair_law_eval_measurable[OF setsN] fstB])
next
  fix \<omega> :: "'n pairpath" assume "\<omega> \<in> space N"
  then have "\<omega> \<in> mspace (path_metric S :: ('n pairpath) metric)"
    using space_of_path_sets[OF setsN] by simp
  then have "continuous_on {0..S} \<omega>" by (rule mspace_path_metricD)
  then show "continuous_on {0..S} (\<lambda>t. fst (\<omega> t))"
    by (intro continuous_intros)
qed

text \<open>\<open>ennreal_min_eq\<close> lives in @{theory Continuous_Time_Martingales.Integrability_Criteria}.\<close>


lemma pexit_pcut_ge:
  fixes K :: "(real^'n::finite) set" and \<omega> :: "'n pairpath"
  assumes S: "0 \<le> S" and ST: "S \<le> T"
  shows "min (pexit T K (\<lambda>t. fst (\<omega> t))) S
      \<le> pexit S K (\<lambda>t. fst (pcut S \<omega> t))"
proof -
  have T0: "0 \<le> T" using S ST by simp
  have lb: "min (pexit T K (\<lambda>t. fst (\<omega> t))) S \<le> z"
    if z: "z \<in> {r. 0 \<le> r \<and> r \<le> S \<and> (\<lambda>t. fst (pcut S \<omega> t)) r \<in> - K} \<union> {S}"
    for z
  proof -
    consider (hit) "0 \<le> z" "z \<le> S" "fst (pcut S \<omega> z) \<in> - K" | (cap) "z = S"
      using z by blast
    then show ?thesis
    proof cases
      case hit
      then have zT: "z \<le> T" using ST by simp
      have notin: "fst (\<omega> z) \<in> - K"
        using hit by (simp add: pcut_apply)
      have "pexit T K (\<lambda>t. fst (\<omega> t)) \<le> z"
        unfolding pexit_def
        by (rule etime_le_of_mem[OF T0 hit(1) zT]) (use notin in simp)
      then show ?thesis using hit(2) by simp
    next
      case cap
      then show ?thesis by simp
    qed
  qed
  have "pexit S K (\<lambda>t. fst (pcut S \<omega> t))
      = Inf ({r. 0 \<le> r \<and> r \<le> S \<and> (\<lambda>t. fst (pcut S \<omega> t)) r \<in> - K} \<union> {S})"
    unfolding pexit_def etime_def ..
  moreover have "min (pexit T K (\<lambda>t. fst (\<omega> t)))  S
      \<le> Inf ({r. 0 \<le> r \<and> r \<le> S \<and> (\<lambda>t. fst (pcut S \<omega> t)) r \<in> - K} \<union> {S})"
    by (intro cInf_greatest) (use lb in auto)
  ultimately show ?thesis by simp
qed

theorem exit_val_horizon_stable:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n" and r :: real
  assumes k: "k < CARD('n)" and L: "0 \<le> L" and S: "0 \<le> S" and ST: "S \<le> T"
    and K: "closed K" and KB: "K \<subseteq> cball 0 r"
    and big: "(r * r - x \<bullet> x) / real (CARD('n) - k) \<le> S"
  shows "exit_val k L T K x \<le> exit_val k L S K x"
proof -
  have T0: "0 \<le> T" using S ST by simp
  let ?B = "(path_borel S :: ('n pairpath) measure)"
  let ?tau = "\<lambda>\<omega> :: 'n pairpath. pexit S K (\<lambda>t. fst (\<omega> t))"
  have taum: "?tau \<in> borel_measurable ?B"
  proof -
    have "(\<lambda>\<omega> :: 'n pairpath. pexit S K (pfst S \<omega>)) \<in> borel_measurable ?B"
      by (rule measurable_compose[OF pfst_measurable[OF S refl]
            pexit_measurable[OF S K]])
    then show ?thesis by (simp add: pexit_pfst)
  qed
  have "exit_val k L T K x
      = Sup ((\<lambda>Q. ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))))
          ` exit_class k L T x)"
    unfolding exit_val_def ..
  also have "\<dots> \<le> exit_val k L S K x"
  proof (rule Sup_least)
    fix e :: ennreal
    assume "e \<in> (\<lambda>Q. ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))))
        ` exit_class k L T x"
    then obtain Q :: "('n pairpath) measure"
      where Q: "Q \<in> exit_class k L T x"
        and e: "e = ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))" by blast
    have eS: "e \<le> ennreal S"
    proof -
      have "e \<le> exit_val k L T K x"
        unfolding exit_val_def e using Q by (intro Sup_upper imageI)
      also have "\<dots> \<le> ennreal ((r * r - x \<bullet> x) / real (CARD('n) - k))"
        by (rule exit_val_le_ball_bound[OF k T0 L KB])
      also have "\<dots> \<le> ennreal S" using big by (rule ennreal_leI)
      finally show ?thesis .
    qed
    have Q': "pair_law_of S (pcut S) Q \<in> exit_class k L S x"
      by (rule exit_class_pcut[OF S ST Q])
    have m1: "pcut S \<in> Q \<rightarrow>\<^sub>M ?B"
      by (rule pcut_measurable[OF S ST exit_class_sets[OF Q]])
    have mset: "{\<omega> \<in> space ?B. e \<le> ennreal (?tau \<omega>)} \<in> sets ?B"
      using taum by measurable
    have iff: "(AE \<omega> in pair_law_of S (pcut S) Q. e \<le> ennreal (?tau \<omega>))
        = (AE \<omega> in Q. e \<le> ennreal (?tau (pcut S \<omega>)))"
      unfolding pair_law_of_def by (rule AE_distr_iff[OF m1 mset])
    have ae1: "AE \<omega> in Q. e \<le> ennreal (pexit T K (\<lambda>t. fst (\<omega> t)))"
      unfolding e by (rule ess_inf_time_AE)
    have "AE \<omega> in Q. e \<le> ennreal (?tau (pcut S \<omega>))"
    proof (rule eventually_mono[OF ae1])
      fix \<omega> :: "'n pairpath"
      assume "e \<le> ennreal (pexit T K (\<lambda>t. fst (\<omega> t)))"
      with eS have "e \<le> ennreal (min (pexit T K (\<lambda>t. fst (\<omega> t))) S)"
        unfolding ennreal_min_eq by simp
      also have "\<dots> \<le> ennreal (pexit S K (\<lambda>t. fst (pcut S \<omega> t)))"
        by (intro ennreal_leI pexit_pcut_ge[OF S ST])
      finally show "e \<le> ennreal (?tau (pcut S \<omega>))" by simp
    qed
    then have ae: "AE \<omega> in pair_law_of S (pcut S) Q. e \<le> ennreal (?tau \<omega>)"
      unfolding iff .
    have "e \<le> ess_inf_time (pair_law_of S (pcut S) Q) ?tau"
      unfolding ess_inf_time_def using ae by (intro Sup_upper) simp
    also have "\<dots> \<le> exit_val k L S K x"
      unfolding exit_val_def using Q' by (intro Sup_upper imageI)
    finally show "e \<le> exit_val k L S K x" .
  qed
  finally show ?thesis .
qed

text \<open>The pasting theorem needs three transfer results: a first-factor
  martingale, a second-factor martingale, and the product of a
  first-factor variable with a second-factor martingale, are all
  martingales for the product filtration.  \<open>sets_pair_measure_mono\<close>,
  \<open>filtered_measure_pair\<close>, \<open>martingale_pair_fst\<close>, \<open>distr_pair_snd\<close>,
  \<open>martingale_pair_snd_param\<close> and \<open>martingale_pair_snd\<close> live in
  @{theory Continuous_Time_Martingales.Martingale_Transfer}.\<close>

text \<open>\<open>martingale_cong_AE\<close>, \<open>martingale_time_change\<close> (used for the second
  factor's \<open>\<omega>' 0 = 0\<close> clause, and reparametrising time by the nondecreasing
  clock \<open>u \<mapsto> (u - r)\<^sup>+\<close>) and \<open>martingale_pair_mult\<close> (the third transfer
  result, needed for the compensated clause) live in
  @{theory Continuous_Time_Martingales.Martingale_Algebra} and
  @{theory Continuous_Time_Martingales.Martingale_Transfer} respectively.\<close>

section \<open>The pasted law is a member of the class\<close>

text \<open>The glued process splits as a first-factor martingale plus a
  second-factor martingale on the shifted clock \<open>u \<mapsto> (u - r)\<^sup>+\<close>: on
  \<open>[0,r]\<close> only the first piece moves, after \<open>r\<close> the first is frozen at
  \<open>X\<^sub>r\<close> and the second runs.  The identity holds only a.e. --- it uses
  \<open>X'(0) = 0\<close> from clause (i) --- which is what \<open>martingale_cong_AE\<close> is
  for.\<close>

lemma nat_filt_eval:
  fixes Q :: "('n::finite pairpath) measure"
  assumes b: "0 \<le> b" and ba: "b \<le> a"
  shows "(\<lambda>\<omega> :: 'n pairpath. \<omega> b)
      \<in> natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v) a \<rightarrow>\<^sub>M borel"
  unfolding natural_filtration_def
  by (rule measurable_family_vimage_algebra) (use b ba in auto)

theorem pglue_law_X_martingale:
  fixes Q R :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and Q: "Q \<in> exit_class k L r x"
    and R: "R \<in> exit_class k L (T - r) 0"
  shows "martingale (pglue_law r T Q R)
      (natural_filtration (pglue_law r T Q R) 0 (\<lambda>v \<omega>. \<omega> v)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u T)) :: real^'n)"
proof -
  let ?M = "Q \<Otimes>\<^sub>M R"
  let ?g = "\<lambda>p :: 'n pairpath \<times> 'n pairpath. pglue r T (fst p) (snd p)"
  let ?FQ = "natural_filtration Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?FR = "natural_filtration R 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?s = "\<lambda>u :: real. max (u - r) 0"
  let ?FF = "\<lambda>u. ?FQ (min u r) \<Otimes>\<^sub>M ?FR (?s u)"
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  have T0: "0 \<le> T" using r rT by simp
  have PQ: "prob_space Q" by (rule exit_class_prob[OF Q])
  have PR: "prob_space R" by (rule exit_class_prob[OF R])
  have setsQ: "sets Q = sets (path_borel r :: ('n pairpath) measure)"
    by (rule exit_class_sets[OF Q])
  have setsR: "sets R = sets ((path_borel (T - r) :: ('n pairpath) measure))"
    by (rule exit_class_sets[OF R])
  have s1_0: "0 \<le> min u r" if "0 \<le> u" for u :: real using that r by simp
  have s1_mono: "min u r \<le> min v r" if "0 \<le> u" "u \<le> v" for u v :: real
    using that by simp
  have s2_0: "0 \<le> ?s u" if "0 \<le> u" for u :: real by simp
  have s2_mono: "?s u \<le> ?s v" if "0 \<le> u" "u \<le> v" for u v :: real
    using that by simp

  \<comment> \<open>the two factor martingales, on their own clocks\<close>
  have mQ0: "martingale Q ?FQ 0 (\<lambda>u \<omega>. fst (\<omega> (min u r)) :: real^'n)"
    by (rule exit_class_X_martingale[OF Q])
  have mQ1: "martingale Q (\<lambda>u. ?FQ (min u r)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min (min u r) r)) :: real^'n)"
    by (rule martingale_time_change[OF mQ0 s1_0 s1_mono])
  have mQ: "martingale Q (\<lambda>u. ?FQ (min u r)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u r)) :: real^'n)"
  proof (rule martingale_cong_ge[OF mQ1])
    fix u :: real assume "0 \<le> u"
    show "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min (min u r) r)) :: real^'n)
        = (\<lambda>\<omega>. fst (\<omega> (min u r)))" by simp
  qed
  have mR0: "martingale R ?FR 0 (\<lambda>u \<omega>. fst (\<omega> (min u (T - r))) :: real^'n)"
    by (rule exit_class_X_martingale[OF R])
  have mR: "martingale R (\<lambda>u. ?FR (?s u)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min (?s u) (T - r))) :: real^'n)"
    by (rule martingale_time_change[OF mR0 s2_0 s2_mono])
  have FQ: "filtered_measure Q (\<lambda>u. ?FQ (min u r)) (0::real)"
  proof -
    interpret MQ: martingale Q "\<lambda>u. ?FQ (min u r)" "0::real"
      "\<lambda>u \<omega>. fst (\<omega> (min u r)) :: real^'n" by (rule mQ)
    show ?thesis by unfold_locales
  qed
  have FR: "filtered_measure R (\<lambda>u. ?FR (?s u)) (0::real)"
  proof -
    interpret MR: martingale R "\<lambda>u. ?FR (?s u)" "0::real"
      "\<lambda>u \<omega>. fst (\<omega> (min (?s u) (T - r))) :: real^'n" by (rule mR)
    show ?thesis by unfold_locales
  qed

  \<comment> \<open>lift both to the product and add\<close>
  have msum: "martingale ?M ?FF 0
      (\<lambda>u p. fst (fst p (min u r)) + fst (snd p (min (?s u) (T - r))) :: real^'n)"
    by (rule martingale_add[OF martingale_pair_fst[OF PQ PR mQ FR]
          martingale_pair_snd[OF PQ PR FQ mR]])

  \<comment> \<open>evaluation measurability on the product filtration\<close>
  have evQ: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. fst p b)
      \<in> borel_measurable (?FF u)" if "0 \<le> b" "b \<le> min u r" for b u
    by (rule measurable_compose[OF measurable_fst nat_filt_eval[OF that]])
  have evR: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. snd p b)
      \<in> borel_measurable (?FF u)" if "0 \<le> b" "b \<le> ?s u" for b u
    by (rule measurable_compose[OF measurable_snd nat_filt_eval[OF that]])
  have gadap: "(\<lambda>p. ?g p v) \<in> borel_measurable (?FF u)"
    if v: "0 \<le> v" and vu: "v \<le> u" for u v
  proof (cases "v \<le> T")
    case False
    then have "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. ?g p v) = (\<lambda>p. undefined)"
      by (auto simp: pglue_def)
    then show ?thesis by simp
  next
    case True
    then have vI: "v \<in> {0..T}" using v by simp
    show ?thesis
    proof (cases "v \<le> r")
      case True
      then have "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. ?g p v) = (\<lambda>p. fst p v)"
        by (simp add: pglue_le[OF vI])
      then show ?thesis using evQ[of v u] v vu True by simp
    next
      case False
      then have rv: "r \<le> v" by simp
      have mur: "min u r = r" using rv vu r False by simp
      have e: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. ?g p v)
          = (\<lambda>p. fst p r + (snd p (v - r) - snd p 0))"
        by (simp add: pglue_ge[OF vI rv])
      have m1: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. fst p r)
          \<in> borel_measurable (?FF u)"
        using evQ[of r u] r mur by simp
      have m2: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. snd p (v - r))
          \<in> borel_measurable (?FF u)"
        using evR[of "v - r" u] rv vu by simp
      have m3: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. snd p 0)
          \<in> borel_measurable (?FF u)" using evR[of 0 u] by simp
      show ?thesis unfolding e using m1 m2 m3 by simp
    qed
  qed

  \<comment> \<open>the glued process agrees with the sum almost everywhere\<close>
  have start: "AE p in ?M. fst (snd p 0) = (0::real^'n)"
  proof -
    interpret PP: pair_prob_space Q R
      by (simp add: pair_prob_space_def pair_sigma_finite_def PQ PR
          prob_space_imp_sigma_finite)
    have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> 0) \<in> borel_measurable R"
      by (rule pair_law_eval_measurable[OF setsR])
    have sm: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. snd p 0) \<in> borel_measurable ?M"
      by (rule measurable_compose[OF measurable_snd ev])
    have "{q :: (real^'n) \<times> (real^'n^'n). fst q = 0}
        = {0::real^'n} \<times> (UNIV :: (real^'n^'n) set)" by auto
    then have cl: "{q :: (real^'n) \<times> (real^'n^'n). fst q = 0} \<in> sets borel"
      by (simp add: borel_closed closed_Times)
    have "{p \<in> space ?M. fst (snd p 0) = (0::real^'n)}
        = (\<lambda>p :: 'n pairpath \<times> 'n pairpath. snd p 0)
            -` {q. fst q = (0::real^'n)} \<inter> space ?M" by auto
    then have mset: "{p \<in> space ?M. fst (snd p 0) = (0::real^'n)} \<in> sets ?M"
      using measurable_sets[OF sm cl] by simp
    have "AE \<omega> in Q. AE \<omega>' in R. fst (snd (\<omega>, \<omega>') 0) = (0::real^'n)"
      using R unfolding exit_class_def by auto
    then show ?thesis by (rule PP.AE_pair_measure[OF mset])
  qed
  have fstB: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
      \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  have FFm: "filtered_measure ?M ?FF (0::real)"
    by (rule filtered_measure_pair[OF FQ FR])
  have gfst: "(\<lambda>p. fst (?g p (min i T)) :: real^'n) \<in> borel_measurable (?FF i)"
    if i: "0 \<le> i" for i
  proof -
    have a1: "0 \<le> min i T" using i T0 by simp
    have a2: "min i T \<le> i" by simp
    show ?thesis by (rule measurable_compose[OF gadap[OF a1 a2] fstB])
  qed
  have mgl: "martingale ?M ?FF 0 (\<lambda>u p. fst (?g p (min u T)) :: real^'n)"
  proof (rule martingale_cong_AE[OF msum])
    show "adapted_process ?M ?FF 0 (\<lambda>u p. fst (?g p (min u T)) :: real^'n)"
      unfolding adapted_process_def adapted_process_axioms_def
      using FFm gfst by blast
  next
    fix u :: real assume u: "0 \<le> u"
    have muI: "min u T \<in> {0..T}" using u T0 by simp
    show "AE p in ?M. fst (fst p (min u r)) + fst (snd p (min (?s u) (T - r)))
        = fst (?g p (min u T))"
    proof (rule eventually_mono[OF start])
      fix p :: "'n pairpath \<times> 'n pairpath"
      assume z: "fst (snd p 0) = (0::real^'n)"
      show "fst (fst p (min u r)) + fst (snd p (min (?s u) (T - r)))
          = fst (?g p (min u T))"
      proof (cases "u \<le> r")
        case True
        then have uT: "u \<le> T" using rT by simp
        then have le: "min u T \<le> r" using True by simp
        have e1: "min u T = min u r" using True uT by simp
        have e2: "min (?s u) (T - r) = 0" using True rT by simp
        have g0: "fst (?g p (min u T)) = fst (fst p (min u r))"
          unfolding e1[symmetric] by (simp add: pglue_le[OF muI le])
        show ?thesis using z e2 g0 by simp
      next
        case False
        then have ru: "r < u" by simp
        have rv: "r \<le> min u T" using ru rT by simp
        have e1: "min u r = r" using ru by simp
        have e2: "min (?s u) (T - r) = min u T - r"
          using ru by (simp add: min_def)
        show ?thesis
          using z by (simp add: pglue_ge[OF muI rv] e1 e2)
      qed
    qed
  qed

  \<comment> \<open>transport to the pasted law\<close>
  have Zm: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min u T)) :: real^'n)
      \<in> borel_measurable (natural_filtration (pglue_law r T Q R) 0
          (\<lambda>v \<omega>. \<omega> v) u)" if u: "0 \<le> u" for u
  proof -
    have fstB: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
        \<in> borel_measurable borel"
      by (intro borel_measurable_continuous_onI continuous_intros)
    have "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u T))
        \<in> natural_filtration (pglue_law r T Q R) 0 (\<lambda>v \<omega>. \<omega> v) u \<rightarrow>\<^sub>M borel"
      by (rule nat_filt_eval) (use u T0 in auto)
    then show ?thesis by (rule measurable_compose[OF _ fstB])
  qed
  show ?thesis
    unfolding pglue_law_def
    by (rule martingale_pair_law[OF prob_space_pair_measure[OF PQ PR]
        pglue_measurable[OF r rT setsQ setsR] gadap Zm[unfolded pglue_law_def]
        mgl])
qed

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

theorem pglue_law_comp_martingale:
  fixes Q R :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and Q: "Q \<in> exit_class k L r x"
    and R: "R \<in> exit_class k L (T - r) 0"
  shows "martingale (pglue_law r T Q R)
      (natural_filtration (pglue_law r T Q R) 0 (\<lambda>v \<omega>. \<omega> v)) 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (min u T)) :: real^'n) - snd (\<omega> (min u T)))"
proof -
  let ?M = "Q \<Otimes>\<^sub>M R"
  let ?g = "\<lambda>p :: 'n pairpath \<times> 'n pairpath. pglue r T (fst p) (snd p)"
  let ?FQ = "natural_filtration Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?FR = "natural_filtration R 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?s = "\<lambda>u :: real. max (u - r) 0"
  let ?t = "\<lambda>u :: real. min (max (u - r) 0) (T - r)"
  let ?FF = "\<lambda>u. ?FQ (min u r) \<Otimes>\<^sub>M ?FR (?s u)"
  let ?A = "\<lambda>u p. fst (fst p (min u r)) :: real^'n"
  let ?Bp = "\<lambda>u p. fst (snd p (?t u)) :: real^'n"
  have T0: "0 \<le> T" using r rT by simp
  have PQ: "prob_space Q" by (rule exit_class_prob[OF Q])
  have PR: "prob_space R" by (rule exit_class_prob[OF R])
  have setsQ: "sets Q = sets (path_borel r :: ('n pairpath) measure)"
    by (rule exit_class_sets[OF Q])
  have setsR: "sets R = sets ((path_borel (T - r) :: ('n pairpath) measure))"
    by (rule exit_class_sets[OF R])
  have s1_0: "0 \<le> min u r" if "0 \<le> u" for u :: real using that r by simp
  have s1_mono: "min u r \<le> min v r" if "0 \<le> u" "u \<le> v" for u v :: real
    using that by simp
  have s2_0: "0 \<le> ?s u" if "0 \<le> u" for u :: real by simp
  have s2_mono: "?s u \<le> ?s v" if "0 \<le> u" "u \<le> v" for u v :: real
    using that by simp

  \<comment> \<open>the four factor martingales, on the two clocks\<close>
  have mQ1: "martingale Q (\<lambda>u. ?FQ (min u r)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min (min u r) r)) :: real^'n)"
    by (rule martingale_time_change
        [OF exit_class_X_martingale[OF Q] s1_0 s1_mono])
  have mQ: "martingale Q (\<lambda>u. ?FQ (min u r)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u r)) :: real^'n)"
  proof (rule martingale_cong_ge[OF mQ1])
    fix u :: real assume "0 \<le> u"
    show "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min (min u r) r)) :: real^'n)
        = (\<lambda>\<omega>. fst (\<omega> (min u r)))" by simp
  qed
  have mR: "martingale R (\<lambda>u. ?FR (?s u)) 0
      (\<lambda>u \<omega>. fst (\<omega> (?t u)) :: real^'n)"
    by (rule martingale_time_change
        [OF exit_class_X_martingale[OF R] s2_0 s2_mono])
  have cQ1: "martingale Q (\<lambda>u. ?FQ (min u r)) 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (min (min u r) r)) :: real^'n)
          - snd (\<omega> (min (min u r) r)))"
    by (rule martingale_time_change
        [OF exit_class_compensated_martingale[OF Q] s1_0 s1_mono])
  have cQ: "martingale Q (\<lambda>u. ?FQ (min u r)) 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (min u r)) :: real^'n) - snd (\<omega> (min u r)))"
  proof (rule martingale_cong_ge[OF cQ1])
    fix u :: real assume "0 \<le> u"
    show "(\<lambda>\<omega> :: 'n pairpath. outerp (fst (\<omega> (min (min u r) r)) :: real^'n)
          - snd (\<omega> (min (min u r) r)))
        = (\<lambda>\<omega>. outerp (fst (\<omega> (min u r))) - snd (\<omega> (min u r)))" by simp
  qed
  have cR: "martingale R (\<lambda>u. ?FR (?s u)) 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (?t u)) :: real^'n) - snd (\<omega> (?t u)))"
    by (rule martingale_time_change
        [OF exit_class_compensated_martingale[OF R] s2_0 s2_mono])
  have FQ: "filtered_measure Q (\<lambda>u. ?FQ (min u r)) (0::real)"
  proof -
    interpret MQ: martingale Q "\<lambda>u. ?FQ (min u r)" "0::real"
      "\<lambda>u \<omega>. fst (\<omega> (min u r)) :: real^'n" by (rule mQ)
    show ?thesis by unfold_locales
  qed
  have FR: "filtered_measure R (\<lambda>u. ?FR (?s u)) (0::real)"
  proof -
    interpret MR: martingale R "\<lambda>u. ?FR (?s u)" "0::real"
      "\<lambda>u \<omega>. fst (\<omega> (?t u)) :: real^'n" by (rule mR)
    show ?thesis by unfold_locales
  qed
  have FFm: "filtered_measure ?M ?FF (0::real)"
    by (rule filtered_measure_pair[OF FQ FR])

  \<comment> \<open>the two cross terms\<close>
  have mA: "martingale ?M ?FF 0 ?A" by (rule martingale_pair_fst[OF PQ PR mQ FR])
  have mB: "martingale ?M ?FF 0 ?Bp" by (rule martingale_pair_snd[OF PQ PR FQ mR])
  have cross1: "martingale ?M ?FF 0 (\<lambda>u p. (\<chi> i j. ?A u p $ i * ?Bp u p $ j))"
  proof (rule martingale_matI)
    fix i j :: 'n
    have "martingale ?M ?FF 0 (\<lambda>u p. ?A u p $ i * ?Bp u p $ j)"
      by (rule martingale_pair_mult[OF PQ PR martingale_vec_nth[OF mQ]
            martingale_vec_nth[OF mR]])
    then show "martingale ?M ?FF 0
        (\<lambda>u p. (\<chi> i j. ?A u p $ i * ?Bp u p $ j) $ i $ j)" by simp
  qed
  have cross2: "martingale ?M ?FF 0 (\<lambda>u p. (\<chi> i j. ?Bp u p $ i * ?A u p $ j))"
  proof (rule martingale_matI)
    fix i j :: 'n
    have "martingale ?M ?FF 0 (\<lambda>u p. ?A u p $ j * ?Bp u p $ i)"
      by (rule martingale_pair_mult[OF PQ PR martingale_vec_nth[OF mQ]
            martingale_vec_nth[OF mR]])
    then show "martingale ?M ?FF 0
        (\<lambda>u p. (\<chi> i j. ?Bp u p $ i * ?A u p $ j) $ i $ j)"
      by (simp add: mult.commute)
  qed
  have csum: "martingale ?M ?FF 0
      (\<lambda>u p. ((outerp (?A u p) - snd (fst p (min u r)))
            + (outerp (?Bp u p) - snd (snd p (?t u))))
          + ((\<chi> i j. ?A u p $ i * ?Bp u p $ j)
            + (\<chi> i j. ?Bp u p $ i * ?A u p $ j)))"
    by (rule martingale_add[OF martingale_add
          [OF martingale_pair_fst[OF PQ PR cQ FR]
              martingale_pair_snd[OF PQ PR FQ cR]]
          martingale_add[OF cross1 cross2]])

  \<comment> \<open>adaptedness of the glued compensated process\<close>
  have cB: "(\<lambda>q :: (real^'n) \<times> (real^'n^'n). outerp (fst q) - snd q)
      \<in> borel_measurable borel"
  proof -
    have e: "(\<lambda>q :: (real^'n) \<times> (real^'n^'n). outerp (fst q) - snd q)
        = (\<lambda>q. \<chi> i j. fst q $ i * fst q $ j - snd q $ i $ j)"
      by (rule ext) (simp add: outerp_def vec_eq_iff)
    show ?thesis unfolding e
      by (intro borel_measurable_continuous_onI continuous_on_vec_lambda
          continuous_intros)
  qed
  have evQ: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. fst p b)
      \<in> borel_measurable (?FF u)" if "0 \<le> b" "b \<le> min u r" for b u
    by (rule measurable_compose[OF measurable_fst nat_filt_eval[OF that]])
  have evR: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. snd p b)
      \<in> borel_measurable (?FF u)" if "0 \<le> b" "b \<le> ?s u" for b u
    by (rule measurable_compose[OF measurable_snd nat_filt_eval[OF that]])
  have gadap: "(\<lambda>p. ?g p v) \<in> borel_measurable (?FF u)"
    if v: "0 \<le> v" and vu: "v \<le> u" for u v
  proof (cases "v \<le> T")
    case False
    then have "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. ?g p v) = (\<lambda>p. undefined)"
      by (auto simp: pglue_def)
    then show ?thesis by simp
  next
    case True
    then have vI: "v \<in> {0..T}" using v by simp
    show ?thesis
    proof (cases "v \<le> r")
      case True
      then have "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. ?g p v) = (\<lambda>p. fst p v)"
        by (simp add: pglue_le[OF vI])
      then show ?thesis using evQ[of v u] v vu True by simp
    next
      case False
      then have rv: "r \<le> v" by simp
      have mur: "min u r = r" using rv vu r False by simp
      have e: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. ?g p v)
          = (\<lambda>p. fst p r + (snd p (v - r) - snd p 0))"
        by (simp add: pglue_ge[OF vI rv])
      have m1: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. fst p r)
          \<in> borel_measurable (?FF u)" using evQ[of r u] r mur by simp
      have m2: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. snd p (v - r))
          \<in> borel_measurable (?FF u)" using evR[of "v - r" u] rv vu by simp
      have m3: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. snd p 0)
          \<in> borel_measurable (?FF u)" using evR[of 0 u] by simp
      show ?thesis unfolding e using m1 m2 m3 by simp
    qed
  qed
  have gcomp: "(\<lambda>p. outerp (fst (?g p (min i T)) :: real^'n)
      - snd (?g p (min i T))) \<in> borel_measurable (?FF i)" if i: "0 \<le> i" for i
  proof -
    have a1: "0 \<le> min i T" using i T0 by simp
    have a2: "min i T \<le> i" by simp
    show ?thesis by (rule measurable_compose[OF gadap[OF a1 a2] cB])
  qed

  \<comment> \<open>the glued compensated process agrees with the sum almost everywhere\<close>
  have start: "AE p in ?M. snd p 0 = ((0::real^'n), (0::real^'n^'n))"
  proof -
    interpret PP: pair_prob_space Q R
      by (simp add: pair_prob_space_def pair_sigma_finite_def PQ PR
          prob_space_imp_sigma_finite)
    have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> 0) \<in> borel_measurable R"
      by (rule pair_law_eval_measurable[OF setsR])
    have sm: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. snd p 0) \<in> borel_measurable ?M"
      by (rule measurable_compose[OF measurable_snd ev])
    have "{p \<in> space ?M. snd p 0 = ((0::real^'n), (0::real^'n^'n))}
        = (\<lambda>p :: 'n pairpath \<times> 'n pairpath. snd p 0) -` {(0, 0)} \<inter> space ?M"
      by auto
    then have mset: "{p \<in> space ?M. snd p 0 = ((0::real^'n), (0::real^'n^'n))}
        \<in> sets ?M" using measurable_sets[OF sm] by simp
    have "AE \<omega> in Q. AE \<omega>' in R.
        snd (\<omega>, \<omega>') 0 = ((0::real^'n), (0::real^'n^'n))"
      using R unfolding exit_class_def by (auto simp: prod_eq_iff)
    then show ?thesis by (rule PP.AE_pair_measure[OF mset])
  qed
  have mgl: "martingale ?M ?FF 0
      (\<lambda>u p. outerp (fst (?g p (min u T)) :: real^'n) - snd (?g p (min u T)))"
  proof (rule martingale_cong_AE[OF csum])
    show "adapted_process ?M ?FF 0
        (\<lambda>u p. outerp (fst (?g p (min u T)) :: real^'n) - snd (?g p (min u T)))"
      unfolding adapted_process_def adapted_process_axioms_def
      using FFm gcomp by blast
  next
    fix u :: real assume u: "0 \<le> u"
    have muI: "min u T \<in> {0..T}" using u T0 by simp
    show "AE p in ?M. ((outerp (?A u p) - snd (fst p (min u r)))
            + (outerp (?Bp u p) - snd (snd p (?t u))))
          + ((\<chi> i j. ?A u p $ i * ?Bp u p $ j)
            + (\<chi> i j. ?Bp u p $ i * ?A u p $ j))
        = outerp (fst (?g p (min u T))) - snd (?g p (min u T))"
    proof (rule eventually_mono[OF start])
      fix p :: "'n pairpath \<times> 'n pairpath"
      assume z: "snd p 0 = ((0::real^'n), (0::real^'n^'n))"
      show "((outerp (?A u p) - snd (fst p (min u r)))
              + (outerp (?Bp u p) - snd (snd p (?t u))))
            + ((\<chi> i j. ?A u p $ i * ?Bp u p $ j)
              + (\<chi> i j. ?Bp u p $ i * ?A u p $ j))
          = outerp (fst (?g p (min u T))) - snd (?g p (min u T))"
      proof (cases "u \<le> r")
        case True
        then have uT: "u \<le> T" using rT by simp
        then have le: "min u T \<le> r" using True by simp
        have e1: "min u T = min u r" using True uT by simp
        have e2: "?t u = 0" using True rT by simp
        have g0: "?g p (min u T) = fst p (min u r)"
          unfolding e1[symmetric] by (simp add: pglue_le[OF muI le])
        show ?thesis
          using z by (simp add: g0 e2 outerp_zero vec_eq_iff)
      next
        case False
        then have ru: "r < u" by simp
        have rv: "r \<le> min u T" using ru rT by simp
        have e1: "min u r = r" using ru by simp
        have e2: "?t u = min u T - r" using ru by (simp add: min_def)
        have g0: "?g p (min u T)
            = fst p r + (snd p (min u T - r) - snd p 0)"
          by (simp add: pglue_ge[OF muI rv])
        have gX: "fst (?g p (min u T)) = ?A u p + ?Bp u p"
          using z by (simp add: g0 e1 e2)
        have gY: "snd (?g p (min u T)) = snd (fst p (min u r)) + snd (snd p (?t u))"
          using z by (simp add: g0 e1 e2)
        show ?thesis by (simp add: gX gY outerp_add)
      qed
    qed
  qed

  \<comment> \<open>transport to the pasted law\<close>
  have Zm: "(\<lambda>\<omega> :: 'n pairpath. outerp (fst (\<omega> (min u T)) :: real^'n)
        - snd (\<omega> (min u T)))
      \<in> borel_measurable (natural_filtration (pglue_law r T Q R) 0
          (\<lambda>v \<omega>. \<omega> v) u)" if u: "0 \<le> u" for u
  proof -
    have "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u T))
        \<in> natural_filtration (pglue_law r T Q R) 0 (\<lambda>v \<omega>. \<omega> v) u \<rightarrow>\<^sub>M borel"
      by (rule nat_filt_eval) (use u T0 in auto)
    then show ?thesis by (rule measurable_compose[OF _ cB])
  qed
  show ?thesis
    unfolding pglue_law_def
    by (rule martingale_pair_law[OF prob_space_pair_measure[OF PQ PR]
        pglue_measurable[OF r rT setsQ setsR] gadap Zm[unfolded pglue_law_def]
        mgl])
qed

text \<open>The class is closed under independent concatenation.  This is the
  constructive half of the pasting the weak dynamic programming principle
  needs; with a countable Borel partition of the endpoint it will give the
  \<open>\<ge>\<close> inequality of (2.9).\<close>

theorem exit_class_pglue_law:
  fixes Q R :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and Q: "Q \<in> exit_class k L r x"
    and R: "R \<in> exit_class k L (T - r) 0"
  shows "pglue_law r T Q R \<in> exit_class k L T x"
  unfolding exit_class_def mem_Collect_eq
  using prob_space_pglue_law[OF r rT exit_class_prob[OF Q]
      exit_class_prob[OF R] exit_class_sets[OF Q]
      exit_class_sets[OF R]]
    sets_pglue_law pglue_law_start[OF r rT Q R]
    pglue_law_diffquot[OF r rT Q R] pglue_law_X_martingale[OF r rT Q R]
    pglue_law_comp_martingale[OF r rT Q R]
  by blast

text \<open>The immediate payoff: \<open>exit_val\<close> is nondecreasing in the horizon ---
  paste the Brownian witness onto the tail of a horizon-\<open>S\<close> member, and the
  glued path agrees with the original on \<open>[0,S]\<close> so cannot exit earlier.
  With \<open>exit_val_horizon_stable\<close> this makes \<open>exit_val k L T K x\<close> constant
  for \<open>T\<close> beyond the scale \<open>(r\<^sup>2 - |x|\<^sup>2)/(n-k)\<close>: the horizon cap is
  invisible, and \<open>exit_val\<close> is the paper's uncapped \<open>v\<close>.\<close>

lemma pexit_pglue_ge:
  fixes K :: "(real^'n::finite) set" and \<omega> \<omega>' :: "'n pairpath"
  assumes S: "0 \<le> S" and ST: "S \<le> T"
  shows "pexit S K (\<lambda>t. fst (\<omega> t)) \<le> pexit T K (\<lambda>t. fst (pglue S T \<omega> \<omega>' t))"
proof -
  have lb: "pexit S K (\<lambda>t. fst (\<omega> t)) \<le> z"
    if z: "z \<in> {t. 0 \<le> t \<and> t \<le> T
        \<and> (\<lambda>t. fst (pglue S T \<omega> \<omega>' t)) t \<in> - K} \<union> {T}" for z
  proof -
    consider (hit) "0 \<le> z" "z \<le> T" "fst (pglue S T \<omega> \<omega>' z) \<in> - K" | (cap) "z = T"
      using z by blast
    then show ?thesis
    proof cases
      case hit
      show ?thesis
      proof (cases "z \<le> S")
        case True
        have zI: "z \<in> {0..T}" using hit by simp
        have notin: "fst (\<omega> z) \<in> - K"
          using hit True by (simp add: pglue_le[OF zI])
        show ?thesis
          unfolding pexit_def
          by (rule etime_le_of_mem[OF S hit(1) True]) (use notin in simp)
      next
        case False
        then show ?thesis
          using pexit_le_T[OF S, of K "\<lambda>t. fst (\<omega> t)"] by linarith
      qed
    next
      case cap
      then show ?thesis
        using pexit_le_T[OF S, of K "\<lambda>t. fst (\<omega> t)"] ST by linarith
    qed
  qed
  have "pexit T K (\<lambda>t. fst (pglue S T \<omega> \<omega>' t))
      = Inf ({t. 0 \<le> t \<and> t \<le> T
          \<and> (\<lambda>t. fst (pglue S T \<omega> \<omega>' t)) t \<in> - K} \<union> {T})"
    unfolding pexit_def etime_def ..
  moreover have "pexit S K (\<lambda>t. fst (\<omega> t))
      \<le> Inf ({t. 0 \<le> t \<and> t \<le> T
          \<and> (\<lambda>t. fst (pglue S T \<omega> \<omega>' t)) t \<in> - K} \<union> {T})"
    by (intro cInf_greatest) (use lb in auto)
  ultimately show ?thesis by simp
qed

theorem exit_val_horizon_mono:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
  assumes S: "0 \<le> S" and ST: "S \<le> T" and L: "1 \<le> L" and K: "closed K"
  shows "exit_val k L S K x \<le> exit_val k L T K x"
proof -
  have T0: "0 \<le> T" using S ST by simp
  have TS: "0 \<le> T - S" using ST by simp
  have "exit_val k L S K x = Sup ((\<lambda>Q. ess_inf_time Q
      (\<lambda>\<omega>. pexit S K (\<lambda>t. fst (\<omega> t)))) ` exit_class k L S x)"
    unfolding exit_val_def ..
  also have "\<dots> \<le> exit_val k L T K x"
  proof (rule Sup_least)
    fix e :: ennreal
    assume "e \<in> (\<lambda>Q. ess_inf_time Q (\<lambda>\<omega>. pexit S K (\<lambda>t. fst (\<omega> t))))
        ` exit_class k L S x"
    then obtain Q :: "('n pairpath) measure"
      where Q: "Q \<in> exit_class k L S x"
        and e: "e = ess_inf_time Q (\<lambda>\<omega>. pexit S K (\<lambda>t. fst (\<omega> t)))" by blast
    define R where "R = pair_law_of (T - S) (bmpair (T - S))
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)"
    have R: "R \<in> exit_class k L (T - S) (0 :: real^'n)"
      unfolding R_def by (rule bmpair_law_in_paper_pair_class[OF TS L])
    have G: "pglue_law S T Q R \<in> exit_class k L T x"
      by (rule exit_class_pglue_law[OF S ST Q R])
    let ?M = "Q \<Otimes>\<^sub>M R"
    let ?g = "\<lambda>p :: 'n pairpath \<times> 'n pairpath. pglue S T (fst p) (snd p)"
    let ?BT = "(path_borel T :: ('n pairpath) measure)"
    have PQ: "prob_space Q" by (rule exit_class_prob[OF Q])
    have PR: "prob_space R" by (rule exit_class_prob[OF R])
    interpret PP: pair_prob_space Q R
      by (simp add: pair_prob_space_def pair_sigma_finite_def PQ PR
          prob_space_imp_sigma_finite)
    have setsQ: "sets Q = sets (path_borel S :: ('n pairpath) measure)"
      by (rule exit_class_sets[OF Q])
    have setsR: "sets R = sets ((path_borel (T - S) :: ('n pairpath) measure))"
      by (rule exit_class_sets[OF R])
    have tauS: "(\<lambda>\<omega> :: 'n pairpath. pexit S K (\<lambda>t. fst (\<omega> t)))
        \<in> borel_measurable Q"
    proof -
      have "(\<lambda>\<omega> :: 'n pairpath. pexit S K (pfst S \<omega>)) \<in> borel_measurable Q"
        by (rule measurable_compose[OF pfst_measurable[OF S setsQ]
              pexit_measurable[OF S K]])
      then show ?thesis by (simp add: pexit_pfst)
    qed
    have tauT: "(\<lambda>\<omega> :: 'n pairpath. pexit T K (\<lambda>t. fst (\<omega> t)))
        \<in> borel_measurable ?BT"
    proof -
      have "(\<lambda>\<omega> :: 'n pairpath. pexit T K (pfst T \<omega>)) \<in> borel_measurable ?BT"
        by (rule measurable_compose[OF pfst_measurable[OF T0 refl]
              pexit_measurable[OF T0 K]])
      then show ?thesis by (simp add: pexit_pfst)
    qed
    have aeQ: "AE \<omega> in Q. e \<le> ennreal (pexit S K (\<lambda>t. fst (\<omega> t)))"
      unfolding e by (rule ess_inf_time_AE)
    have aeM: "AE p in ?M. e \<le> ennreal (pexit S K (\<lambda>t. fst (fst p t)))"
    proof (rule PP.AE_pair_measure)
      have m1: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. pexit S K (\<lambda>t. fst (fst p t)))
          \<in> borel_measurable ?M"
        by (rule measurable_compose[OF measurable_fst tauS])
      show "{p \<in> space ?M. e \<le> ennreal (pexit S K (\<lambda>t. fst (fst p t)))}
          \<in> sets ?M" using m1 by measurable
      show "AE \<omega> in Q. AE \<omega>' in R.
          e \<le> ennreal (pexit S K (\<lambda>t. fst (fst (\<omega>, \<omega>') t)))"
        using aeQ by simp
    qed
    have aeG: "AE p in ?M. e \<le> ennreal (pexit T K (\<lambda>t. fst (?g p t)))"
    proof (rule eventually_mono[OF aeM])
      fix p :: "'n pairpath \<times> 'n pairpath"
      assume "e \<le> ennreal (pexit S K (\<lambda>t. fst (fst p t)))"
      also have "\<dots> \<le> ennreal (pexit T K (\<lambda>t. fst (?g p t)))"
        by (intro ennreal_leI pexit_pglue_ge[OF S ST])
      finally show "e \<le> ennreal (pexit T K (\<lambda>t. fst (?g p t)))" .
    qed
    have iff: "(AE \<omega> in pglue_law S T Q R.
          e \<le> ennreal (pexit T K (\<lambda>t. fst (\<omega> t))))
        = (AE p in ?M. e \<le> ennreal (pexit T K (\<lambda>t. fst (?g p t))))"
    proof -
      have mset: "{\<omega> \<in> space ?BT.
          e \<le> ennreal (pexit T K (\<lambda>t. fst (\<omega> t)))} \<in> sets ?BT"
        using tauT by measurable
      show ?thesis
        unfolding pglue_law_def pair_law_of_def
        by (rule AE_distr_iff[OF pglue_measurable[OF S ST setsQ setsR] mset])
    qed
    have "e \<le> ess_inf_time (pglue_law S T Q R)
        (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))"
      unfolding ess_inf_time_def using aeG unfolding iff[symmetric]
      by (intro Sup_upper) simp
    also have "\<dots> \<le> exit_val k L T K x"
      unfolding exit_val_def using G by (intro Sup_upper imageI)
    finally show "e \<le> exit_val k L T K x" .
  qed
  finally show ?thesis .
qed

text \<open>Horizon-cap invisibility, both halves.  Past the natural scale of
  Example 3.1 the horizon does not matter at all, so \<open>exit_val\<close> --- defined
  on the capped path space --- computes the paper's uncapped \<open>v\<close> of (1.6).\<close>

section \<open>The pasting lower bound (Prop. 2.4)\<close>

text \<open>The mechanism behind the \<open>\<ge>\<close> half of the dynamic programming principle
  (2.9): pasting produces a member of the class, so the essential infimum
  of its exit time lower-bounds \<open>v(x)\<close>, and a glued path's exit time is at
  least \<open>r + c\<close> once the first piece stays in \<open>K\<close> to \<open>r\<close> and the re-based
  continuation stays in \<open>K\<close> for a further \<open>c\<close>.  A single law \<open>R\<close> started
  at \<open>0\<close> supplies a continuation from every endpoint via \<open>pglue\<close>; the full
  (2.9) needs that law chosen depending on the endpoint.\<close>

lemma pexit_path_measurable:
  fixes K :: "(real^'n::finite) set" and N :: "('n pairpath) measure"
  assumes T: "0 \<le> T" and K: "closed K"
    and setsN: "sets N = sets (path_borel T :: ('n pairpath) measure)"
  shows "(\<lambda>\<omega> :: 'n pairpath. pexit T K (\<lambda>t. fst (\<omega> t))) \<in> borel_measurable N"
proof -
  have "(\<lambda>\<omega> :: 'n pairpath. pexit T K (pfst T \<omega>)) \<in> borel_measurable N"
    by (rule measurable_compose[OF pfst_measurable[OF T setsN]
          pexit_measurable[OF T K]])
  then show ?thesis by (simp add: pexit_pfst)
qed

theorem exit_val_paste_ge:
  fixes Q R :: "('n::finite pairpath) measure" and K :: "(real^'n) set"
  assumes r: "0 \<le> r" and rT: "r \<le> T" and K: "closed K"
    and Q: "Q \<in> exit_class k L r x"
    and R: "R \<in> exit_class k L (T - r) 0"
    and stay: "AE p in Q \<Otimes>\<^sub>M R.
        c \<le> pexit T K (\<lambda>t. fst (pglue r T (fst p) (snd p) t))"
  shows "ennreal c \<le> exit_val k L T K x"
proof -
  have T0: "0 \<le> T" using r rT by simp
  let ?BT = "(path_borel T :: ('n pairpath) measure)"
  have G: "pglue_law r T Q R \<in> exit_class k L T x"
    by (rule exit_class_pglue_law[OF r rT Q R])
  have tauT: "(\<lambda>\<omega> :: 'n pairpath. pexit T K (\<lambda>t. fst (\<omega> t)))
      \<in> borel_measurable ?BT"
    by (rule pexit_path_measurable[OF T0 K refl])
  have mset: "{\<omega> \<in> space ?BT.
      ennreal c \<le> ennreal (pexit T K (\<lambda>t. fst (\<omega> t)))} \<in> sets ?BT"
    using tauT by measurable
  have iff: "(AE \<omega> in pglue_law r T Q R.
        ennreal c \<le> ennreal (pexit T K (\<lambda>t. fst (\<omega> t))))
      = (AE p in Q \<Otimes>\<^sub>M R. ennreal c
          \<le> ennreal (pexit T K (\<lambda>t. fst (pglue r T (fst p) (snd p) t))))"
    unfolding pglue_law_def pair_law_of_def
    by (rule AE_distr_iff[OF pglue_measurable[OF r rT
          exit_class_sets[OF Q] exit_class_sets[OF R]] mset])
  have "AE p in Q \<Otimes>\<^sub>M R. ennreal c
      \<le> ennreal (pexit T K (\<lambda>t. fst (pglue r T (fst p) (snd p) t)))"
    using stay by (auto intro: ennreal_leI elim: eventually_mono)
  then have ae: "AE \<omega> in pglue_law r T Q R.
      ennreal c \<le> ennreal (pexit T K (\<lambda>t. fst (\<omega> t)))"
    unfolding iff .
  have "ennreal c
      \<le> ess_inf_time (pglue_law r T Q R) (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))"
    unfolding ess_inf_time_def using ae by (intro Sup_upper) simp
  also have "\<dots> \<le> exit_val k L T K x"
    unfolding exit_val_def using G by (intro Sup_upper imageI)
  finally show ?thesis .
qed

lemma pexit_pglue_split:
  fixes K :: "(real^'n::finite) set" and \<omega> \<omega>' :: "'n pairpath"
  assumes r: "0 \<le> r" and rT: "r \<le> T" and c: "0 \<le> c" and cT: "r + c \<le> T"
    and stay: "\<And>t. t \<in> {0..r} \<Longrightarrow> fst (\<omega> t) \<in> K"
    and cont: "\<And>s. s \<in> {0..c} \<Longrightarrow> fst (\<omega> r + (\<omega>' s - \<omega>' 0)) \<in> K"
  shows "r + c \<le> pexit T K (\<lambda>t. fst (pglue r T \<omega> \<omega>' t))"
proof -
  have lb: "r + c \<le> z"
    if z: "z \<in> {t. 0 \<le> t \<and> t \<le> T
        \<and> (\<lambda>t. fst (pglue r T \<omega> \<omega>' t)) t \<in> - K} \<union> {T}" for z
  proof -
    consider (hit) "0 \<le> z" "z \<le> T" "fst (pglue r T \<omega> \<omega>' z) \<in> - K" | (cap) "z = T"
      using z by blast
    then show ?thesis
    proof cases
      case hit
      then have zI: "z \<in> {0..T}" by simp
      show ?thesis
      proof (rule ccontr)
        assume "\<not> r + c \<le> z"
        then have zc: "z < r + c" by simp
        show False
        proof (cases "z \<le> r")
          case True
          have "fst (\<omega> z) \<in> K" using hit(1) True by (intro stay) simp
          then show False using hit(3) by (simp add: pglue_le[OF zI True])
        next
          case False
          then have rz: "r \<le> z" by simp
          have "z - r \<in> {0..c}" using rz zc by simp
          then have "fst (\<omega> r + (\<omega>' (z - r) - \<omega>' 0)) \<in> K" by (rule cont)
          then show False using hit(3) by (simp add: pglue_ge[OF zI rz])
        qed
      qed
    next
      case cap
      then show ?thesis using cT by simp
    qed
  qed
  have "pexit T K (\<lambda>t. fst (pglue r T \<omega> \<omega>' t))
      = Inf ({t. 0 \<le> t \<and> t \<le> T
          \<and> (\<lambda>t. fst (pglue r T \<omega> \<omega>' t)) t \<in> - K} \<union> {T})"
    unfolding pexit_def etime_def ..
  moreover have "r + c \<le> Inf ({t. 0 \<le> t \<and> t \<le> T
      \<and> (\<lambda>t. fst (pglue r T \<omega> \<omega>' t)) t \<in> - K} \<union> {T})"
    by (intro cInf_greatest) (use lb in auto)
  ultimately show ?thesis by simp
qed

text \<open>\<open>sets_PiM_mono\<close>, \<open>filtered_measure_PiM\<close>, \<open>martingale_distr\<close> and
  \<open>martingale_PiM_component\<close> live in
  @{theory Continuous_Time_Martingales.Martingale_Transfer}.\<close>

section \<open>Kernel pasting: a continuation chosen by the endpoint\<close>

text \<open>The step from \<open>pglue_law\<close> (one continuation for every endpoint) to
  what (2.9) needs: a countable family \<open>RR\<close> of candidate continuations and
  a past-measurable index \<open>N\<close> selecting one.  The second factor is the
  product \<open>\<Pi>\<^sub>M i. RR i\<close>, from which the glue picks the \<open>N \<omega>\<close>-th;
  freezing the first coordinate makes the index constant, so
  \<open>martingale_pair_snd_param\<close> and \<open>martingale_PiM_component\<close> carry the
  construction.\<close>

definition kglue :: "real \<Rightarrow> real \<Rightarrow> ('n::finite pairpath \<Rightarrow> nat)
    \<Rightarrow> ('n pairpath \<times> (nat \<Rightarrow> 'n pairpath)) \<Rightarrow> 'n pairpath"
  where "kglue r T N p = pglue r T (fst p) (snd p (N (fst p)))"

definition kglue_law :: "real \<Rightarrow> real \<Rightarrow> ('n::finite pairpath \<Rightarrow> nat)
    \<Rightarrow> ('n pairpath) measure \<Rightarrow> (nat \<Rightarrow> ('n pairpath) measure)
    \<Rightarrow> ('n pairpath) measure"
  where "kglue_law r T N Q RR
     = pair_law_of T (kglue r T N) (Q \<Otimes>\<^sub>M Pi\<^sub>M UNIV RR)"

lemma sets_kglue_law[simp]:
  "sets (kglue_law r T N Q RR)
     = sets (path_borel T :: ('n::finite pairpath) measure)"
  unfolding kglue_law_def by (rule sets_pair_law_of)

lemma kglue_measurable:
  fixes Q :: "('n::finite pairpath) measure"
    and RR :: "nat \<Rightarrow> ('n pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsQ: "sets Q = sets (path_borel r :: ('n pairpath) measure)"
    and setsR: "\<And>j. sets (RR j) = sets ((path_borel (T - r) :: ('n pairpath) measure))"
    and Nm: "N \<in> Q \<rightarrow>\<^sub>M count_space UNIV"
  shows "kglue r T N \<in> Q \<Otimes>\<^sub>M Pi\<^sub>M UNIV RR \<rightarrow>\<^sub>M
      (path_borel T :: ('n pairpath) measure)"
proof -
  let ?M = "Q \<Otimes>\<^sub>M Pi\<^sub>M UNIV RR"
  have T0: "0 \<le> T" using r rT by simp
  have eQ: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). fst p v)
      \<in> borel_measurable ?M" for v
    by (rule measurable_compose[OF measurable_fst
          pair_law_eval_measurable[OF setsQ]])
  have Nfst: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). N (fst p))
      \<in> ?M \<rightarrow>\<^sub>M count_space UNIV"
    by (rule measurable_compose[OF measurable_fst Nm])
  have eS: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). snd p (N (fst p)) v)
      \<in> borel_measurable ?M" for v
  proof (rule measurable_compose_countable[OF _ Nfst])
    fix j :: nat
    have "(\<lambda>f :: nat \<Rightarrow> 'n pairpath. f j) \<in> Pi\<^sub>M UNIV RR \<rightarrow>\<^sub>M RR j"
      by (rule measurable_component_singleton) simp
    from measurable_compose[OF measurable_snd this]
    have "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). snd p j) \<in> ?M \<rightarrow>\<^sub>M RR j" .
    from measurable_compose[OF this pair_law_eval_measurable[OF setsR]]
    show "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). snd p j v)
        \<in> borel_measurable ?M" .
  qed
  have Xm: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). if t \<le> r then fst p t
        else fst p r + (snd p (N (fst p)) (t - r) - snd p (N (fst p)) 0))
      \<in> borel_measurable ?M" for t
    using eQ eS by simp
  have cont: "continuous_on {0..T} (\<lambda>t. if t \<le> r then fst p t
        else fst p r + (snd p (N (fst p)) (t - r) - snd p (N (fst p)) 0))"
    if p: "p \<in> space ?M" for p :: "'n pairpath \<times> (nat \<Rightarrow> 'n pairpath)"
  proof (rule continuous_on_pglue[OF r rT])
    have "fst p \<in> space Q" and sp: "snd p \<in> space (Pi\<^sub>M UNIV RR)"
      using p by (auto simp: space_pair_measure)
    then show "continuous_on {0..r} (fst p)"
      using space_of_path_sets[OF setsQ] by (auto intro: mspace_path_metricD)
    have "snd p (N (fst p)) \<in> space (RR (N (fst p)))"
      using sp by (simp add: space_PiM PiE_iff)
    then show "continuous_on {0..T - r} (snd p (N (fst p)))"
      using space_of_path_sets[OF setsR] by (auto intro: mspace_path_metricD)
  qed
  show ?thesis
    using pathify_measurable[OF T0 Xm cont]
    unfolding kglue_def pglue_def by simp
qed

lemma prob_space_kglue_law:
  fixes Q :: "('n::finite pairpath) measure"
    and RR :: "nat \<Rightarrow> ('n pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and PQ: "prob_space Q" and PR: "\<And>j. prob_space (RR j)"
    and setsQ: "sets Q = sets (path_borel r :: ('n pairpath) measure)"
    and setsR: "\<And>j. sets (RR j) = sets ((path_borel (T - r) :: ('n pairpath) measure))"
    and Nm: "N \<in> Q \<rightarrow>\<^sub>M count_space UNIV"
  shows "prob_space (kglue_law r T N Q RR)"
proof -
  interpret PP: prob_space "Q \<Otimes>\<^sub>M Pi\<^sub>M UNIV RR"
    by (rule prob_space_pair_measure[OF PQ prob_space_PiM]) (rule PR)
  show ?thesis
    unfolding kglue_law_def pair_law_of_def
    by (rule PP.prob_space_distr
        [OF kglue_measurable[OF r rT setsQ setsR Nm]])
qed

lemma AE_kglue_law:
  fixes Q :: "('n::finite pairpath) measure"
    and RR :: "nat \<Rightarrow> ('n pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and PQ: "prob_space Q" and PR: "\<And>j. prob_space (RR j)"
    and setsQ: "sets Q = sets (path_borel r :: ('n pairpath) measure)"
    and setsR: "\<And>j. sets (RR j) = sets ((path_borel (T - r) :: ('n pairpath) measure))"
    and Nm: "N \<in> Q \<rightarrow>\<^sub>M count_space UNIV"
    and mset: "{\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric). P \<omega>}
        \<in> sets (path_borel T :: ('n pairpath) measure)"
    and A: "AE \<omega> in Q. A \<omega>" and B: "AE f in Pi\<^sub>M UNIV RR. B f"
    and imp: "\<And>\<omega> f. \<omega> \<in> mspace (path_metric r :: ('n pairpath) metric) \<Longrightarrow>
        f \<in> space (Pi\<^sub>M UNIV RR) \<Longrightarrow> A \<omega> \<Longrightarrow> B f \<Longrightarrow> P (kglue r T N (\<omega>, f))"
  shows "AE \<omega> in kglue_law r T N Q RR. P \<omega>"
proof -
  let ?S = "Pi\<^sub>M UNIV RR"
  let ?M = "Q \<Otimes>\<^sub>M ?S"
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  interpret PQ: prob_space Q by (rule PQ)
  interpret PS: prob_space ?S by (rule prob_space_PiM) (rule PR)
  interpret PP: pair_prob_space Q ?S by unfold_locales
  have phim: "kglue r T N \<in> ?M \<rightarrow>\<^sub>M ?B"
    by (rule kglue_measurable[OF r rT setsQ setsR Nm])
  have mset': "{\<omega> \<in> space ?B. P \<omega>} \<in> sets ?B"
    using mset by (simp add: space_borel_of)
  have iff: "(AE \<omega> in kglue_law r T N Q RR. P \<omega>)
      = (AE p in ?M. P (kglue r T N p))"
    unfolding kglue_law_def pair_law_of_def by (rule AE_distr_iff[OF phim mset'])
  have evm: "{p \<in> space ?M. P (kglue r T N p)} \<in> sets ?M"
  proof -
    have "{p \<in> space ?M. P (kglue r T N p)}
        = kglue r T N -` {\<omega> \<in> space ?B. P \<omega>} \<inter> space ?M"
      using measurable_space[OF phim] by auto
    then show ?thesis using measurable_sets[OF phim mset'] by simp
  qed
  have inner: "AE \<omega> in Q. AE f in ?S. P (kglue r T N (\<omega>, f))"
  proof -
    have SB: "AE f in ?S. B f \<and> f \<in> space ?S"
      using B AE_space[of ?S] by (auto intro: eventually_conj)
    have QA: "AE \<omega> in Q. A \<omega>
        \<and> \<omega> \<in> mspace (path_metric r :: ('n pairpath) metric)"
      using A AE_space[of Q] space_of_path_sets[OF setsQ]
      by (auto intro: eventually_conj)
    show ?thesis
    proof (rule eventually_mono[OF QA])
      fix \<omega> :: "'n pairpath"
      assume w: "A \<omega> \<and> \<omega> \<in> mspace (path_metric r :: ('n pairpath) metric)"
      show "AE f in ?S. P (kglue r T N (\<omega>, f))"
      proof (rule eventually_mono[OF SB])
        fix f :: "nat \<Rightarrow> 'n pairpath"
        assume "B f \<and> f \<in> space ?S"
        with w show "P (kglue r T N (\<omega>, f))" by (simp add: imp)
      qed
    qed
  qed
  have "AE p in ?M. P (kglue r T N p)"
    using PP.AE_pair_measure[OF evm] inner by simp
  then show ?thesis unfolding iff .
qed

lemma kglue_law_start:
  fixes Q :: "('n::finite pairpath) measure"
    and RR :: "nat \<Rightarrow> ('n pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and Q: "Q \<in> exit_class k L r x"
    and R: "\<And>j. RR j \<in> exit_class k L (T - r) 0"
    and Nm: "N \<in> Q \<rightarrow>\<^sub>M count_space UNIV"
  shows "AE \<omega> in kglue_law r T N Q RR. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> 0) \<in> borel_measurable ?B"
    by (rule pair_law_eval_measurable[OF refl])
  have mset: "{\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
      fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0} \<in> sets ?B"
  proof -
    have "{\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
        fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0}
        = (\<lambda>\<omega> :: 'n pairpath. \<omega> 0) -` {(x, 0)} \<inter> space ?B"
      by (auto simp: prod_eq_iff space_borel_of)
    then show ?thesis using measurable_sets[OF ev] by simp
  qed
  show ?thesis
  proof (rule AE_kglue_law[OF r rT exit_class_prob[OF Q]
        exit_class_prob[OF R] exit_class_sets[OF Q]
        exit_class_sets[OF R] Nm mset])
    show "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
      using Q unfolding exit_class_def by blast
    show "AE f in Pi\<^sub>M UNIV RR. True" by simp
    fix \<omega> :: "'n pairpath" and f :: "nat \<Rightarrow> 'n pairpath"
    assume "\<omega> \<in> mspace (path_metric r :: ('n pairpath) metric)"
      and "f \<in> space (Pi\<^sub>M UNIV RR)"
      and st: "fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0" and "True"
    from st show "fst (kglue r T N (\<omega>, f) 0) = x
        \<and> snd (kglue r T N (\<omega>, f) 0) = 0"
      using r rT by (simp add: kglue_def pglue_zero)
  qed
qed

lemma kglue_law_diffquot:
  fixes Q :: "('n::finite pairpath) measure"
    and RR :: "nat \<Rightarrow> ('n pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and Q: "Q \<in> exit_class k L r x"
    and R: "\<And>j. RR j \<in> exit_class k L (T - r) 0"
    and Nm: "N \<in> Q \<rightarrow>\<^sub>M count_space UNIV"
  shows "AE \<omega> in kglue_law r T N Q RR. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
proof (rule exit_class_diffquot_of_pairs[OF sets_kglue_law])
  fix p q :: real
  assume pq: "p \<in> {0..T}" "q \<in> {0..T}" "p < q"
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  have mset: "{\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
      (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L} \<in> sets ?B"
    by (rule borel_of_closed[OF closedin_diffquot_constraint[OF pq(1) pq(2)]])
  show "AE \<omega> in kglue_law r T N Q RR.
      (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
  proof (rule AE_kglue_law[OF r rT exit_class_prob[OF Q]
        exit_class_prob[OF R] exit_class_sets[OF Q]
        exit_class_sets[OF R] Nm mset])
    show "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> r \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
      using Q unfolding exit_class_def by blast
    show "AE f in Pi\<^sub>M UNIV RR. \<forall>j. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T - r \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (f j t) - snd (f j s)) \<in> sconstraint k L"
      unfolding AE_all_countable
    proof
      fix j :: nat
      have Pj: "prob_space (RR i)" if "i \<in> (UNIV :: nat set)" for i
        by (rule exit_class_prob[OF R])
      have dj: "distr (Pi\<^sub>M UNIV RR) (RR j) (\<lambda>f. f j) = RR j"
        by (rule distr_PiM_component[OF Pj UNIV_I])
      have mj: "(\<lambda>f :: nat \<Rightarrow> 'n pairpath. f j) \<in> Pi\<^sub>M UNIV RR \<rightarrow>\<^sub>M RR j"
        by (rule measurable_component_singleton) simp
      have "AE \<omega>' in RR j. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T - r \<longrightarrow>
          (1 / (t - s)) *\<^sub>R (snd (\<omega>' t) - snd (\<omega>' s)) \<in> sconstraint k L"
        using R unfolding exit_class_def by blast
      then have "AE \<omega>' in distr (Pi\<^sub>M UNIV RR) (RR j) (\<lambda>f. f j).
          \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T - r \<longrightarrow>
            (1 / (t - s)) *\<^sub>R (snd (\<omega>' t) - snd (\<omega>' s)) \<in> sconstraint k L"
        unfolding dj .
      from AE_distrD[OF mj this]
      show "AE f in Pi\<^sub>M UNIV RR. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T - r \<longrightarrow>
          (1 / (t - s)) *\<^sub>R (snd (f j t) - snd (f j s)) \<in> sconstraint k L" .
    qed
    fix \<omega> :: "'n pairpath" and f :: "nat \<Rightarrow> 'n pairpath"
    assume "\<omega> \<in> mspace (path_metric r :: ('n pairpath) metric)"
      and "f \<in> space (Pi\<^sub>M UNIV RR)"
      and Aw: "\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> r \<longrightarrow>
          (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
      and Bf: "\<forall>j. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T - r \<longrightarrow>
          (1 / (t - s)) *\<^sub>R (snd (f j t) - snd (f j s)) \<in> sconstraint k L"
    show "(1 / (q - p)) *\<^sub>R (snd (kglue r T N (\<omega>, f) q)
        - snd (kglue r T N (\<omega>, f) p)) \<in> sconstraint k L"
      using pq Aw Bf unfolding kglue_def
      by (intro pglue_diffquot[OF r rT]) auto
  qed
qed

text \<open>The decomposition for clauses (iii) and (iv) of the kernel glue is
  pointwise: the second summand subtracts the continuation's initial
  value, so it is literally \<open>0\<close> before \<open>r\<close>, keeping it adapted since \<open>N\<close>
  is only \<open>\<F>\<^sub>r\<close>-measurable.  Freezing the first coordinate turns \<open>X\<^sub>r\<close>
  into a constant, so even clause (iv)'s cross term is a second-factor
  martingale (a bounded-linear image of one), and
  \<open>martingale_pair_snd_param\<close> carries everything.\<close>

text \<open>\<open>martingale_sub_initial\<close> lives in
  @{theory Continuous_Time_Martingales.Martingale_Algebra}.\<close>

lemma kglue_param_martingale:
  fixes RR :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and Z :: "nat \<Rightarrow> real \<Rightarrow> ('n pairpath)
        \<Rightarrow> 'c::{banach,second_countable_topology}"
  assumes rT: "r \<le> T"
    and mg: "\<And>j. martingale (RR j) (natural_filtration (RR j) 0 (\<lambda>v \<omega>. \<omega> v)) 0 (Z j)"
    and PR: "\<And>j. prob_space (RR j)"
  shows "martingale (Pi\<^sub>M UNIV RR)
      (\<lambda>u. Pi\<^sub>M UNIV (\<lambda>j. natural_filtration (RR j) 0 (\<lambda>v \<omega>. \<omega> v) (max (u - r) 0)))
      0 (\<lambda>u f. Z i (max (u - r) 0) (f i))"
proof -
  let ?GR = "\<lambda>j. natural_filtration (RR j) 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  have FR: "filtered_measure (RR j) (?GR j) (0::real)" for j
  proof -
    interpret MJ: martingale "RR j" "?GR j" "0::real" "Z j" by (rule mg)
    show ?thesis by unfold_locales
  qed
  have s0: "0 \<le> max (u - r) 0" for u :: real by simp
  have smono: "max (u - r) 0 \<le> max (v - r) 0" if "0 \<le> u" "u \<le> v" for u v :: real
    using that by simp
  have "martingale (Pi\<^sub>M UNIV RR) (\<lambda>u. Pi\<^sub>M UNIV (\<lambda>j. ?GR j u)) 0
      (\<lambda>u f. Z i u (f i))"
    by (rule martingale_PiM_component[OF PR FR mg])
  from martingale_time_change[OF this s0 smono] show ?thesis .
qed

text \<open>The uniform first-moment bound the kernel glue's integrability needs:
  the bound depends only on \<open>k\<close>, \<open>L\<close> and the horizon, not on the member ---
  so it holds simultaneously for every candidate continuation in the
  family.  \<open>a \<le> 1 + a\<^sup>2\<close> avoids a square root, so no Cauchy--Schwarz is
  needed.\<close>

lemma exit_class_norm_mean_le:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> exit_class k L T (0 :: real^'n)" and t: "t \<in> {0..T}"
  shows "(\<integral>\<omega>. norm (fst (\<omega> t)) \<partial>Q)
      \<le> 1 + real CARD('n) * (real CARD('n) * L * T)"
proof -
  interpret P: prob_space Q by (rule exit_class_prob[OF Q])
  have key: "a \<le> 1 + a * a" for a :: real
  proof -
    have "0 \<le> (a - 1/2) * (a - 1/2)" by simp
    then have "0 \<le> a * a - a + 1/4" by (simp add: algebra_simps)
    then show ?thesis by linarith
  qed
  have ni: "integrable Q (\<lambda>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t))"
    by (rule exit_class_norm_sq_integrable[OF T L Q t])
  have i1: "integrable Q (\<lambda>\<omega>. 1 + fst (\<omega> t) \<bullet> fst (\<omega> t))"
    using ni by simp
  have fstB: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
      \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  have nm: "(\<lambda>\<omega> :: 'n pairpath. norm (fst (\<omega> t))) \<in> borel_measurable Q"
  proof -
    have "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> t)) \<in> borel_measurable Q"
      by (rule measurable_compose
          [OF exit_class_eval_measurable[OF Q t] fstB])
    then show ?thesis by measurable
  qed
  have le: "norm (fst (\<omega> t)) \<le> 1 + fst (\<omega> t) \<bullet> fst (\<omega> t)" for \<omega> :: "'n pairpath"
    using key[of "norm (fst (\<omega> t))"]
    by (simp add: power2_norm_eq_inner[symmetric] power2_eq_square)
  have i0: "integrable Q (\<lambda>\<omega> :: 'n pairpath. norm (fst (\<omega> t)))"
  proof (rule Bochner_Integration.integrable_bound[OF i1 nm])
    show "AE \<omega> in Q. norm (norm (fst (\<omega> t)))
        \<le> norm (1 + fst (\<omega> t) \<bullet> fst (\<omega> t))"
      using le by (intro AE_I2) auto
  qed
  have "(\<integral>\<omega>. norm (fst (\<omega> t)) \<partial>Q) \<le> (\<integral>\<omega>. 1 + fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q)"
    by (rule integral_mono[OF i0 i1]) (rule le)
  also have "\<dots> = 1 + (\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q)"
    using ni by (simp add: P.prob_space)
  also have "(\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q)
      = (\<Sum>i\<in>UNIV. (\<integral>\<omega>. (fst (\<omega> t) $ i)\<^sup>2 \<partial>Q))"
  proof -
    have "(\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q)
        = (\<integral>\<omega>. (\<Sum>i\<in>UNIV. (fst (\<omega> t) $ i)\<^sup>2) \<partial>Q)"
      by (rule Bochner_Integration.integral_cong)
        (simp_all add: inner_vec_def power2_eq_square)
    also have "\<dots> = (\<Sum>i\<in>UNIV. (\<integral>\<omega>. (fst (\<omega> t) $ i)\<^sup>2 \<partial>Q))"
      by (rule Bochner_Integration.integral_sum)
        (rule exit_class_sq_integrable[OF T L Q t])
    finally show ?thesis .
  qed
  also have "(\<Sum>i\<in>UNIV. (\<integral>\<omega>. (fst (\<omega> t) $ i)\<^sup>2 \<partial>Q))
      \<le> (\<Sum>i\<in>(UNIV :: 'n set). real CARD('n) * L * T)"
  proof (rule sum_mono)
    fix i :: 'n
    have "(\<integral>\<omega>. (fst (\<omega> t) $ i)\<^sup>2 \<partial>Q)
        \<le> ((0 :: real^'n) $ i)\<^sup>2 + real CARD('n) * L * T"
      by (rule exit_class_sq_mean_le[OF T L Q t])
    then show "(\<integral>\<omega>. (fst (\<omega> t) $ i)\<^sup>2 \<partial>Q) \<le> real CARD('n) * L * T" by simp
  qed
  finally show ?thesis by simp
qed

theorem kglue_law_X_martingale:
  fixes Q :: "('n::finite pairpath) measure"
    and RR :: "nat \<Rightarrow> ('n pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T" and L0: "0 \<le> L"
    and Q: "Q \<in> exit_class k L r x"
    and R: "\<And>j. RR j \<in> exit_class k L (T - r) 0"
    and Nm: "N \<in> natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v) r \<rightarrow>\<^sub>M count_space UNIV"
  shows "martingale (kglue_law r T N Q RR)
      (natural_filtration (kglue_law r T N Q RR) 0 (\<lambda>v \<omega>. \<omega> v)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u T)) :: real^'n)"
proof -
  let ?S = "Pi\<^sub>M UNIV RR"
  let ?M = "Q \<Otimes>\<^sub>M ?S"
  let ?FQ = "natural_filtration Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?GR = "\<lambda>j. natural_filtration (RR j) 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?s = "\<lambda>u :: real. max (u - r) 0"
  let ?t = "\<lambda>u :: real. min (max (u - r) 0) (T - r)"
  let ?GS = "\<lambda>u. Pi\<^sub>M UNIV (\<lambda>j. ?GR j (?s u))"
  let ?FF = "\<lambda>u. ?FQ (min u r) \<Otimes>\<^sub>M ?GS u"
  let ?B = "\<lambda>u p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath).
      fst (snd p (N (fst p)) (?t u)) - fst (snd p (N (fst p)) 0) :: real^'n"
  have T0: "0 \<le> T" using r rT by simp
  have TR: "0 \<le> T - r" using rT by simp
  have PQ: "prob_space Q" by (rule exit_class_prob[OF Q])
  have PRj: "prob_space (RR j)" for j by (rule exit_class_prob[OF R])
  have PS: "prob_space ?S" by (rule prob_space_PiM) (rule PRj)
  interpret PQi: prob_space Q by (rule PQ)
  interpret PS': pair_sigma_finite Q ?S
    by (simp add: pair_sigma_finite_def PQ PS prob_space_imp_sigma_finite)
  have setsQ: "sets Q = sets (path_borel r :: ('n pairpath) measure)"
    by (rule exit_class_sets[OF Q])
  have setsR: "sets (RR j) = sets ((path_borel (T - r) :: ('n pairpath) measure))" for j
    by (rule exit_class_sets[OF R])
  have fstB: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
      \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)

  \<comment> \<open>the first factor's martingale, on the clock \<open>min u r\<close>\<close>
  have mQ0: "martingale Q ?FQ 0 (\<lambda>u \<omega>. fst (\<omega> (min u r)) :: real^'n)"
    by (rule exit_class_X_martingale[OF Q])
  have s1_0: "0 \<le> min u r" if "0 \<le> u" for u :: real using that r by simp
  have s1_mono: "min u r \<le> min v r" if "0 \<le> u" "u \<le> v" for u v :: real
    using that by simp
  have mQ: "martingale Q (\<lambda>u. ?FQ (min u r)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u r)) :: real^'n)"
  proof (rule martingale_cong_ge
      [OF martingale_time_change[OF mQ0 s1_0 s1_mono]])
    fix u :: real assume "0 \<le> u"
    show "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min (min u r) r)) :: real^'n)
        = (\<lambda>\<omega>. fst (\<omega> (min u r)))" by simp
  qed
  have FQf: "filtered_measure Q (\<lambda>u. ?FQ (min u r)) (0::real)"
  proof -
    interpret MQ: martingale Q "\<lambda>u. ?FQ (min u r)" "0::real"
      "\<lambda>u \<omega>. fst (\<omega> (min u r)) :: real^'n" by (rule mQ)
    show ?thesis by unfold_locales
  qed
  have NmQ: "N \<in> Q \<rightarrow>\<^sub>M count_space UNIV"
  proof -
    interpret MQ0: martingale Q ?FQ "0::real"
      "\<lambda>u \<omega>. fst (\<omega> (min u r)) :: real^'n" by (rule mQ0)
    show ?thesis
      by (rule measurable_from_subalg[OF MQ0.subalgebras[OF r] Nm])
  qed

  \<comment> \<open>the second factor's martingale, per index, on the clock \<open>(u-r)\<^sup>+\<close>\<close>
  have mZ: "martingale (RR j) (?GR j) 0
      (\<lambda>v \<omega>'. fst (\<omega>' (min v (T - r))) - fst (\<omega>' 0) :: real^'n)" for j
  proof -
    have "martingale (RR j) (?GR j) 0 (\<lambda>v \<omega>'.
        (fst (\<omega>' (min v (T - r))) :: real^'n)
          - (\<lambda>w \<omega>'. fst (\<omega>' (min w (T - r))) :: real^'n) 0 \<omega>')"
      by (rule martingale_sub_initial[OF exit_class_X_martingale[OF R]])
    then show ?thesis using TR by simp
  qed
  have mBj: "martingale ?S ?GS 0
      (\<lambda>u f. fst (f i (?t u)) - fst (f i 0) :: real^'n)" for i
    by (rule kglue_param_martingale[OF rT mZ PRj])
  have FSf: "filtered_measure ?S ?GS (0::real)"
  proof -
    interpret MS: martingale ?S ?GS "0::real"
      "\<lambda>u f. fst (f 0 (?t u)) - fst (f 0 0) :: real^'n" by (rule mBj)
    show ?thesis by unfold_locales
  qed

  \<comment> \<open>evaluation measurability on the product filtration\<close>
  have evQ: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). fst p b)
      \<in> borel_measurable (?FF u)" if "0 \<le> b" "b \<le> min u r" for b u
    by (rule measurable_compose[OF measurable_fst nat_filt_eval[OF that]])
  have Nidx: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). N (fst p))
      \<in> ?FF u \<rightarrow>\<^sub>M count_space UNIV" if u: "r \<le> u" for u
  proof -
    have "min u r = r" using u by simp
    then show ?thesis using measurable_compose[OF measurable_fst Nm] by simp
  qed
  have evK: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). snd p (N (fst p)) w)
      \<in> borel_measurable (?FF u)" if u: "r \<le> u" and w: "0 \<le> w" "w \<le> ?s u"
    for u w
  proof (rule measurable_compose_countable[OF _ Nidx[OF u]])
    fix j :: nat
    have "(\<lambda>f :: nat \<Rightarrow> 'n pairpath. f j) \<in> ?GS u \<rightarrow>\<^sub>M ?GR j (?s u)"
      by (rule measurable_component_singleton) simp
    from measurable_compose[OF measurable_snd this]
    have "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). snd p j)
        \<in> ?FF u \<rightarrow>\<^sub>M ?GR j (?s u)" .
    from measurable_compose[OF this nat_filt_eval[OF w]]
    show "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). snd p j w)
        \<in> borel_measurable (?FF u)" .
  qed
  have adapB: "?B u \<in> borel_measurable (?FF u)" if u: "0 \<le> u" for u
  proof (cases "u \<le> r")
    case True
    then have "?t u = 0" using TR by simp
    then have "?B u = (\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). 0)" by simp
    then show ?thesis by simp
  next
    case False
    then have ru: "r \<le> u" by simp
    have m1: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath).
        snd p (N (fst p)) (?t u)) \<in> borel_measurable (?FF u)"
      by (rule evK[OF ru]) (use TR in auto)
    have m2: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath).
        snd p (N (fst p)) 0) \<in> borel_measurable (?FF u)"
      by (rule evK[OF ru]) auto
    show ?thesis
      using measurable_compose[OF m1 fstB] measurable_compose[OF m2 fstB]
      by (rule borel_measurable_diff)
  qed
  have BM: "?B u \<in> borel_measurable ?M" if u: "0 \<le> u" for u
  proof -
    interpret FP: filtered_measure ?M ?FF "0::real"
      by (rule filtered_measure_pair[OF FQf FSf])
    show ?thesis
      by (rule measurable_from_subalg[OF FP.subalgebras[OF u] adapB[OF u]])
  qed
  \<comment> \<open>integrability, uniformly over the family of continuations\<close>
  define C where "C = 1 + real CARD('n) * (real CARD('n) * L * (T - r))"
  have mj: "(\<lambda>f :: nat \<Rightarrow> 'n pairpath. f j) \<in> ?S \<rightarrow>\<^sub>M RR j" for j
    by (rule measurable_component_singleton) simp
  have dj: "distr ?S (RR j) (\<lambda>f. f j) = RR j" for j
    by (rule distr_PiM_component) (rule PRj, simp)
  have hX: "(\<lambda>\<omega>' :: 'n pairpath. fst (\<omega>' v) :: real^'n)
      \<in> borel_measurable (RR j)" for j v
    by (rule measurable_compose[OF pair_law_eval_measurable[OF setsR] fstB])
  have intRj: "integrable (RR j) (\<lambda>\<omega>' :: 'n pairpath. fst (\<omega>' v) :: real^'n)"
    if v: "v \<in> {0..T - r}" for j v
  proof -
    interpret MJ: martingale "RR j" "?GR j" "0::real"
      "\<lambda>w \<omega>'. fst (\<omega>' (min w (T - r))) :: real^'n"
      by (rule exit_class_X_martingale[OF R])
    have "integrable (RR j) (\<lambda>\<omega>'. fst (\<omega>' (min v (T - r))) :: real^'n)"
      using MJ.integrable[of v] v by simp
    then show ?thesis using v by simp
  qed
  have intSj: "integrable ?S (\<lambda>f. fst (f j v) :: real^'n)"
    if v: "v \<in> {0..T - r}" for j v
  proof -
    have "integrable (distr ?S (RR j) (\<lambda>f. f j))
        (\<lambda>\<omega>'. fst (\<omega>' v) :: real^'n)"
      unfolding dj by (rule intRj[OF v])
    then show ?thesis using integrable_distr_eq[OF mj hX] by simp
  qed
  have bndSj: "(\<integral>f. norm (fst (f j v)) \<partial>?S) \<le> C"
    if v: "v \<in> {0..T - r}" for j v
  proof -
    have hn: "(\<lambda>\<omega>' :: 'n pairpath. norm (fst (\<omega>' v)))
        \<in> borel_measurable (RR j)" using hX by measurable
    have "(\<integral>f. norm (fst (f j v)) \<partial>?S) = (\<integral>\<omega>'. norm (fst (\<omega>' v)) \<partial>(RR j))"
      by (rule integral_distr[OF mj hn, unfolded dj, symmetric])
    also have "\<dots> \<le> C" unfolding C_def
      by (rule exit_class_norm_mean_le[OF TR L0 R v])
    finally show ?thesis .
  qed
  have tI: "?t u \<in> {0..T - r}" for u using TR by auto
  have zI: "(0::real) \<in> {0..T - r}" using TR by simp
  have secInt: "integrable ?S
      (\<lambda>f. fst (f i (?t u)) - fst (f i 0) :: real^'n)" for i u
    using intSj[OF tI] intSj[OF zI] by simp
  have secBnd: "(\<integral>f. norm (fst (f i (?t u)) - fst (f i 0)) \<partial>?S) \<le> 2 * C"
    for i u
  proof -
    have i1: "integrable ?S (\<lambda>f. norm (fst (f i (?t u))))"
      by (rule integrable_norm[OF intSj[OF tI]])
    have i2: "integrable ?S (\<lambda>f. norm (fst (f i 0)))"
      by (rule integrable_norm[OF intSj[OF zI]])
    have "(\<integral>f. norm (fst (f i (?t u)) - fst (f i 0)) \<partial>?S)
        \<le> (\<integral>f. norm (fst (f i (?t u))) + norm (fst (f i 0)) \<partial>?S)"
      using integrable_norm[OF secInt] i1 i2
      by (intro integral_mono) (auto simp: norm_triangle_ineq4)
    also have "\<dots> = (\<integral>f. norm (fst (f i (?t u))) \<partial>?S)
        + (\<integral>f. norm (fst (f i 0)) \<partial>?S)"
      using i1 i2 by simp
    also have "\<dots> \<le> C + C"
    proof -
      have b1: "(\<integral>f. norm (fst (f i (?t u))) \<partial>?S) \<le> C" by (rule bndSj[OF tI])
      have b2: "(\<integral>f. norm (fst (f i 0)) \<partial>?S) \<le> C" by (rule bndSj[OF zI])
      show ?thesis using b1 b2 by simp
    qed
    finally show ?thesis by simp
  qed
  have intB: "integrable ?M (?B u)" if u: "0 \<le> u" for u
  proof (rule PS'.Fubini_integrable[OF BM[OF u]])
    have e: "(\<lambda>\<omega>. \<integral>f. norm (?B u (\<omega>, f)) \<partial>?S)
        = (\<lambda>\<omega>. \<integral>f. norm (fst (f (N \<omega>) (?t u)) - fst (f (N \<omega>) 0)) \<partial>?S)"
      by simp
    have meas: "(\<lambda>\<omega> :: 'n pairpath.
          (\<integral>f. norm (fst (f (N \<omega>) (?t u)) - fst (f (N \<omega>) 0)) \<partial>?S))
        \<in> borel_measurable Q"
    proof (rule measurable_compose_countable
        [where f = "\<lambda>j (_ :: 'n pairpath).
            (\<integral>f. norm (fst (f j (?t u)) - fst (f j 0)) \<partial>?S)"])
      show "(\<lambda>_ :: 'n pairpath.
          (\<integral>f. norm (fst (f j (?t u)) - fst (f j 0)) \<partial>?S))
          \<in> borel_measurable Q" for j by simp
      show "N \<in> Q \<rightarrow>\<^sub>M count_space UNIV" by (rule NmQ)
    qed
    show "integrable Q (\<lambda>\<omega>. \<integral>f. norm (?B u (\<omega>, f)) \<partial>?S)"
      unfolding e
    proof (rule PQi.integrable_const_bound[where B = "2 * C"])
      show "AE \<omega> in Q. norm (\<integral>f. norm (fst (f (N \<omega>) (?t u))
          - fst (f (N \<omega>) 0)) \<partial>?S) \<le> 2 * C"
      proof (intro AE_I2)
        fix \<omega> :: "'n pairpath"
        have nn: "0 \<le> (\<integral>f. norm (fst (f (N \<omega>) (?t u))
            - fst (f (N \<omega>) 0)) \<partial>?S)"
          by (rule integral_nonneg_AE) simp
        show "norm (\<integral>f. norm (fst (f (N \<omega>) (?t u))
            - fst (f (N \<omega>) 0)) \<partial>?S) \<le> 2 * C"
          using nn secBnd[of "N \<omega>" u] by simp
      qed
    qed (rule meas)
    show "AE \<omega> in Q. integrable ?S (\<lambda>f. ?B u (\<omega>, f))"
      using secInt by simp
  qed

  \<comment> \<open>the two halves, added and matched to the glued process\<close>
  have mB: "martingale ?M ?FF 0 ?B"
  proof (rule martingale_pair_snd_param[OF PQ PS FQf FSf adapB intB])
    fix \<omega> :: "'n pairpath" assume "\<omega> \<in> space Q"
    show "martingale ?S ?GS 0 (\<lambda>u f. ?B u (\<omega>, f))"
      using mBj[of "N \<omega>"] by simp
  qed
  have mA: "martingale ?M ?FF 0
      (\<lambda>u p. fst (fst p (min u r)) :: real^'n)"
    by (rule martingale_pair_fst[OF PQ PS mQ FSf])
  have mgl: "martingale ?M ?FF 0
      (\<lambda>u p. fst (kglue r T N p (min u T)) :: real^'n)"
  proof (rule martingale_cong_ge[OF martingale_add[OF mA mB]])
    fix u :: real assume u: "0 \<le> u"
    have muI: "min u T \<in> {0..T}" using u T0 by simp
    show "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath).
          fst (fst p (min u r)) + ?B u p)
        = (\<lambda>p. fst (kglue r T N p (min u T)) :: real^'n)"
    proof (rule ext)
      fix p :: "'n pairpath \<times> (nat \<Rightarrow> 'n pairpath)"
      show "fst (fst p (min u r)) + ?B u p
          = fst (kglue r T N p (min u T))"
      proof (cases "u \<le> r")
        case True
        then have uT: "u \<le> T" using rT by simp
        then have le: "min u T \<le> r" using True by simp
        have e1: "min u T = min u r" using True uT by simp
        have e2: "?t u = 0" using True TR by simp
        have g0: "kglue r T N p (min u T) = fst p (min u r)"
          unfolding kglue_def e1[symmetric]
          by (simp add: pglue_le[OF muI le])
        show ?thesis by (simp add: g0 e2)
      next
        case False
        then have ru: "r < u" by simp
        have rv: "r \<le> min u T" using ru rT by simp
        have e1: "min u r = r" using ru by simp
        have e2: "?t u = min u T - r" using ru by (simp add: min_def)
        have g0: "kglue r T N p (min u T)
            = fst p r + (snd p (N (fst p)) (min u T - r)
                - snd p (N (fst p)) 0)"
          unfolding kglue_def by (simp add: pglue_ge[OF muI rv])
        show ?thesis by (simp add: g0 e1 e2)
      qed
    qed
  qed

  \<comment> \<open>transport to the pasted law\<close>
  have gadap: "(\<lambda>p. kglue r T N p v) \<in> borel_measurable (?FF u)"
    if v: "0 \<le> v" and vu: "v \<le> u" for u v
  proof (cases "v \<le> T")
    case False
    then have "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). kglue r T N p v)
        = (\<lambda>p. undefined)" by (auto simp: kglue_def pglue_def)
    then show ?thesis by simp
  next
    case True
    then have vI: "v \<in> {0..T}" using v by simp
    show ?thesis
    proof (cases "v \<le> r")
      case True
      then have "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). kglue r T N p v)
          = (\<lambda>p. fst p v)" by (simp add: kglue_def pglue_le[OF vI])
      then show ?thesis using evQ[of v u] v vu True by simp
    next
      case False
      then have rv: "r \<le> v" by simp
      have ru: "r \<le> u" using rv vu by simp
      have e: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). kglue r T N p v)
          = (\<lambda>p. fst p r + (snd p (N (fst p)) (v - r)
              - snd p (N (fst p)) 0))"
        by (simp add: kglue_def pglue_ge[OF vI rv])
      have m1: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). fst p r)
          \<in> borel_measurable (?FF u)"
        by (rule evQ) (use r ru in auto)
      have m2: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath).
          snd p (N (fst p)) (v - r)) \<in> borel_measurable (?FF u)"
        by (rule evK[OF ru]) (use rv vu in auto)
      have m3: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath).
          snd p (N (fst p)) 0) \<in> borel_measurable (?FF u)"
        by (rule evK[OF ru]) auto
      show ?thesis unfolding e using m1 m2 m3 by simp
    qed
  qed
  have Zm: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min u T)) :: real^'n)
      \<in> borel_measurable (natural_filtration (kglue_law r T N Q RR) 0
          (\<lambda>v \<omega>. \<omega> v) u)" if u: "0 \<le> u" for u
  proof -
    have "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u T))
        \<in> natural_filtration (kglue_law r T N Q RR) 0 (\<lambda>v \<omega>. \<omega> v) u
          \<rightarrow>\<^sub>M borel"
      by (rule nat_filt_eval) (use u T0 in auto)
    then show ?thesis by (rule measurable_compose[OF _ fstB])
  qed
  show ?thesis
    unfolding kglue_law_def
    by (rule martingale_pair_law[OF prob_space_pair_measure[OF PQ PS]
        kglue_measurable[OF r rT setsQ setsR NmQ] gadap
        Zm[unfolded kglue_law_def] mgl])
qed

text \<open>The cross term of \<open>outerp (X\<^sub>r + W)\<close> is \<open>X\<^sub>r \<otimes> W + W \<otimes> X\<^sub>r\<close>; once the
  first coordinate is frozen, \<open>X\<^sub>r\<close> is constant and \<open>v \<mapsto> c \<otimes> v + v \<otimes> c\<close>
  is linear, hence bounded on a finite-dimensional space --- so the cross
  term is a bounded-linear image of the second factor's martingale, not a
  product of two martingales.\<close>

text \<open>\<open>norm_outer_prod\<close> lives in
  @{theory Symmetric_Matrix_Spectra.Poincare_Separation}, stated through
  \<open>outer_prod\<close>; \<open>outerp x\<close> is \<open>outer_prod x x\<close>.\<close>

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

lemma kglue_param_comp_martingale:
  fixes RR :: "nat \<Rightarrow> ('n::finite pairpath) measure"
  assumes rT: "r \<le> T"
    and R: "\<And>j. RR j \<in> exit_class k L (T - r) 0"
  shows "martingale (Pi\<^sub>M UNIV RR)
      (\<lambda>u. Pi\<^sub>M UNIV (\<lambda>j. natural_filtration (RR j) 0 (\<lambda>v \<omega>. \<omega> v) (max (u - r) 0)))
      0 (\<lambda>u f. outerp (fst (f i (min (max (u - r) 0) (T - r)))
              - fst (f i 0) :: real^'n)
          - (snd (f i (min (max (u - r) 0) (T - r))) - snd (f i 0)))"
proof -
  let ?S = "Pi\<^sub>M UNIV RR"
  let ?GR = "\<lambda>j. natural_filtration (RR j) 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?s = "\<lambda>u :: real. max (u - r) 0"
  let ?t = "\<lambda>u :: real. min (max (u - r) 0) (T - r)"
  let ?GS = "\<lambda>u. Pi\<^sub>M UNIV (\<lambda>j. ?GR j (?s u))"
  have TR: "0 \<le> T - r" using rT by simp
  have PRj: "prob_space (RR j)" for j by (rule exit_class_prob[OF R])
  have m0: "martingale ?S ?GS 0
      (\<lambda>u f. outerp (fst (f i (?t u)) :: real^'n) - snd (f i (?t u)))"
    by (rule kglue_param_martingale
        [OF rT exit_class_compensated_martingale[OF R] PRj])
  have FSf: "filtered_measure ?S ?GS (0::real)"
  proof -
    interpret MS: martingale ?S ?GS "0::real"
      "\<lambda>u f. outerp (fst (f i (?t u)) :: real^'n) - snd (f i (?t u))"
      by (rule m0)
    show ?thesis by unfold_locales
  qed
  have start: "AE f in ?S. fst (f i 0) = (0::real^'n) \<and> snd (f i 0) = 0"
  proof -
    have Pj: "prob_space (RR j)" if "j \<in> (UNIV::nat set)" for j by (rule PRj)
    have dj: "distr ?S (RR i) (\<lambda>f. f i) = RR i"
      by (rule distr_PiM_component[OF Pj UNIV_I])
    have mi: "(\<lambda>f :: nat \<Rightarrow> 'n pairpath. f i) \<in> ?S \<rightarrow>\<^sub>M RR i"
      by (rule measurable_component_singleton) simp
    have "AE \<omega>' in RR i. fst (\<omega>' 0) = (0::real^'n) \<and> snd (\<omega>' 0) = 0"
      using R unfolding exit_class_def by blast
    then have "AE \<omega>' in distr ?S (RR i) (\<lambda>f. f i).
        fst (\<omega>' 0) = (0::real^'n) \<and> snd (\<omega>' 0) = 0" unfolding dj .
    from AE_distrD[OF mi this] show ?thesis .
  qed
  have adap: "(\<lambda>f :: nat \<Rightarrow> 'n pairpath.
      outerp (fst (f i (?t u)) - fst (f i 0) :: real^'n)
        - (snd (f i (?t u)) - snd (f i 0))) \<in> borel_measurable (?GS u)"
    if u: "0 \<le> u" for u
  proof -
    have ev: "(\<lambda>f :: nat \<Rightarrow> 'n pairpath. f i v) \<in> borel_measurable (?GS u)"
      if "0 \<le> v" "v \<le> ?s u" for v
    proof -
      have "(\<lambda>f :: nat \<Rightarrow> 'n pairpath. f i) \<in> ?GS u \<rightarrow>\<^sub>M ?GR i (?s u)"
        by (rule measurable_component_singleton) simp
      from measurable_compose[OF this nat_filt_eval[OF that]] show ?thesis .
    qed
    have e1: "(\<lambda>f :: nat \<Rightarrow> 'n pairpath. f i (?t u)) \<in> borel_measurable (?GS u)"
      by (rule ev) (use TR in auto)
    have e2: "(\<lambda>f :: nat \<Rightarrow> 'n pairpath. f i 0) \<in> borel_measurable (?GS u)"
      by (rule ev) auto
    have a1: "(\<lambda>f. fst (f i (?t u)) :: real^'n) \<in> borel_measurable (?GS u)"
      by (rule measurable_compose[OF e1 pair_fst_borel])
    have a2: "(\<lambda>f. fst (f i 0) :: real^'n) \<in> borel_measurable (?GS u)"
      by (rule measurable_compose[OF e2 pair_fst_borel])
    have b1: "(\<lambda>f. snd (f i (?t u)) :: real^'n^'n) \<in> borel_measurable (?GS u)"
      by (rule measurable_compose[OF e1 pair_snd_borel])
    have b2: "(\<lambda>f. snd (f i 0) :: real^'n^'n) \<in> borel_measurable (?GS u)"
      by (rule measurable_compose[OF e2 pair_snd_borel])
    have d1: "(\<lambda>f. fst (f i (?t u)) - fst (f i 0) :: real^'n)
        \<in> borel_measurable (?GS u)" using a1 a2 by (rule borel_measurable_diff)
    have o1: "(\<lambda>f. outerp (fst (f i (?t u)) - fst (f i 0)) :: real^'n^'n)
        \<in> borel_measurable (?GS u)"
      by (rule measurable_compose[OF d1 outerp_borel])
    have d2: "(\<lambda>f. snd (f i (?t u)) - snd (f i 0) :: real^'n^'n)
        \<in> borel_measurable (?GS u)" using b1 b2 by (rule borel_measurable_diff)
    show ?thesis using o1 d2 by (rule borel_measurable_diff)
  qed
  show ?thesis
  proof (rule martingale_cong_AE[OF m0])
    show "adapted_process ?S ?GS 0 (\<lambda>u f.
        outerp (fst (f i (?t u)) - fst (f i 0) :: real^'n)
          - (snd (f i (?t u)) - snd (f i 0)))"
      unfolding adapted_process_def adapted_process_axioms_def
      using FSf adap by blast
  next
    fix u :: real assume "0 \<le> u"
    show "AE f in ?S. outerp (fst (f i (?t u)) :: real^'n) - snd (f i (?t u))
        = outerp (fst (f i (?t u)) - fst (f i 0)) - (snd (f i (?t u)) - snd (f i 0))"
      by (rule eventually_mono[OF start]) simp
  qed
qed

lemma exit_class_inner_mean_le:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> exit_class k L T (0 :: real^'n)" and t: "t \<in> {0..T}"
  shows "(\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q)
      \<le> real CARD('n) * (real CARD('n) * L * T)"
proof -
  have "(\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q)
      = (\<Sum>i\<in>UNIV. (\<integral>\<omega>. (fst (\<omega> t) $ i)\<^sup>2 \<partial>Q))"
  proof -
    have "(\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q)
        = (\<integral>\<omega>. (\<Sum>i\<in>UNIV. (fst (\<omega> t) $ i)\<^sup>2) \<partial>Q)"
      by (rule Bochner_Integration.integral_cong)
        (simp_all add: inner_vec_def power2_eq_square)
    also have "\<dots> = (\<Sum>i\<in>UNIV. (\<integral>\<omega>. (fst (\<omega> t) $ i)\<^sup>2 \<partial>Q))"
      by (rule Bochner_Integration.integral_sum)
        (rule exit_class_sq_integrable[OF T L Q t])
    finally show ?thesis .
  qed
  also have "\<dots> \<le> (\<Sum>i\<in>(UNIV :: 'n set). real CARD('n) * L * T)"
  proof (rule sum_mono)
    fix i :: 'n
    have "(\<integral>\<omega>. (fst (\<omega> t) $ i)\<^sup>2 \<partial>Q)
        \<le> ((0 :: real^'n) $ i)\<^sup>2 + real CARD('n) * L * T"
      by (rule exit_class_sq_mean_le[OF T L Q t])
    then show "(\<integral>\<omega>. (fst (\<omega> t) $ i)\<^sup>2 \<partial>Q) \<le> real CARD('n) * L * T" by simp
  qed
  finally show ?thesis by simp
qed

lemma exit_class_comp_norm_mean_le:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> exit_class k L T (0 :: real^'n)" and t: "t \<in> {0..T}"
  shows "(\<integral>\<omega>. norm (outerp (fst (\<omega> t)) - snd (\<omega> t)) \<partial>Q)
      \<le> real CARD('n) * (real CARD('n) * L * T) + real CARD('n) * L * T"
proof -
  interpret P: prob_space Q by (rule exit_class_prob[OF Q])
  have iC: "integrable Q (\<lambda>\<omega>. outerp (fst (\<omega> t)) - snd (\<omega> t))"
    by (rule exit_class_compensated_integrable[OF Q t])
  have iN: "integrable Q (\<lambda>\<omega>. norm (outerp (fst (\<omega> t)) - snd (\<omega> t)))"
    by (rule integrable_norm[OF iC])
  have iX: "integrable Q (\<lambda>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t))"
    by (rule exit_class_norm_sq_integrable[OF T L Q t])
  have Ym: "(\<lambda>\<omega> :: 'n pairpath. norm (snd (\<omega> t))) \<in> borel_measurable Q"
  proof -
    have "(\<lambda>\<omega> :: 'n pairpath. snd (\<omega> t)) \<in> borel_measurable Q"
      by (rule measurable_compose
          [OF exit_class_eval_measurable[OF Q t] pair_snd_borel])
    then show ?thesis by measurable
  qed
  have Yb: "AE \<omega> in Q. norm (snd (\<omega> t)) \<le> real CARD('n) * L * T"
    using exit_class_Y_bounded_ae[OF T L Q] t by (auto elim: eventually_mono)
  have iY: "integrable Q (\<lambda>\<omega> :: 'n pairpath. norm (snd (\<omega> t)))"
  proof (rule P.integrable_const_bound[where B = "real CARD('n) * L * T"])
    show "AE \<omega> in Q. norm (norm (snd (\<omega> t))) \<le> real CARD('n) * L * T"
      using Yb by simp
  qed (rule Ym)
  have "(\<integral>\<omega>. norm (outerp (fst (\<omega> t)) - snd (\<omega> t)) \<partial>Q)
      \<le> (\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) + norm (snd (\<omega> t)) \<partial>Q)"
  proof (rule integral_mono[OF iN])
    show "integrable Q (\<lambda>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) + norm (snd (\<omega> t)))"
      using iX iY by simp
    fix \<omega> :: "'n pairpath"
    have "norm (outerp (fst (\<omega> t)) - snd (\<omega> t))
        \<le> norm (outerp (fst (\<omega> t))) + norm (snd (\<omega> t))"
      by (rule norm_triangle_ineq4)
    then show "norm (outerp (fst (\<omega> t)) - snd (\<omega> t))
        \<le> fst (\<omega> t) \<bullet> fst (\<omega> t) + norm (snd (\<omega> t))"
      by (simp add: norm_outerp power2_norm_eq_inner[symmetric] power2_eq_square)
  qed
  also have "\<dots> = (\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q)
      + (\<integral>\<omega>. norm (snd (\<omega> t)) \<partial>Q)" using iX iY by simp
  also have "\<dots> \<le> real CARD('n) * (real CARD('n) * L * T)
      + real CARD('n) * L * T"
  proof -
    have b1: "(\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q)
        \<le> real CARD('n) * (real CARD('n) * L * T)"
      by (rule exit_class_inner_mean_le[OF T L Q t])
    have b2: "(\<integral>\<omega>. norm (snd (\<omega> t)) \<partial>Q) \<le> real CARD('n) * L * T"
    proof -
      have "(\<integral>\<omega>. norm (snd (\<omega> t)) \<partial>Q)
          \<le> (\<integral>\<omega>. real CARD('n) * L * T \<partial>Q)"
        using iY Yb by (intro integral_mono_AE) auto
      also have "\<dots> = real CARD('n) * L * T" by (simp add: P.prob_space)
      finally show ?thesis .
    qed
    from b1 b2 show ?thesis by simp
  qed
  finally show ?thesis .
qed

theorem kglue_law_comp_martingale:
  fixes Q :: "('n::finite pairpath) measure"
    and RR :: "nat \<Rightarrow> ('n pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T" and L0: "0 \<le> L"
    and Q: "Q \<in> exit_class k L r x"
    and R: "\<And>j. RR j \<in> exit_class k L (T - r) 0"
    and Nm: "N \<in> natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v) r \<rightarrow>\<^sub>M count_space UNIV"
  shows "martingale (kglue_law r T N Q RR)
      (natural_filtration (kglue_law r T N Q RR) 0 (\<lambda>v \<omega>. \<omega> v)) 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (min u T)) :: real^'n) - snd (\<omega> (min u T)))"
proof -
  let ?S = "Pi\<^sub>M UNIV RR"
  let ?M = "Q \<Otimes>\<^sub>M ?S"
  let ?FQ = "natural_filtration Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?GR = "\<lambda>j. natural_filtration (RR j) 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?s = "\<lambda>u :: real. max (u - r) 0"
  let ?t = "\<lambda>u :: real. min (max (u - r) 0) (T - r)"
  let ?GS = "\<lambda>u. Pi\<^sub>M UNIV (\<lambda>j. ?GR j (?s u))"
  let ?FF = "\<lambda>u. ?FQ (min u r) \<Otimes>\<^sub>M ?GS u"
  let ?Ap = "\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). fst (fst p r) :: real^'n"
  let ?bb = "\<lambda>u p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath).
      fst (snd p (N (fst p)) (?t u)) - fst (snd p (N (fst p)) 0) :: real^'n"
  let ?YY = "\<lambda>u p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath).
      snd (snd p (N (fst p)) (?t u)) - snd (snd p (N (fst p)) 0) :: real^'n^'n"
  let ?P1 = "\<lambda>u p. outerp (?bb u p) - ?YY u p"
  let ?P2 = "\<lambda>u p. (\<chi> i j. ?Ap p $ i * ?bb u p $ j)
      + (\<chi> i j. ?bb u p $ i * ?Ap p $ j)"
  let ?D = "\<lambda>u p. ?P1 u p + ?P2 u p"
  define KK where "KK = real CARD('n) * (real CARD('n) * L * (T - r))
      + real CARD('n) * L * (T - r)"
  define C where "C = 1 + real CARD('n) * (real CARD('n) * L * (T - r))"
  have T0: "0 \<le> T" using r rT by simp
  have TR: "0 \<le> T - r" using rT by simp
  have Cnn: "0 \<le> C" unfolding C_def using L0 TR by simp
  have PQ: "prob_space Q" by (rule exit_class_prob[OF Q])
  have PRj: "prob_space (RR j)" for j by (rule exit_class_prob[OF R])
  have PS: "prob_space ?S" by (rule prob_space_PiM) (rule PRj)
  interpret PQi: prob_space Q by (rule PQ)
  interpret PS': pair_sigma_finite Q ?S
    by (simp add: pair_sigma_finite_def PQ PS prob_space_imp_sigma_finite)
  have setsQ: "sets Q = sets (path_borel r :: ('n pairpath) measure)"
    by (rule exit_class_sets[OF Q])
  have setsR: "sets (RR j) = sets ((path_borel (T - r) :: ('n pairpath) measure))" for j
    by (rule exit_class_sets[OF R])
  have cB: "(\<lambda>q :: (real^'n) \<times> (real^'n^'n). outerp (fst q) - snd q)
      \<in> borel_measurable borel"
    using measurable_compose[OF pair_fst_borel outerp_borel] pair_snd_borel
    by (rule borel_measurable_diff)

  \<comment> \<open>the first factor, on the clock \<open>min u r\<close>\<close>
  have s1_0: "0 \<le> min u r" if "0 \<le> u" for u :: real using that r by simp
  have s1_mono: "min u r \<le> min v r" if "0 \<le> u" "u \<le> v" for u v :: real
    using that by simp
  have mQ0: "martingale Q ?FQ 0 (\<lambda>u \<omega>. fst (\<omega> (min u r)) :: real^'n)"
    by (rule exit_class_X_martingale[OF Q])
  have mQ: "martingale Q (\<lambda>u. ?FQ (min u r)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u r)) :: real^'n)"
  proof (rule martingale_cong_ge
      [OF martingale_time_change[OF mQ0 s1_0 s1_mono]])
    fix u :: real assume "0 \<le> u"
    show "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min (min u r) r)) :: real^'n)
        = (\<lambda>\<omega>. fst (\<omega> (min u r)))" by simp
  qed
  have FQf: "filtered_measure Q (\<lambda>u. ?FQ (min u r)) (0::real)"
  proof -
    interpret MQ: martingale Q "\<lambda>u. ?FQ (min u r)" "0::real"
      "\<lambda>u \<omega>. fst (\<omega> (min u r)) :: real^'n" by (rule mQ)
    show ?thesis by unfold_locales
  qed
  have NmQ: "N \<in> Q \<rightarrow>\<^sub>M count_space UNIV"
  proof -
    interpret MQ0: martingale Q ?FQ "0::real"
      "\<lambda>u \<omega>. fst (\<omega> (min u r)) :: real^'n" by (rule mQ0)
    show ?thesis
      by (rule measurable_from_subalg[OF MQ0.subalgebras[OF r] Nm])
  qed
  have iAQ: "integrable Q (\<lambda>\<omega> :: 'n pairpath. norm (fst (\<omega> r) :: real^'n))"
  proof -
    interpret MQ0: martingale Q ?FQ "0::real"
      "\<lambda>u \<omega>. fst (\<omega> (min u r)) :: real^'n" by (rule mQ0)
    have "integrable Q (\<lambda>\<omega>. fst (\<omega> (min r r)) :: real^'n)"
      by (rule MQ0.integrable[OF r])
    then show ?thesis by simp
  qed
  have cQ: "martingale Q (\<lambda>u. ?FQ (min u r)) 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (min u r)) :: real^'n) - snd (\<omega> (min u r)))"
  proof (rule martingale_cong_ge[OF martingale_time_change
        [OF exit_class_compensated_martingale[OF Q] s1_0 s1_mono]])
    fix u :: real assume "0 \<le> u"
    show "(\<lambda>\<omega> :: 'n pairpath. outerp (fst (\<omega> (min (min u r) r)) :: real^'n)
          - snd (\<omega> (min (min u r) r)))
        = (\<lambda>\<omega>. outerp (fst (\<omega> (min u r))) - snd (\<omega> (min u r)))" by simp
  qed

  \<comment> \<open>the second factor, per index\<close>
  have mZ: "martingale (RR j) (?GR j) 0
      (\<lambda>v \<omega>'. fst (\<omega>' (min v (T - r))) - fst (\<omega>' 0) :: real^'n)" for j
  proof -
    have "martingale (RR j) (?GR j) 0 (\<lambda>v \<omega>'.
        (fst (\<omega>' (min v (T - r))) :: real^'n)
          - (\<lambda>w \<omega>'. fst (\<omega>' (min w (T - r))) :: real^'n) 0 \<omega>')"
      by (rule martingale_sub_initial[OF exit_class_X_martingale[OF R]])
    then show ?thesis using TR by simp
  qed
  have mBj: "martingale ?S ?GS 0
      (\<lambda>u f. fst (f i (?t u)) - fst (f i 0) :: real^'n)" for i
    by (rule kglue_param_martingale[OF rT mZ PRj])
  have mCi: "martingale ?S ?GS 0
      (\<lambda>u f. outerp (fst (f i (?t u)) - fst (f i 0) :: real^'n)
          - (snd (f i (?t u)) - snd (f i 0)))" for i
    by (rule kglue_param_comp_martingale[OF rT R])
  have FSf: "filtered_measure ?S ?GS (0::real)"
  proof -
    interpret MS: martingale ?S ?GS "0::real"
      "\<lambda>u f. fst (f 0 (?t u)) - fst (f 0 0) :: real^'n" by (rule mBj)
    show ?thesis by unfold_locales
  qed
  have Dfroz: "martingale ?S ?GS 0 (\<lambda>u f.
      (outerp (fst (f i (?t u)) - fst (f i 0) :: real^'n)
          - (snd (f i (?t u)) - snd (f i 0)))
      + ((\<chi> p q. c $ p * (fst (f i (?t u)) - fst (f i 0)) $ q)
          + (\<chi> p q. (fst (f i (?t u)) - fst (f i 0)) $ p * c $ q)))"
    for i and c :: "real^'n"
    by (rule martingale_add[OF mCi martingale_bounded_linear_image
          [OF bounded_linear_cross_pair mBj]])

  \<comment> \<open>evaluation measurability on the product filtration\<close>
  have evQ: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). fst p b)
      \<in> borel_measurable (?FF u)" if "0 \<le> b" "b \<le> min u r" for b u
    by (rule measurable_compose[OF measurable_fst nat_filt_eval[OF that]])
  have Nidx: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). N (fst p))
      \<in> ?FF u \<rightarrow>\<^sub>M count_space UNIV" if u: "r \<le> u" for u
  proof -
    have "min u r = r" using u by simp
    then show ?thesis using measurable_compose[OF measurable_fst Nm] by simp
  qed
  have evK: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). snd p (N (fst p)) w)
      \<in> borel_measurable (?FF u)" if u: "r \<le> u" and w: "0 \<le> w" "w \<le> ?s u"
    for u w
  proof (rule measurable_compose_countable[OF _ Nidx[OF u]])
    fix j :: nat
    have "(\<lambda>f :: nat \<Rightarrow> 'n pairpath. f j) \<in> ?GS u \<rightarrow>\<^sub>M ?GR j (?s u)"
      by (rule measurable_component_singleton) simp
    from measurable_compose[OF measurable_snd this]
    have "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). snd p j)
        \<in> ?FF u \<rightarrow>\<^sub>M ?GR j (?s u)" .
    from measurable_compose[OF this nat_filt_eval[OF w]]
    show "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). snd p j w)
        \<in> borel_measurable (?FF u)" .
  qed
  have crB: "(\<lambda>ab :: (real^'n) \<times> (real^'n).
      (\<chi> i j. fst ab $ i * snd ab $ j) + (\<chi> i j. snd ab $ i * fst ab $ j))
      \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_on_vec_lambda
        continuous_intros)
  have adapP: "?P1 u \<in> borel_measurable (?FF u)
      \<and> ?P2 u \<in> borel_measurable (?FF u)
      \<and> (\<lambda>p. 2 * norm (?Ap p) * norm (?bb u p)) \<in> borel_measurable (?FF u)"
    if u: "0 \<le> u" for u
  proof (cases "u \<le> r")
    case True
    then have z: "?t u = 0" using TR by simp
    have e1: "?P1 u = (\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). 0)"
      by (rule ext) (simp add: z outerp_zero)
    have e2: "?P2 u = (\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). 0)"
      by (rule ext) (simp add: z vec_eq_iff)
    have e3: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath).
        2 * norm (?Ap p) * norm (?bb u p)) = (\<lambda>p. 0)"
      by (rule ext) (simp add: z)
    show ?thesis unfolding e1 e2 e3 by simp
  next
    case False
    then have ru: "r \<le> u" by simp
    have k1: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath).
        snd p (N (fst p)) (?t u)) \<in> borel_measurable (?FF u)"
      by (rule evK[OF ru]) (use TR in auto)
    have k2: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath).
        snd p (N (fst p)) 0) \<in> borel_measurable (?FF u)"
      by (rule evK[OF ru]) auto
    have a0: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). fst p r)
        \<in> borel_measurable (?FF u)" by (rule evQ) (use r ru in auto)
    have mA: "?Ap \<in> borel_measurable (?FF u)"
      by (rule measurable_compose[OF a0 pair_fst_borel])
    have mb: "?bb u \<in> borel_measurable (?FF u)"
      using measurable_compose[OF k1 pair_fst_borel]
        measurable_compose[OF k2 pair_fst_borel]
      by (rule borel_measurable_diff)
    have my: "?YY u \<in> borel_measurable (?FF u)"
      using measurable_compose[OF k1 pair_snd_borel]
        measurable_compose[OF k2 pair_snd_borel]
      by (rule borel_measurable_diff)
    have m1: "?P1 u \<in> borel_measurable (?FF u)"
      using measurable_compose[OF mb outerp_borel] my
      by (rule borel_measurable_diff)
    have mp: "(\<lambda>p. (?Ap p, ?bb u p)) \<in> ?FF u \<rightarrow>\<^sub>M borel"
      using measurable_Pair[OF mA mb] by (simp add: borel_prod)
    have m2: "?P2 u \<in> borel_measurable (?FF u)"
      using measurable_compose[OF mp crB] by simp
    have m3: "(\<lambda>p. 2 * norm (?Ap p) * norm (?bb u p))
        \<in> borel_measurable (?FF u)" using mA mb by measurable
    show ?thesis using m1 m2 m3 by blast
  qed
  have adapD: "?D u \<in> borel_measurable (?FF u)" if u: "0 \<le> u" for u
    using adapP[OF u, THEN conjunct1]
      adapP[OF u, THEN conjunct2, THEN conjunct1]
    by (rule borel_measurable_add)
  have FPf: "filtered_measure ?M ?FF (0::real)"
    by (rule filtered_measure_pair[OF FQf FSf])
  have subM: "h \<in> borel_measurable ?M"
    if u: "0 \<le> u" and h: "h \<in> borel_measurable (?FF u)"
    for u :: real and h :: "'n pairpath \<times> (nat \<Rightarrow> 'n pairpath)
        \<Rightarrow> 'b::{banach,second_countable_topology}"
  proof -
    interpret FP: filtered_measure ?M ?FF "0::real" by (rule FPf)
    show ?thesis
      by (rule measurable_from_subalg[OF FP.subalgebras[OF u] h])
  qed

  \<comment> \<open>uniform bounds on the family, transferred to the product\<close>
  have mj: "(\<lambda>f :: nat \<Rightarrow> 'n pairpath. f j) \<in> ?S \<rightarrow>\<^sub>M RR j" for j
    by (rule measurable_component_singleton) simp
  have dj: "distr ?S (RR j) (\<lambda>f. f j) = RR j" for j
    by (rule distr_PiM_component) (rule PRj, simp)
  have tI: "?t u \<in> {0..T - r}" for u using TR by auto
  have zI: "(0::real) \<in> {0..T - r}" using TR by simp
  have startj: "AE \<omega>' in RR j. fst (\<omega>' 0) = (0::real^'n) \<and> snd (\<omega>' 0) = 0" for j
    using R unfolding exit_class_def by blast
  have evR: "(\<lambda>\<omega>' :: 'n pairpath. \<omega>' v) \<in> borel_measurable (RR j)" for j v
    by (rule pair_law_eval_measurable[OF setsR])
  have iCS: "integrable ?S (\<lambda>f. outerp (fst (f j (?t u)) - fst (f j 0) :: real^'n)
      - (snd (f j (?t u)) - snd (f j 0)))" if u: "0 \<le> u" for j u
  proof -
    interpret MC: martingale ?S ?GS "0::real"
      "\<lambda>u f. outerp (fst (f j (?t u)) - fst (f j 0) :: real^'n)
          - (snd (f j (?t u)) - snd (f j 0))" by (rule mCi)
    show ?thesis by (rule MC.integrable[OF u])
  qed
  have iBS: "integrable ?S (\<lambda>f. fst (f j (?t u)) - fst (f j 0) :: real^'n)"
    if u: "0 \<le> u" for j u
  proof -
    interpret MB: martingale ?S ?GS "0::real"
      "\<lambda>u f. fst (f j (?t u)) - fst (f j 0) :: real^'n" by (rule mBj)
    show ?thesis by (rule MB.integrable[OF u])
  qed
  have bCS: "(\<integral>f. norm (outerp (fst (f j (?t u)) - fst (f j 0) :: real^'n)
      - (snd (f j (?t u)) - snd (f j 0))) \<partial>?S) \<le> KK" if u: "0 \<le> u" for j u
  proof -
    have h1: "(\<lambda>\<omega>' :: 'n pairpath.
        norm (outerp (fst (\<omega>' (?t u)) - fst (\<omega>' 0) :: real^'n)
          - (snd (\<omega>' (?t u)) - snd (\<omega>' 0)))) \<in> borel_measurable (RR j)"
      using measurable_compose[OF evR pair_fst_borel]
        measurable_compose[OF evR pair_snd_borel] outerp_borel by measurable
    have h2: "(\<lambda>\<omega>' :: 'n pairpath.
        norm (outerp (fst (\<omega>' (?t u)) :: real^'n) - snd (\<omega>' (?t u))))
        \<in> borel_measurable (RR j)"
      using measurable_compose[OF evR pair_fst_borel]
        measurable_compose[OF evR pair_snd_borel] outerp_borel by measurable
    have "(\<integral>f. norm (outerp (fst (f j (?t u)) - fst (f j 0) :: real^'n)
          - (snd (f j (?t u)) - snd (f j 0))) \<partial>?S)
        = (\<integral>\<omega>'. norm (outerp (fst (\<omega>' (?t u)) - fst (\<omega>' 0) :: real^'n)
            - (snd (\<omega>' (?t u)) - snd (\<omega>' 0))) \<partial>(RR j))"
      by (rule integral_distr[OF mj h1, unfolded dj, symmetric])
    also have "\<dots> = (\<integral>\<omega>'. norm (outerp (fst (\<omega>' (?t u)) :: real^'n)
        - snd (\<omega>' (?t u))) \<partial>(RR j))"
      by (rule integral_cong_AE[OF h1 h2])
        (rule eventually_mono[OF startj], simp)
    also have "\<dots> \<le> KK" unfolding KK_def
      by (rule exit_class_comp_norm_mean_le[OF TR L0 R tI])
    finally show ?thesis .
  qed
  have hX: "(\<lambda>\<omega>' :: 'n pairpath. fst (\<omega>' v) :: real^'n)
      \<in> borel_measurable (RR j)" for j v
    by (rule measurable_compose[OF evR pair_fst_borel])
  have istep: "integrable ?S (\<lambda>f. fst (f j v) :: real^'n)"
    if v: "v \<in> {0..T - r}" for j v
  proof -
    have "integrable (distr ?S (RR j) (\<lambda>f. f j)) (\<lambda>\<omega>'. fst (\<omega>' v) :: real^'n)"
      unfolding dj
    proof -
      interpret MJ: martingale "RR j" "?GR j" "0::real"
        "\<lambda>w \<omega>'. fst (\<omega>' (min w (T - r))) :: real^'n"
        by (rule exit_class_X_martingale[OF R])
      have "integrable (RR j) (\<lambda>\<omega>'. fst (\<omega>' (min v (T - r))) :: real^'n)"
        using MJ.integrable[of v] v by simp
      then show "integrable (RR j) (\<lambda>\<omega>'. fst (\<omega>' v) :: real^'n)"
        using v by simp
    qed
    then show ?thesis using integrable_distr_eq[OF mj hX] by simp
  qed
  have bstep: "(\<integral>f. norm (fst (f j v) :: real^'n) \<partial>?S) \<le> C"
    if v: "v \<in> {0..T - r}" for j v
  proof -
    have hn: "(\<lambda>\<omega>' :: 'n pairpath. norm (fst (\<omega>' v) :: real^'n))
        \<in> borel_measurable (RR j)" using hX by measurable
    have "(\<integral>f. norm (fst (f j v) :: real^'n) \<partial>?S)
        = (\<integral>\<omega>'. norm (fst (\<omega>' v) :: real^'n) \<partial>(RR j))"
      by (rule integral_distr[OF mj hn, unfolded dj, symmetric])
    also have "\<dots> \<le> C" unfolding C_def
      by (rule exit_class_norm_mean_le[OF TR L0 R v])
    finally show ?thesis .
  qed
  have bBS: "(\<integral>f. norm (fst (f j (?t u)) - fst (f j 0) :: real^'n) \<partial>?S)
      \<le> 2 * C" if u: "0 \<le> u" for j u
  proof -
    have i1: "integrable ?S (\<lambda>f. norm (fst (f j (?t u)) :: real^'n))"
      by (rule integrable_norm[OF istep[OF tI]])
    have i2: "integrable ?S (\<lambda>f. norm (fst (f j 0) :: real^'n))"
      by (rule integrable_norm[OF istep[OF zI]])
    have "(\<integral>f. norm (fst (f j (?t u)) - fst (f j 0) :: real^'n) \<partial>?S)
        \<le> (\<integral>f. norm (fst (f j (?t u)) :: real^'n)
            + norm (fst (f j 0) :: real^'n) \<partial>?S)"
      using integrable_norm[OF iBS[OF u]] i1 i2
      by (intro integral_mono) (auto simp: norm_triangle_ineq4)
    also have "\<dots> = (\<integral>f. norm (fst (f j (?t u)) :: real^'n) \<partial>?S)
        + (\<integral>f. norm (fst (f j 0) :: real^'n) \<partial>?S)" using i1 i2 by simp
    also have "\<dots> \<le> C + C"
    proof -
      have "(\<integral>f. norm (fst (f j (?t u)) :: real^'n) \<partial>?S) \<le> C"
        by (rule bstep[OF tI])
      moreover have "(\<integral>f. norm (fst (f j 0) :: real^'n) \<partial>?S) \<le> C"
        by (rule bstep[OF zI])
      ultimately show ?thesis by simp
    qed
    finally show ?thesis by simp
  qed
  have bBnn: "0 \<le> (\<integral>f. norm (fst (f j (?t u)) - fst (f j 0) :: real^'n) \<partial>?S)"
    for j u by (rule integral_nonneg_AE) simp

  \<comment> \<open>integrability of the two summands on the product\<close>
  have intP1: "integrable ?M (?P1 u)" if u: "0 \<le> u" for u
  proof (rule PS'.Fubini_integrable[OF subM[OF u adapP[OF u, THEN conjunct1]]])
    have meas: "(\<lambda>\<omega> :: 'n pairpath. (\<integral>f. norm (outerp
          (fst (f (N \<omega>) (?t u)) - fst (f (N \<omega>) 0) :: real^'n)
            - (snd (f (N \<omega>) (?t u)) - snd (f (N \<omega>) 0))) \<partial>?S))
        \<in> borel_measurable Q"
    proof (rule measurable_compose_countable
        [where f = "\<lambda>j (_ :: 'n pairpath). (\<integral>f. norm (outerp
            (fst (f j (?t u)) - fst (f j 0) :: real^'n)
              - (snd (f j (?t u)) - snd (f j 0))) \<partial>?S)"])
      show "(\<lambda>_ :: 'n pairpath. (\<integral>f. norm (outerp
          (fst (f j (?t u)) - fst (f j 0) :: real^'n)
            - (snd (f j (?t u)) - snd (f j 0))) \<partial>?S))
          \<in> borel_measurable Q" for j by simp
      show "N \<in> Q \<rightarrow>\<^sub>M count_space UNIV" by (rule NmQ)
    qed
    have e: "(\<lambda>\<omega> :: 'n pairpath. \<integral>f. norm (?P1 u (\<omega>, f)) \<partial>?S)
        = (\<lambda>\<omega>. \<integral>f. norm (outerp
            (fst (f (N \<omega>) (?t u)) - fst (f (N \<omega>) 0) :: real^'n)
              - (snd (f (N \<omega>) (?t u)) - snd (f (N \<omega>) 0))) \<partial>?S)" by simp
    show "integrable Q (\<lambda>\<omega>. \<integral>f. norm (?P1 u (\<omega>, f)) \<partial>?S)"
      unfolding e
    proof (rule PQi.integrable_const_bound[where B = KK])
      show "AE \<omega> in Q. norm (\<integral>f. norm (outerp
          (fst (f (N \<omega>) (?t u)) - fst (f (N \<omega>) 0) :: real^'n)
            - (snd (f (N \<omega>) (?t u)) - snd (f (N \<omega>) 0))) \<partial>?S) \<le> KK"
      proof (intro AE_I2)
        fix \<omega> :: "'n pairpath"
        have nn: "0 \<le> (\<integral>f. norm (outerp
            (fst (f (N \<omega>) (?t u)) - fst (f (N \<omega>) 0) :: real^'n)
              - (snd (f (N \<omega>) (?t u)) - snd (f (N \<omega>) 0))) \<partial>?S)"
          by (rule integral_nonneg_AE) simp
        show "norm (\<integral>f. norm (outerp
            (fst (f (N \<omega>) (?t u)) - fst (f (N \<omega>) 0) :: real^'n)
              - (snd (f (N \<omega>) (?t u)) - snd (f (N \<omega>) 0))) \<partial>?S) \<le> KK"
          using nn bCS[OF u, of "N \<omega>"] by simp
      qed
    qed (rule meas)
    show "AE \<omega> in Q. integrable ?S (\<lambda>f. ?P1 u (\<omega>, f))"
      using iCS[OF u] by simp
  qed
  have intG: "integrable ?M (\<lambda>p. 2 * norm (?Ap p) * norm (?bb u p))"
    if u: "0 \<le> u" for u
  proof (rule PS'.Fubini_integrable
      [OF subM[OF u adapP[OF u, THEN conjunct2, THEN conjunct2]]])
    have pull: "(\<integral>f. 2 * norm (fst (\<omega> r) :: real^'n)
          * norm (fst (f (N \<omega>) (?t u)) - fst (f (N \<omega>) 0) :: real^'n) \<partial>?S)
        = 2 * norm (fst (\<omega> r) :: real^'n)
          * (\<integral>f. norm (fst (f (N \<omega>) (?t u)) - fst (f (N \<omega>) 0)
              :: real^'n) \<partial>?S)" for \<omega> :: "'n pairpath" by simp
    have meas: "(\<lambda>\<omega> :: 'n pairpath. 2 * norm (fst (\<omega> r) :: real^'n)
          * (\<integral>f. norm (fst (f (N \<omega>) (?t u)) - fst (f (N \<omega>) 0)
              :: real^'n) \<partial>?S)) \<in> borel_measurable Q"
    proof -
      have m1: "(\<lambda>\<omega> :: 'n pairpath. norm (fst (\<omega> r) :: real^'n))
          \<in> borel_measurable Q" using iAQ by (rule borel_measurable_integrable)
      have m2: "(\<lambda>\<omega> :: 'n pairpath. (\<integral>f. norm (fst (f (N \<omega>) (?t u))
            - fst (f (N \<omega>) 0) :: real^'n) \<partial>?S)) \<in> borel_measurable Q"
      proof (rule measurable_compose_countable
          [where f = "\<lambda>j (_ :: 'n pairpath). (\<integral>f. norm (fst (f j (?t u))
              - fst (f j 0) :: real^'n) \<partial>?S)"])
        show "(\<lambda>_ :: 'n pairpath. (\<integral>f. norm (fst (f j (?t u))
            - fst (f j 0) :: real^'n) \<partial>?S)) \<in> borel_measurable Q" for j
          by simp
        show "N \<in> Q \<rightarrow>\<^sub>M count_space UNIV" by (rule NmQ)
      qed
      show ?thesis using m1 m2 by measurable
    qed
    show "integrable Q (\<lambda>\<omega>. \<integral>f. norm (2 * norm (?Ap (\<omega>, f))
        * norm (?bb u (\<omega>, f))) \<partial>?S)"
    proof (rule Bochner_Integration.integrable_bound
        [where f = "\<lambda>\<omega> :: 'n pairpath. 4 * C * norm (fst (\<omega> r) :: real^'n)"])
      show "integrable Q (\<lambda>\<omega> :: 'n pairpath.
          4 * C * norm (fst (\<omega> r) :: real^'n))" using iAQ by simp
      show "(\<lambda>\<omega>. \<integral>f. norm (2 * norm (?Ap (\<omega>, f))
          * norm (?bb u (\<omega>, f))) \<partial>?S) \<in> borel_measurable Q"
        using meas by simp
      show "AE \<omega> in Q. norm (\<integral>f. norm (2 * norm (?Ap (\<omega>, f))
          * norm (?bb u (\<omega>, f))) \<partial>?S)
          \<le> norm (4 * C * norm (fst (\<omega> r) :: real^'n))"
      proof (intro AE_I2)
        fix \<omega> :: "'n pairpath"
        have "(\<integral>f. norm (2 * norm (fst (\<omega> r) :: real^'n)
              * norm (fst (f (N \<omega>) (?t u)) - fst (f (N \<omega>) 0) :: real^'n)) \<partial>?S)
            = 2 * norm (fst (\<omega> r) :: real^'n)
              * (\<integral>f. norm (fst (f (N \<omega>) (?t u)) - fst (f (N \<omega>) 0)
                  :: real^'n) \<partial>?S)" by simp
        moreover have "2 * norm (fst (\<omega> r) :: real^'n)
              * (\<integral>f. norm (fst (f (N \<omega>) (?t u)) - fst (f (N \<omega>) 0)
                  :: real^'n) \<partial>?S)
            \<le> 2 * norm (fst (\<omega> r) :: real^'n) * (2 * C)"
          using bBS[OF u, of "N \<omega>"] by (intro mult_left_mono) auto
        moreover have "0 \<le> 2 * norm (fst (\<omega> r) :: real^'n)
              * (\<integral>f. norm (fst (f (N \<omega>) (?t u)) - fst (f (N \<omega>) 0)
                  :: real^'n) \<partial>?S)"
          using bBnn[of "N \<omega>" u] by simp
        ultimately show "norm (\<integral>f. norm (2 * norm (?Ap (\<omega>, f))
            * norm (?bb u (\<omega>, f))) \<partial>?S)
            \<le> norm (4 * C * norm (fst (\<omega> r) :: real^'n))"
          using Cnn by simp
      qed
    qed
    show "AE \<omega> in Q. integrable ?S
        (\<lambda>f. 2 * norm (?Ap (\<omega>, f)) * norm (?bb u (\<omega>, f)))"
      using integrable_norm[OF iBS[OF u]] by simp
  qed
  have intD: "integrable ?M (?D u)" if u: "0 \<le> u" for u
  proof -
    have iP2: "integrable ?M (?P2 u)"
    proof (rule Bochner_Integration.integrable_bound[OF intG[OF u]])
      show "?P2 u \<in> borel_measurable ?M"
        by (rule subM[OF u adapP[OF u, THEN conjunct2, THEN conjunct1]])
      show "AE p in ?M. norm (?P2 u p)
          \<le> norm (2 * norm (?Ap p) * norm (?bb u p))"
      proof (intro AE_I2)
        fix p :: "'n pairpath \<times> (nat \<Rightarrow> 'n pairpath)"
        have key: "norm ((\<chi> i j. a $ i * b $ j) + (\<chi> i j. b $ i * a $ j))
            \<le> norm (2 * norm a * norm b)" for a b :: "real^'n"
        proof -
          have "norm ((\<chi> i j. a $ i * b $ j) + (\<chi> i j. b $ i * a $ j))
              \<le> norm (\<chi> i j. a $ i * b $ j) + norm (\<chi> i j. b $ i * a $ j)"
            by (rule norm_triangle_ineq)
          also have "\<dots> = 2 * norm a * norm b"
          proof -
            have n1: "norm (\<chi> i j. a $ i * b $ j) = norm a * norm b"
              using norm_outer_prod[of a b] by (simp add: outer_prod_def)
            have n2: "norm (\<chi> i j. b $ i * a $ j) = norm b * norm a"
              using norm_outer_prod[of b a] by (simp add: outer_prod_def)
            show ?thesis unfolding n1 n2 by simp
          qed
          finally show ?thesis by simp
        qed
        show "norm (?P2 u p)
            \<le> norm (2 * norm (?Ap p) * norm (?bb u p))" by (rule key)
      qed
    qed
    show ?thesis using intP1[OF u] iP2 by simp
  qed
  have mD: "martingale ?M ?FF 0 ?D"
  proof (rule martingale_pair_snd_param[OF PQ PS FQf FSf adapD intD])
    fix \<omega> :: "'n pairpath" assume "\<omega> \<in> space Q"
    show "martingale ?S ?GS 0 (\<lambda>u f. ?D u (\<omega>, f))"
      using Dfroz[of "N \<omega>" "fst (\<omega> r)"] by simp
  qed
  have mCQ: "martingale ?M ?FF 0
      (\<lambda>u p. outerp (fst (fst p (min u r)) :: real^'n) - snd (fst p (min u r)))"
    by (rule martingale_pair_fst[OF PQ PS cQ FSf])
  have mgl: "martingale ?M ?FF 0
      (\<lambda>u p. outerp (fst (kglue r T N p (min u T)) :: real^'n)
          - snd (kglue r T N p (min u T)))"
  proof (rule martingale_cong_ge[OF martingale_add[OF mCQ mD]])
    fix u :: real assume u: "0 \<le> u"
    have muI: "min u T \<in> {0..T}" using u T0 by simp
    show "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath).
          (outerp (fst (fst p (min u r)) :: real^'n) - snd (fst p (min u r)))
            + ?D u p)
        = (\<lambda>p. outerp (fst (kglue r T N p (min u T)) :: real^'n)
            - snd (kglue r T N p (min u T)))"
    proof (rule ext)
      fix p :: "'n pairpath \<times> (nat \<Rightarrow> 'n pairpath)"
      show "(outerp (fst (fst p (min u r)) :: real^'n) - snd (fst p (min u r)))
            + ?D u p
          = outerp (fst (kglue r T N p (min u T)) :: real^'n)
            - snd (kglue r T N p (min u T))"
      proof (cases "u \<le> r")
        case True
        then have uT: "u \<le> T" using rT by simp
        then have le: "min u T \<le> r" using True by simp
        have e1: "min u T = min u r" using True uT by simp
        have e2: "?t u = 0" using True TR by simp
        have g0: "kglue r T N p (min u T) = fst p (min u r)"
          unfolding kglue_def e1[symmetric]
          by (simp add: pglue_le[OF muI le])
        show ?thesis by (simp add: g0 e2 outerp_zero vec_eq_iff)
      next
        case False
        then have ru: "r < u" by simp
        have rv: "r \<le> min u T" using ru rT by simp
        have e1: "min u r = r" using ru by simp
        have e2: "?t u = min u T - r" using ru by (simp add: min_def)
        have g0: "kglue r T N p (min u T)
            = fst p r + (snd p (N (fst p)) (min u T - r)
                - snd p (N (fst p)) 0)"
          unfolding kglue_def by (simp add: pglue_ge[OF muI rv])
        have gX: "fst (kglue r T N p (min u T)) = ?Ap p + ?bb u p"
          by (simp add: g0 e2)
        have gY: "snd (kglue r T N p (min u T)) = snd (fst p r) + ?YY u p"
          by (simp add: g0 e2)
        have "outerp (fst (kglue r T N p (min u T)) :: real^'n)
              - snd (kglue r T N p (min u T))
            = (outerp (?Ap p) + outerp (?bb u p)
                + ((\<chi> i j. ?Ap p $ i * ?bb u p $ j)
                    + (\<chi> i j. ?bb u p $ i * ?Ap p $ j)))
              - (snd (fst p r) + ?YY u p)"
          unfolding gX gY by (simp only: outerp_add)
        also have "\<dots> = (outerp (?Ap p) - snd (fst p r)) + ?D u p"
          by (simp add: algebra_simps)
        finally show ?thesis using e1 by simp
      qed
    qed
  qed

  \<comment> \<open>transport to the pasted law\<close>
  have gadap: "(\<lambda>p. kglue r T N p v) \<in> borel_measurable (?FF u)"
    if v: "0 \<le> v" and vu: "v \<le> u" for u v
  proof (cases "v \<le> T")
    case False
    then have "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). kglue r T N p v)
        = (\<lambda>p. undefined)" by (auto simp: kglue_def pglue_def)
    then show ?thesis by simp
  next
    case True
    then have vI: "v \<in> {0..T}" using v by simp
    show ?thesis
    proof (cases "v \<le> r")
      case True
      then have "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). kglue r T N p v)
          = (\<lambda>p. fst p v)" by (simp add: kglue_def pglue_le[OF vI])
      then show ?thesis using evQ[of v u] v vu True by simp
    next
      case False
      then have rv: "r \<le> v" by simp
      have ru: "r \<le> u" using rv vu by simp
      have e: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). kglue r T N p v)
          = (\<lambda>p. fst p r + (snd p (N (fst p)) (v - r)
              - snd p (N (fst p)) 0))"
        by (simp add: kglue_def pglue_ge[OF vI rv])
      have m1: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). fst p r)
          \<in> borel_measurable (?FF u)" by (rule evQ) (use r ru in auto)
      have m2: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath).
          snd p (N (fst p)) (v - r)) \<in> borel_measurable (?FF u)"
        by (rule evK[OF ru]) (use rv vu in auto)
      have m3: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath).
          snd p (N (fst p)) 0) \<in> borel_measurable (?FF u)"
        by (rule evK[OF ru]) auto
      show ?thesis unfolding e using m1 m2 m3 by simp
    qed
  qed
  have Zm: "(\<lambda>\<omega> :: 'n pairpath. outerp (fst (\<omega> (min u T)) :: real^'n)
        - snd (\<omega> (min u T)))
      \<in> borel_measurable (natural_filtration (kglue_law r T N Q RR) 0
          (\<lambda>v \<omega>. \<omega> v) u)" if u: "0 \<le> u" for u
  proof -
    have "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u T))
        \<in> natural_filtration (kglue_law r T N Q RR) 0 (\<lambda>v \<omega>. \<omega> v) u
          \<rightarrow>\<^sub>M borel"
      by (rule nat_filt_eval) (use u T0 in auto)
    then show ?thesis by (rule measurable_compose[OF _ cB])
  qed
  show ?thesis
    unfolding kglue_law_def
    by (rule martingale_pair_law[OF prob_space_pair_measure[OF PQ PS]
        kglue_measurable[OF r rT setsQ setsR NmQ] gadap
        Zm[unfolded kglue_law_def] mgl])
qed

text \<open>The class is closed under concatenation with a continuation chosen by
  the endpoint along any countable past-measurable selector --- what
  Prop. 2.4's \<open>\<ge>\<close> inequality needs beyond \<open>exit_class_pglue_law\<close>:
  with an \<open>\<epsilon>\<close>-optimal continuation attached to each cell of a countable
  Borel partition of \<open>X(r)\<close>, the pasted law realises \<open>r + v(X(r))\<close> up to
  \<open>\<epsilon>\<close>.\<close>

theorem exit_class_kglue_law:
  fixes Q :: "('n::finite pairpath) measure"
    and RR :: "nat \<Rightarrow> ('n pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T" and L0: "0 \<le> L"
    and Q: "Q \<in> exit_class k L r x"
    and R: "\<And>j. RR j \<in> exit_class k L (T - r) 0"
    and Nm: "N \<in> natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v) r \<rightarrow>\<^sub>M count_space UNIV"
  shows "kglue_law r T N Q RR \<in> exit_class k L T x"
proof -
  have NmQ: "N \<in> Q \<rightarrow>\<^sub>M count_space UNIV"
  proof -
    interpret MQ0: martingale Q "natural_filtration Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
      "0::real" "\<lambda>u \<omega>. fst (\<omega> (min u r)) :: real^'n"
      by (rule exit_class_X_martingale[OF Q])
    show ?thesis
      by (rule measurable_from_subalg[OF MQ0.subalgebras[OF r] Nm])
  qed
  show ?thesis
    unfolding exit_class_def mem_Collect_eq
  proof (intro conjI)
    show "prob_space (kglue_law r T N Q RR)"
      by (rule prob_space_kglue_law[OF r rT exit_class_prob[OF Q]
            exit_class_prob[OF R] exit_class_sets[OF Q]
            exit_class_sets[OF R] NmQ])
    show "sets (kglue_law r T N Q RR)
        = sets (path_borel T :: ('n pairpath) measure)" by (rule sets_kglue_law)
    show "AE \<omega> in kglue_law r T N Q RR. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
      by (rule kglue_law_start[OF r rT Q R NmQ])
    show "AE \<omega> in kglue_law r T N Q RR. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
      by (rule kglue_law_diffquot[OF r rT Q R NmQ])
    show "martingale (kglue_law r T N Q RR)
        (natural_filtration (kglue_law r T N Q RR) 0 (\<lambda>v \<omega>. \<omega> v)) 0
        (\<lambda>u \<omega>. fst (\<omega> (min u T)) :: real^'n)"
      by (rule kglue_law_X_martingale[OF r rT L0 Q R Nm])
    show "martingale (kglue_law r T N Q RR)
        (natural_filtration (kglue_law r T N Q RR) 0 (\<lambda>v \<omega>. \<omega> v)) 0
        (\<lambda>u \<omega>. outerp (fst (\<omega> (min u T)) :: real^'n) - snd (\<omega> (min u T)))"
      by (rule kglue_law_comp_martingale[OF r rT L0 Q R Nm])
  qed
qed


(*<*)
end
(*>*)
