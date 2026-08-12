section \<open>The class and the value function on the half-line\<close>

(*<*)
theory Exit_Class_Infinite
  imports Exit_Class_DPP "Path_Space_Tightness.Path_Space_Infinite"
begin
(*>*)

text \<open>Eq. (1.6)--(1.7) of arXiv:2512.17702 without the horizon cap: the class
  is a set of laws on the paths of @{theory Path_Space_Tightness.Path_Space_Infinite},
  the covariation constraint is required at every pair of times, and the
  martingale clauses carry no stopping.  The capped development is reached
  through the restriction of a law to a compact horizon.\<close>

subsection \<open>The uncapped exit time\<close>

text \<open>The exit time from \<open>K\<close> is the increasing limit of the capped exit times.
  It takes the value \<open>\<top>\<close> exactly on the paths that never leave \<open>K\<close>.\<close>

definition iexit :: "'b::polish_space set \<Rightarrow> (real \<Rightarrow> 'b) \<Rightarrow> ennreal" where
  "iexit K f = (SUP T \<in> {0..}. ennreal (pexit T K f))"

lemma pexit_le_iexit:
  assumes T: "0 \<le> T"
  shows "ennreal (pexit T K f) \<le> iexit K f"
  unfolding iexit_def using T by (intro SUP_upper) simp

text \<open>Capping the uncapped exit time returns the capped one.  This is the
  pathwise form of the statement that the horizon is a device: everything the
  capped development says about \<open>pexit T\<close> is a statement about \<open>iexit\<close> below
  the level \<open>T\<close>.\<close>

theorem iexit_cap:
  assumes T: "0 \<le> T"
  shows "min (iexit K f) (ennreal T) = ennreal (pexit T K f)"
proof (cases "iexit K f \<le> ennreal T")
  case True
  have eq: "pexit S K f = pexit T K f" if S: "T \<le> S" for S
  proof -
    have S0: "0 \<le> S" using T S by simp
    have "ennreal (pexit S K f) \<le> ennreal T"
      using True pexit_le_iexit[OF S0, of K f] by simp
    then have "pexit S K f \<le> T" using T by simp
    moreover have "pexit T K f = min (pexit S K f) T"
      by (rule pexit_min_horizon[OF T S])
    ultimately show ?thesis by simp
  qed
  have "iexit K f = ennreal (pexit T K f)"
    unfolding iexit_def
  proof (rule antisym)
    show "(SUP S\<in>{0..}. ennreal (pexit S K f)) \<le> ennreal (pexit T K f)"
    proof (rule SUP_least)
      fix S :: real assume "S \<in> {0..}"
      then have S0: "0 \<le> S" by simp
      show "ennreal (pexit S K f) \<le> ennreal (pexit T K f)"
      proof (cases "T \<le> S")
        case True
        then have "pexit S K f = pexit T K f" by (rule eq)
        then show ?thesis by simp
      next
        case False
        then have "pexit S K f = min (pexit T K f) S"
          by (intro pexit_min_horizon[OF S0]) simp
        then show ?thesis by (simp add: ennreal_leI)
      qed
    qed
    show "ennreal (pexit T K f) \<le> (SUP S\<in>{0..}. ennreal (pexit S K f))"
      using T by (intro SUP_upper) simp
  qed
  with True show ?thesis by simp
next
  case False
  then have gt: "ennreal T < iexit K f" by simp
  obtain S where S0: "0 \<le> S" and Sgt: "ennreal T < ennreal (pexit S K f)"
    using gt unfolding iexit_def by (auto simp: less_SUP_iff)
  have pS: "0 \<le> pexit S K f" by (rule pexit_nonneg[OF S0])
  have TltS: "T < pexit S K f"
    using Sgt pS T by (simp add: ennreal_less_iff)
  have TS: "T \<le> S" using TltS pexit_le_T[OF S0, of K f] by simp
  have "pexit T K f = min (pexit S K f) T"
    by (rule pexit_min_horizon[OF T TS])
  then have pT: "pexit T K f = T" using TltS by simp
  have "min (iexit K f) (ennreal T) = ennreal T"
    using gt by (simp add: min_absorb2 order_less_imp_le)
  then show ?thesis using pT by simp
qed

text \<open>Hence the elementary bound identifying \<open>iexit\<close> as the first time the
  path is outside \<open>K\<close>.\<close>

lemma iexit_le:
  assumes r: "0 \<le> r" and out: "f r \<notin> K"
  shows "iexit K f \<le> ennreal r"
proof -
  have r1: "0 \<le> r + 1" using r by simp
  have "pexit (r + 1) K f \<le> r"
    unfolding pexit_def etime_def using r out by (intro cInf_lower) auto
  then have "ennreal (pexit (r + 1) K f) \<le> ennreal r" by (simp add: ennreal_leI)
  also have "ennreal r < ennreal (r + 1)" using r by (simp add: ennreal_less_iff)
  finally have lt: "min (iexit K f) (ennreal (r + 1)) < ennreal (r + 1)"
    using iexit_cap[OF r1, of K f] by simp
  then have "min (iexit K f) (ennreal (r + 1)) = iexit K f"
    by (simp add: min_def split: if_splits)
  then show ?thesis
    using iexit_cap[OF r1, of K f] \<open>ennreal (pexit (r + 1) K f) \<le> ennreal r\<close>
    by simp
qed

subsection \<open>The essential infimum of an unbounded time\<close>

definition ess_inf_enn :: "'a measure \<Rightarrow> ('a \<Rightarrow> ennreal) \<Rightarrow> ennreal" where
  "ess_inf_enn M tau = Sup {c. AE \<omega> in M. c \<le> tau \<omega>}"

lemma ess_inf_enn_ge_zero: "0 \<le> ess_inf_enn M tau"
  by simp

lemma ess_inf_ennI:
  assumes "AE \<omega> in M. c \<le> tau \<omega>"
  shows "c \<le> ess_inf_enn M tau"
  unfolding ess_inf_enn_def using assms by (intro Sup_upper) simp

lemma ess_inf_enn_mono:
  assumes "AE \<omega> in M. tau \<omega> \<le> tau' \<omega>"
  shows "ess_inf_enn M tau \<le> ess_inf_enn M tau'"
  unfolding ess_inf_enn_def
proof (rule Sup_least)
  fix c assume "c \<in> {c. AE \<omega> in M. c \<le> tau \<omega>}"
  then have "AE \<omega> in M. c \<le> tau \<omega>" by simp
  with assms have "AE \<omega> in M. c \<le> tau' \<omega>" by eventually_elim simp
  then show "c \<le> \<Squnion> {c. AE \<omega> in M. c \<le> tau' \<omega>}"
    by (intro Sup_upper) simp
qed

lemma ess_inf_enn_AE: "AE \<omega> in M. ess_inf_enn M tau \<le> tau \<omega>"
proof -
  define S where "S = {c. AE \<omega> in M. c \<le> tau \<omega>}"
  have "0 \<in> S" unfolding S_def by simp
  then have ne: "S \<noteq> {}" by blast
  obtain f :: "nat \<Rightarrow> ennreal"
    where f: "range f \<subseteq> S" and sup: "Sup S = Sup (range f)"
    using ennreal_Sup_countable_SUP[OF ne] by blast
  have fS: "AE \<omega> in M. f n \<le> tau \<omega>" for n
    using f unfolding S_def by blast
  have "AE \<omega> in M. \<forall>n. f n \<le> tau \<omega>"
    using fS by (subst AE_all_countable) blast
  then have "AE \<omega> in M. Sup (range f) \<le> tau \<omega>"
    by eventually_elim (auto intro: Sup_least)
  thus ?thesis unfolding ess_inf_enn_def S_def[symmetric] using sup by simp
qed

lemma ess_inf_enn_min_const:
  "min (ess_inf_enn M tau) c \<le> ess_inf_enn M (\<lambda>\<omega>. min (tau \<omega>) c)"
proof (rule ess_inf_ennI)
  have "AE \<omega> in M. ess_inf_enn M tau \<le> tau \<omega>" by (rule ess_inf_enn_AE)
  then show "AE \<omega> in M. min (ess_inf_enn M tau) c \<le> min (tau \<omega>) c"
  proof eventually_elim
    case (elim \<omega>)
    then show ?case by (rule min.mono[OF _ order_refl])
  qed
qed

lemma ess_inf_enn_ennreal:
  "ess_inf_enn M (\<lambda>\<omega>. ennreal (tau \<omega>)) = ess_inf_time M tau"
  unfolding ess_inf_enn_def ess_inf_time_def by simp

subsection \<open>The class of Eq. (1.7)\<close>

definition iexit_class ::
  "nat \<Rightarrow> real \<Rightarrow> real^'n::finite \<Rightarrow> (('n pairpath) measure) set"
  where
  "iexit_class k L x = {P.
     prob_space P \<and>
     sets P = sets (ipath_space :: ('n pairpath) measure) \<and>
     (AE \<omega> in P. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0) \<and>
     (AE \<omega> in P. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L) \<and>
     martingale P (natural_filtration P 0 (\<lambda>t \<omega>. \<omega> t)) 0
       (\<lambda>t \<omega>. fst (\<omega> t)) \<and>
     martingale P (natural_filtration P 0 (\<lambda>t \<omega>. \<omega> t)) 0
       (\<lambda>t \<omega>. outerp (fst (\<omega> t)) - snd (\<omega> t))}"

definition iexit_val ::
  "nat \<Rightarrow> real \<Rightarrow> (real^'n::finite) set \<Rightarrow> real^'n \<Rightarrow> ennreal"
  where
  "iexit_val k L K x =
     Sup ((\<lambda>Q. ess_inf_enn Q (\<lambda>\<omega>. iexit K (\<lambda>t. fst (\<omega> t)))) ` iexit_class k L x)"

lemma iexit_class_prob:
  "P \<in> iexit_class k L x \<Longrightarrow> prob_space P"
  unfolding iexit_class_def by blast

lemma iexit_class_sets:
  "P \<in> iexit_class k L x \<Longrightarrow> sets P = sets (ipath_space :: ('n::finite pairpath) measure)"
  unfolding iexit_class_def by blast

lemma iexit_class_start:
  "P \<in> iexit_class k L x \<Longrightarrow> AE \<omega> in P. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
  unfolding iexit_class_def by blast

subsection \<open>Restriction to a compact horizon\<close>

text \<open>The cut of a law on the half-line is a law on the horizon-\<open>S\<close> path
  space.  @{thm [source] pcut_adapted} needs nothing of the underlying space,
  so the adaptedness of the cut coordinates carries over unchanged.\<close>

lemma ipcut_measurable:
  fixes P :: "('n::finite pairpath) measure"
  assumes S: "0 \<le> S"
    and setsP: "sets P = sets (ipath_space :: ('n pairpath) measure)"
  shows "pcut S \<in> P \<rightarrow>\<^sub>M borel_of (mtopology_of
      (path_metric S :: ('n pairpath) metric))"
  unfolding pcut_def measurable_cong_sets[OF setsP refl]
  by (rule restrict_ipath_measurable[OF S])

lemma iexit_class_pcut_measurable:
  assumes S: "0 \<le> S" and P: "P \<in> iexit_class k L x"
  shows "pcut S \<in> P \<rightarrow>\<^sub>M borel_of (mtopology_of
      (path_metric S :: ('n::finite pairpath) metric))"
  by (rule ipcut_measurable[OF S iexit_class_sets[OF P]])

lemma iexit_class_diffquot:
  "P \<in> iexit_class k L x \<Longrightarrow>
     AE \<omega> in P. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
       (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
  unfolding iexit_class_def by blast

lemma iexit_class_X_martingale:
  "P \<in> iexit_class k L x \<Longrightarrow>
     martingale P (natural_filtration P 0 (\<lambda>t \<omega>. \<omega> t)) 0
       (\<lambda>t \<omega>. fst (\<omega> t) :: real^'n::finite)"
  unfolding iexit_class_def by blast

lemma iexit_class_comp_martingale:
  "P \<in> iexit_class k L x \<Longrightarrow>
     martingale P (natural_filtration P 0 (\<lambda>t \<omega>. \<omega> t)) 0
       (\<lambda>t \<omega>. outerp (fst (\<omega> t) :: real^'n::finite) - snd (\<omega> t))"
  unfolding iexit_class_def by blast

text \<open>The cut of a member of the uncapped class is a member of the capped one.
  Every clause transfers along @{const pcut}; the covariation and martingale
  clauses are simpler here than in @{thm [source] exit_class_pcut}, since the
  uncapped class constrains every pair of times and stops nothing.\<close>

theorem iexit_class_pcut:
  fixes P :: "('n::finite pairpath) measure"
  assumes S: "0 \<le> S" and P: "P \<in> iexit_class k L x"
  shows "pair_law_of S (pcut S) P \<in> exit_class k L S x"
proof -
  let ?Q = "pair_law_of S (pcut S) P"
  let ?B = "borel_of (mtopology_of (path_metric S :: ('n pairpath) metric))"
  let ?F = "natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?G = "natural_filtration ?Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  interpret P: prob_space P by (rule iexit_class_prob[OF P])
  have phim: "pcut S \<in> P \<rightarrow>\<^sub>M ?B"
    by (rule ipcut_measurable[OF S iexit_class_sets[OF P]])
  have prob': "prob_space ?Q"
    unfolding pair_law_of_def by (rule P.prob_space_distr[OF phim])
  have adap: "(\<lambda>\<omega> :: 'n pairpath. pcut S \<omega> r) \<in> borel_measurable (?F u)"
    if "0 \<le> r" "r \<le> u" for r u
    by (rule pcut_adapted[OF S that])

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
        = (AE \<omega> in P. fst (pcut S \<omega> 0) = x \<and> snd (pcut S \<omega> 0) = 0)"
      unfolding pair_law_of_def by (rule AE_distr_iff[OF phim mset])
    have z: "(0::real) \<in> {0..S}" using S by simp
    have "AE \<omega> in P. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
      by (rule iexit_class_start[OF P])
    then have "AE \<omega> in P. fst (pcut S \<omega> 0) = x \<and> snd (pcut S \<omega> 0) = 0"
      by eventually_elim (simp add: pcut_apply[OF z])
    then show ?thesis unfolding iff .
  qed

  \<comment> \<open>clause (ii): the covariation constraint\<close>
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
        = (AE \<omega> in P. (1 / (q - p))
            *\<^sub>R (snd (pcut S \<omega> q) - snd (pcut S \<omega> p)) \<in> sconstraint k L)"
      unfolding pair_law_of_def by (rule AE_distr_iff[OF phim mm])
    have "AE \<omega> in P. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
      by (rule iexit_class_diffquot[OF P])
    then have "AE \<omega> in P. (1 / (q - p))
        *\<^sub>R (snd (pcut S \<omega> q) - snd (pcut S \<omega> p)) \<in> sconstraint k L"
    proof eventually_elim
      case (elim \<omega>)
      have "(1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
        using elim pq by auto
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
    show "martingale P ?F 0 (\<lambda>u \<omega>. fst (pcut S \<omega> (min u S)) :: real^'n)"
    proof (rule martingale_cong_ge
        [OF martingale_stopped_const[OF S iexit_class_X_martingale[OF P]]])
      fix u :: real assume u: "0 \<le> u"
      have mI: "min u S \<in> {0..S}" using u S by simp
      show "(\<lambda>\<omega>. fst (pcut S \<omega> (min u S)) :: real^'n)
          = (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min u S)))"
        by (rule ext) (simp add: pcut_apply[OF mI])
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
    show "martingale P ?F 0 (\<lambda>u \<omega>. outerp (fst (pcut S \<omega> (min u S)) :: real^'n)
        - snd (pcut S \<omega> (min u S)))"
    proof (rule martingale_cong_ge[OF martingale_stopped_const
          [OF S iexit_class_comp_martingale[OF P]]])
      fix u :: real assume u: "0 \<le> u"
      have mI: "min u S \<in> {0..S}" using u S by simp
      show "(\<lambda>\<omega>. outerp (fst (pcut S \<omega> (min u S)) :: real^'n)
              - snd (pcut S \<omega> (min u S)))
          = (\<lambda>\<omega> :: 'n pairpath. outerp (fst (\<omega> (min u S))) - snd (\<omega> (min u S)))"
        by (rule ext) (simp add: pcut_apply[OF mI])
    qed
  qed

  show ?thesis
    unfolding exit_class_def mem_Collect_eq
    using prob' sets_pair_law_of start' cov' mgX' mgC' by blast
qed

(*<*)
end
(*>*)
