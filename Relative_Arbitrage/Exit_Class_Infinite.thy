section \<open>The class and the value function on the half-line\<close>

(*<*)
theory Exit_Class_Infinite
  imports Dynamic_Programming_Assembly "Continuous_Path_Spaces.Path_Space_Infinite"
begin
(*>*)

text \<open>Eq. (1.6)--(1.7) of \<^cite>\<open>LaiShkolnikovSoner\<close> without the horizon cap: the class
  is a set of laws on the paths of @{theory Continuous_Path_Spaces.Path_Space_Infinite},
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

subsection \<open>The essential infimum of an unbounded time\<close>

definition ess_inf_enn :: "'a measure \<Rightarrow> ('a \<Rightarrow> ennreal) \<Rightarrow> ennreal" where
  "ess_inf_enn M tau = Sup {c. AE \<omega> in M. c \<le> tau \<omega>}"

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
  shows "pcut S \<in> P \<rightarrow>\<^sub>M (path_borel S :: ('n pairpath) measure)"
  unfolding pcut_def measurable_cong_sets[OF setsP refl]
  by (rule restrict_ipath_measurable[OF S])

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

text \<open>The class is a set of laws of the pair \<open>(X, \<langle>X\<rangle>)\<close>, and the martingale
  clauses above are stated for the natural filtration of that pair, which is a
  priori larger than the natural filtration of \<open>X\<close>.  The paper's own filtration
  is the one generated by the coordinate process \<open>X\<close>; the martingale property
  transfers to it by the tower property, so a member of the class does have \<open>X\<close>
  a martingale in the paper's sense, via \<open>martingale_coarser_filtration\<close> from
  @{theory Continuous_Time_Martingales.Martingale_Algebra}.\<close>

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
  let ?B = "(path_borel S :: ('n pairpath) measure)"
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
      show "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min u S)))
          = (\<lambda>\<omega>. fst (pcut S \<omega> (min u S)) :: real^'n)"
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
      show "(\<lambda>\<omega> :: 'n pairpath. outerp (fst (\<omega> (min u S))) - snd (\<omega> (min u S)))
          = (\<lambda>\<omega>. outerp (fst (pcut S \<omega> (min u S)) :: real^'n)
              - snd (pcut S \<omega> (min u S)))"
        by (rule ext) (simp add: pcut_apply[OF mI])
    qed
  qed

  show ?thesis
    unfolding exit_class_def mem_Collect_eq
    using prob' sets_pair_law_of start' cov' mgX' mgC' by blast
qed

subsection \<open>The capped value dominates the capped uncapped value\<close>

text \<open>Restricting a member of the uncapped class to \<open>[0,T]\<close> gives a competitor
  for @{const exit_val} whose exit time is the uncapped one capped at \<open>T\<close>.
  Hence \<open>min (v, T) \<le> v\<^sub>T\<close>, one half of the identification of the two value
  functions.\<close>

theorem iexit_val_cap_le:
  fixes K :: "(real^'n::finite) set"
  assumes T: "0 \<le> T" and Kc: "closed K"
  shows "min (iexit_val k L K x) (ennreal T) \<le> exit_val k L T K x"
proof -
  have step: "min (ess_inf_enn P (\<lambda>\<omega>. iexit K (\<lambda>t. fst (\<omega> t)))) (ennreal T)
      \<le> exit_val k L T K x"
    if P: "P \<in> iexit_class k L x" for P :: "('n pairpath) measure"
  proof -
    let ?Q = "pair_law_of T (pcut T) P"
    let ?B = "(path_borel T :: ('n pairpath) measure)"
    have Q: "?Q \<in> exit_class k L T x" by (rule iexit_class_pcut[OF T P])
    have phim: "pcut T \<in> P \<rightarrow>\<^sub>M ?B"
      by (rule ipcut_measurable[OF T iexit_class_sets[OF P]])
    have taum: "(\<lambda>\<omega> :: 'n pairpath. pexit T K (\<lambda>t. fst (\<omega> t)))
        \<in> borel_measurable ?B"
      by (rule pexit_path_measurable[OF T Kc refl])
    have "ess_inf_time ?Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))
        = ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (pcut T \<omega> t)))"
      unfolding pair_law_of_def
    proof (rule ess_inf_time_distr[OF phim])
      fix c :: ennreal
      show "{\<omega> \<in> space ?B. c \<le> ennreal (pexit T K (\<lambda>t. fst (\<omega> t)))} \<in> sets ?B"
        using taum by measurable
    qed
    also have "\<dots> = ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))"
      by (simp add: pexit_pcut)
    also have "\<dots> = ess_inf_enn P (\<lambda>\<omega>. ennreal (pexit T K (\<lambda>t. fst (\<omega> t))))"
      by (rule ess_inf_enn_ennreal[symmetric])
    also have "\<dots> = ess_inf_enn P
        (\<lambda>\<omega>. min (iexit K (\<lambda>t. fst (\<omega> t))) (ennreal T))"
      by (simp add: iexit_cap[OF T])
    finally have eq: "ess_inf_time ?Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))
        = ess_inf_enn P (\<lambda>\<omega>. min (iexit K (\<lambda>t. fst (\<omega> t))) (ennreal T))" .
    have "min (ess_inf_enn P (\<lambda>\<omega>. iexit K (\<lambda>t. fst (\<omega> t)))) (ennreal T)
        \<le> ess_inf_enn P (\<lambda>\<omega>. min (iexit K (\<lambda>t. fst (\<omega> t))) (ennreal T))"
      by (rule ess_inf_enn_min_const)
    also have "\<dots> = ess_inf_time ?Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))"
      using eq by simp
    also have "\<dots> \<le> exit_val k L T K x"
      unfolding exit_val_def using Q by (intro Sup_upper) blast
    finally show ?thesis .
  qed
  show ?thesis
  proof (cases "ennreal T \<le> exit_val k L T K x")
    case True
    then show ?thesis using min.cobounded2 order_trans by blast
  next
    case False
    then have lt: "exit_val k L T K x < ennreal T" by simp
    have "iexit_val k L K x \<le> exit_val k L T K x"
      unfolding iexit_val_def
    proof (rule Sup_least)
      fix v assume "v \<in> (\<lambda>Q. ess_inf_enn Q (\<lambda>\<omega>. iexit K (\<lambda>t. fst (\<omega> t))))
          ` iexit_class k L x"
      then obtain P :: "('n pairpath) measure"
        where P: "P \<in> iexit_class k L x"
          and v: "v = ess_inf_enn P (\<lambda>\<omega>. iexit K (\<lambda>t. fst (\<omega> t)))" by blast
      have "min v (ennreal T) \<le> exit_val k L T K x" using step[OF P] v by simp
      then show "v \<le> exit_val k L T K x"
        using lt by (simp add: min_def split: if_splits)
    qed
    then show ?thesis using min.cobounded1 order_trans by blast
  qed
qed

subsection \<open>The converse, from an extension of a capped law\<close>

text \<open>The other half reduces to a single construction: every member of the
  horizon-\<open>T\<close> class is the cut of a member of the uncapped class.  Given that,
  the uncapped exit time dominates the capped one on the extension, and the
  inequality follows.  The construction itself is an iterated application of
  @{thm [source] exit_class_pglue_law}, whose continuation may be taken with
  covariation the identity by @{thm [source] mat_1_in_sconstraint}.\<close>

theorem iexit_val_ge_of_extension:
  fixes K :: "(real^'n::finite) set"
  assumes T: "0 \<le> T" and Kc: "closed K"
    and ext: "\<And>Q :: ('n pairpath) measure. Q \<in> exit_class k L T x \<Longrightarrow>
      \<exists>P \<in> iexit_class k L x. pair_law_of T (pcut T) P = Q"
  shows "exit_val k L T K x \<le> iexit_val k L K x"
  unfolding exit_val_def
proof (rule Sup_least)
  fix w assume "w \<in> (\<lambda>Q. ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))))
      ` exit_class k L T x"
  then obtain Q :: "('n pairpath) measure"
    where Q: "Q \<in> exit_class k L T x"
      and w: "w = ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))" by blast
  obtain P :: "('n pairpath) measure"
    where P: "P \<in> iexit_class k L x" and cut: "pair_law_of T (pcut T) P = Q"
    using ext[OF Q] by blast
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  have phim: "pcut T \<in> P \<rightarrow>\<^sub>M ?B"
    by (rule ipcut_measurable[OF T iexit_class_sets[OF P]])
  have taum: "(\<lambda>\<omega> :: 'n pairpath. pexit T K (\<lambda>t. fst (\<omega> t)))
      \<in> borel_measurable ?B"
    by (rule pexit_path_measurable[OF T Kc refl])
  have "w = ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (pcut T \<omega> t)))"
    unfolding w cut[symmetric] pair_law_of_def
  proof (rule ess_inf_time_distr[OF phim])
    fix c :: ennreal
    show "{\<omega> \<in> space ?B. c \<le> ennreal (pexit T K (\<lambda>t. fst (\<omega> t)))} \<in> sets ?B"
      using taum by measurable
  qed
  also have "\<dots> = ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))"
    by (simp add: pexit_pcut)
  also have "\<dots> = ess_inf_enn P (\<lambda>\<omega>. ennreal (pexit T K (\<lambda>t. fst (\<omega> t))))"
    by (rule ess_inf_enn_ennreal[symmetric])
  also have "\<dots> \<le> ess_inf_enn P (\<lambda>\<omega>. iexit K (\<lambda>t. fst (\<omega> t)))"
    by (rule ess_inf_enn_mono) (simp add: pexit_le_iexit[OF T])
  also have "\<dots> \<le> iexit_val k L K x"
    unfolding iexit_val_def using P by (intro Sup_upper) blast
  finally show "w \<le> iexit_val k L K x" .
qed

subsection \<open>The two value functions agree once the horizon does not bind\<close>

text \<open>The hypothesis \<open>exit_val k L T K x < ennreal T\<close> is what the a priori
  bound \<open>exit_val_le_ball_bound\<close> supplies for a bounded \<open>K\<close> and a horizon
  above \<open>rK\<^sup>2 / (n - k)\<close>: the capped value is then strictly below the cap.  With both halves, the two value functions coincide, and every
  statement about @{const exit_val} is a statement about the value function of
  Eq. (1.6) as the paper writes it.\<close>

theorem iexit_val_eq_of_extension:
  fixes K :: "(real^'n::finite) set"
  assumes T: "0 \<le> T" and Kc: "closed K"
    and nobind: "exit_val k L T K x < ennreal T"
    and ext: "\<And>Q :: ('n pairpath) measure. Q \<in> exit_class k L T x \<Longrightarrow>
      \<exists>P \<in> iexit_class k L x. pair_law_of T (pcut T) P = Q"
  shows "iexit_val k L K x = exit_val k L T K x"
proof (rule antisym)
  have le: "min (iexit_val k L K x) (ennreal T) \<le> exit_val k L T K x"
    by (rule iexit_val_cap_le[OF T Kc])
  show "iexit_val k L K x \<le> exit_val k L T K x"
    using le nobind by (simp add: min_def split: if_splits)
next
  show "exit_val k L T K x \<le> iexit_val k L K x"
    by (rule iexit_val_ge_of_extension[OF T Kc ext])
qed

subsection \<open>Towards the extension: cutting a glue back\<close>

text \<open>Gluing a continuation onto a path at \<open>r\<close> and cutting back at \<open>r\<close>
  returns the original path, so an extension built by
  @{thm [source] exit_class_pglue_law} restricts to the law it extends.
  \<open>pcut_pglue\<close> lives in @{theory Relative_Arbitrage.Dynamic_Programming_Kernels}.\<close>

text \<open>Members of the horizon-\<open>r\<close> path space are extensional on \<open>{0..r}\<close>, so
  cutting there is the identity on them.  This is what turns
  @{thm [source] pcut_pglue} into the statement that the extension of a law
  restricts to that law.\<close>

lemma pcut_id_on_mspace:
  fixes \<omega> :: "'n::finite pairpath"
  assumes "\<omega> \<in> mspace (path_metric r :: ('n pairpath) metric)"
  shows "pcut r \<omega> = \<omega>"
proof -
  have "\<omega> \<in> extensional {0..r}"
    using assms unfolding path_metric_def mspace_cfunspace by simp
  then show ?thesis unfolding pcut_def by (rule extensional_restrict)
qed

subsection \<open>Gluing a continuation onto the half-line\<close>

text \<open>The half-line analogue of @{const pglue}.  Cutting it at any horizon
  beyond the glue point returns the compact glue, so the finite-horizon
  theory applies to every restriction of an extension without further
  work.\<close>

definition iglue :: "real \<Rightarrow> 'n::finite pairpath \<Rightarrow> 'n pairpath \<Rightarrow> 'n pairpath"
  where "iglue r \<omega> \<omega>' =
     restrict (\<lambda>t. if t \<le> r then \<omega> t else \<omega> r + (\<omega>' (t - r) - \<omega>' 0)) {0..}"

lemma pcut_iglue:
  fixes \<omega> \<omega>' :: "'n::finite pairpath"
  assumes S: "0 \<le> S"
  shows "pcut S (iglue r \<omega> \<omega>') = pglue r S \<omega> \<omega>'"
  by (rule ext) (auto simp: pcut_def iglue_def pglue_def)

lemma continuous_on_iglue:
  fixes \<omega> \<omega>' :: "'n::finite pairpath"
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

text \<open>The witness of @{thm [source] bmpair_law_in_paper_pair_class} without
  the horizon cap: Brownian motion paired with the covariation \<open>Y\<^sub>t = t \<sqdot> I\<close>.
  Cutting it at \<open>S\<close> returns @{const bmpair} exactly, so every restriction of
  its law is the horizon-\<open>S\<close> witness and lies in the class.\<close>

definition ibmpair :: "('n::finite \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> 'n pairpath"
  where "ibmpair \<omega> = restrict (\<lambda>t. (cbmX 0 t \<omega>, t *\<^sub>R mat 1)) {0..}"

lemma pcut_ibmpair: "pcut S (ibmpair \<omega>) = bmpair S \<omega>"
  by (rule ext) (auto simp: pcut_def ibmpair_def bmpair_def)

lemma ibmpair_measurable:
  "(ibmpair :: ('n::finite \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> 'n pairpath)
      \<in> bm_paths \<rightarrow>\<^sub>M ipath_space"
proof -
  have "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. restrict
          (\<lambda>t. (cbmX (0 :: real^'n) t \<omega>, t *\<^sub>R (mat 1 :: real^'n^'n))) {0..})
      \<in> bm_paths \<rightarrow>\<^sub>M ipath_space"
  proof (rule ipathify_measurable)
    fix t :: real assume "0 \<le> t"
    have c: "(\<lambda>v :: real^'n. (v, t *\<^sub>R (mat 1 :: real^'n^'n)))
        \<in> borel_measurable borel"
      by (intro borel_measurable_continuous_onI continuous_intros)
    show "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real.
          (cbmX (0 :: real^'n) t \<omega>, t *\<^sub>R (mat 1 :: real^'n^'n)))
        \<in> borel_measurable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)"
      by (rule measurable_compose[OF measurable_cbmX c])
  next
    fix \<omega> :: "'n \<Rightarrow> real \<Rightarrow> real"
    show "continuous_on {0..}
        (\<lambda>t. (cbmX (0 :: real^'n) t \<omega>, t *\<^sub>R (mat 1 :: real^'n^'n)))"
      by (intro continuous_on_Pair cbmX_cont
          linear_continuous_on[OF bounded_linear_scaleR_left])
  qed
  then show ?thesis unfolding ibmpair_def by simp
qed

definition ibm_law :: "('n::finite pairpath) measure"
  where "ibm_law = distr bm_paths ipath_space ibmpair"

lemma sets_ibm_law[simp]:
  "sets (ibm_law :: ('n::finite pairpath) measure) = sets ipath_space"
  unfolding ibm_law_def by simp

lemma prob_space_ibm_law: "prob_space (ibm_law :: ('n::finite pairpath) measure)"
  unfolding ibm_law_def
  by (rule BMP.prob_space_distr[OF ibmpair_measurable])

lemma pair_law_of_pcut_ibm_law:
  assumes S: "0 \<le> S"
  shows "pair_law_of S (pcut S) (ibm_law :: ('n::finite pairpath) measure)
      = pair_law_of S (bmpair S) bm_paths"
proof -
  have "pair_law_of S (pcut S) (ibm_law :: ('n pairpath) measure)
      = distr bm_paths (path_borel S :: ('n pairpath) measure) (pcut S \<circ> ibmpair)"
    unfolding ibm_law_def pair_law_of_def
    by (rule distr_distr[OF ipcut_measurable[OF S refl] ibmpair_measurable])
  also have "\<dots> = pair_law_of S (bmpair S) bm_paths"
    unfolding pair_law_of_def by (simp add: comp_def pcut_ibmpair)
  finally show ?thesis .
qed

theorem ibm_law_cut_in_class:
  assumes S: "0 \<le> S" and L: "1 \<le> L"
  shows "pair_law_of S (pcut S) (ibm_law :: ('n::finite pairpath) measure)
      \<in> exit_class k L S (0 :: real^'n)"
  unfolding pair_law_of_pcut_ibm_law[OF S]
  by (rule bmpair_law_in_paper_pair_class[OF S L])

subsection \<open>The extension of a horizon law to the half-line\<close>

text \<open>Only the values of the continuation on \<open>{0..S-r}\<close> reach the glue, and
  at the glue point itself the glue is the cut of the law it extends.\<close>

lemma pglue_pcut:
  fixes \<omega> \<omega>' :: "'n::finite pairpath"
  assumes r: "0 \<le> r" and rS: "r \<le> S"
  shows "pglue r S \<omega> (pcut (S - r) \<omega>') = pglue r S \<omega> \<omega>'"
  using r rS by (auto simp: pglue_def pcut_def)

lemma pglue_self:
  fixes \<omega> \<omega>' :: "'n::finite pairpath"
  shows "pglue r r \<omega> \<omega>' = pcut r \<omega>"
  by (rule ext) (auto simp: pglue_def pcut_def)

lemma iglue_measurable:
  fixes Q R :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r"
    and setsQ: "sets Q = sets (path_borel r :: ('n pairpath) measure)"
    and setsR: "sets R = sets (ipath_space :: ('n pairpath) measure)"
  shows "(\<lambda>p. iglue r (fst p) (snd p)) \<in> Q \<Otimes>\<^sub>M R \<rightarrow>\<^sub>M ipath_space"
proof -
  have eQ: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. fst p v) \<in> borel_measurable (Q \<Otimes>\<^sub>M R)"
    for v
    by (rule measurable_compose[OF measurable_fst
          pair_law_eval_measurable[OF setsQ]])
  have eR: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. snd p v) \<in> borel_measurable (Q \<Otimes>\<^sub>M R)"
    if v: "0 \<le> v" for v
  proof -
    have "(\<lambda>f :: 'n pairpath. f v) \<in> borel_measurable R"
      unfolding measurable_cong_sets[OF setsR refl]
      by (rule ipath_eval_measurable[OF v])
    then show ?thesis by (rule measurable_compose[OF measurable_snd])
  qed
  have Xm: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath.
        if t \<le> r then fst p t else fst p r + (snd p (t - r) - snd p 0))
      \<in> borel_measurable (Q \<Otimes>\<^sub>M R)" if t: "0 \<le> t" for t
  proof (cases "t \<le> r")
    case True
    then show ?thesis using eQ by simp
  next
    case False
    have m2: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. snd p (t - r))
        \<in> borel_measurable (Q \<Otimes>\<^sub>M R)" using False by (intro eR) simp
    have m3: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. snd p 0)
        \<in> borel_measurable (Q \<Otimes>\<^sub>M R)" by (rule eR) simp
    show ?thesis unfolding if_not_P[OF False]
      by (intro borel_measurable_add borel_measurable_diff eQ m2 m3)
  qed
  have cont: "continuous_on {0..} (\<lambda>t. if t \<le> r then fst p t
        else fst p r + (snd p (t - r) - snd p 0))"
    if p: "p \<in> space (Q \<Otimes>\<^sub>M R)" for p :: "'n pairpath \<times> 'n pairpath"
  proof (rule continuous_on_iglue[OF r])
    have "fst p \<in> space Q" "snd p \<in> space R"
      using p by (auto simp: space_pair_measure)
    moreover have "space R = ipath" using setsR
      by (metis sets_eq_imp_space_eq space_ipath_space)
    ultimately show "continuous_on {0..r} (fst p)" "continuous_on {0..} (snd p)"
      using space_of_path_sets[OF setsQ]
      by (auto intro: mspace_path_metricD ipath_continuous_on)
  qed
  show ?thesis
    using ipathify_measurable[OF Xm cont] unfolding iglue_def by simp
qed

definition iextend ::
  "real \<Rightarrow> ('n::finite pairpath) measure \<Rightarrow> ('n pairpath) measure"
  where "iextend T Q =
     distr (Q \<Otimes>\<^sub>M ibm_law) ipath_space (\<lambda>p. iglue T (fst p) (snd p))"

lemma sets_iextend[simp]:
  "sets (iextend T Q :: ('n::finite pairpath) measure) = sets ipath_space"
  unfolding iextend_def by simp

lemma iextend_measurable:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
  shows "(\<lambda>p. iglue T (fst p) (snd p)) \<in> Q \<Otimes>\<^sub>M ibm_law \<rightarrow>\<^sub>M ipath_space"
  by (rule iglue_measurable[OF T setsQ sets_ibm_law])

lemma prob_space_iextend:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T" and Q: "Q \<in> exit_class k L T x"
  shows "prob_space (iextend T Q)"
proof -
  interpret PQ: prob_space Q by (rule exit_class_prob[OF Q])
  interpret PR: prob_space "ibm_law :: ('n pairpath) measure"
    by (rule prob_space_ibm_law)
  interpret PP: prob_space "Q \<Otimes>\<^sub>M (ibm_law :: ('n pairpath) measure)"
    by (rule prob_space_pair_measure[OF PQ.prob_space_axioms
          PR.prob_space_axioms])
  show ?thesis
    unfolding iextend_def
    by (rule PP.prob_space_distr[OF iextend_measurable[OF T exit_class_sets[OF Q]]])
qed

text \<open>Cutting the extension at a horizon beyond the glue point returns the
  compact concatenation, so @{thm [source] exit_class_pglue_law} places every
  restriction of the extension in the class.\<close>

lemma pair_law_of_pcut_iextend:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T" and TS: "T \<le> S" and Q: "Q \<in> exit_class k L T x"
  shows "pair_law_of S (pcut S) (iextend T Q)
      = pglue_law T S Q (pair_law_of (S - T) (pcut (S - T)) ibm_law)"
proof -
  let ?B = "\<lambda>r. (path_borel r :: ('n pairpath) measure)"
  let ?R = "ibm_law :: ('n pairpath) measure"
  let ?g = "\<lambda>p :: 'n pairpath \<times> 'n pairpath. pglue T S (fst p) (snd p)"
  have S0: "0 \<le> S" using T TS by simp
  have ST0: "0 \<le> S - T" using TS by simp
  interpret PQ: prob_space Q by (rule exit_class_prob[OF Q])
  interpret PR: prob_space ?R by (rule prob_space_ibm_law)
  have setsQ: "sets Q = sets (?B T)" by (rule exit_class_sets[OF Q])
  have gm: "(\<lambda>p. iglue T (fst p) (snd p)) \<in> Q \<Otimes>\<^sub>M ?R \<rightarrow>\<^sub>M ipath_space"
    by (rule iextend_measurable[OF T setsQ])
  have cm: "pcut S \<in> (ipath_space :: ('n pairpath) measure) \<rightarrow>\<^sub>M ?B S"
    by (rule ipcut_measurable[OF S0 refl])
  have step1: "pair_law_of S (pcut S) (iextend T Q)
      = distr (Q \<Otimes>\<^sub>M ?R) (?B S) ?g"
  proof -
    have "pair_law_of S (pcut S) (iextend T Q)
        = distr (Q \<Otimes>\<^sub>M ?R) (?B S) (pcut S \<circ> (\<lambda>p. iglue T (fst p) (snd p)))"
      unfolding pair_law_of_def iextend_def by (rule distr_distr[OF cm gm])
    also have "\<dots> = distr (Q \<Otimes>\<^sub>M ?R) (?B S) ?g"
      by (simp add: comp_def pcut_iglue[OF S0])
    finally show ?thesis .
  qed
  have cutm: "pcut (S - T) \<in> ?R \<rightarrow>\<^sub>M ?B (S - T)"
    by (rule ipcut_measurable[OF ST0 sets_ibm_law])
  have sf: "sigma_finite_measure (distr ?R (?B (S - T)) (pcut (S - T)))"
    using PR.prob_space_distr[OF cutm]
    by (simp add: prob_space_imp_sigma_finite)
  have prodeq: "Q \<Otimes>\<^sub>M (pair_law_of (S - T) (pcut (S - T)) ?R)
      = distr (Q \<Otimes>\<^sub>M ?R) (?B T \<Otimes>\<^sub>M ?B (S - T))
          (\<lambda>p. (fst p, pcut (S - T) (snd p)))"
  proof -
    have "Q \<Otimes>\<^sub>M (pair_law_of (S - T) (pcut (S - T)) ?R)
        = distr Q (?B T) (\<lambda>u. u) \<Otimes>\<^sub>M distr ?R (?B (S - T)) (pcut (S - T))"
      unfolding pair_law_of_def by (simp add: distr_id2[OF setsQ[symmetric]])
    also have "\<dots> = distr (Q \<Otimes>\<^sub>M ?R) (?B T \<Otimes>\<^sub>M ?B (S - T))
        (\<lambda>(u, v). (u, pcut (S - T) v))"
      by (rule pair_measure_distr[OF measurable_ident_sets[OF setsQ] cutm sf])
    also have "\<dots> = distr (Q \<Otimes>\<^sub>M ?R) (?B T \<Otimes>\<^sub>M ?B (S - T))
        (\<lambda>p. (fst p, pcut (S - T) (snd p)))"
    proof -
      have "(\<lambda>(u, v). (u, pcut (S - T) v))
          = (\<lambda>p :: 'n pairpath \<times> 'n pairpath. (fst p, pcut (S - T) (snd p)))"
        by auto
      then show ?thesis by simp
    qed
    finally show ?thesis .
  qed
  have pgm: "?g \<in> ?B T \<Otimes>\<^sub>M ?B (S - T) \<rightarrow>\<^sub>M ?B S"
    by (rule pglue_measurable[OF T TS refl refl])
  have pairm: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. (fst p, pcut (S - T) (snd p)))
      \<in> Q \<Otimes>\<^sub>M ?R \<rightarrow>\<^sub>M ?B T \<Otimes>\<^sub>M ?B (S - T)"
    by (intro measurable_Pair measurable_compose[OF measurable_snd cutm]
        measurable_compose[OF measurable_fst measurable_ident_sets[OF setsQ]])
  have "pglue_law T S Q (pair_law_of (S - T) (pcut (S - T)) ?R)
      = distr (Q \<Otimes>\<^sub>M (pair_law_of (S - T) (pcut (S - T)) ?R)) (?B S) ?g"
    unfolding pglue_law_def pair_law_of_def ..
  also have "\<dots> = distr (Q \<Otimes>\<^sub>M ?R) (?B S)
      (?g \<circ> (\<lambda>p. (fst p, pcut (S - T) (snd p))))"
    unfolding prodeq by (rule distr_distr[OF pgm pairm])
  also have "\<dots> = distr (Q \<Otimes>\<^sub>M ?R) (?B S) ?g"
    by (simp add: comp_def pglue_pcut[OF T TS])
  finally show ?thesis unfolding step1 ..
qed

theorem iextend_cut_in_class:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T" and TS: "T \<le> S" and L: "1 \<le> L"
    and Q: "Q \<in> exit_class k L T x"
  shows "pair_law_of S (pcut S) (iextend T Q) \<in> exit_class k L S x"
proof -
  have ST0: "0 \<le> S - T" using TS by simp
  show ?thesis
    unfolding pair_law_of_pcut_iextend[OF T TS Q]
    by (rule exit_class_pglue_law[OF T TS Q ibm_law_cut_in_class[OF ST0 L]])
qed

text \<open>At the glue point itself the extension restricts to the law it
  extends: this is the identity the bridge asks for.\<close>

theorem pcut_law_iextend:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T" and Q: "Q \<in> exit_class k L T x"
  shows "pair_law_of T (pcut T) (iextend T Q) = Q"
proof -
  let ?B = "\<lambda>r. (path_borel r :: ('n pairpath) measure)"
  let ?R = "ibm_law :: ('n pairpath) measure"
  interpret PQ: prob_space Q by (rule exit_class_prob[OF Q])
  interpret PR: prob_space ?R by (rule prob_space_ibm_law)
  have setsQ: "sets Q = sets (?B T)" by (rule exit_class_sets[OF Q])
  have gm: "(\<lambda>p. iglue T (fst p) (snd p)) \<in> Q \<Otimes>\<^sub>M ?R \<rightarrow>\<^sub>M ipath_space"
    by (rule iextend_measurable[OF T setsQ])
  have cm: "pcut T \<in> (ipath_space :: ('n pairpath) measure) \<rightarrow>\<^sub>M ?B T"
    by (rule ipcut_measurable[OF T refl])
  have "pair_law_of T (pcut T) (iextend T Q)
      = distr (Q \<Otimes>\<^sub>M ?R) (?B T) (pcut T \<circ> (\<lambda>p. iglue T (fst p) (snd p)))"
    unfolding pair_law_of_def iextend_def by (rule distr_distr[OF cm gm])
  also have "\<dots> = distr (Q \<Otimes>\<^sub>M ?R) (?B T) (\<lambda>p. pcut T (fst p))"
    by (simp add: comp_def pcut_iglue[OF T] pglue_self)
  also have "\<dots> = distr (Q \<Otimes>\<^sub>M ?R) Q fst"
  proof (rule distr_cong[OF refl setsQ[symmetric]])
    fix p :: "'n pairpath \<times> 'n pairpath"
    assume "p \<in> space (Q \<Otimes>\<^sub>M ?R)"
    then have "fst p \<in> space Q" by (auto simp: space_pair_measure)
    then show "pcut T (fst p) = fst p"
      using space_of_path_sets[OF setsQ] by (simp add: pcut_id_on_mspace)
  qed
  also have "\<dots> = Q" by (rule PR.distr_pair_fst)
  finally show ?thesis .
qed

subsection \<open>Martingales from the restrictions\<close>

text \<open>Cutting at a horizon beyond \<open>u\<close> leaves the evaluations up to \<open>u\<close>
  untouched, so it identifies the two natural filtrations at \<open>u\<close>: every
  event of the half-line filtration is the preimage of an event of the
  horizon one.\<close>

lemma natural_filtration_pcut:
  fixes P :: "('n::finite pairpath) measure"
  assumes u: "0 \<le> u" and uS: "u \<le> S"
    and setsP: "sets P = sets (ipath_space :: ('n pairpath) measure)"
  shows "{pcut S -` A \<inter> space P | A.
        A \<in> sets (natural_filtration (pair_law_of S (pcut S) P) 0 (\<lambda>v \<omega>. \<omega> v) u)}
      = sets (natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) u)"
proof -
  let ?Q = "pair_law_of S (pcut S) P"
  let ?g = "\<lambda>N. (\<Union>i\<in>{0..u}. {(\<lambda>\<omega> :: 'n pairpath. \<omega> i) -` B \<inter> N | B. B \<in> sets borel})"
  have S0: "0 \<le> S" using u uS by simp
  have spP: "space P = ipath"
    using setsP by (metis sets_eq_imp_space_eq space_ipath_space)
  have spQ: "space ?Q = mspace (path_metric S :: ('n pairpath) metric)"
    by (rule space_pair_law_of)
  have into': "pcut S \<omega> \<in> space ?Q" if "\<omega> \<in> space P" for \<omega>
    using that spP spQ restrict_ipath_mspace[OF S0] by (simp add: pcut_def)
  then have into: "pcut S \<in> space P \<rightarrow> space ?Q" by blast
  have pre: "pcut S -` ((\<lambda>\<omega> :: 'n pairpath. \<omega> i) -` B \<inter> space ?Q) \<inter> space P
      = (\<lambda>\<omega> :: 'n pairpath. \<omega> i) -` B \<inter> space P" if i: "i \<in> {0..u}" for i B
  proof -
    have iS: "i \<in> {0..S}" using i uS by auto
    show ?thesis using into' by (auto simp: pcut_apply[OF iS])
  qed
  have geneq: "{pcut S -` A \<inter> space P | A. A \<in> ?g (space ?Q)} = ?g (space P)"
  proof (rule set_eqI)
    fix C :: "('n pairpath) set"
    show "C \<in> {pcut S -` A \<inter> space P | A. A \<in> ?g (space ?Q)} \<longleftrightarrow> C \<in> ?g (space P)"
    proof
      assume "C \<in> {pcut S -` A \<inter> space P | A. A \<in> ?g (space ?Q)}"
      then obtain i B where i: "i \<in> {0..u}" and B: "B \<in> sets borel"
        and C: "C = pcut S -` ((\<lambda>\<omega> :: 'n pairpath. \<omega> i) -` B \<inter> space ?Q) \<inter> space P"
        by blast
      show "C \<in> ?g (space P)" unfolding C pre[OF i] using i B by blast
    next
      assume "C \<in> ?g (space P)"
      then obtain i B where i: "i \<in> {0..u}" and B: "B \<in> sets borel"
        and C: "C = (\<lambda>\<omega> :: 'n pairpath. \<omega> i) -` B \<inter> space P" by blast
      have "C = pcut S -` ((\<lambda>\<omega> :: 'n pairpath. \<omega> i) -` B \<inter> space ?Q) \<inter> space P"
        unfolding C by (rule pre[OF i, symmetric])
      moreover have "(\<lambda>\<omega> :: 'n pairpath. \<omega> i) -` B \<inter> space ?Q \<in> ?g (space ?Q)"
        using i B by blast
      ultimately show "C \<in> {pcut S -` A \<inter> space P | A. A \<in> ?g (space ?Q)}" by blast
    qed
  qed
  have "{pcut S -` A \<inter> space P | A. A \<in> sets (natural_filtration ?Q 0 (\<lambda>v \<omega>. \<omega> v) u)}
      = sigma_sets (space P) {pcut S -` A \<inter> space P | A. A \<in> ?g (space ?Q)}"
    unfolding sets_natural_filtration by (rule sigma_sets_vimage_commute[OF into])
  also have "\<dots> = sigma_sets (space P) (?g (space P))" unfolding geneq ..
  finally show ?thesis unfolding sets_natural_filtration .
qed

text \<open>Hence a process whose restrictions are martingales at every horizon is
  a martingale on the half-line: the set-integral identity at \<open>u \<le> v\<close> is the
  one the restriction at \<open>v\<close> already satisfies.\<close>

lemma martingale_of_cuts:
  fixes P :: "('n::finite pairpath) measure"
    and Z :: "real \<Rightarrow> 'n pairpath \<Rightarrow> 'b::{banach,second_countable_topology}"
  assumes prob: "prob_space P"
    and setsP: "sets P = sets (ipath_space :: ('n pairpath) measure)"
    and Zm: "\<And>u. 0 \<le> u \<Longrightarrow> Z u \<in> borel_measurable
        (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) u)"
    and Zloc: "\<And>u S \<omega>. 0 \<le> u \<Longrightarrow> u \<le> S \<Longrightarrow> Z u (pcut S \<omega>) = Z u \<omega>"
    and mg: "\<And>S. 0 \<le> S \<Longrightarrow> martingale (pair_law_of S (pcut S) P)
        (natural_filtration (pair_law_of S (pcut S) P) 0 (\<lambda>v \<omega>. \<omega> v)) 0
        (\<lambda>u \<omega>. Z (min u S) \<omega>)"
  shows "martingale P (natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)) 0 Z"
proof -
  let ?G = "natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?B = "\<lambda>S. (path_borel S :: ('n pairpath) measure)"
  let ?Q = "\<lambda>S. pair_law_of S (pcut S) P"
  let ?H = "\<lambda>S. natural_filtration (?Q S) 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  interpret PP: prob_space P by (rule prob)
  have SP: "Stochastic_Process.stochastic_process P (0::real)
      (\<lambda>u \<omega> :: 'n pairpath. \<omega> u)"
  proof (unfold_locales)
    fix i :: real assume i: "0 \<le> i"
    show "(\<lambda>\<omega> :: 'n pairpath. \<omega> i) \<in> borel_measurable P"
      unfolding measurable_cong_sets[OF setsP refl]
      by (rule ipath_eval_measurable[OF i])
  qed
  have fin: "finite_measure P" using prob by (simp add: prob_space_def)
  interpret SF: finite_filtered_measure P ?G 0
    by (rule Stochastic_Process.stochastic_process.finite_filtered_measure_natural_filtration
        [OF SP fin])
  have cutm: "pcut S \<in> P \<rightarrow>\<^sub>M ?B S" if S: "0 \<le> S" for S
    by (rule ipcut_measurable[OF S setsP])
  have ZB: "Z w \<in> borel_measurable (?B S)" if w: "0 \<le> w" and wS: "w \<le> S" for w S
  proof -
    have S0: "0 \<le> S" using w wS by simp
    interpret MS: martingale "?Q S" "?H S" 0 "\<lambda>u \<omega>. Z (min u S) \<omega>"
      by (rule mg[OF S0])
    have "(\<lambda>\<omega>. Z (min w S) \<omega>) \<in> borel_measurable (?H S w)" by (rule MS.adapted[OF w])
    then have "Z w \<in> borel_measurable (?H S w)" using wS by simp
    then have "Z w \<in> borel_measurable (?Q S)"
      by (rule measurable_from_subalg[OF MS.subalgebras[OF w]])
    then show ?thesis using measurable_cong_sets[OF sets_pair_law_of refl] by blast
  qed
  have integ: "integrable P (Z w)" if w: "0 \<le> w" for w
  proof -
    interpret MS: martingale "?Q w" "?H w" 0 "\<lambda>u \<omega>. Z (min u w) \<omega>" by (rule mg[OF w])
    have "integrable (?Q w) (\<lambda>\<omega>. Z (min w w) \<omega>)" by (rule MS.integrable[OF w])
    then have "integrable (?Q w) (Z w)" by simp
    then have "integrable P (\<lambda>\<omega>. Z w (pcut w \<omega>))"
      unfolding pair_law_of_def
      using integrable_distr_eq[OF cutm[OF w] ZB[OF w order.refl]] by simp
    then show ?thesis using Zloc[OF w order.refl] by simp
  qed
  show ?thesis
  proof (rule SF.martingale_of_set_integral_eq)
    show "adapted_process P ?G 0 Z"
    proof (unfold_locales)
      fix u :: real assume u: "0 \<le> u"
      show "Z u \<in> borel_measurable (?G u)" by (rule Zm[OF u])
    qed
    show "integrable P (Z u)" if "0 \<le> u" for u by (rule integ[OF that])
    fix A and u v :: real
    assume A: "A \<in> ?G u" and uv: "0 \<le> u" "u \<le> v"
    have v0: "0 \<le> v" using uv by simp
    interpret MS: martingale "?Q v" "?H v" 0 "\<lambda>w \<omega>. Z (min w v) \<omega>" by (rule mg[OF v0])
    obtain A' where A': "A' \<in> sets (?H v u)" and AA: "A = pcut v -` A' \<inter> space P"
      using A natural_filtration_pcut[OF uv(1) uv(2) setsP] by blast
    have key: "set_lebesgue_integral P A (Z w)
        = set_lebesgue_integral (?Q v) A' (\<lambda>\<omega>. Z (min w v) \<omega>)"
      if w: "0 \<le> w" and wv: "w \<le> v" for w
    proof -
      have AB: "A' \<in> sets (?B v)"
        using A' MS.subalgebras[OF uv(1)] by (auto simp: subalgebra_def)
      have gb: "(\<lambda>\<omega> :: 'n pairpath. indicat_real A' \<omega> *\<^sub>R Z w \<omega>)
          \<in> borel_measurable (?B v)"
        using AB ZB[OF w wv] by measurable
      have "set_lebesgue_integral (?Q v) A' (\<lambda>\<omega>. Z (min w v) \<omega>)
          = (\<integral>\<omega>. indicat_real A' \<omega> *\<^sub>R Z w \<omega> \<partial>(?Q v))"
        unfolding set_lebesgue_integral_def using wv by simp
      also have "\<dots> = (\<integral>\<omega>. indicat_real A' (pcut v \<omega>) *\<^sub>R Z w (pcut v \<omega>) \<partial>P)"
        unfolding pair_law_of_def by (rule integral_distr[OF cutm[OF v0] gb])
      also have "\<dots> = (\<integral>\<omega>. indicat_real A \<omega> *\<^sub>R Z w \<omega> \<partial>P)"
        using AA Zloc[OF w wv]
        by (intro Bochner_Integration.integral_cong) (auto simp: indicator_def)
      finally show ?thesis unfolding set_lebesgue_integral_def ..
    qed
    have "set_lebesgue_integral P A (Z u)
        = set_lebesgue_integral (?Q v) A' (\<lambda>\<omega>. Z (min u v) \<omega>)"
      by (rule key[OF uv(1) uv(2)])
    also have "\<dots> = set_lebesgue_integral (?Q v) A' (\<lambda>\<omega>. Z (min v v) \<omega>)"
      by (rule MS.set_integral_eq[OF A' uv(1) uv(2)])
    also have "\<dots> = set_lebesgue_integral P A (Z v)"
      by (rule key[OF v0 order.refl, symmetric])
    finally show "set_lebesgue_integral P A (Z u) = set_lebesgue_integral P A (Z v)" .
  qed
qed

subsection \<open>The extension lies in the uncapped class\<close>

lemma pcut_pcut:
  fixes \<omega> :: "'n::finite pairpath"
  assumes ST: "S \<le> T"
  shows "pcut S (pcut T \<omega>) = pcut S \<omega>"
proof (rule ext)
  fix t :: real
  show "pcut S (pcut T \<omega>) t = pcut S \<omega> t" using ST by (auto simp: pcut_def)
qed

lemma iextend_pcut_in_class:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T" and S: "0 \<le> S" and L: "1 \<le> L"
    and Q: "Q \<in> exit_class k L T x"
  shows "pair_law_of S (pcut S) (iextend T Q) \<in> exit_class k L S x"
proof (cases "T \<le> S")
  case True
  then show ?thesis by (rule iextend_cut_in_class[OF T _ L Q])
next
  case False
  let ?B = "\<lambda>r. (path_borel r :: ('n pairpath) measure)"
  have ST: "S \<le> T" using False by simp
  have "pair_law_of S (pcut S) Q
      = pair_law_of S (pcut S) (pair_law_of T (pcut T) (iextend T Q))"
    unfolding pcut_law_iextend[OF T Q] ..
  also have "\<dots> = distr (iextend T Q) (?B S) (pcut S \<circ> pcut T)"
    unfolding pair_law_of_def
    by (rule distr_distr[OF pcut_measurable[OF S ST refl]
          ipcut_measurable[OF T sets_iextend]])
  also have "\<dots> = pair_law_of S (pcut S) (iextend T Q)"
    unfolding pair_law_of_def by (simp add: comp_def pcut_pcut[OF ST])
  finally show ?thesis using exit_class_pcut[OF S ST Q] by simp
qed

theorem iextend_in_iexit_class:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T" and L: "1 \<le> L" and Q: "Q \<in> exit_class k L T x"
  shows "iextend T Q \<in> iexit_class k L x"
proof -
  let ?P = "iextend T Q"
  let ?G = "natural_filtration ?P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  have prob: "prob_space ?P" by (rule prob_space_iextend[OF T Q])
  have cutm: "pcut S \<in> ?P \<rightarrow>\<^sub>M (path_borel S :: ('n pairpath) measure)" if S: "0 \<le> S" for S
    by (rule ipcut_measurable[OF S sets_iextend])
  have cls: "pair_law_of S (pcut S) ?P \<in> exit_class k L S x" if S: "0 \<le> S" for S
    by (rule iextend_pcut_in_class[OF T S L Q])

  \<comment> \<open>clause (i): the initial condition\<close>
  have start: "AE \<omega> in ?P. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
  proof -
    have "AE \<omega> in pair_law_of T (pcut T) ?P. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
      using cls[OF T] unfolding exit_class_def by blast
    then have "AE \<omega> in ?P. fst (pcut T \<omega> 0) = x \<and> snd (pcut T \<omega> 0) = 0"
      unfolding pair_law_of_def by (rule AE_distrD[OF cutm[OF T]])
    then show ?thesis using T by (simp add: pcut_def)
  qed

  \<comment> \<open>clause (ii): the covariation constraint, at every pair of times\<close>
  have dq: "AE \<omega> in ?P. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
  proof -
    have step: "AE \<omega> in ?P. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T + real n \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L" for n :: nat
    proof -
      have S: "0 \<le> T + real n" using T by simp
      have "AE \<omega> in pair_law_of (T + real n) (pcut (T + real n)) ?P.
          \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T + real n \<longrightarrow>
            (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
        using cls[OF S] unfolding exit_class_def by blast
      then have "AE \<omega> in ?P. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T + real n \<longrightarrow>
          (1 / (t - s)) *\<^sub>R (snd (pcut (T + real n) \<omega> t)
            - snd (pcut (T + real n) \<omega> s)) \<in> sconstraint k L"
        unfolding pair_law_of_def by (rule AE_distrD[OF cutm[OF S]])
      then show ?thesis by eventually_elim (auto simp: pcut_def)
    qed
    have "AE \<omega> in ?P. \<forall>n :: nat. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T + real n \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
      using step by (subst AE_all_countable) blast
    then show ?thesis
    proof eventually_elim
      case (elim \<omega>)
      show ?case
      proof (intro allI impI)
        fix s t :: real assume st: "0 \<le> s" "s < t"
        obtain n :: nat where "t < real n" using reals_Archimedean2 by blast
        then have "t \<le> T + real n" using T by simp
        then show "(1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
          using elim st by blast
      qed
    qed
  qed

  \<comment> \<open>clause (iii): the coordinate process is a martingale\<close>
  have Xmg: "martingale ?P ?G 0 (\<lambda>u \<omega>. fst (\<omega> u) :: real^'n)"
  proof (rule martingale_of_cuts[OF prob sets_iextend])
    fix u :: real assume u: "0 \<le> u"
    have fstB: "(\<lambda>p :: (real^'n) \<times> (real^'n^'n). fst p) \<in> borel_measurable borel"
      by (intro borel_measurable_continuous_onI continuous_intros)
    have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> u) \<in> ?G u \<rightarrow>\<^sub>M borel"
      unfolding natural_filtration_def
      by (rule measurable_family_vimage_algebra) (use u in auto)
    show "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> u)) \<in> borel_measurable (?G u)"
      by (rule measurable_compose[OF ev fstB])
  next
    fix u S :: real and \<omega> :: "'n pairpath"
    assume "0 \<le> u" "u \<le> S"
    then show "fst (pcut S \<omega> u) = fst (\<omega> u)" by (auto simp: pcut_def)
  next
    fix S :: real assume S: "0 \<le> S"
    show "martingale (pair_law_of S (pcut S) ?P)
        (natural_filtration (pair_law_of S (pcut S) ?P) 0 (\<lambda>v \<omega>. \<omega> v)) 0
        (\<lambda>u \<omega>. fst (\<omega> (min u S)) :: real^'n)"
      by (rule exit_class_X_martingale[OF cls[OF S]])
  qed

  \<comment> \<open>clause (iv): the compensated process is a martingale\<close>
  have Cmg: "martingale ?P ?G 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> u) :: real^'n) - snd (\<omega> u))"
  proof (rule martingale_of_cuts[OF prob sets_iextend])
    fix u :: real assume u: "0 \<le> u"
    have e: "(\<lambda>p :: (real^'n) \<times> (real^'n^'n). outerp (fst p) - snd p)
        = (\<lambda>p. \<chi> i j. fst p $ i * fst p $ j - snd p $ i $ j)"
      by (rule ext) (simp add: outerp_def vec_eq_iff)
    have cB: "(\<lambda>p :: (real^'n) \<times> (real^'n^'n). outerp (fst p) - snd p)
        \<in> borel_measurable borel"
      unfolding e
      by (intro borel_measurable_continuous_onI continuous_on_vec_lambda
          continuous_intros)
    have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> u) \<in> ?G u \<rightarrow>\<^sub>M borel"
      unfolding natural_filtration_def
      by (rule measurable_family_vimage_algebra) (use u in auto)
    show "(\<lambda>\<omega> :: 'n pairpath. outerp (fst (\<omega> u)) - snd (\<omega> u))
        \<in> borel_measurable (?G u)"
      by (rule measurable_compose[OF ev cB])
  next
    fix u S :: real and \<omega> :: "'n pairpath"
    assume "0 \<le> u" "u \<le> S"
    then show "outerp (fst (pcut S \<omega> u) :: real^'n) - snd (pcut S \<omega> u)
        = outerp (fst (\<omega> u)) - snd (\<omega> u)" by (auto simp: pcut_def)
  next
    fix S :: real assume S: "0 \<le> S"
    show "martingale (pair_law_of S (pcut S) ?P)
        (natural_filtration (pair_law_of S (pcut S) ?P) 0 (\<lambda>v \<omega>. \<omega> v)) 0
        (\<lambda>u \<omega>. outerp (fst (\<omega> (min u S)) :: real^'n) - snd (\<omega> (min u S)))"
      by (rule exit_class_compensated_martingale[OF cls[OF S]])
  qed

  show ?thesis
    unfolding iexit_class_def mem_Collect_eq
    using prob sets_iextend start dq Xmg Cmg by blast
qed

text \<open>The construction the bridge was reduced to: every member of the
  horizon-\<open>T\<close> class is the restriction of a member of the uncapped class.\<close>

theorem exit_class_has_extension:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T" and L: "1 \<le> L" and Q: "Q \<in> exit_class k L T x"
  shows "\<exists>P \<in> iexit_class k L x. pair_law_of T (pcut T) P = Q"
  using iextend_in_iexit_class[OF T L Q] pcut_law_iextend[OF T Q] by blast

subsection \<open>The two value functions, unconditionally\<close>

text \<open>With the construction in place, both hypotheses of
  @{thm [source] iexit_val_eq_of_extension} that were about the class are
  discharged, and only the paper's own standing assumptions remain.\<close>

theorem iexit_val_eq_exit_val:
  fixes K :: "(real^'n::finite) set"
  assumes T: "0 \<le> T" and L: "1 \<le> L" and Kc: "closed K"
    and nobind: "exit_val k L T K x < ennreal T"
  shows "iexit_val k L K x = exit_val k L T K x"
  by (rule iexit_val_eq_of_extension[OF T Kc nobind
        exit_class_has_extension[OF T L]])

text \<open>For a bounded \<open>K\<close> the a priori bound
  @{thm [source] exit_val_le_ball_bound} makes the remaining hypothesis a
  condition on the horizon alone, so the paper's value function of Eq. (1.6)
  is the capped one at every horizon past the scale \<open>(r\<^sup>2 - |x|\<^sup>2)/(n-k)\<close>.\<close>

corollary iexit_val_eq_exit_val_bounded:
  fixes K :: "(real^'n::finite) set" and r :: real
  assumes k: "k < CARD('n)" and L: "1 \<le> L" and T: "0 < T"
    and Kc: "closed K" and KB: "K \<subseteq> cball 0 r"
    and big: "(r * r - x \<bullet> x) / real (CARD('n) - k) < T"
  shows "iexit_val k L K x = exit_val k L T K x"
proof (rule iexit_val_eq_exit_val[OF less_imp_le[OF T] L Kc])
  have "exit_val k L T K x
      \<le> ennreal ((r * r - x \<bullet> x) / real (CARD('n) - k))"
    using L by (intro exit_val_le_ball_bound[OF k less_imp_le[OF T] _ KB]) simp
  also have "\<dots> < ennreal T" by (rule ennreal_lessI[OF T big])
  finally show "exit_val k L T K x < ennreal T" .
qed

text \<open>The bound is largest at the centre, so the hypothesis is uniform in
  \<open>x\<close>: one horizon beyond \<open>r\<^sup>2/(n-k)\<close> identifies the two value functions
  everywhere at once, which is what a clause quantified over points needs.\<close>

corollary iexit_val_eq_exit_val_ball:
  fixes K :: "(real^'n::finite) set" and rK :: real
  assumes k: "k < CARD('n)" and L: "1 \<le> L" and Kc: "closed K"
    and KB: "K \<subseteq> cball 0 rK"
    and big: "rK * rK / real (CARD('n) - k) < T"
  shows "iexit_val k L K x = exit_val k L T K x"
proof (rule iexit_val_eq_exit_val_bounded[OF k L _ Kc KB])
  have nk: "0 < real (CARD('n) - k)" using k by simp
  have sq: "0 \<le> rK * rK" by simp
  then have "0 \<le> rK * rK / real (CARD('n) - k)" using nk by simp
  then show "0 < T" using big by (rule order.strict_trans1)
  have "(rK * rK - x \<bullet> x) / real (CARD('n) - k)
      \<le> rK * rK / real (CARD('n) - k)"
    using nk by (intro divide_right_mono) auto
  then show "(rK * rK - x \<bullet> x) / real (CARD('n) - k) < T" using big by simp
qed

(*<*)
end
(*>*)
