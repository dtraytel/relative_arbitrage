section \<open>The class and the value function on the half-line\<close>

(*<*)
theory Covariation_Class_Infinite
  imports
    Covariation_Class_Pasting
begin
(*>*)

text \<open>Eq. (1.6)--(1.7) of \<^cite>\<open>LaiShkolnikovSoner\<close> without the horizon cap: the class
  is a set of laws on the paths of @{theory Continuous_Path_Spaces.Path_Space_Infinite},
  the covariation constraint is required at every pair of times, and the
  martingale clauses carry no stopping.  The capped development is reached
  through the restriction of a law to a compact horizon.\<close>

subsection \<open>The uncapped class for an abstract constraint set\<close>

text \<open>The class on the half-line for any constraint set \<open>S\<close>: the analogue of
  @{const covariation_class} without the horizon, and its value function.\<close>

definition icovariation_class ::
  "(real^'n::finite^'n) set \<Rightarrow> real^'n \<Rightarrow> (('n pairpath) measure) set"
  where
  "icovariation_class S x = {P.
     prob_space P \<and>
     sets P = sets (ipath_space :: ('n pairpath) measure) \<and>
     (AE \<omega> in P. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0) \<and>
     (AE \<omega> in P. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> S) \<and>
     martingale P (natural_filtration P 0 (\<lambda>t \<omega>. \<omega> t)) 0
       (\<lambda>t \<omega>. fst (\<omega> t)) \<and>
     martingale P (natural_filtration P 0 (\<lambda>t \<omega>. \<omega> t)) 0
       (\<lambda>t \<omega>. outerp (fst (\<omega> t)) - snd (\<omega> t))}"

definition icovariation_val ::
  "(real^'n::finite^'n) set \<Rightarrow> (real^'n) set \<Rightarrow> real^'n \<Rightarrow> ennreal"
  where
  "icovariation_val S K x =
     Sup ((\<lambda>Q. ess_inf Q (\<lambda>\<omega>. iexit K (\<lambda>t. fst (\<omega> t)))) ` icovariation_class S x)"

lemma icovariation_class_prob:
  "P \<in> icovariation_class S x \<Longrightarrow> prob_space P"
  unfolding icovariation_class_def by blast

lemma icovariation_class_sets:
  "P \<in> icovariation_class S x \<Longrightarrow> sets P = sets (ipath_space :: ('n::finite pairpath) measure)"
  unfolding icovariation_class_def by blast

lemma icovariation_class_start:
  "P \<in> icovariation_class S x \<Longrightarrow> AE \<omega> in P. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
  unfolding icovariation_class_def by blast

lemma icovariation_class_diffquot:
  "P \<in> icovariation_class S x \<Longrightarrow>
     AE \<omega> in P. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
       (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> S"
  unfolding icovariation_class_def by blast

lemma icovariation_class_X_martingale:
  "P \<in> icovariation_class S x \<Longrightarrow>
     martingale P (natural_filtration P 0 (\<lambda>t \<omega>. \<omega> t)) 0
       (\<lambda>t \<omega>. fst (\<omega> t) :: real^'n::finite)"
  unfolding icovariation_class_def by blast

lemma icovariation_class_comp_martingale:
  "P \<in> icovariation_class S x \<Longrightarrow>
     martingale P (natural_filtration P 0 (\<lambda>t \<omega>. \<omega> t)) 0
       (\<lambda>t \<omega>. outerp (fst (\<omega> t) :: real^'n::finite) - snd (\<omega> t))"
  unfolding icovariation_class_def by blast

subsection \<open>Restriction to a compact horizon\<close>

text \<open>The cut of a member of the uncapped class is a member of the capped one.
  Every clause transfers along @{const pcut}; the covariation and martingale
  clauses are simpler here than in @{thm [source] covariation_class_pcut}, since the
  uncapped class constrains every pair of times and stops nothing.\<close>

theorem icovariation_class_pcut:
  fixes P :: "('n::finite pairpath) measure"
  assumes U: "0 \<le> U" and Sc: "closed S" and P: "P \<in> icovariation_class S x"
  shows "process_law U (pcut U) P \<in> covariation_class S U x"
proof -
  let ?Q = "process_law U (pcut U) P"
  let ?B = "(path_borel U :: ('n pairpath) measure)"
  let ?G = "natural_filtration ?Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  interpret P: prob_space P by (rule icovariation_class_prob[OF P])
  have phim: "pcut U \<in> P \<rightarrow>\<^sub>M ?B"
    by (rule ipcut_measurable[OF U icovariation_class_sets[OF P]])
  have prob': "prob_space ?Q"
    unfolding process_law_def by (rule P.prob_space_distr[OF phim])

  \<comment> \<open>clause (i): the initial condition\<close>
  have start': "AE \<omega> in ?Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
  proof -
    have mset: "{\<omega> \<in> space ?B. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0} \<in> sets ?B"
      by (rule start_set_sets[OF refl])
    have iff: "(AE \<omega> in ?Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0)
        = (AE \<omega> in P. fst (pcut U \<omega> 0) = x \<and> snd (pcut U \<omega> 0) = 0)"
      unfolding process_law_def by (rule AE_distr_iff[OF phim mset])
    have z: "(0::real) \<in> {0..U}" using U by simp
    have "AE \<omega> in P. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
      by (rule icovariation_class_start[OF P])
    then have "AE \<omega> in P. fst (pcut U \<omega> 0) = x \<and> snd (pcut U \<omega> 0) = 0"
      by eventually_elim (simp add: pcut_apply[OF z])
    then show ?thesis unfolding iff .
  qed

  \<comment> \<open>clause (ii): the covariation constraint\<close>
  have cov': "AE \<omega> in ?Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> U \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> S"
  proof -
    have "AE \<omega> in P. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> S"
      by (rule icovariation_class_diffquot[OF P])
    then have "AE \<omega> in P. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> U \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (pcut U \<omega> t) - snd (pcut U \<omega> s)) \<in> S"
      by eventually_elim (auto simp: pcut_apply)
    then show ?thesis unfolding process_law_def AE_distr_iff[OF phim diffquot_all_sets[OF Sc]] .
  qed

  \<comment> \<open>clauses (iii) and (iv): the martingales\<close>
  have mgX': "martingale ?Q ?G 0 (\<lambda>u \<omega>. fst (\<omega> (min u U)) :: real^'n)"
    by (rule martingale_pcut_law[OF U P.prob_space_axioms phim pair_fst_borel
          martingale_stopped_const[OF U icovariation_class_X_martingale[OF P]]])
  have mgC': "martingale ?Q ?G 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (min u U)) :: real^'n) - snd (\<omega> (min u U)))"
    by (rule martingale_pcut_law[OF U P.prob_space_axioms phim compensated_map_borel
          martingale_stopped_const[OF U icovariation_class_comp_martingale[OF P]]])

  show ?thesis
    unfolding covariation_class_def mem_Collect_eq
    using prob' sets_process_law start' cov' mgX' mgC' by blast
qed

subsection \<open>The capped value dominates the capped uncapped value\<close>

text \<open>The exit time of the cut law is the uncapped exit time capped at the
  horizon, in essential infimum.\<close>

lemma ess_inf_pexit_cut:
  fixes P :: "('n::finite pairpath) measure" and K :: "(real^'n) set"
  assumes T: "0 \<le> T" and Kc: "closed K"
    and setsP: "sets P = sets (ipath_space :: ('n pairpath) measure)"
  shows "ess_inf_time (process_law T (pcut T) P) (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))
      = ess_inf P (\<lambda>\<omega>. min (iexit K (\<lambda>t. fst (\<omega> t))) (ennreal T))"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  have phim: "pcut T \<in> P \<rightarrow>\<^sub>M ?B" by (rule ipcut_measurable[OF T setsP])
  have taum: "(\<lambda>\<omega> :: 'n pairpath. pexit T K (\<lambda>t. fst (\<omega> t))) \<in> borel_measurable ?B"
    by (rule pexit_path_measurable[OF T Kc refl])
  have "ess_inf_time (process_law T (pcut T) P) (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))
      = ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (pcut T \<omega> t)))"
    unfolding process_law_def
  proof (rule ess_inf_time_distr[OF phim])
    fix c :: ennreal
    show "{\<omega> \<in> space ?B. c \<le> ennreal (pexit T K (\<lambda>t. fst (\<omega> t)))} \<in> sets ?B"
      using taum by measurable
  qed
  also have "\<dots> = ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))"
    by (simp add: pexit_pcut)
  also have "\<dots> = ess_inf P (\<lambda>\<omega>. ennreal (pexit T K (\<lambda>t. fst (\<omega> t))))"
    by (rule ess_inf_ennreal[symmetric])
  also have "\<dots> = ess_inf P (\<lambda>\<omega>. min (iexit K (\<lambda>t. fst (\<omega> t))) (ennreal T))"
    by (simp add: iexit_cap[OF T])
  finally show ?thesis .
qed

text \<open>Restricting a member of the uncapped class to \<open>[0,T]\<close> gives a competitor
  for @{const covariation_val} whose exit time is the uncapped one capped at \<open>T\<close>.
  Hence \<open>min (v, T) \<le> v\<^sub>T\<close>, one half of the identification of the two value
  functions.\<close>

theorem icovariation_val_cap_le:
  fixes K :: "(real^'n::finite) set"
  assumes T: "0 \<le> T" and Sc: "closed S" and Kc: "closed K"
  shows "min (icovariation_val S K x) (ennreal T) \<le> covariation_val S T K x"
proof -
  have step: "min (ess_inf P (\<lambda>\<omega>. iexit K (\<lambda>t. fst (\<omega> t)))) (ennreal T)
      \<le> covariation_val S T K x"
    if P: "P \<in> icovariation_class S x" for P :: "('n pairpath) measure"
  proof -
    have "min (ess_inf P (\<lambda>\<omega>. iexit K (\<lambda>t. fst (\<omega> t)))) (ennreal T)
        \<le> ess_inf P (\<lambda>\<omega>. min (iexit K (\<lambda>t. fst (\<omega> t))) (ennreal T))"
      by (rule ess_inf_min_const)
    also have "\<dots> = ess_inf_time (process_law T (pcut T) P)
        (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))"
      by (rule ess_inf_pexit_cut[OF T Kc icovariation_class_sets[OF P], symmetric])
    also have "\<dots> \<le> covariation_val S T K x"
      by (rule covariation_val_ge_ess_inf[OF icovariation_class_pcut[OF T Sc P]])
    finally show ?thesis .
  qed
  show ?thesis
  proof (cases "ennreal T \<le> covariation_val S T K x")
    case True
    then show ?thesis using min.cobounded2 order_trans by blast
  next
    case False
    then have lt: "covariation_val S T K x < ennreal T" by simp
    have "icovariation_val S K x \<le> covariation_val S T K x"
      unfolding icovariation_val_def
    proof (rule Sup_least)
      fix v assume "v \<in> (\<lambda>Q. ess_inf Q (\<lambda>\<omega>. iexit K (\<lambda>t. fst (\<omega> t))))
          ` icovariation_class S x"
      then obtain P :: "('n pairpath) measure"
        where P: "P \<in> icovariation_class S x"
          and v: "v = ess_inf P (\<lambda>\<omega>. iexit K (\<lambda>t. fst (\<omega> t)))" by blast
      have "min v (ennreal T) \<le> covariation_val S T K x" using step[OF P] v by simp
      then show "v \<le> covariation_val S T K x"
        using lt by (simp add: min_def split: if_splits)
    qed
    then show ?thesis using min.cobounded1 order_trans by blast
  qed
qed

subsection \<open>The converse, from an extension of a capped law\<close>

text \<open>The other half reduces to a single construction: every member of the
  horizon-\<open>T\<close> class is the cut of a member of the uncapped class.  Given that,
  the uncapped exit time dominates the capped one on the extension, and the
  inequality follows.  The construction itself is an application of
  @{thm [source] covariation_class_pglue_law}, whose continuation may be taken
  with any covariation rate \<open>\<sigma> \<sigma>\<^sup>T \<in> S\<close>.\<close>

theorem icovariation_val_ge_of_extension:
  fixes K :: "(real^'n::finite) set"
  assumes T: "0 \<le> T" and Kc: "closed K"
    and ext: "\<And>Q :: ('n pairpath) measure. Q \<in> covariation_class S T x \<Longrightarrow>
      \<exists>P \<in> icovariation_class S x. process_law T (pcut T) P = Q"
  shows "covariation_val S T K x \<le> icovariation_val S K x"
  unfolding covariation_val_def
proof (rule Sup_least)
  fix w assume "w \<in> (\<lambda>Q. ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))))
      ` covariation_class S T x"
  then obtain Q :: "('n pairpath) measure"
    where Q: "Q \<in> covariation_class S T x"
      and w: "w = ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))" by blast
  obtain P :: "('n pairpath) measure"
    where P: "P \<in> icovariation_class S x" and cut: "process_law T (pcut T) P = Q"
    using ext[OF Q] by blast
  have "w = ess_inf P (\<lambda>\<omega>. min (iexit K (\<lambda>t. fst (\<omega> t))) (ennreal T))"
    unfolding w cut[symmetric] by (rule ess_inf_pexit_cut[OF T Kc icovariation_class_sets[OF P]])
  also have "\<dots> \<le> ess_inf P (\<lambda>\<omega>. iexit K (\<lambda>t. fst (\<omega> t)))"
    by (rule ess_inf_mono) simp
  also have "\<dots> \<le> icovariation_val S K x"
    unfolding icovariation_val_def using P by (intro Sup_upper) blast
  finally show "w \<le> icovariation_val S K x" .
qed

subsection \<open>The two value functions agree once the horizon does not bind\<close>

text \<open>The hypothesis \<open>covariation_val S T K x < ennreal T\<close> is what the a priori
  bound @{thm [source] covariation_val_le_ball_bound} supplies for a bounded \<open>K\<close>
  and a horizon above \<open>rK\<^sup>2 / \<theta>\<close>: the capped value is then strictly below
  the cap.  With both halves, the two value functions coincide, and every
  statement about @{const covariation_val} is a statement about the value
  function on the half-line.\<close>

theorem icovariation_val_eq_of_extension:
  fixes K :: "(real^'n::finite) set"
  assumes T: "0 \<le> T" and Sc: "closed S" and Kc: "closed K"
    and nobind: "covariation_val S T K x < ennreal T"
    and ext: "\<And>Q :: ('n pairpath) measure. Q \<in> covariation_class S T x \<Longrightarrow>
      \<exists>P \<in> icovariation_class S x. process_law T (pcut T) P = Q"
  shows "icovariation_val S K x = covariation_val S T K x"
proof (rule antisym)
  have le: "min (icovariation_val S K x) (ennreal T) \<le> covariation_val S T K x"
    by (rule icovariation_val_cap_le[OF T Sc Kc])
  show "icovariation_val S K x \<le> covariation_val S T K x"
    using le nobind by (simp add: min_def split: if_splits)
next
  show "covariation_val S T K x \<le> icovariation_val S K x"
    by (rule icovariation_val_ge_of_extension[OF T Kc ext])
qed

subsection \<open>The Brownian continuation on the half-line\<close>

text \<open>Brownian motion pushed through \<open>\<sigma>\<close>, paired with its covariation
  \<open>t \<sigma> \<sigma>\<^sup>T\<close>, on the half-line.  Cutting it at \<open>U\<close> returns \<open>sbmpair \<sigma> U\<close>, so
  every cut of its law is the witness at that horizon and lies in the class.\<close>

definition ibmpair ::
  "real^'n::finite^'n \<Rightarrow> ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> 'n pairpath"
  where "ibmpair \<sigma> \<omega> =
    restrict (\<lambda>t. (\<sigma> *v cbmX 0 t \<omega>, t *\<^sub>R (\<sigma> ** transpose \<sigma>))) {0..}"

lemma pcut_ibmpair: "pcut U (ibmpair \<sigma> \<omega>) = sbmpair \<sigma> U \<omega>"
  by (rule ext) (auto simp: pcut_def ibmpair_def sbmpair_def)

lemma ibmpair_measurable:
  "(ibmpair \<sigma> :: ('n::finite \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> 'n pairpath)
      \<in> bm_paths \<rightarrow>\<^sub>M ipath_space"
proof -
  have "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. restrict
          (\<lambda>t. (\<sigma> *v cbmX (0 :: real^'n) t \<omega>, t *\<^sub>R (\<sigma> ** transpose \<sigma>))) {0..})
      \<in> bm_paths \<rightarrow>\<^sub>M ipath_space"
  proof (rule ipathify_measurable)
    fix t :: real assume "0 \<le> t"
    have c: "(\<lambda>v :: real^'n. (\<sigma> *v v, t *\<^sub>R (\<sigma> ** transpose \<sigma>)))
        \<in> borel_measurable borel"
      by (intro borel_measurable_continuous_onI continuous_on_Pair continuous_on_const
          continuous_on_compose2[OF linear_continuous_on[OF matrix_vector_mul_bounded_linear]
            continuous_on_id]) auto
    show "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real.
          (\<sigma> *v cbmX (0 :: real^'n) t \<omega>, t *\<^sub>R (\<sigma> ** transpose \<sigma>)))
        \<in> borel_measurable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)"
      by (rule measurable_compose[OF measurable_cbmX c])
  next
    fix \<omega> :: "'n \<Rightarrow> real \<Rightarrow> real"
    show "continuous_on {0..}
        (\<lambda>t. (\<sigma> *v cbmX (0 :: real^'n) t \<omega>, t *\<^sub>R (\<sigma> ** transpose \<sigma>)))"
      by (intro continuous_on_Pair linear_continuous_on[OF bounded_linear_scaleR_left]
          continuous_on_compose2[OF linear_continuous_on[OF matrix_vector_mul_bounded_linear]
            cbmX_cont]) auto
  qed
  then show ?thesis unfolding ibmpair_def by simp
qed

definition ibm_law :: "real^'n::finite^'n \<Rightarrow> ('n pairpath) measure"
  where "ibm_law \<sigma> = distr bm_paths ipath_space (ibmpair \<sigma>)"

lemma sets_ibm_law[simp]:
  "sets (ibm_law \<sigma> :: ('n::finite pairpath) measure) = sets ipath_space"
  unfolding ibm_law_def by simp

lemma prob_space_ibm_law: "prob_space (ibm_law \<sigma> :: ('n::finite pairpath) measure)"
  unfolding ibm_law_def
  by (rule BMP.prob_space_distr[OF ibmpair_measurable])

lemma process_law_pcut_ibm_law:
  assumes U: "0 \<le> U"
  shows "process_law U (pcut U) (ibm_law \<sigma> :: ('n::finite pairpath) measure)
      = process_law U (sbmpair \<sigma> U) bm_paths"
proof -
  have "process_law U (pcut U) (ibm_law \<sigma> :: ('n pairpath) measure)
      = distr bm_paths (path_borel U :: ('n pairpath) measure) (pcut U \<circ> ibmpair \<sigma>)"
    unfolding ibm_law_def process_law_def
    by (rule distr_distr[OF ipcut_measurable[OF U refl] ibmpair_measurable])
  also have "\<dots> = process_law U (sbmpair \<sigma> U) bm_paths"
    unfolding process_law_def by (simp add: comp_def pcut_ibmpair)
  finally show ?thesis .
qed

theorem ibm_law_cut_in_covariation_class:
  assumes U: "0 \<le> U" and Sc: "closed S" and SST: "\<sigma> ** transpose \<sigma> \<in> S"
  shows "process_law U (pcut U) (ibm_law \<sigma> :: ('n::finite pairpath) measure)
      \<in> covariation_class S U (0 :: real^'n)"
  unfolding process_law_pcut_ibm_law[OF U]
  by (rule sbmpair_law_in_covariation_class[OF U Sc SST])

subsection \<open>The extension of a horizon law to the half-line\<close>

text \<open>The extension of a horizon-\<open>T\<close> law \<open>Q\<close> to the half-line: glue the
  Brownian continuation onto \<open>Q\<close> at \<open>T\<close>.\<close>




definition iextend ::
  "real^'n::finite^'n \<Rightarrow> real \<Rightarrow> ('n pairpath) measure \<Rightarrow> ('n pairpath) measure"
  where "iextend \<sigma> T Q =
     distr (Q \<Otimes>\<^sub>M ibm_law \<sigma>) ipath_space (\<lambda>p. iglue T (fst p) (snd p))"

lemma sets_iextend[simp]:
  "sets (iextend \<sigma> T Q :: ('n::finite pairpath) measure) = sets ipath_space"
  unfolding iextend_def by simp

lemma iextend_measurable:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
  shows "(\<lambda>p. iglue T (fst p) (snd p)) \<in> Q \<Otimes>\<^sub>M ibm_law \<sigma> \<rightarrow>\<^sub>M ipath_space"
  by (rule iglue_measurable[OF T setsQ sets_ibm_law])

lemma prob_space_iextend:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T" and Q: "Q \<in> covariation_class S T x"
  shows "prob_space (iextend \<sigma> T Q)"
proof -
  interpret PQ: prob_space Q by (rule covariation_class_prob[OF Q])
  interpret PR: prob_space "ibm_law \<sigma> :: ('n pairpath) measure"
    by (rule prob_space_ibm_law)
  interpret PP: prob_space "Q \<Otimes>\<^sub>M (ibm_law \<sigma> :: ('n pairpath) measure)"
    by (rule prob_space_pair[OF PQ.prob_space_axioms
          PR.prob_space_axioms])
  show ?thesis
    unfolding iextend_def
    by (rule PP.prob_space_distr[OF iextend_measurable[OF T covariation_class_sets[OF Q]]])
qed

text \<open>Cutting the extension at a horizon beyond the glue point returns the
  compact concatenation, so @{thm [source] covariation_class_pglue_law} places every
  restriction of the extension in the class.\<close>

lemma process_law_pcut_iextend:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T" and TU: "T \<le> U" and Q: "Q \<in> covariation_class S T x"
  shows "process_law U (pcut U) (iextend \<sigma> T Q)
      = pglue_law T U Q (process_law (U - T) (pcut (U - T)) (ibm_law \<sigma>))"
proof -
  let ?B = "\<lambda>r. (path_borel r :: ('n pairpath) measure)"
  let ?R = "ibm_law \<sigma> :: ('n pairpath) measure"
  let ?g = "\<lambda>p :: 'n pairpath \<times> 'n pairpath. pglue T U (fst p) (snd p)"
  have U0: "0 \<le> U" using T TU by simp
  have UT0: "0 \<le> U - T" using TU by simp
  interpret PQ: prob_space Q by (rule covariation_class_prob[OF Q])
  interpret PR: prob_space ?R by (rule prob_space_ibm_law)
  have setsQ: "sets Q = sets (?B T)" by (rule covariation_class_sets[OF Q])
  have gm: "(\<lambda>p. iglue T (fst p) (snd p)) \<in> Q \<Otimes>\<^sub>M ?R \<rightarrow>\<^sub>M ipath_space"
    by (rule iextend_measurable[OF T setsQ])
  have cm: "pcut U \<in> (ipath_space :: ('n pairpath) measure) \<rightarrow>\<^sub>M ?B U"
    by (rule ipcut_measurable[OF U0 refl])
  have step1: "process_law U (pcut U) (iextend \<sigma> T Q)
      = distr (Q \<Otimes>\<^sub>M ?R) (?B U) ?g"
  proof -
    have "process_law U (pcut U) (iextend \<sigma> T Q)
        = distr (Q \<Otimes>\<^sub>M ?R) (?B U) (pcut U \<circ> (\<lambda>p. iglue T (fst p) (snd p)))"
      unfolding process_law_def iextend_def by (rule distr_distr[OF cm gm])
    also have "\<dots> = distr (Q \<Otimes>\<^sub>M ?R) (?B U) ?g"
      by (simp add: comp_def pcut_iglue[OF U0])
    finally show ?thesis .
  qed
  have cutm: "pcut (U - T) \<in> ?R \<rightarrow>\<^sub>M ?B (U - T)"
    by (rule ipcut_measurable[OF UT0 sets_ibm_law])
  have sf: "sigma_finite_measure (distr ?R (?B (U - T)) (pcut (U - T)))"
    using PR.prob_space_distr[OF cutm]
    by (simp add: prob_space_imp_sigma_finite)
  have prodeq: "Q \<Otimes>\<^sub>M (process_law (U - T) (pcut (U - T)) ?R)
      = distr (Q \<Otimes>\<^sub>M ?R) (?B T \<Otimes>\<^sub>M ?B (U - T))
          (\<lambda>p. (fst p, pcut (U - T) (snd p)))"
  proof -
    have "Q \<Otimes>\<^sub>M (process_law (U - T) (pcut (U - T)) ?R)
        = distr Q (?B T) (\<lambda>u. u) \<Otimes>\<^sub>M distr ?R (?B (U - T)) (pcut (U - T))"
      unfolding process_law_def by (simp add: distr_id2[OF setsQ[symmetric]])
    also have "\<dots> = distr (Q \<Otimes>\<^sub>M ?R) (?B T \<Otimes>\<^sub>M ?B (U - T))
        (\<lambda>(u, v). (u, pcut (U - T) v))"
      by (rule pair_measure_distr[OF measurable_ident_sets[OF setsQ] cutm sf])
    also have "\<dots> = distr (Q \<Otimes>\<^sub>M ?R) (?B T \<Otimes>\<^sub>M ?B (U - T))
        (\<lambda>p. (fst p, pcut (U - T) (snd p)))"
    proof -
      have "(\<lambda>(u, v). (u, pcut (U - T) v))
          = (\<lambda>p :: 'n pairpath \<times> 'n pairpath. (fst p, pcut (U - T) (snd p)))"
        by auto
      then show ?thesis by simp
    qed
    finally show ?thesis .
  qed
  have pgm: "?g \<in> ?B T \<Otimes>\<^sub>M ?B (U - T) \<rightarrow>\<^sub>M ?B U"
    by (rule pglue_measurable[OF T TU refl refl])
  have pairm: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. (fst p, pcut (U - T) (snd p)))
      \<in> Q \<Otimes>\<^sub>M ?R \<rightarrow>\<^sub>M ?B T \<Otimes>\<^sub>M ?B (U - T)"
    by (intro measurable_Pair measurable_compose[OF measurable_snd cutm]
        measurable_compose[OF measurable_fst measurable_ident_sets[OF setsQ]])
  have "pglue_law T U Q (process_law (U - T) (pcut (U - T)) ?R)
      = distr (Q \<Otimes>\<^sub>M (process_law (U - T) (pcut (U - T)) ?R)) (?B U) ?g"
    unfolding pglue_law_def process_law_def ..
  also have "\<dots> = distr (Q \<Otimes>\<^sub>M ?R) (?B U)
      (?g \<circ> (\<lambda>p. (fst p, pcut (U - T) (snd p))))"
    unfolding prodeq by (rule distr_distr[OF pgm pairm])
  also have "\<dots> = distr (Q \<Otimes>\<^sub>M ?R) (?B U) ?g"
    by (simp add: comp_def pglue_pcut[OF T TU])
  finally show ?thesis unfolding step1 ..
qed

theorem iextend_cut_in_covariation_class:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T" and TU: "T \<le> U" and Sc: "closed S" and Sv: "convex S"
    and SST: "\<sigma> ** transpose \<sigma> \<in> S" and Q: "Q \<in> covariation_class S T x"
  shows "process_law U (pcut U) (iextend \<sigma> T Q) \<in> covariation_class S U x"
proof -
  have UT0: "0 \<le> U - T" using TU by simp
  show ?thesis
    unfolding process_law_pcut_iextend[OF T TU Q]
    by (rule covariation_class_pglue_law[OF T TU Sc Sv Q
          ibm_law_cut_in_covariation_class[OF UT0 Sc SST]])
qed

text \<open>At the glue point itself the extension restricts to the law it
  extends: this is the identity the bridge asks for.\<close>

theorem pcut_law_iextend:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T" and Q: "Q \<in> covariation_class S T x"
  shows "process_law T (pcut T) (iextend \<sigma> T Q) = Q"
proof -
  let ?B = "\<lambda>r. (path_borel r :: ('n pairpath) measure)"
  let ?R = "ibm_law \<sigma> :: ('n pairpath) measure"
  interpret PQ: prob_space Q by (rule covariation_class_prob[OF Q])
  interpret PR: prob_space ?R by (rule prob_space_ibm_law)
  have setsQ: "sets Q = sets (?B T)" by (rule covariation_class_sets[OF Q])
  have gm: "(\<lambda>p. iglue T (fst p) (snd p)) \<in> Q \<Otimes>\<^sub>M ?R \<rightarrow>\<^sub>M ipath_space"
    by (rule iextend_measurable[OF T setsQ])
  have cm: "pcut T \<in> (ipath_space :: ('n pairpath) measure) \<rightarrow>\<^sub>M ?B T"
    by (rule ipcut_measurable[OF T refl])
  have "process_law T (pcut T) (iextend \<sigma> T Q)
      = distr (Q \<Otimes>\<^sub>M ?R) (?B T) (pcut T \<circ> (\<lambda>p. iglue T (fst p) (snd p)))"
    unfolding process_law_def iextend_def by (rule distr_distr[OF cm gm])
  also have "\<dots> = distr (Q \<Otimes>\<^sub>M ?R) (?B T) (\<lambda>p. pcut T (fst p))"
    by (simp add: comp_def pcut_iglue[OF T] pglue_self)
  also have "\<dots> = distr (Q \<Otimes>\<^sub>M ?R) Q fst"
  proof (rule distr_cong[OF refl setsQ[symmetric]])
    fix p :: "'n pairpath \<times> 'n pairpath"
    assume "p \<in> space (Q \<Otimes>\<^sub>M ?R)"
    then have "fst p \<in> space Q" by (auto simp: space_pair_measure)
    then show "pcut T (fst p) = fst p"
      using space_of_path_sets[OF setsQ] by (simp add: pcut_def mspace_path_restrict_self)
  qed
  also have "\<dots> = Q" by (rule PR.distr_pair_fst)
  finally show ?thesis .
qed

subsection \<open>Martingales from the restrictions\<close>

text \<open>Every cut of the extension lies in the capped class, below \<open>T\<close> as well
  as beyond.  A process on the half-line that is a martingale under every
  cut law is a martingale, since cutting beyond \<open>u\<close> identifies the two
  natural filtrations at \<open>u\<close>; so the extension lies in the uncapped class.\<close>




lemma iextend_pcut_in_covariation_class:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T" and U: "0 \<le> U" and Sc: "closed S" and Sv: "convex S"
    and SST: "\<sigma> ** transpose \<sigma> \<in> S" and Q: "Q \<in> covariation_class S T x"
  shows "process_law U (pcut U) (iextend \<sigma> T Q) \<in> covariation_class S U x"
proof (cases "T \<le> U")
  case True
  then show ?thesis by (rule iextend_cut_in_covariation_class[OF T _ Sc Sv SST Q])
next
  case False
  let ?B = "\<lambda>r. (path_borel r :: ('n pairpath) measure)"
  have UT: "U \<le> T" using False by simp
  have "process_law U (pcut U) Q
      = process_law U (pcut U) (process_law T (pcut T) (iextend \<sigma> T Q))"
    unfolding pcut_law_iextend[OF T Q] ..
  also have "\<dots> = distr (iextend \<sigma> T Q) (?B U) (pcut U \<circ> pcut T)"
    unfolding process_law_def
    by (rule distr_distr[OF pcut_measurable[OF U UT refl]
          ipcut_measurable[OF T sets_iextend]])
  also have "\<dots> = process_law U (pcut U) (iextend \<sigma> T Q)"
    unfolding process_law_def by (simp add: comp_def pcut_pcut[OF UT])
  finally show ?thesis using covariation_class_pcut[OF U UT Sc Q] by simp
qed

lemma martingale_of_cut_laws:
  fixes P :: "((real \<Rightarrow> 'a::{polish_space,banach} \<times> 'x::{polish_space,banach})) measure"
    and f :: "'a \<times> 'x \<Rightarrow> 'b::{banach,second_countable_topology}"
  assumes prob: "prob_space P"
    and setsP: "sets P = sets (ipath_space :: ((real \<Rightarrow> 'a \<times> 'x)) measure)"
    and f: "f \<in> borel_measurable borel"
    and mg: "\<And>S. 0 \<le> S \<Longrightarrow> martingale (process_law S (pcut S) P)
        (natural_filtration (process_law S (pcut S) P) 0 (\<lambda>v \<omega>. \<omega> v)) 0
        (\<lambda>u \<omega>. f (\<omega> (min u S)))"
  shows "martingale P (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v)) 0 (\<lambda>u \<omega>. f (\<omega> u))"
proof (rule martingale_of_cuts[OF prob setsP])
  fix u :: real assume u: "0 \<le> u"
  have "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'x). \<omega> u)
      \<in> borel_measurable (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) u)"
    by (rule natural_filtration_eval) (use u in auto)
  then show "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'x). f (\<omega> u))
      \<in> borel_measurable (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) u)"
    by (rule measurable_compose[OF _ f])
next
  fix u S :: real and \<omega> :: "real \<Rightarrow> 'a \<times> 'x"
  assume "0 \<le> u" "u \<le> S"
  then show "f (pcut S \<omega> u) = f (\<omega> u)" by (simp add: pcut_def)
next
  fix S :: real assume "0 \<le> S"
  then show "martingale (process_law S (pcut S) P)
      (natural_filtration (process_law S (pcut S) P) 0 (\<lambda>v \<omega>. \<omega> v)) 0
      (\<lambda>u \<omega>. f (\<omega> (min u S)))"
    by (rule mg)
qed

theorem iextend_in_icovariation_class:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T" and Sc: "closed S" and Sv: "convex S"
    and SST: "\<sigma> ** transpose \<sigma> \<in> S" and Q: "Q \<in> covariation_class S T x"
  shows "iextend \<sigma> T Q \<in> icovariation_class S x"
proof -
  let ?P = "iextend \<sigma> T Q"
  let ?G = "natural_filtration ?P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  have prob: "prob_space ?P" by (rule prob_space_iextend[OF T Q])
  have cutm: "pcut U \<in> ?P \<rightarrow>\<^sub>M (path_borel U :: ('n pairpath) measure)" if U: "0 \<le> U" for U
    by (rule ipcut_measurable[OF U sets_iextend])
  have cls: "process_law U (pcut U) ?P \<in> covariation_class S U x" if U: "0 \<le> U" for U
    by (rule iextend_pcut_in_covariation_class[OF T U Sc Sv SST Q])

  \<comment> \<open>clause (i): the initial condition\<close>
  have start: "AE \<omega> in ?P. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
  proof -
    have "AE \<omega> in process_law T (pcut T) ?P. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
      by (rule covariation_class_start[OF cls[OF T]])
    then have "AE \<omega> in ?P. fst (pcut T \<omega> 0) = x \<and> snd (pcut T \<omega> 0) = 0"
      unfolding process_law_def by (rule AE_distrD[OF cutm[OF T]])
    then show ?thesis using T by (simp add: pcut_def)
  qed

  \<comment> \<open>clause (ii): the covariation constraint, at every pair of times\<close>
  have dq: "AE \<omega> in ?P. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> S"
  proof -
    have step: "AE \<omega> in ?P. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T + real n \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> S" for n :: nat
    proof -
      have U: "0 \<le> T + real n" using T by simp
      have "AE \<omega> in process_law (T + real n) (pcut (T + real n)) ?P.
          \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T + real n \<longrightarrow>
            (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> S"
        by (rule covariation_class_diffquot[OF cls[OF U]])
      then have "AE \<omega> in ?P. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T + real n \<longrightarrow>
          (1 / (t - s)) *\<^sub>R (snd (pcut (T + real n) \<omega> t)
            - snd (pcut (T + real n) \<omega> s)) \<in> S"
        unfolding process_law_def by (rule AE_distrD[OF cutm[OF U]])
      then show ?thesis by eventually_elim (auto simp: pcut_def)
    qed
    have "AE \<omega> in ?P. \<forall>n :: nat. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T + real n \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> S"
      using step by (subst AE_all_countable) blast
    then show ?thesis
    proof eventually_elim
      case (elim \<omega>)
      show ?case
      proof (intro allI impI)
        fix s t :: real assume st: "0 \<le> s" "s < t"
        obtain n :: nat where "t < real n" using reals_Archimedean2 by blast
        then have "t \<le> T + real n" using T by simp
        then show "(1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> S"
          using elim st by blast
      qed
    qed
  qed

  \<comment> \<open>clauses (iii) and (iv): the martingales, from those of the cuts\<close>
  have Xmg: "martingale ?P ?G 0 (\<lambda>u \<omega>. fst (\<omega> u) :: real^'n)"
    by (rule martingale_of_cut_laws[OF prob sets_iextend pair_fst_borel])
      (rule covariation_class_martingale_fst[OF cls])
  have Cmg: "martingale ?P ?G 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> u) :: real^'n) - snd (\<omega> u))"
    by (rule martingale_of_cut_laws[OF prob sets_iextend compensated_map_borel])
      (rule covariation_class_martingale_compensated[OF cls])

  show ?thesis
    unfolding icovariation_class_def mem_Collect_eq
    using prob sets_iextend start dq Xmg Cmg by blast
qed

text \<open>The construction the bridge was reduced to: every member of the
  horizon-\<open>T\<close> class is the restriction of a member of the uncapped class,
  as soon as \<open>S\<close> is closed, convex and contains one rate \<open>\<sigma> \<sigma>\<^sup>T\<close>.\<close>

theorem covariation_class_has_extension:
  fixes Q :: "('n::finite pairpath) measure" and \<sigma> :: "real^'n^'n"
  assumes T: "0 \<le> T" and Sc: "closed S" and Sv: "convex S"
    and SST: "\<sigma> ** transpose \<sigma> \<in> S" and Q: "Q \<in> covariation_class S T x"
  shows "\<exists>P \<in> icovariation_class S x. process_law T (pcut T) P = Q"
  using iextend_in_icovariation_class[OF T Sc Sv SST Q] pcut_law_iextend[OF T Q] by blast

subsection \<open>The two value functions, unconditionally\<close>

text \<open>With the construction in place, both hypotheses of
  @{thm [source] icovariation_val_eq_of_extension} that were about the class are
  discharged, and only the standing assumptions on \<open>S\<close> remain.\<close>

theorem icovariation_val_eq_covariation_val:
  fixes K :: "(real^'n::finite) set"
    and \<sigma> :: "real^'n^'n"
  assumes T: "0 \<le> T" and Sc: "closed S" and Sv: "convex S"
    and SST: "\<sigma> ** transpose \<sigma> \<in> S" and Kc: "closed K"
    and nobind: "covariation_val S T K x < ennreal T"
  shows "icovariation_val S K x = covariation_val S T K x"
  by (rule icovariation_val_eq_of_extension[OF T Sc Kc nobind
        covariation_class_has_extension[OF T Sc Sv SST]])

text \<open>For a bounded \<open>K\<close> the a priori bound
  @{thm [source] covariation_val_le_ball_bound} makes the remaining hypothesis a
  condition on the horizon alone, so the value function on the half-line is
  the capped one at every horizon past the scale \<open>(r\<^sup>2 - |x|\<^sup>2)/\<theta>\<close>, \<open>\<theta>\<close> a
  lower bound for the trace on \<open>S\<close>.\<close>

corollary icovariation_val_eq_covariation_val_bounded:
  fixes K :: "(real^'n::finite) set" and r :: real
    and \<sigma> :: "real^'n^'n"
  assumes T: "0 < T" and Sc: "closed S" and Sv: "convex S"
    and SST: "\<sigma> ** transpose \<sigma> \<in> S"
    and B0: "0 \<le> B" and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and th0: "0 < \<theta>" and th: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> \<theta> \<le> trace a"
    and Kc: "closed K" and KB: "K \<subseteq> cball 0 r"
    and big: "(r * r - x \<bullet> x) / \<theta> < T"
  shows "icovariation_val S K x = covariation_val S T K x"
proof (rule icovariation_val_eq_covariation_val[OF less_imp_le[OF T] Sc Sv SST Kc])
  have "covariation_val S T K x \<le> ennreal ((r * r - x \<bullet> x) / \<theta>)"
    by (rule covariation_val_le_ball_bound[OF less_imp_le[OF T] B0 B th0 th KB])
  also have "\<dots> < ennreal T" by (rule ennreal_lessI[OF T big])
  finally show "covariation_val S T K x < ennreal T" .
qed

text \<open>The bound is largest at the centre, so the hypothesis is uniform in
  \<open>x\<close>: one horizon beyond \<open>r\<^sup>2/\<theta>\<close> identifies the two value functions
  everywhere at once, which is what a clause quantified over points needs.\<close>

corollary icovariation_val_eq_covariation_val_ball:
  fixes K :: "(real^'n::finite) set" and rK :: real
    and \<sigma> :: "real^'n^'n"
  assumes Sc: "closed S" and Sv: "convex S" and SST: "\<sigma> ** transpose \<sigma> \<in> S"
    and B0: "0 \<le> B" and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and th0: "0 < \<theta>" and th: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> \<theta> \<le> trace a"
    and Kc: "closed K" and KB: "K \<subseteq> cball 0 rK"
    and big: "rK * rK / \<theta> < T"
  shows "icovariation_val S K x = covariation_val S T K x"
proof (rule icovariation_val_eq_covariation_val_bounded[OF _ Sc Sv SST B0 B th0 th Kc KB])
  have "0 \<le> rK * rK / \<theta>" using th0 by simp
  then show "0 < T" using big by (rule order.strict_trans1)
  have "(rK * rK - x \<bullet> x) / \<theta> \<le> rK * rK / \<theta>"
    using th0 by (intro divide_right_mono) auto
  then show "(rK * rK - x \<bullet> x) / \<theta> < T" using big by simp
qed

text \<open>Such a horizon always exists, so for a bounded closed \<open>K\<close> the value
  function on the half-line is a capped one, as a function; the horizon also
  clears the doubled scale \<open>2r\<^sup>2/\<theta>\<close> that the cap-inertness argument needs.\<close>

corollary icovariation_val_eq_covariation_val_horizon:
  fixes K :: "(real^'n::finite) set" and rK :: real
    and \<sigma> :: "real^'n^'n"
  assumes Sc: "closed S" and Sv: "convex S" and SST: "\<sigma> ** transpose \<sigma> \<in> S"
    and B0: "0 \<le> B" and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and th0: "0 < \<theta>" and th: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> \<theta> \<le> trace a"
    and Kc: "closed K" and KB: "K \<subseteq> cball 0 rK"
  obtains T where "0 < T" and "rK * rK / \<theta> < T" and "2 * (rK * rK) / \<theta> < T"
    and "icovariation_val S K = covariation_val S T K"
proof -
  define T where "T = 2 * (rK * rK) / \<theta> + 1"
  have le: "rK * rK / \<theta> \<le> 2 * (rK * rK) / \<theta>"
    using th0 by (intro divide_right_mono) auto
  have ge: "0 \<le> 2 * (rK * rK) / \<theta>" using th0 by simp
  have T0: "0 < T" unfolding T_def by (rule add_nonneg_pos[OF ge]) simp
  have T1: "rK * rK / \<theta> < T"
    unfolding T_def by (rule order.strict_trans1[OF le less_add_one])
  have T2: "2 * (rK * rK) / \<theta> < T"
    unfolding T_def by (rule less_add_one)
  have "icovariation_val S K = covariation_val S T K"
    by (rule ext) (rule icovariation_val_eq_covariation_val_ball[OF Sc Sv SST B0 B th0 th Kc KB T1])
  then show ?thesis by (rule that[OF T0 T1 T2])
qed

(*<*)
end
(*>*)
