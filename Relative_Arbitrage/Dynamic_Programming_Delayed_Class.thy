section \<open>The delayed class and the horizon-parametrised selector\<close>

(*<*)
theory Dynamic_Programming_Delayed_Class
  imports Dynamic_Programming_Additive_Glue
    "Continuous_Time_Martingales.Integrability_Criteria"
    "Continuous_Path_Spaces.Increment_Moments"
    "Continuous_Time_Martingales.Essential_Infimum"
    "Continuous_Path_Spaces.Path_Exit_Times"
    Path_Law_Sampling
begin

(*>*)

section \<open>The delayed class on a fixed space\<close>




definition pdelclass :: "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real
    \<Rightarrow> (('n::finite pairpath) measure) set"
  where "pdelclass k L T s =
     (\<lambda>\<nu>. distr \<nu> (path_borel T :: ('n pairpath) measure) (pembed s T))
       ` exit_class k L (T - s) (0::real^'n)"

text \<open>A delayed law is a probability law on the \<open>T\<close>-space, it stands still on
  \<open>[0,s]\<close>, and re-basing recovers the original --- which is what makes
  \<^const>\<open>pdelclass\<close> the right object for the additive glue to consume.\<close>

lemma pdelclass_prob:
  fixes \<nu> :: "('n::finite pairpath) measure"
  assumes s0: "0 \<le> s" and sT: "s \<le> T" and m: "\<nu> \<in> pdelclass k L T s"
  shows "prob_space \<nu>"
    and "sets \<nu> = sets (path_borel T :: ('n pairpath) measure)"
proof -
  from m obtain \<mu> where mu: "\<mu> \<in> exit_class k L (T - s) (0::real^'n)"
    and nu: "\<nu> = distr \<mu> (path_borel T :: ('n pairpath) measure) (pembed s T)"
    unfolding pdelclass_def by blast
  have setsmu: "sets \<mu> = sets ((path_borel (T - s) :: ('n pairpath) measure))"
    by (rule exit_class_sets[OF mu])
  have pm: "pembed s T \<in> \<mu> \<rightarrow>\<^sub>M (path_borel T :: ('n pairpath) measure)"
    unfolding measurable_cong_sets[OF setsmu refl]
    by (rule pembed_measurable[OF s0 sT])
  show "prob_space \<nu>"
    unfolding nu
    by (rule prob_space.prob_space_distr[OF exit_class_prob[OF mu] pm])
  show "sets \<nu> = sets (path_borel T :: ('n pairpath) measure)" unfolding nu by simp
qed

lemma pdelclass_frozen_at:
  fixes \<nu> :: "('n::finite pairpath) measure"
  assumes s0: "0 \<le> s" and sT: "s \<le> T" and m: "\<nu> \<in> pdelclass k L T s"
    and u: "u \<in> {0..T}" and us: "u \<le> s"
  shows "AE w in \<nu>. w u = 0"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  from m obtain \<mu> where mu: "\<mu> \<in> exit_class k L (T - s) (0::real^'n)"
    and nu: "\<nu> = distr \<mu> ?B (pembed s T)"
    unfolding pdelclass_def by blast
  have setsmu: "sets \<mu> = sets ((path_borel (T - s) :: ('n pairpath) measure))"
    by (rule exit_class_sets[OF mu])
  have pm: "pembed s T \<in> \<mu> \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsmu refl]
    by (rule pembed_measurable[OF s0 sT])
  have ev: "(\<lambda>w :: 'n pairpath. w u) \<in> borel_measurable ?B"
    by (rule pair_law_eval_measurable[OF refl])
  have Phi: "{w \<in> space ?B. w u = 0} \<in> sets ?B"
  proof -
    have "{w \<in> space ?B. w u = 0}
        = (\<lambda>w :: 'n pairpath. w u) -` {0} \<inter> space ?B" by auto
    then show ?thesis
      using measurable_sets[OF ev borel_closed[OF closed_singleton]] by simp
  qed
  have start: "AE v in \<mu>. fst (v 0) = 0 \<and> snd (v 0) = 0"
    by (rule exit_class_start[OF mu])
  have "AE v in \<mu>. pembed s T v u = 0"
    using start
  proof eventually_elim
    case (elim v)
    have "max (u - s) 0 = 0" using us by simp
    then have "pembed s T v u = v 0" unfolding pembed_apply[OF u] by simp
    then show ?case using elim by (simp add: prod_eq_iff)
  qed
  then show ?thesis unfolding nu AE_distr_iff[OF pm Phi] .
qed

text \<open>\<open>vanishes_of_rational\<close> lives in @{theory Continuous_Path_Spaces.Increment_Moments}.\<close>



lemma pdelclass_frozen:
  fixes \<nu> :: "('n::finite pairpath) measure"
  assumes s0: "0 \<le> s" and sT: "s \<le> T" and m: "\<nu> \<in> pdelclass k L T s"
  shows "AE w in \<nu>. \<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> s \<longrightarrow> w u = 0"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  have T0: "0 \<le> T" using s0 sT by simp
  from m obtain \<mu> where mu: "\<mu> \<in> exit_class k L (T - s) (0::real^'n)"
    and nu: "\<nu> = distr \<mu> ?B (pembed s T)"
    unfolding pdelclass_def by blast
  have setsmu: "sets \<mu> = sets ((path_borel (T - s) :: ('n pairpath) measure))"
    by (rule exit_class_sets[OF mu])
  have pm: "pembed s T \<in> \<mu> \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsmu refl]
    by (rule pembed_measurable[OF s0 sT])
  have Phi: "{w \<in> space ?B. \<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> s \<longrightarrow> w u = 0} \<in> sets ?B"
    by (rule frozen_set_measurable[OF T0])
  have start: "AE v in \<mu>. fst (v 0) = 0 \<and> snd (v 0) = 0"
    by (rule exit_class_start[OF mu])
  have "AE v in \<mu>. \<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> s \<longrightarrow> pembed s T v u = 0"
    using start
  proof eventually_elim
    case (elim v)
    show ?case
    proof (intro allI impI)
      fix u assume uT: "u \<in> {0..T}" and us: "u \<le> s"
      have "max (u - s) 0 = 0" using us by simp
      then have "pembed s T v u = v 0" unfolding pembed_apply[OF uT] by simp
      then show "pembed s T v u = 0" using elim by (simp add: prod_eq_iff)
    qed
  qed
  then show ?thesis unfolding nu AE_distr_iff[OF pm Phi] .
qed

section \<open>The horizon enters the value only as a cap\<close>

text \<open>A single identity reduces the horizon-parametrised selector to a
  pushforward, not a new selection theorem: the capped exit time at a
  shorter horizon is the capped exit time at the longer one, capped again
  --- \<^term>\<open>pexit S K f = min (pexit T K f) S\<close>.  Capping by a constant
  commutes with the essential infimum and with the supremum over the
  class, so the horizon acts on the value function as an outer \<open>min\<close> and
  not on which law is optimal.  Consequently one selector, built once at
  the full horizon \<open>T\<close>, is optimal at every shorter horizon, and the
  parameter \<open>s\<close> is carried through only by a pushforward.\<close>



theorem exit_val_horizon_cap:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
  assumes S0: "0 \<le> S" and ST: "S \<le> T" and L: "1 \<le> L" and K: "closed K"
  shows "exit_val k L S K x = min (exit_val k L T K x) (ennreal S)"
proof (rule order.antisym)
  show "exit_val k L S K x \<le> min (exit_val k L T K x) (ennreal S)"
    by (intro min.boundedI exit_val_horizon_mono[OF S0 ST L K] exit_val_le_T[OF S0])
  show "min (exit_val k L T K x) (ennreal S) \<le> exit_val k L S K x"
  proof (rule ccontr)
    let ?BS = "(path_borel S :: ('n pairpath) measure)"
    assume "\<not> min (exit_val k L T K x) (ennreal S) \<le> exit_val k L S K x"
    then have "exit_val k L S K x < min (exit_val k L T K x) (ennreal S)"
      by (rule not_le_imp_less)
    then obtain b where b1: "exit_val k L S K x < b"
      and b2: "b < min (exit_val k L T K x) (ennreal S)"
      using ennreal_strict_between by blast
    from b2 have bT: "b < exit_val k L T K x"
      by (rule order.strict_trans2[OF _ min.cobounded1])
    from b2 have bS: "b < ennreal S"
      by (rule order.strict_trans2[OF _ min.cobounded2])
    from bT have "b < Sup ((\<lambda>Q. ess_inf_time Q
        (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))) ` exit_class k L T x)"
      unfolding exit_val_def .
    then obtain Q :: "('n pairpath) measure"
      where Q: "Q \<in> exit_class k L T x"
        and bQ: "b < ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))"
      by (auto simp: less_Sup_iff)
    have setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
      by (rule exit_class_sets[OF Q])
    have PQ: "prob_space Q" by (rule exit_class_prob[OF Q])
    have cutm: "pcut S \<in> Q \<rightarrow>\<^sub>M ?BS" by (rule pcut_measurable[OF S0 ST setsQ])
    have taum: "(\<lambda>\<omega> :: 'n pairpath. pexit S K (\<lambda>t. fst (\<omega> t)))
        \<in> borel_measurable ?BS"
    proof -
      have "(\<lambda>\<omega> :: 'n pairpath. pexit S K (pfst S \<omega>)) \<in> borel_measurable ?BS"
        by (rule measurable_compose[OF pfst_measurable[OF S0 refl]
              pexit_measurable[OF S0 K]])
      then show ?thesis by (simp add: pexit_pfst)
    qed
    have mset: "{\<omega> \<in> space ?BS. c \<le> ennreal (pexit S K (\<lambda>t. fst (\<omega> t)))}
        \<in> sets ?BS" for c :: ennreal using taum by measurable
    have "ess_inf_time (pair_law_of S (pcut S) Q)
          (\<lambda>\<omega>. pexit S K (\<lambda>t. fst (\<omega> t)))
        = ess_inf_time Q (\<lambda>\<omega>. pexit S K (\<lambda>t. fst (pcut S \<omega> t)))"
      unfolding pair_law_of_def by (rule ess_inf_time_distr[OF cutm mset])
    also have "\<dots> = ess_inf_time Q (\<lambda>\<omega>. min (pexit T K (\<lambda>t. fst (\<omega> t))) S)"
    proof (rule arg_cong[where f = "ess_inf_time Q"], rule ext)
      fix \<omega> :: "'n pairpath"
      have "pexit S K (\<lambda>t. fst (pcut S \<omega> t)) = pexit S K (\<lambda>t. fst (\<omega> t))"
        by (rule pexit_cong_on) (auto simp: pcut_apply)
      then show "pexit S K (\<lambda>t. fst (pcut S \<omega> t))
          = min (pexit T K (\<lambda>t. fst (\<omega> t))) S"
        using pexit_min_horizon[OF S0 ST, of K "\<lambda>t. fst (\<omega> t)"] by simp
    qed
    also have "\<dots> = min (ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))))
        (ennreal S)"
      by (rule ess_inf_time_min_const[OF PQ])
    finally have val: "ess_inf_time (pair_law_of S (pcut S) Q)
          (\<lambda>\<omega>. pexit S K (\<lambda>t. fst (\<omega> t)))
        = min (ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))) (ennreal S)" .
    have inS: "pair_law_of S (pcut S) Q \<in> exit_class k L S x"
      by (rule exit_class_pcut[OF S0 ST Q])
    have "b < min (ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))) (ennreal S)"
      using bQ bS by simp
    also have "\<dots> = ess_inf_time (pair_law_of S (pcut S) Q)
        (\<lambda>\<omega>. pexit S K (\<lambda>t. fst (\<omega> t)))" using val ..
    also have "\<dots> \<le> exit_val k L S K x"
      unfolding exit_val_def using inS by (intro Sup_upper imageI)
    finally show False using b1 by simp
  qed
qed

section \<open>The horizon-parametrised measurable selector\<close>

text \<open>@{thm [source] exit_val_horizon_cap} turns the selection problem into a
  pushforward problem.  The optimizer of the capped value is the optimizer
  of the uncapped one --- capping is an outer \<open>min\<close>, which is monotone ---
  so the selector \<^emph>\<open>at the full horizon\<close> already selects optimally at
  every shorter horizon, once it is cut there.  The parameter \<open>s\<close>
  therefore enters only through the map \<^const>\<open>pembed\<close>, and what has to
  be proved is joint measurability of a pushforward, not a new selection
  theorem.

  Three small facts make the composite work.  First, \<^const>\<open>pembed\<close> reads
  a path only on \<open>[0,T-s]\<close>, so pre-cutting is invisible to it
  (\<open>pembed_pcut\<close>) --- which is what identifies the pushforward of a
  \<open>T\<close>-law with the pushforward of its cut, i.e. with a member of
  \<^const>\<open>pdelclass\<close>.  Second, \<^const>\<open>pembed\<close> maps the \<open>T\<close>-space to itself
  (\<open>pembed_mspace_full\<close>), so no horizon bookkeeping is needed.  Third,
  clamping \<open>s\<close> to \<open>[0,T]\<close> makes the map total, and then
  @{thm [source] path_eval_at_measurable_time} gives joint measurability in
  the pair \<open>(s,\<omega>)\<close>: each evaluation of \<open>pembed s T \<omega>\<close> is the evaluation
  of \<open>\<omega>\<close> at a time that depends measurably on \<open>s\<close>.\<close>















theorem exit_val_measurable_selector_horizon:
  fixes K :: "(real^'n::finite) set"
  assumes T: "0 < T" and L: "1 \<le> L" and K: "closed K"
  obtains Sel where
    "Sel \<in> (borel :: real measure) \<Otimes>\<^sub>M (borel :: (real^'n) measure)
        \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and "\<And>s y. 0 \<le> s \<Longrightarrow> s \<le> T \<Longrightarrow> Sel (s, y) \<in> pdelclass k L T s"
    and "\<And>s y. 0 \<le> s \<Longrightarrow> s \<le> T \<Longrightarrow>
        distr (Sel (s, y)) ((path_borel (T - s) :: ('n pairpath) measure)) (prebase s T)
          \<in> exit_class k L (T - s) (0 :: real^'n)"
    and "\<And>s y. 0 \<le> s \<Longrightarrow> s \<le> T \<Longrightarrow>
        ess_inf_time (pshift_law (T - s) y
            (distr (Sel (s, y)) ((path_borel (T - s) :: ('n pairpath) measure)) (prebase s T)))
          (\<lambda>\<omega>. pexit (T - s) K (\<lambda>t. fst (\<omega> t))) = exit_val k L (T - s) K y"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?P = "(borel :: real measure) \<Otimes>\<^sub>M (borel :: (real^'n) measure)"
  have T0: "0 \<le> T" using T by simp
  obtain S0 where S0k: "S0 \<in> borel \<rightarrow>\<^sub>M prob_algebra ?B"
    and S0C: "\<And>y. S0 y \<in> exit_class k L T (0 :: real^'n)"
    and S0val: "\<And>y. ess_inf_time (pshift_law T y (S0 y))
        (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))) = exit_val k L T K y"
    by (rule exit_val_measurable_selector_kernel'[where k = k, OF T L K]) blast
  have setsS0: "sets (S0 y) = sets ?B" for y by (rule exit_class_sets[OF S0C])
  have PS0: "prob_space (S0 y)" for y by (rule exit_class_prob[OF S0C])
  define Sel where "Sel = (\<lambda>p :: real \<times> (real^'n).
      distr (S0 (snd p)) ?B (pdel (fst p) T))"

  \<comment> \<open>joint measurability: a pushforward along a jointly measurable map\<close>
  have fm: "case_prod (\<lambda>p :: real \<times> (real^'n). pdel (fst p) T)
      \<in> ?P \<Otimes>\<^sub>M ?B \<rightarrow>\<^sub>M ?B"
  proof -
    have m1: "(\<lambda>q :: (real \<times> (real^'n)) \<times> ('n pairpath). (fst (fst q), snd q))
        \<in> ?P \<Otimes>\<^sub>M ?B \<rightarrow>\<^sub>M (borel :: real measure) \<Otimes>\<^sub>M ?B" by measurable
    have "(\<lambda>q :: (real \<times> (real^'n)) \<times> ('n pairpath).
        pdel (fst (fst q)) T (snd q)) \<in> ?P \<Otimes>\<^sub>M ?B \<rightarrow>\<^sub>M ?B"
      using measurable_compose[OF m1 pdel_measurable_pair[OF T0]] by simp
    then show ?thesis by (simp add: case_prod_beta)
  qed
  have gm: "(\<lambda>p :: real \<times> (real^'n). S0 (snd p)) \<in> ?P \<rightarrow>\<^sub>M subprob_algebra ?B"
    by (rule measurable_prob_algebraD[OF measurable_compose[OF measurable_snd S0k]])
  have Selm: "Sel \<in> ?P \<rightarrow>\<^sub>M prob_algebra ?B"
    unfolding Sel_def
  proof (rule measurable_prob_algebraI)
    fix p :: "real \<times> (real^'n)" assume "p \<in> space ?P"
    show "prob_space (distr (S0 (snd p)) ?B (pdel (fst p) T))"
    proof (rule prob_space.prob_space_distr[OF PS0])
      show "pdel (fst p) T \<in> S0 (snd p) \<rightarrow>\<^sub>M ?B"
        unfolding measurable_cong_sets[OF setsS0 refl]
        by (rule pdel_measurable[OF T0])
    qed
  next
    show "(\<lambda>p :: real \<times> (real^'n). distr (S0 (snd p)) ?B (pdel (fst p) T))
        \<in> ?P \<rightarrow>\<^sub>M subprob_algebra ?B"
      by (rule measurable_distr2[OF fm gm])
  qed

  \<comment> \<open>the cut law, and the two identifications it produces\<close>
  have main: "Sel (s, y) = distr (pair_law_of (T - s) (pcut (T - s)) (S0 y))
        ?B (pembed s T)
      \<and> distr (Sel (s, y)) ((path_borel (T - s) :: ('n pairpath) measure)) (prebase s T)
        = pair_law_of (T - s) (pcut (T - s)) (S0 y)"
    if s0: "0 \<le> s" and sT: "s \<le> T" for s y
  proof -
    let ?Bs = "(path_borel (T - s) :: ('n pairpath) measure)"
    have a: "0 \<le> T - s" using sT by simp
    have b: "T - s \<le> T" using s0 by simp
    have cutm: "pcut (T - s) \<in> S0 y \<rightarrow>\<^sub>M ?Bs"
      by (rule pcut_measurable[OF a b setsS0])
    have cutB: "pcut (T - s) \<in> ?B \<rightarrow>\<^sub>M ?Bs" by (rule pcut_measurable[OF a b refl])
    have emb: "pembed s T \<in> ?Bs \<rightarrow>\<^sub>M ?B" by (rule pembed_measurable[OF s0 sT])
    have embB: "pembed s T \<in> S0 y \<rightarrow>\<^sub>M ?B"
      unfolding measurable_cong_sets[OF setsS0 refl]
      by (rule pembed_measurable_full[OF s0 sT])
    have reb: "prebase s T \<in> ?B \<rightarrow>\<^sub>M ?Bs" by (rule prebase_measurable[OF s0 sT])
    have comp: "pembed s T \<circ> pcut (T - s) = pembed s T"
      by (rule ext) (simp add: pembed_pcut[OF s0 sT])
    have first: "Sel (s, y)
        = distr (pair_law_of (T - s) (pcut (T - s)) (S0 y)) ?B (pembed s T)"
    proof -
      have "distr (pair_law_of (T - s) (pcut (T - s)) (S0 y)) ?B (pembed s T)
          = distr (S0 y) ?B (pembed s T \<circ> pcut (T - s))"
        unfolding pair_law_of_def by (rule distr_distr[OF emb cutm])
      also have "\<dots> = distr (S0 y) ?B (pembed s T)" unfolding comp ..
      finally show ?thesis
        unfolding Sel_def fst_conv snd_conv pdel_eq_pembed[OF s0 sT] ..
    qed
    have second: "distr (Sel (s, y)) ?Bs (prebase s T)
        = pair_law_of (T - s) (pcut (T - s)) (S0 y)"
    proof -
      have "distr (Sel (s, y)) ?Bs (prebase s T)
          = distr (distr (S0 y) ?B (pembed s T)) ?Bs (prebase s T)"
        unfolding Sel_def fst_conv snd_conv pdel_eq_pembed[OF s0 sT] ..
      also have "\<dots> = distr (S0 y) ?Bs (prebase s T \<circ> pembed s T)"
        by (rule distr_distr[OF reb embB])
      also have "\<dots> = distr (S0 y) ?Bs (pcut (T - s))"
      proof (rule distr_cong[OF refl refl])
        fix \<omega> :: "'n pairpath" assume "\<omega> \<in> space (S0 y)"
        then have wm: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
          using space_of_path_sets[OF setsS0] by simp
        then have cm: "pcut (T - s) \<omega>
            \<in> mspace (path_metric (T - s) :: ('n pairpath) metric)"
          using measurable_space[OF cutB] by (simp add: space_borel_of)
        have "(prebase s T \<circ> pembed s T) \<omega> = prebase s T (pembed s T \<omega>)" by simp
        also have "\<dots> = prebase s T (pembed s T (pcut (T - s) \<omega>))"
          unfolding pembed_pcut[OF s0 sT] ..
        also have "\<dots> = pcut (T - s) \<omega>" by (rule prebase_pembed[OF s0 sT cm])
        finally show "(prebase s T \<circ> pembed s T) \<omega> = pcut (T - s) \<omega>" .
      qed
      finally show ?thesis unfolding pair_law_of_def .
    qed
    show ?thesis using first second by blast
  qed

  show ?thesis
  proof (rule that)
    show "Sel \<in> ?P \<rightarrow>\<^sub>M prob_algebra ?B" by (rule Selm)
  next
    show "Sel (s, y) \<in> pdelclass k L T s" if s0: "0 \<le> s" and sT: "s \<le> T"
      for s :: real and y :: "real^'n"
    proof -
      have a: "0 \<le> T - s" using sT by simp
      have b: "T - s \<le> T" using s0 by simp
      have cutC: "pair_law_of (T - s) (pcut (T - s)) (S0 y)
          \<in> exit_class k L (T - s) (0 :: real^'n)"
        by (rule exit_class_pcut[OF a b S0C])
      have m1: "Sel (s, y)
          = distr (pair_law_of (T - s) (pcut (T - s)) (S0 y)) ?B (pembed s T)"
        using main[OF s0 sT, of y] by blast
      show ?thesis unfolding pdelclass_def m1 using cutC by (rule imageI)
    qed
  next
    show "distr (Sel (s, y)) ((path_borel (T - s) :: ('n pairpath) measure)) (prebase s T)
        \<in> exit_class k L (T - s) (0 :: real^'n)"
      if s0: "0 \<le> s" and sT: "s \<le> T" for s :: real and y :: "real^'n"
    proof -
      have a: "0 \<le> T - s" using sT by simp
      have b: "T - s \<le> T" using s0 by simp
      have m2: "distr (Sel (s, y)) ((path_borel (T - s) :: ('n pairpath) measure)) (prebase s T)
          = pair_law_of (T - s) (pcut (T - s)) (S0 y)"
        using main[OF s0 sT, of y] by blast
      show ?thesis unfolding m2 by (rule exit_class_pcut[OF a b S0C])
    qed
  next
    show "ess_inf_time (pshift_law (T - s) y
          (distr (Sel (s, y)) ((path_borel (T - s) :: ('n pairpath) measure)) (prebase s T)))
        (\<lambda>\<omega>. pexit (T - s) K (\<lambda>t. fst (\<omega> t))) = exit_val k L (T - s) K y"
      if s0: "0 \<le> s" and sT: "s \<le> T" for s :: real and y :: "real^'n"
    proof -
      have a: "0 \<le> T - s" using sT by simp
      have b: "T - s \<le> T" using s0 by simp
      have m2: "distr (Sel (s, y)) ((path_borel (T - s) :: ('n pairpath) measure)) (prebase s T)
          = pair_law_of (T - s) (pcut (T - s)) (S0 y)"
        using main[OF s0 sT, of y] by blast
      have "ess_inf_time (pshift_law (T - s) y
            (pair_law_of (T - s) (pcut (T - s)) (S0 y)))
          (\<lambda>\<omega>. pexit (T - s) K (\<lambda>t. fst (\<omega> t)))
          = min (ess_inf_time (pshift_law T y (S0 y))
              (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))) (ennreal (T - s))"
        by (rule ess_inf_pexit_pcut_law[OF a b PS0 setsS0 K])
      also have "\<dots> = min (exit_val k L T K y) (ennreal (T - s))"
        unfolding S0val ..
      also have "\<dots> = exit_val k L (T - s) K y"
        by (rule exit_val_horizon_cap[OF a b L K, symmetric])
      finally show ?thesis unfolding m2 .
    qed
  qed
qed

section \<open>The delayed class supplies the additive glue's kernel clauses\<close>

text \<open>@{thm [source] exit_class_aglue} asks its continuation kernel for
  nine facts.  Four are already in hand for \<^const>\<open>pdelclass\<close> --- \<open>Kp\<close>
  (the selector's own measurability), \<open>prob_space\<close>/\<open>sets\<close>
  (@{thm [source] pdelclass_prob}), \<open>K0\<close>
  (@{thm [source] pdelclass_frozen_at} at \<open>u = 0\<close>) and \<open>Kfr\<close>
  (@{thm [source] pdelclass_frozen}).  The rest follow from one structural
  statement: a delayed law's two class processes are still martingales on
  the fixed \<open>T\<close>-space, in the delayed law's own natural filtration.

  The reason is that delaying is a time change: a delayed path evaluated
  at \<open>u\<close> is the base path evaluated at \<open>\<rho> u = (u - s) \<or> 0 \<and> (T - s)\<close>,
  which is nondecreasing, so @{thm [source] martingale_time_change} turns
  the base martingale into a martingale for the time-changed filtration
  \<open>\<F>\<^sup>\<mu>\<^sub>(\<rho> u)\<close> --- exactly what @{thm [source] martingale_pair_law}
  needs to push the martingale forward along \<^const>\<open>pembed\<close>.  A delayed
  path carries no extra information at time \<open>u\<close>, which is why the
  martingale property survives the delay; taking the base's own filtration
  instead would make the statement false.  \<open>martingale_time_change_cong\<close>
  lives in @{theory Continuous_Time_Martingales.Martingale_Algebra}.\<close>




theorem pdelclass_X_martingale:
  fixes \<nu> :: "('n::finite pairpath) measure"
  assumes s0: "0 \<le> s" and sT: "s \<le> T" and m: "\<nu> \<in> pdelclass k L T s"
  shows "martingale \<nu> (natural_filtration \<nu> 0 (\<lambda>v w. w v)) 0
      (\<lambda>u w. fst (w (min u T)))"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?Bs = "(path_borel (T - s) :: ('n pairpath) measure)"
  let ?rho = "\<lambda>u :: real. min (max (u - s) 0) (T - s)"
  have T0: "0 \<le> T" using s0 sT by simp
  have Ts: "0 \<le> T - s" using sT by simp
  from m obtain \<mu> where mu: "\<mu> \<in> exit_class k L (T - s) (0::real^'n)"
    and nu: "\<nu> = distr \<mu> ?B (pembed s T)" unfolding pdelclass_def by blast
  have setsmu: "sets \<mu> = sets ?Bs" by (rule exit_class_sets[OF mu])
  have Pmu: "prob_space \<mu>" by (rule exit_class_prob[OF mu])
  have pm: "pembed s T \<in> \<mu> \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsmu refl]
    by (rule pembed_measurable[OF s0 sT])
  have nu': "\<nu> = pair_law_of T (pembed s T) \<mu>"
    unfolding nu pair_law_of_def ..
  let ?F = "natural_filtration \<mu> 0 (\<lambda>v w :: 'n pairpath. w v)"
  have mgb: "martingale \<mu> ?F 0 (\<lambda>t w. fst (w (min t (T - s))))"
    by (rule exit_class_X_martingale[OF mu])
  have tc: "martingale \<mu> (\<lambda>u. ?F (?rho u)) 0
      (\<lambda>u w. fst (pembed s T w (min u T)))"
  proof (rule martingale_time_change_cong[OF mgb])
    show "0 \<le> ?rho u" if "0 \<le> u" for u :: real using Ts that by simp
    show "?rho u \<le> ?rho v" if "0 \<le> u" "u \<le> v" for u v :: real
      using that by simp
    show "(\<lambda>w :: 'n pairpath. fst (pembed s T w (min u T)))
        = (\<lambda>w. fst (w (min (?rho u) (T - s))))" if u: "0 \<le> u" for u :: real
    proof (rule ext)
      fix w :: "'n pairpath"
      have "pembed s T w (min u T) = w (?rho u)"
        by (rule pembed_eval_min[OF u s0 sT])
      moreover have "min (?rho u) (T - s) = ?rho u" by simp
      ultimately show "fst (pembed s T w (min u T))
          = fst (w (min (?rho u) (T - s)))" by simp
    qed
  qed
  show ?thesis
    unfolding nu'
  proof (rule martingale_pair_law[where T = T and FF = "\<lambda>u. ?F (?rho u)"])
    show "prob_space \<mu>" by (rule Pmu)
    show "pembed s T \<in> \<mu> \<rightarrow>\<^sub>M ?B" by (rule pm)
    show "(\<lambda>w. pembed s T w r) \<in> borel_measurable (?F (?rho u))"
      if "0 \<le> r" "r \<le> u" for u r :: real
      by (rule pembed_eval_le[OF that s0 sT])
    show "(\<lambda>w :: 'n pairpath. fst (w (min u T))) \<in> borel_measurable
        (natural_filtration (pair_law_of T (pembed s T) \<mu>)
          0 (\<lambda>v w. w v) u)" if u: "0 \<le> u" for u :: real
    proof -
      have a: "0 \<le> min u T" using u T0 by simp
      have b: "min u T \<le> u" by simp
      have fstB: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
          \<in> borel_measurable borel"
        by (intro borel_measurable_continuous_onI continuous_intros)
      show ?thesis
        by (rule measurable_compose
            [OF path_eval_natural_filtration[OF a b] fstB])
    qed
    show "martingale \<mu> (\<lambda>u. ?F (?rho u)) 0
        (\<lambda>u w. fst (pembed s T w (min u T)))" by (rule tc)
  qed
qed

theorem pdelclass_comp_martingale:
  fixes \<nu> :: "('n::finite pairpath) measure"
  assumes s0: "0 \<le> s" and sT: "s \<le> T" and m: "\<nu> \<in> pdelclass k L T s"
  shows "martingale \<nu> (natural_filtration \<nu> 0 (\<lambda>v w. w v)) 0
      (\<lambda>u w. outerp (fst (w (min u T))) - snd (w (min u T)))"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?Bs = "(path_borel (T - s) :: ('n pairpath) measure)"
  let ?rho = "\<lambda>u :: real. min (max (u - s) 0) (T - s)"
  have T0: "0 \<le> T" using s0 sT by simp
  have Ts: "0 \<le> T - s" using sT by simp
  from m obtain \<mu> where mu: "\<mu> \<in> exit_class k L (T - s) (0::real^'n)"
    and nu: "\<nu> = distr \<mu> ?B (pembed s T)" unfolding pdelclass_def by blast
  have setsmu: "sets \<mu> = sets ?Bs" by (rule exit_class_sets[OF mu])
  have Pmu: "prob_space \<mu>" by (rule exit_class_prob[OF mu])
  have pm: "pembed s T \<in> \<mu> \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsmu refl]
    by (rule pembed_measurable[OF s0 sT])
  have nu': "\<nu> = pair_law_of T (pembed s T) \<mu>"
    unfolding nu pair_law_of_def ..
  let ?F = "natural_filtration \<mu> 0 (\<lambda>v w :: 'n pairpath. w v)"
  have mgb: "martingale \<mu> ?F 0
      (\<lambda>t w. outerp (fst (w (min t (T - s)))) - snd (w (min t (T - s))))"
    by (rule exit_class_comp_martingale[OF mu])
  have tc: "martingale \<mu> (\<lambda>u. ?F (?rho u)) 0
      (\<lambda>u w. outerp (fst (pembed s T w (min u T)))
          - snd (pembed s T w (min u T)))"
  proof (rule martingale_time_change_cong[OF mgb])
    show "0 \<le> ?rho u" if "0 \<le> u" for u :: real using Ts that by simp
    show "?rho u \<le> ?rho v" if "0 \<le> u" "u \<le> v" for u v :: real
      using that by simp
    show "(\<lambda>w :: 'n pairpath. outerp (fst (pembed s T w (min u T)))
          - snd (pembed s T w (min u T)))
        = (\<lambda>w. outerp (fst (w (min (?rho u) (T - s))))
          - snd (w (min (?rho u) (T - s))))" if u: "0 \<le> u" for u :: real
    proof (rule ext)
      fix w :: "'n pairpath"
      have "pembed s T w (min u T) = w (?rho u)"
        by (rule pembed_eval_min[OF u s0 sT])
      moreover have "min (?rho u) (T - s) = ?rho u" by simp
      ultimately show "outerp (fst (pembed s T w (min u T)))
            - snd (pembed s T w (min u T))
          = outerp (fst (w (min (?rho u) (T - s))))
            - snd (w (min (?rho u) (T - s)))" by simp
    qed
  qed
  show ?thesis
    unfolding nu'
  proof (rule martingale_pair_law[where T = T and FF = "\<lambda>u. ?F (?rho u)"])
    show "prob_space \<mu>" by (rule Pmu)
    show "pembed s T \<in> \<mu> \<rightarrow>\<^sub>M ?B" by (rule pm)
    show "(\<lambda>w. pembed s T w r) \<in> borel_measurable (?F (?rho u))"
      if "0 \<le> r" "r \<le> u" for u r :: real
      by (rule pembed_eval_le[OF that s0 sT])
    show "(\<lambda>w :: 'n pairpath. outerp (fst (w (min u T))) - snd (w (min u T)))
        \<in> borel_measurable (natural_filtration
          (pair_law_of T (pembed s T) \<mu>) 0 (\<lambda>v w. w v) u)"
      if u: "0 \<le> u" for u :: real
    proof -
      have a: "0 \<le> min u T" using u T0 by simp
      have b: "min u T \<le> u" by simp
      have cm: "(\<lambda>z :: (real^'n) \<times> (real^'n^'n). outerp (fst z) - snd z)
          \<in> borel_measurable borel"
        unfolding outerp_def
        by (intro borel_measurable_continuous_onI continuous_intros)
      show ?thesis
        by (rule measurable_compose
            [OF path_eval_natural_filtration[OF a b] cm])
    qed
    show "martingale \<mu> (\<lambda>u. ?F (?rho u)) 0
        (\<lambda>u w. outerp (fst (pembed s T w (min u T)))
            - snd (pembed s T w (min u T)))" by (rule tc)
  qed
qed

subsection \<open>The covariation clause of the continuation\<close>

text \<open>The guard \<open>s \<le> a\<close> makes this the delayed constraint: below \<open>s\<close> the
  path stands still, so no difference quotient there can lie in
  \<^const>\<open>sconstraint\<close>, and the kernel is only ever asked about the
  stretch after the freeze.  One rational pair at a time
  (@{thm [source] closedin_diffquot_constraint} for measurability, so that
  @{thm [source] AE_distr_iff} applies), then two countable passes, then
  @{thm [source] diffquot_all_of_rational_ge} for the real pairs.\<close>

theorem pdelclass_diffquot:
  fixes \<nu> :: "('n::finite pairpath) measure"
  assumes s0: "0 \<le> s" and sT: "s \<le> T" and m: "\<nu> \<in> pdelclass k L T s"
  shows "AE w in \<nu>. \<forall>a b. s \<le> a \<longrightarrow> a < b \<longrightarrow> b \<le> T \<longrightarrow>
      (1 / (b - a)) *\<^sub>R (snd (w b) - snd (w a)) \<in> sconstraint k L"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?Bs = "(path_borel (T - s) :: ('n pairpath) measure)"
  have T0: "0 \<le> T" using s0 sT by simp
  from m obtain \<mu> where mu: "\<mu> \<in> exit_class k L (T - s) (0::real^'n)"
    and nu: "\<nu> = distr \<mu> ?B (pembed s T)" unfolding pdelclass_def by blast
  have setsmu: "sets \<mu> = sets ?Bs" by (rule exit_class_sets[OF mu])
  have pm: "pembed s T \<in> \<mu> \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsmu refl]
    by (rule pembed_measurable[OF s0 sT])
  have setsnu: "sets \<nu> = sets ?B" unfolding nu by simp
  have cov: "AE w in \<mu>. \<forall>a b. 0 \<le> a \<longrightarrow> a < b \<longrightarrow> b \<le> T - s \<longrightarrow>
      (1 / (b - a)) *\<^sub>R (snd (w b) - snd (w a)) \<in> sconstraint k L"
    using mu unfolding exit_class_def by blast
  have one: "AE w in \<nu>.
      (1 / (q - p)) *\<^sub>R (snd (w q) - snd (w p)) \<in> sconstraint k L"
    if p: "p \<in> {0..T}" and q: "q \<in> {0..T}" and pq: "p < q" and sp: "s \<le> p"
    for p q :: real
  proof -
    have spB: "space ?B = mspace (path_metric T :: ('n pairpath) metric)"
      by (simp add: space_borel_of)
    have mset: "{w \<in> space ?B.
        (1 / (q - p)) *\<^sub>R (snd (w q) - snd (w p)) \<in> sconstraint k L}
        \<in> sets ?B"
      unfolding spB
      by (rule borel_of_closed[OF closedin_diffquot_constraint[OF p q]])
    have "AE w in \<mu>. (1 / (q - p)) *\<^sub>R
        (snd (pembed s T w q) - snd (pembed s T w p)) \<in> sconstraint k L"
      using cov
    proof eventually_elim
      case (elim w)
      have ep: "pembed s T w p = w (p - s)"
      proof -
        have "pembed s T w p = w (max (p - s) 0)" by (rule pembed_apply[OF p])
        moreover have "max (p - s) 0 = p - s" using sp by simp
        ultimately show ?thesis by simp
      qed
      have eqq: "pembed s T w q = w (q - s)"
      proof -
        have "pembed s T w q = w (max (q - s) 0)" by (rule pembed_apply[OF q])
        moreover have "max (q - s) 0 = q - s" using sp pq by simp
        ultimately show ?thesis by simp
      qed
      have a0: "0 \<le> p - s" using sp by simp
      have ab: "p - s < q - s" using pq by simp
      have bT: "q - s \<le> T - s" using q by simp
      from elim have "(1 / ((q - s) - (p - s))) *\<^sub>R
          (snd (w (q - s)) - snd (w (p - s))) \<in> sconstraint k L"
        using a0 ab bT by blast
      then show ?case unfolding ep eqq by simp
    qed
    then show ?thesis unfolding nu AE_distr_iff[OF pm mset] .
  qed
  have rat: "AE w in \<nu>. \<forall>p\<in>(\<rat>::real set). \<forall>q\<in>(\<rat>::real set).
      p \<in> {0..T} \<longrightarrow> q \<in> {0..T} \<longrightarrow> p < q \<longrightarrow> s \<le> p \<longrightarrow>
        (1 / (q - p)) *\<^sub>R (snd (w q) - snd (w p)) \<in> sconstraint k L"
  proof (rule AE_ball_countable'[OF _ countable_rat])
    fix p :: real assume "p \<in> \<rat>"
    show "AE w in \<nu>. \<forall>q\<in>(\<rat>::real set).
        p \<in> {0..T} \<longrightarrow> q \<in> {0..T} \<longrightarrow> p < q \<longrightarrow> s \<le> p \<longrightarrow>
          (1 / (q - p)) *\<^sub>R (snd (w q) - snd (w p)) \<in> sconstraint k L"
    proof (rule AE_ball_countable'[OF _ countable_rat])
      fix q :: real assume "q \<in> \<rat>"
      show "AE w in \<nu>. p \<in> {0..T} \<longrightarrow> q \<in> {0..T} \<longrightarrow> p < q \<longrightarrow> s \<le> p \<longrightarrow>
          (1 / (q - p)) *\<^sub>R (snd (w q) - snd (w p)) \<in> sconstraint k L"
      proof (cases "p \<in> {0..T} \<and> q \<in> {0..T} \<and> p < q \<and> s \<le> p")
        case True
        then show ?thesis using one[of p q] by auto
      next
        case False
        then show ?thesis by auto
      qed
    qed
  qed
  have spn: "AE w in \<nu>. w \<in> space \<nu>" by (rule AE_space)
  from rat spn show ?thesis
  proof eventually_elim
    case (elim w)
    then have R: "\<forall>p\<in>(\<rat>::real set). \<forall>q\<in>(\<rat>::real set).
        p \<in> {0..T} \<longrightarrow> q \<in> {0..T} \<longrightarrow> p < q \<longrightarrow> s \<le> p \<longrightarrow>
          (1 / (q - p)) *\<^sub>R (snd (w q) - snd (w p)) \<in> sconstraint k L"
      and W: "w \<in> space \<nu>" by blast+
    have mw: "w \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using W sets_eq_imp_space_eq[OF setsnu] by (simp add: space_borel_of)
    have cont: "continuous_on {0..T} (\<lambda>u. snd (w u))"
      using mspace_path_metricD[OF mw] by (intro continuous_intros)
    show ?case
    proof (intro allI impI)
      fix a b :: real
      assume sa: "s \<le> a" and ab: "a < b" and bT: "b \<le> T"
      have a0: "0 \<le> a" using sa s0 by simp
      show "(1 / (b - a)) *\<^sub>R (snd (w b) - snd (w a)) \<in> sconstraint k L"
      proof (rule diffquot_all_of_rational_ge
          [OF closed_sconstraint cont _ sa a0 ab bT])
        fix p q :: real
        assume "p \<in> \<rat>" "q \<in> \<rat>" "0 \<le> p" "p < q" "q \<le> T" "s \<le> p"
        then show "(1 / (q - p)) *\<^sub>R (snd (w q) - snd (w p))
            \<in> sconstraint k L" using R bT by auto
      qed
    qed
  qed
qed

subsection \<open>Mean, integrability and the increment identity\<close>

text \<open>A martingale that starts at \<open>0\<close> has mean \<open>0\<close> at every later time; the
  set-integral identity over the whole space is the case \<open>i = 0\<close> of the
  martingale property, and @{thm [source] pdelclass_frozen_at} supplies the
  start.  \<open>martingale_mean_zero_of_start\<close> lives in
  @{theory Continuous_Time_Martingales.Martingale_Algebra}.\<close>

lemma pdelclass_start_zero:
  fixes \<nu> :: "('n::finite pairpath) measure"
  assumes s0: "0 \<le> s" and sT: "s \<le> T" and m: "\<nu> \<in> pdelclass k L T s"
  shows "AE w in \<nu>. w (min (0::real) T) = 0"
proof -
  have T0: "0 \<le> T" using s0 sT by simp
  have z: "(0::real) \<in> {0..T}" using T0 by simp
  have "AE w in \<nu>. w (0::real) = 0"
    by (rule pdelclass_frozen_at[OF s0 sT m z s0])
  then show ?thesis using T0 by simp
qed

corollary pdelclass_X_int:
  fixes \<nu> :: "('n::finite pairpath) measure"
  assumes s0: "0 \<le> s" and sT: "s \<le> T" and m: "\<nu> \<in> pdelclass k L T s"
    and u: "0 \<le> u"
  shows "integrable \<nu> (\<lambda>w. fst (w (min u T)) $ e)"
  by (rule martingale.integrable
      [OF martingale_vec_component[OF pdelclass_X_martingale[OF s0 sT m]] u])

corollary pdelclass_comp_int:
  fixes \<nu> :: "('n::finite pairpath) measure"
  assumes s0: "0 \<le> s" and sT: "s \<le> T" and m: "\<nu> \<in> pdelclass k L T s"
    and u: "0 \<le> u"
  shows "integrable \<nu>
      (\<lambda>w. (outerp (fst (w (min u T))) - snd (w (min u T))) $ c $ d)"
  by (rule martingale.integrable
      [OF martingale_mat_component[OF pdelclass_comp_martingale[OF s0 sT m]] u])

corollary pdelclass_X_increment:
  fixes \<nu> :: "('n::finite pairpath) measure"
  assumes s0: "0 \<le> s" and sT: "s \<le> T" and m: "\<nu> \<in> pdelclass k L T s"
    and C: "C \<in> sets (natural_filtration \<nu> 0 (\<lambda>t w. w t) u)"
    and u: "0 \<le> u" and uv: "u \<le> v"
  shows "set_lebesgue_integral \<nu> C (\<lambda>w. fst (w (min u T)) $ e)
      = set_lebesgue_integral \<nu> C (\<lambda>w. fst (w (min v T)) $ e)"
  by (rule martingale.set_integral_eq
      [OF martingale_vec_component[OF pdelclass_X_martingale[OF s0 sT m]]
        C u uv])

corollary pdelclass_comp_increment:
  fixes \<nu> :: "('n::finite pairpath) measure"
  assumes s0: "0 \<le> s" and sT: "s \<le> T" and m: "\<nu> \<in> pdelclass k L T s"
    and C: "C \<in> sets (natural_filtration \<nu> 0 (\<lambda>t w. w t) u)"
    and u: "0 \<le> u" and uv: "u \<le> v"
  shows "set_lebesgue_integral \<nu> C
        (\<lambda>w. (outerp (fst (w (min u T))) - snd (w (min u T))) $ c $ d)
      = set_lebesgue_integral \<nu> C
        (\<lambda>w. (outerp (fst (w (min v T))) - snd (w (min v T))) $ c $ d)"
  by (rule martingale.set_integral_eq
      [OF martingale_mat_component[OF pdelclass_comp_martingale[OF s0 sT m]]
        C u uv])

corollary pdelclass_X_mean:
  fixes \<nu> :: "('n::finite pairpath) measure"
  assumes s0: "0 \<le> s" and sT: "s \<le> T" and m: "\<nu> \<in> pdelclass k L T s"
    and u: "0 \<le> u"
  shows "(\<integral>w. fst (w (min u T)) $ e \<partial>\<nu>) = 0"
proof (rule martingale_mean_zero_of_start
    [OF martingale_vec_component[OF pdelclass_X_martingale[OF s0 sT m]] _ u])
  show "AE w in \<nu>. fst (w (min (0::real) T)) $ e = 0"
    using pdelclass_start_zero[OF s0 sT m] by (rule eventually_mono) simp
qed

corollary pdelclass_comp_mean:
  fixes \<nu> :: "('n::finite pairpath) measure"
  assumes s0: "0 \<le> s" and sT: "s \<le> T" and m: "\<nu> \<in> pdelclass k L T s"
    and u: "0 \<le> u"
  shows "(\<integral>w. (outerp (fst (w (min u T))) - snd (w (min u T))) $ c $ d \<partial>\<nu>)
      = 0"
proof (rule martingale_mean_zero_of_start
    [OF martingale_mat_component[OF pdelclass_comp_martingale[OF s0 sT m]] _ u])
  show "AE w in \<nu>. (outerp (fst (w (min (0::real) T)))
      - snd (w (min (0::real) T))) $ c $ d = 0"
    using pdelclass_start_zero[OF s0 sT m]
  proof (rule eventually_mono)
    fix w :: "'n pairpath" assume z: "w (min (0::real) T) = 0"
    have "outerp (fst (w (min (0::real) T))) = 0"
      unfolding z by (simp add: outerp_def zero_vec_def vec_eq_iff)
    then show "(outerp (fst (w (min (0::real) T)))
        - snd (w (min (0::real) T))) $ c $ d = 0" unfolding z by simp
  qed
qed

section \<open>The stopped past law satisfies the additive glue's \<open>Q\<close>-clauses\<close>

text \<open>\<open>Qst\<close> --- that the past law is carried by paths which are their own
  stopped versions --- is where the a.e. form is unavoidable, so its
  transfer needs the fixed-point set to be measurable.  It is: two paths
  that agree at every rational of \<open>[0,T]\<close> and are both continuous there
  agree everywhere (@{thm [source] vanishes_of_rational} on their
  difference), so the fixed-point set is a countable intersection of
  evaluation conditions --- the same shape as
  @{thm [source] frozen_set_measurable}.\<close>






theorem pstopped_law_diffquot:
  fixes P :: "('n::finite pairpath) measure"
  assumes T0: "0 \<le> T"
    and setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
    and Pcov: "AE \<omega> in P. \<forall>a b. 0 \<le> a \<longrightarrow> a < b \<longrightarrow> b \<le> T \<longrightarrow>
        (1 / (b - a)) *\<^sub>R (snd (\<omega> b) - snd (\<omega> a)) \<in> sconstraint k L"
  shows "AE p' in pair_law_of T (pstopped T \<theta>) P.
      \<forall>a b. 0 \<le> a \<longrightarrow> a < b \<longrightarrow> b \<le> \<theta> p' \<longrightarrow>
        (1 / (b - a)) *\<^sub>R (snd (p' b) - snd (p' a)) \<in> sconstraint k L"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?Q = "pair_law_of T (pstopped T \<theta>) P"
  have th0: "0 \<le> \<theta> \<omega>" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF st])
  have thT: "\<theta> \<omega> \<le> T" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_le[OF st])
  have m1: "pstopped T \<theta> \<in> P \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsP refl]
    by (rule pstopped_measurable[OF T0 thM th0 thT])
  have setsQ: "sets ?Q = sets ?B" by (rule sets_pair_law_of)
  have spB: "space ?B = mspace (path_metric T :: ('n pairpath) metric)"
    by (simp add: space_borel_of)
  have one: "AE p' in ?Q. q \<le> \<theta> p' \<longrightarrow>
      (1 / (q - p)) *\<^sub>R (snd (p' q) - snd (p' p)) \<in> sconstraint k L"
    if p: "p \<in> {0..T}" and q: "q \<in> {0..T}" and pq: "p < q" for p q :: real
  proof -
    have S: "{p' \<in> space ?B.
        (1 / (q - p)) *\<^sub>R (snd (p' q) - snd (p' p)) \<in> sconstraint k L}
        \<in> sets ?B"
      unfolding spB
      by (rule borel_of_closed[OF closedin_diffquot_constraint[OF p q]])
    have G: "{p' \<in> space ?B. q \<le> \<theta> p'} \<in> sets ?B" using thM by measurable
    have mset: "{p' \<in> space ?B. q \<le> \<theta> p' \<longrightarrow>
        (1 / (q - p)) *\<^sub>R (snd (p' q) - snd (p' p)) \<in> sconstraint k L}
        \<in> sets ?B"
    proof -
      have "{p' \<in> space ?B. q \<le> \<theta> p' \<longrightarrow>
          (1 / (q - p)) *\<^sub>R (snd (p' q) - snd (p' p)) \<in> sconstraint k L}
          = (space ?B - {p' \<in> space ?B. q \<le> \<theta> p'})
            \<union> {p' \<in> space ?B.
              (1 / (q - p)) *\<^sub>R (snd (p' q) - snd (p' p)) \<in> sconstraint k L}"
        by auto
      then show ?thesis using S G by (simp add: sets.Un sets.compl_sets)
    qed
    have "AE \<omega> in P. q \<le> \<theta> (pstopped T \<theta> \<omega>) \<longrightarrow>
        (1 / (q - p)) *\<^sub>R (snd (pstopped T \<theta> \<omega> q) - snd (pstopped T \<theta> \<omega> p))
          \<in> sconstraint k L"
      using Pcov AE_space
    proof eventually_elim
      case (elim \<omega>)
      have cw: "continuous_on {0..T} (\<lambda>v. fst (\<omega> v))"
        by (rule path_sets_fst_continuous[OF setsP elim(2)])
      show ?case
      proof
        assume "q \<le> \<theta> (pstopped T \<theta> \<omega>)"
        then have le: "q \<le> \<theta> \<omega>"
          unfolding path_stopping_time_stopped[OF st cw] .
        have eq: "pstopped T \<theta> \<omega> q = \<omega> q"
        proof -
          have "pstopped T \<theta> \<omega> q = \<omega> (min q (\<theta> \<omega>))" by (rule pstopped_apply[OF q])
          also have "min q (\<theta> \<omega>) = q" using le by simp
          finally show ?thesis .
        qed
        have ep: "pstopped T \<theta> \<omega> p = \<omega> p"
        proof -
          have "pstopped T \<theta> \<omega> p = \<omega> (min p (\<theta> \<omega>))" by (rule pstopped_apply[OF p])
          also have "min p (\<theta> \<omega>) = p" using le pq by simp
          finally show ?thesis .
        qed
        show "(1 / (q - p)) *\<^sub>R
            (snd (pstopped T \<theta> \<omega> q) - snd (pstopped T \<theta> \<omega> p)) \<in> sconstraint k L"
          unfolding eq ep using elim p q pq by auto
      qed
    qed
    then show ?thesis
      unfolding pair_law_of_def AE_distr_iff[OF m1 mset] .
  qed
  have rat: "AE p' in ?Q. \<forall>p\<in>(\<rat>::real set). \<forall>q\<in>(\<rat>::real set).
      p \<in> {0..T} \<longrightarrow> q \<in> {0..T} \<longrightarrow> p < q \<longrightarrow> q \<le> \<theta> p' \<longrightarrow>
        (1 / (q - p)) *\<^sub>R (snd (p' q) - snd (p' p)) \<in> sconstraint k L"
  proof (rule AE_ball_countable'[OF _ countable_rat])
    fix p :: real assume "p \<in> \<rat>"
    show "AE p' in ?Q. \<forall>q\<in>(\<rat>::real set).
        p \<in> {0..T} \<longrightarrow> q \<in> {0..T} \<longrightarrow> p < q \<longrightarrow> q \<le> \<theta> p' \<longrightarrow>
          (1 / (q - p)) *\<^sub>R (snd (p' q) - snd (p' p)) \<in> sconstraint k L"
    proof (rule AE_ball_countable'[OF _ countable_rat])
      fix q :: real assume "q \<in> \<rat>"
      show "AE p' in ?Q. p \<in> {0..T} \<longrightarrow> q \<in> {0..T} \<longrightarrow> p < q \<longrightarrow> q \<le> \<theta> p' \<longrightarrow>
          (1 / (q - p)) *\<^sub>R (snd (p' q) - snd (p' p)) \<in> sconstraint k L"
      proof (cases "p \<in> {0..T} \<and> q \<in> {0..T} \<and> p < q")
        case True
        then show ?thesis using one[of p q] by auto
      next
        case False
        then show ?thesis by auto
      qed
    qed
  qed
  have spn: "AE p' in ?Q. p' \<in> space ?Q" by (rule AE_space)
  from rat spn show ?thesis
  proof eventually_elim
    case (elim p')
    then have R: "\<forall>p\<in>(\<rat>::real set). \<forall>q\<in>(\<rat>::real set).
        p \<in> {0..T} \<longrightarrow> q \<in> {0..T} \<longrightarrow> p < q \<longrightarrow> q \<le> \<theta> p' \<longrightarrow>
          (1 / (q - p)) *\<^sub>R (snd (p' q) - snd (p' p)) \<in> sconstraint k L"
      and W: "p' \<in> space ?Q" by blast+
    have mw: "p' \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using W by (simp add: space_pair_law_of)
    have cT: "continuous_on {0..T} (\<lambda>u. snd (p' u))"
      using mspace_path_metricD[OF mw] by (intro continuous_intros)
    have sub: "{0..\<theta> p'} \<subseteq> {0..T}" using thT[of p'] by auto
    have cont: "continuous_on {0..\<theta> p'} (\<lambda>u. snd (p' u))"
      by (rule continuous_on_subset[OF cT sub])
    show ?case
    proof (intro allI impI)
      fix a b :: real
      assume a0: "0 \<le> a" and ab: "a < b" and bth: "b \<le> \<theta> p'"
      show "(1 / (b - a)) *\<^sub>R (snd (p' b) - snd (p' a)) \<in> sconstraint k L"
      proof (rule diffquot_all_of_rational[OF closed_sconstraint cont _ a0 ab bth])
        fix p q :: real
        assume pq: "p \<in> \<rat>" "q \<in> \<rat>" "0 \<le> p" "p < q" "q \<le> \<theta> p'"
        have pT: "p \<in> {0..T}" using pq thT[of p'] by auto
        have qT: "q \<in> {0..T}" using pq thT[of p'] th0[of p'] by auto
        show "(1 / (q - p)) *\<^sub>R (snd (p' q) - snd (p' p)) \<in> sconstraint k L"
          using R pq pT qT by blast
      qed
    qed
  qed
qed

text \<open>The last input the two martingale clauses need: the stopped path,
  evaluated at a time \<open>r \<le> u\<close>, is \<open>\<F>\<^sub>u\<close>-measurable as a path point, with
  no componentwise decomposition.  The trick reads it off the \<open>u\<close>-cut
  rather than off the whole path: \<^const>\<open>pcut\<close> is measurable into the
  \<open>u\<close>-horizon space by the description of the natural filtration
  (@{thm [source] sets_natural_filtration_eq_pcut_vimage}), the truncated
  stopping time \<open>r \<and> \<theta>\<close> is \<open>\<F>\<^sub>u\<close>-measurable because \<open>{r \<and> \<theta> \<le> t}\<close> is
  either everything or \<open>{\<theta> \<le> t}\<close> with \<open>t < r\<close>, and
  @{thm [source] path_eval_at_measurable_time} joins the two.\<close>




theorem pstopped_law_horizon_component:
  fixes P :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T0: "0 < T" and L0: "0 \<le> L" and P: "P \<in> exit_class k L T x"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
  shows "horizon_sq_int_martingale (pair_law_of T (pstopped T \<theta>) P)
      (natural_filtration (pair_law_of T (pstopped T \<theta>) P) 0 (\<lambda>v \<omega>. \<omega> v))
      (\<lambda>u p'. fst (p' (min u T)) $ c) T"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?Q = "pair_law_of T (pstopped T \<theta>) P"
  let ?F = "natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?G = "natural_filtration ?Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?Z = "\<lambda>u \<omega> :: 'n pairpath. fst (\<omega> (min u T)) $ c"
  have T0': "0 \<le> T" using T0 by simp
  have setsP: "sets P = sets ?B" by (rule exit_class_sets[OF P])
  have PS: "prob_space P" by (rule exit_class_prob[OF P])
  have th0: "0 \<le> \<theta> \<omega>" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF st])
  have thT: "\<theta> \<omega> \<le> T" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_le[OF st])
  have m1: "pstopped T \<theta> \<in> P \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsP refl]
    by (rule pstopped_measurable[OF T0' thM th0 thT])
  have PQ: "prob_space ?Q" by (rule pstopped_law_prob[OF T0' PS setsP st thM])
  have sp: "space P = space ?B" by (rule sets_eq_imp_space_eq[OF setsP])
  have nf: "?F v = natural_filtration ?B 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) v" for v
    by (rule natural_filtration_cong_space[OF sp])
  have spF: "space (?F v) = space P" for v
    unfolding natural_filtration_def by simp
  have tstop: "{\<omega> \<in> space P. \<theta> \<omega> \<le> s} \<in> sets (?F s)" if s: "0 \<le> s" for s
  proof -
    have "{\<omega> \<in> space ?B. \<theta> \<omega> \<le> s}
        \<in> sets (natural_filtration ?B 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) s)"
      by (rule path_stopping_time_event_filtration_all[OF T0' st thM s])
    then show ?thesis unfolding nf using sp by simp
  qed
  have HZ: "horizon_sq_int_martingale P ?F ?Z T"
    by (rule exit_class_horizon_component[OF T0 L0 P])
  have contT: "continuous_on {0..T} (\<lambda>s. ?Z s \<omega>)" if w: "\<omega> \<in> space P" for \<omega>
  proof -
    have "continuous_on {0..} (\<lambda>s. ?Z s \<omega>)"
      by (rule exit_class_coord_paths_cont[OF T0' setsP w])
    then show ?thesis by (rule continuous_on_subset) auto
  qed
  have cap: "?Z s \<omega> = ?Z (min s T) \<omega>" for s and \<omega> :: "'n pairpath" by simp
  have mgs: "martingale P ?F 0 (\<lambda>v \<omega>. ?Z (min v (\<theta> \<omega>)) \<omega>)"
    by (rule horizon_sq_int_martingale_stopped(1)
        [OF T0 HZ cap contT th0 tstop])
  have sqs: "integrable P (\<lambda>\<omega>. (?Z (min s (\<theta> \<omega>)) \<omega>)\<^sup>2)" if s: "0 \<le> s" for s
    by (rule horizon_sq_int_martingale_stopped(2)
        [OF T0 HZ cap contT th0 tstop s])

  \<comment> \<open>step two: push the stopped martingale forward\<close>
  have mgp: "martingale P ?F 0 (\<lambda>u \<omega>. ?Z u (pstopped T \<theta> \<omega>))"
  proof (rule martingale_cong_ge[OF mgs])
    fix u :: real assume u: "0 \<le> u"
    show "(\<lambda>\<omega>. ?Z (min u (\<theta> \<omega>)) \<omega>)
        = (\<lambda>\<omega> :: 'n pairpath. ?Z u (pstopped T \<theta> \<omega>))"
    proof (rule ext)
      fix \<omega> :: "'n pairpath"
      show "?Z (min u (\<theta> \<omega>)) \<omega> = ?Z u (pstopped T \<theta> \<omega>)"
        using pstopped_eval_min_T[OF T0' u, of \<theta> \<omega>] by simp
    qed
  qed
  have Zm: "?Z u \<in> borel_measurable (?G u)" if u: "0 \<le> u" for u
  proof -
    have a: "0 \<le> min u T" using u T0' by simp
    have b: "min u T \<le> u" by simp
    have fcB: "(\<lambda>z :: (real^'n) \<times> (real^'n^'n). fst z $ c)
        \<in> borel_measurable borel"
    proof -
      have s: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
          \<in> borel_measurable borel"
        by (intro borel_measurable_continuous_onI continuous_intros)
      show ?thesis by (rule measurable_compose[OF s borel_measurable_nth])
    qed
    show ?thesis
      by (rule measurable_compose[OF path_eval_natural_filtration[OF a b] fcB])
  qed
  have mgQ: "martingale ?Q ?G 0 ?Z"
  proof (rule martingale_pair_law[where T = T and FF = ?F])
    show "prob_space P" by (rule PS)
    show "pstopped T \<theta> \<in> P \<rightarrow>\<^sub>M ?B" by (rule m1)
    show "(\<lambda>\<omega>. pstopped T \<theta> \<omega> r) \<in> borel_measurable (?F u)"
      if "0 \<le> r" "r \<le> u" for u r :: real
      by (rule pstopped_eval_filtration[OF T0' setsP st thM that])
    show "?Z u \<in> borel_measurable
        (natural_filtration (pair_law_of T (pstopped T \<theta>) P) 0 (\<lambda>v \<omega>. \<omega> v) u)"
      if "0 \<le> u" for u by (rule Zm[OF that])
    show "martingale P ?F 0 (\<lambda>u \<omega>. ?Z u (pstopped T \<theta> \<omega>))" by (rule mgp)
  qed

  \<comment> \<open>step three: square integrability travels with the pushforward\<close>
  have sqQ: "integrable ?Q (\<lambda>p'. (?Z s p')\<^sup>2)" if s: "0 \<le> s" for s
  proof -
    have zb: "(\<lambda>p' :: 'n pairpath. (?Z s p')\<^sup>2) \<in> borel_measurable ?B"
    proof -
      have "(\<lambda>p' :: 'n pairpath. p' (min s T)) \<in> borel_measurable ?B"
        by (rule pair_law_eval_measurable[OF refl])
      moreover have "(\<lambda>z :: (real^'n) \<times> (real^'n^'n). fst z $ c)
          \<in> borel_measurable borel"
      proof -
        have s': "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
            \<in> borel_measurable borel"
          by (intro borel_measurable_continuous_onI continuous_intros)
        show ?thesis by (rule measurable_compose[OF s' borel_measurable_nth])
      qed
      ultimately have "(\<lambda>p' :: 'n pairpath. ?Z s p') \<in> borel_measurable ?B"
        by (rule measurable_compose)
      then show ?thesis by simp
    qed
    have "integrable ?Q (\<lambda>p'. (?Z s p')\<^sup>2)
        = integrable P (\<lambda>\<omega>. (?Z s (pstopped T \<theta> \<omega>))\<^sup>2)"
      unfolding pair_law_of_def by (rule integrable_distr_eq[OF m1 zb])
    moreover have "(\<lambda>\<omega> :: 'n pairpath. (?Z s (pstopped T \<theta> \<omega>))\<^sup>2)
        = (\<lambda>\<omega>. (?Z (min s (\<theta> \<omega>)) \<omega>)\<^sup>2)"
    proof (rule ext)
      fix \<omega> :: "'n pairpath"
      show "(?Z s (pstopped T \<theta> \<omega>))\<^sup>2 = (?Z (min s (\<theta> \<omega>)) \<omega>)\<^sup>2"
        using pstopped_eval_min_T[OF T0' s, of \<theta> \<omega>] by simp
    qed
    ultimately show ?thesis using sqs[OF s] by simp
  qed
  show ?thesis
    by (intro horizon_sq_int_martingale.intro
        horizon_sq_int_martingale_axioms.intro mgQ T0 PQ sqQ)
qed

theorem pstopped_law_horizon_compensated:
  fixes P :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T0: "0 < T" and L0: "0 \<le> L" and P: "P \<in> exit_class k L T x"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
  shows "horizon_sq_int_martingale (pair_law_of T (pstopped T \<theta>) P)
      (natural_filtration (pair_law_of T (pstopped T \<theta>) P) 0 (\<lambda>v \<omega>. \<omega> v))
      (\<lambda>u p'. (outerp (fst (p' (min u T))) - snd (p' (min u T))) $ c $ d) T"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?Q = "pair_law_of T (pstopped T \<theta>) P"
  let ?F = "natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?G = "natural_filtration ?Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?Z = "\<lambda>u \<omega> :: 'n pairpath.
      (outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T))) $ c $ d"
  have T0': "0 \<le> T" using T0 by simp
  have setsP: "sets P = sets ?B" by (rule exit_class_sets[OF P])
  have PS: "prob_space P" by (rule exit_class_prob[OF P])
  have th0: "0 \<le> \<theta> \<omega>" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF st])
  have thT: "\<theta> \<omega> \<le> T" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_le[OF st])
  have m1: "pstopped T \<theta> \<in> P \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsP refl]
    by (rule pstopped_measurable[OF T0' thM th0 thT])
  have PQ: "prob_space ?Q" by (rule pstopped_law_prob[OF T0' PS setsP st thM])
  have sp: "space P = space ?B" by (rule sets_eq_imp_space_eq[OF setsP])
  have nf: "?F v = natural_filtration ?B 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) v" for v
    by (rule natural_filtration_cong_space[OF sp])
  have tstop: "{\<omega> \<in> space P. \<theta> \<omega> \<le> s} \<in> sets (?F s)" if s: "0 \<le> s" for s
  proof -
    have "{\<omega> \<in> space ?B. \<theta> \<omega> \<le> s}
        \<in> sets (natural_filtration ?B 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) s)"
      by (rule path_stopping_time_event_filtration_all[OF T0' st thM s])
    then show ?thesis unfolding nf using sp by simp
  qed
  have HZ: "horizon_sq_int_martingale P ?F ?Z T"
    by (rule exit_class_horizon_compensated[OF T0 L0 P])
  have contT: "continuous_on {0..T} (\<lambda>s. ?Z s \<omega>)" if w: "\<omega> \<in> space P" for \<omega>
  proof -
    have mw: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using w sp by (simp add: space_borel_of)
    show ?thesis by (rule comp_entry_continuous[OF mw])
  qed
  have cap: "?Z s \<omega> = ?Z (min s T) \<omega>" for s and \<omega> :: "'n pairpath" by simp
  have mgs: "martingale P ?F 0 (\<lambda>v \<omega>. ?Z (min v (\<theta> \<omega>)) \<omega>)"
    by (rule horizon_sq_int_martingale_stopped(1)
        [OF T0 HZ cap contT th0 tstop])
  have sqs: "integrable P (\<lambda>\<omega>. (?Z (min s (\<theta> \<omega>)) \<omega>)\<^sup>2)" if s: "0 \<le> s" for s
    by (rule horizon_sq_int_martingale_stopped(2)
        [OF T0 HZ cap contT th0 tstop s])
  have entB: "(\<lambda>z :: (real^'n) \<times> (real^'n^'n).
      (outerp (fst z) - snd z) $ c $ d) \<in> borel_measurable borel"
  proof -
    have s: "(\<lambda>z :: (real^'n) \<times> (real^'n^'n). outerp (fst z) - snd z)
        \<in> borel_measurable borel"
      unfolding outerp_def
      by (intro borel_measurable_continuous_onI continuous_intros)
    have bl: "bounded_linear (\<lambda>M :: real^'n^'n. M $ c $ d)"
      by (rule bounded_linear_compose[OF bounded_linear_vec_nth
          bounded_linear_vec_nth])
    have n: "(\<lambda>M :: real^'n^'n. M $ c $ d) \<in> borel_measurable borel"
      by (rule borel_measurable_continuous_onI) (rule linear_continuous_on[OF bl])
    show ?thesis by (rule measurable_compose[OF s n])
  qed
  have mgp: "martingale P ?F 0 (\<lambda>u \<omega>. ?Z u (pstopped T \<theta> \<omega>))"
  proof (rule martingale_cong_ge[OF mgs])
    fix u :: real assume u: "0 \<le> u"
    show "(\<lambda>\<omega>. ?Z (min u (\<theta> \<omega>)) \<omega>)
        = (\<lambda>\<omega> :: 'n pairpath. ?Z u (pstopped T \<theta> \<omega>))"
    proof (rule ext)
      fix \<omega> :: "'n pairpath"
      show "?Z (min u (\<theta> \<omega>)) \<omega> = ?Z u (pstopped T \<theta> \<omega>)"
        using pstopped_eval_min_T[OF T0' u, of \<theta> \<omega>] by simp
    qed
  qed
  have Zm: "?Z u \<in> borel_measurable (?G u)" if u: "0 \<le> u" for u
  proof -
    have a: "0 \<le> min u T" using u T0' by simp
    have b: "min u T \<le> u" by simp
    show ?thesis
      by (rule measurable_compose[OF path_eval_natural_filtration[OF a b] entB])
  qed
  have mgQ: "martingale ?Q ?G 0 ?Z"
  proof (rule martingale_pair_law[where T = T and FF = ?F])
    show "prob_space P" by (rule PS)
    show "pstopped T \<theta> \<in> P \<rightarrow>\<^sub>M ?B" by (rule m1)
    show "(\<lambda>\<omega>. pstopped T \<theta> \<omega> r) \<in> borel_measurable (?F u)"
      if "0 \<le> r" "r \<le> u" for u r :: real
      by (rule pstopped_eval_filtration[OF T0' setsP st thM that])
    show "?Z u \<in> borel_measurable
        (natural_filtration (pair_law_of T (pstopped T \<theta>) P) 0 (\<lambda>v \<omega>. \<omega> v) u)"
      if "0 \<le> u" for u by (rule Zm[OF that])
    show "martingale P ?F 0 (\<lambda>u \<omega>. ?Z u (pstopped T \<theta> \<omega>))" by (rule mgp)
  qed
  have sqQ: "integrable ?Q (\<lambda>p'. (?Z s p')\<^sup>2)" if s: "0 \<le> s" for s
  proof -
    have zb: "(\<lambda>p' :: 'n pairpath. (?Z s p')\<^sup>2) \<in> borel_measurable ?B"
    proof -
      have "(\<lambda>p' :: 'n pairpath. p' (min s T)) \<in> borel_measurable ?B"
        by (rule pair_law_eval_measurable[OF refl])
      from measurable_compose[OF this entB]
      have "(\<lambda>p' :: 'n pairpath. ?Z s p') \<in> borel_measurable ?B" by simp
      then show ?thesis by simp
    qed
    have "integrable ?Q (\<lambda>p'. (?Z s p')\<^sup>2)
        = integrable P (\<lambda>\<omega>. (?Z s (pstopped T \<theta> \<omega>))\<^sup>2)"
      unfolding pair_law_of_def by (rule integrable_distr_eq[OF m1 zb])
    moreover have "(\<lambda>\<omega> :: 'n pairpath. (?Z s (pstopped T \<theta> \<omega>))\<^sup>2)
        = (\<lambda>\<omega>. (?Z (min s (\<theta> \<omega>)) \<omega>)\<^sup>2)"
    proof (rule ext)
      fix \<omega> :: "'n pairpath"
      show "(?Z s (pstopped T \<theta> \<omega>))\<^sup>2 = (?Z (min s (\<theta> \<omega>)) \<omega>)\<^sup>2"
        using pstopped_eval_min_T[OF T0' s, of \<theta> \<omega>] by simp
    qed
    ultimately show ?thesis using sqs[OF s] by simp
  qed
  show ?thesis
    by (intro horizon_sq_int_martingale.intro
        horizon_sq_int_martingale_axioms.intro mgQ T0 PQ sqQ)
qed

subsection \<open>Uniform first moments for the delayed class\<close>

text \<open>The six remaining side conditions of the additive glue are Fubini
  statements about \<^const>\<open>ksemi\<close>, needing beyond the per-\<open>p'\<close>
  integrability \<open>Kint\<close>/\<open>KintC\<close> an outer bound: a bound on the inner
  integral that does not depend on \<open>p'\<close>.  The class has one
  (@{thm [source] exit_class_norm_mean_le},
  @{thm [source] exit_class_comp_norm_mean_le}) --- depending only on
  \<open>CARD('n)\<close>, \<open>L\<close> and the horizon --- and it survives the delay, because
  the delayed law reads the base law at an earlier time and the bound is
  monotone in the horizon.  The same constant works for every freezing
  time \<open>s\<close>, which makes the outer integral finite.\<close>

lemma pdelclass_norm_mean_le:
  fixes \<nu> :: "('n::finite pairpath) measure"
  assumes L0: "0 \<le> L" and s0: "0 \<le> s" and sT: "s \<le> T"
    and m: "\<nu> \<in> pdelclass k L T s" and u: "u \<in> {0..T}"
  shows "(\<integral>w. norm (fst (w u)) \<partial>\<nu>)
      \<le> 1 + real CARD('n) * (real CARD('n) * L * T)"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?Bs = "(path_borel (T - s) :: ('n pairpath) measure)"
  have T0: "0 \<le> T" using s0 sT by simp
  have Ts: "0 \<le> T - s" using sT by simp
  from m obtain \<mu> where mu: "\<mu> \<in> exit_class k L (T - s) (0::real^'n)"
    and nu: "\<nu> = distr \<mu> ?B (pembed s T)" unfolding pdelclass_def by blast
  have setsmu: "sets \<mu> = sets ?Bs" by (rule exit_class_sets[OF mu])
  have pm: "pembed s T \<in> \<mu> \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsmu refl]
    by (rule pembed_measurable[OF s0 sT])
  have nb: "(\<lambda>w :: 'n pairpath. norm (fst (w u))) \<in> borel_measurable ?B"
  proof -
    have e: "(\<lambda>w :: 'n pairpath. w u) \<in> borel_measurable ?B"
      by (rule pair_law_eval_measurable[OF refl])
    have f: "(\<lambda>z :: (real^'n) \<times> (real^'n^'n). norm (fst z))
        \<in> borel_measurable borel"
      by (intro borel_measurable_continuous_onI continuous_intros)
    show ?thesis by (rule measurable_compose[OF e f])
  qed
  have tmem: "max (u - s) 0 \<in> {0..T - s}" using u s0 sT by auto
  have "(\<integral>w. norm (fst (w u)) \<partial>\<nu>)
      = (\<integral>w'. norm (fst (pembed s T w' u)) \<partial>\<mu>)"
    unfolding nu by (rule integral_distr[OF pm nb])
  also have "\<dots> = (\<integral>w'. norm (fst (w' (max (u - s) 0))) \<partial>\<mu>)"
    by (rule Bochner_Integration.integral_cong[OF refl])
       (simp add: pembed_apply[OF u])
  also have "\<dots> \<le> 1 + real CARD('n) * (real CARD('n) * L * (T - s))"
    by (rule exit_class_norm_mean_le[OF Ts L0 mu tmem])
  also have "\<dots> \<le> 1 + real CARD('n) * (real CARD('n) * L * T)"
    using L0 s0 by (intro add_left_mono mult_left_mono mult_left_mono) auto
  finally show ?thesis .
qed

lemma pdelclass_comp_norm_mean_le:
  fixes \<nu> :: "('n::finite pairpath) measure"
  assumes L0: "0 \<le> L" and s0: "0 \<le> s" and sT: "s \<le> T"
    and m: "\<nu> \<in> pdelclass k L T s" and u: "u \<in> {0..T}"
  shows "(\<integral>w. norm (outerp (fst (w u)) - snd (w u)) \<partial>\<nu>)
      \<le> real CARD('n) * (real CARD('n) * L * T) + real CARD('n) * L * T"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?Bs = "(path_borel (T - s) :: ('n pairpath) measure)"
  have T0: "0 \<le> T" using s0 sT by simp
  have Ts: "0 \<le> T - s" using sT by simp
  from m obtain \<mu> where mu: "\<mu> \<in> exit_class k L (T - s) (0::real^'n)"
    and nu: "\<nu> = distr \<mu> ?B (pembed s T)" unfolding pdelclass_def by blast
  have setsmu: "sets \<mu> = sets ?Bs" by (rule exit_class_sets[OF mu])
  have pm: "pembed s T \<in> \<mu> \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsmu refl]
    by (rule pembed_measurable[OF s0 sT])
  have nb: "(\<lambda>w :: 'n pairpath. norm (outerp (fst (w u)) - snd (w u)))
      \<in> borel_measurable ?B"
  proof -
    have e: "(\<lambda>w :: 'n pairpath. w u) \<in> borel_measurable ?B"
      by (rule pair_law_eval_measurable[OF refl])
    have f: "(\<lambda>z :: (real^'n) \<times> (real^'n^'n). norm (outerp (fst z) - snd z))
        \<in> borel_measurable borel"
      unfolding outerp_def
      by (intro borel_measurable_continuous_onI continuous_intros)
    show ?thesis by (rule measurable_compose[OF e f])
  qed
  have tmem: "max (u - s) 0 \<in> {0..T - s}" using u s0 sT by auto
  have "(\<integral>w. norm (outerp (fst (w u)) - snd (w u)) \<partial>\<nu>)
      = (\<integral>w'. norm (outerp (fst (pembed s T w' u))
            - snd (pembed s T w' u)) \<partial>\<mu>)"
    unfolding nu by (rule integral_distr[OF pm nb])
  also have "\<dots> = (\<integral>w'. norm (outerp (fst (w' (max (u - s) 0)))
        - snd (w' (max (u - s) 0))) \<partial>\<mu>)"
    by (rule Bochner_Integration.integral_cong[OF refl])
       (simp add: pembed_apply[OF u])
  also have "\<dots> \<le> real CARD('n) * (real CARD('n) * L * (T - s))
      + real CARD('n) * L * (T - s)"
    by (rule exit_class_comp_norm_mean_le[OF Ts L0 mu tmem])
  also have "\<dots> \<le> real CARD('n) * (real CARD('n) * L * T)
      + real CARD('n) * L * T"
    using L0 s0 by (intro add_mono mult_left_mono mult_left_mono) auto
  finally show ?thesis .
qed

section \<open>Fubini over the semidirect product: the glue's side conditions\<close>

text \<open>Three generic facts about \<^const>\<open>ksemi\<close>, all from
  @{thm [source] nn_integral_ksemi}: a function of the past alone is
  integrable as soon as it is integrable on the base; a function whose
  inner \<open>\<kappa>\<close>-integral is bounded uniformly in the past is integrable; and
  the inner integral is measurable in the past.  Together with the
  uniform first moments of the delayed class these discharge every side
  condition of the additive glue.\<close>

text \<open>\<open>integral_kernel_measurable\<close> and \<open>integrable_ksemi_of_past_bound\<close> (the
  workhorse: the inner bound may itself be a function of the past, as long
  as that function is integrable --- covering all three shapes the glue
  produces, a constant, \<open>norm (f \<omega>)\<close>, and \<open>norm (f \<omega>) * C\<close>) live in
  @{theory Continuous_Time_Martingales.Semidirect_Kernels}.\<close>

subsection \<open>\<open>RXint\<close> and \<open>RCint\<close>\<close>











end
(*>*)
