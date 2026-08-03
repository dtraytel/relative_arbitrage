(*
  Title:   Brownian_Market.thy
  Content: An n-dimensional Brownian market model discharging the locale
           "sufficiently_volatile_market" of Relative_Arbitrage_Stochastic.

  The market is the product of CARD('n) independent copies of the Wiener
  measure wiener_pre from Brownian_Motion, started at x0, with constant
  instantaneous covariance mat 1 and a deterministic horizon.  For this
  model every assumption of sufficiently_volatile_market --- including the
  martingale property with respect to the natural filtration and the
  martingale-problem identity dynkin_quadratic --- becomes a theorem,
  showing that the axiomatization of the class \<P>\<^sub>x is non-vacuous.
*)

theory Brownian_Market
  imports
    Brownian_Motion
    Relative_Arbitrage_Stochastic
    "Kolmogorov_Chentsov.Kolmogorov_Chentsov_Extras"
begin

section \<open>Independence toolkit\<close>

text \<open>Independence of a pair of random variables transports along a
  pushforward in both directions.\<close>

lemma indep_var_distr_iff:
  assumes M: "prob_space M"
    and T[measurable]: "T \<in> M \<rightarrow>\<^sub>M N"
    and f[measurable]: "f \<in> N \<rightarrow>\<^sub>M S" and g[measurable]: "g \<in> N \<rightarrow>\<^sub>M S'"
  shows "prob_space.indep_var (distr M N T) S f S' g
     \<longleftrightarrow> prob_space.indep_var M S (\<lambda>x. f (T x)) S' (\<lambda>x. g (T x))"
proof -
  interpret prob_space M by fact
  interpret D: prob_space "distr M N T"
    by (rule prob_space_distr[OF T])
  have fD: "f \<in> distr M N T \<rightarrow>\<^sub>M S"
    by (subst measurable_cong_sets[OF sets_distr refl]) (rule f)
  have gD: "g \<in> distr M N T \<rightarrow>\<^sub>M S'"
    by (subst measurable_cong_sets[OF sets_distr refl]) (rule g)
  have fT: "(\<lambda>x. f (T x)) \<in> M \<rightarrow>\<^sub>M S"
    by (rule measurable_compose[OF T f])
  have gT: "(\<lambda>x. g (T x)) \<in> M \<rightarrow>\<^sub>M S'"
    by (rule measurable_compose[OF T g])
  have pair: "(\<lambda>x. (f x, g x)) \<in> N \<rightarrow>\<^sub>M S \<Otimes>\<^sub>M S'"
    by (intro measurable_Pair f g)
  have j: "distr (distr M N T) (S \<Otimes>\<^sub>M S') (\<lambda>x. (f x, g x))
      = distr M (S \<Otimes>\<^sub>M S') (\<lambda>x. (f (T x), g (T x)))"
    by (subst distr_distr[OF pair T]) (simp add: comp_def)
  have m1: "distr (distr M N T) S f = distr M S (\<lambda>x. f (T x))"
    by (subst distr_distr[OF f T]) (simp add: comp_def)
  have m2: "distr (distr M N T) S' g = distr M S' (\<lambda>x. g (T x))"
    by (subst distr_distr[OF g T]) (simp add: comp_def)
  show ?thesis
    unfolding D.indep_var_distribution_eq indep_var_distribution_eq
    using fD gD fT gT j m1 m2 by auto
qed

text \<open>Independence is invariant under replacing the target measures by
  ones with the same sets.\<close>

lemma (in prob_space) indep_vars_cong_sets:
  assumes eq: "\<And>i. i \<in> I \<Longrightarrow> sets (M' i) = sets (N' i)"
    and ind: "indep_vars M' X I"
  shows "indep_vars N' X I"
proof -
  have rv: "random_variable (N' i) (X i)" if i: "i \<in> I" for i
  proof -
    have "random_variable (M' i) (X i)"
      using ind i by (auto simp: indep_vars_def)
    then show ?thesis
      using measurable_cong_sets[OF refl eq[OF i]] by blast
  qed
  have "indep_sets (\<lambda>i. sigma_sets (space M)
      {X i -` A \<inter> space M |A. A \<in> sets (M' i)}) I"
    using ind by (auto simp: indep_vars_def)
  then have "indep_sets (\<lambda>i. sigma_sets (space M)
      {X i -` A \<inter> space M |A. A \<in> sets (N' i)}) I"
    by (rule indep_sets_cong[THEN iffD1, OF refl, rotated])
      (simp add: eq)
  with rv show ?thesis
    by (auto simp: indep_vars_def)
qed

text \<open>Componentwise independent pairs over a finite product measure give an
  independent pair of product-valued vectors.\<close>

lemma indep_var_PiM_components:
  fixes N :: "'i \<Rightarrow> 'b measure" and S :: "'i \<Rightarrow> 'c measure"
    and S' :: "'i \<Rightarrow> 'c measure"
    and g :: "'i \<Rightarrow> 'b \<Rightarrow> 'c" and h :: "'i \<Rightarrow> 'b \<Rightarrow> 'c"
  assumes fin: "finite I"
    and prob: "\<And>i. prob_space (N i)"
    and g: "\<And>i. i \<in> I \<Longrightarrow> g i \<in> N i \<rightarrow>\<^sub>M S i"
    and h: "\<And>i. i \<in> I \<Longrightarrow> h i \<in> N i \<rightarrow>\<^sub>M S' i"
    and ind: "\<And>i. i \<in> I \<Longrightarrow>
      prob_space.indep_var (N i) (S i) (g i) (S' i) (h i)"
  shows "prob_space.indep_var (Pi\<^sub>M I N)
      (Pi\<^sub>M I S) (\<lambda>\<omega>. \<lambda>i\<in>I. g i (\<omega> i))
      (Pi\<^sub>M I S') (\<lambda>\<omega>. \<lambda>i\<in>I. h i (\<omega> i))"
proof -
  interpret P: prob_space "Pi\<^sub>M I N"
    by (intro prob_space_PiM prob)
  interpret PSF: product_sigma_finite N
    by (intro product_sigma_finite.intro prob_space_imp_sigma_finite prob)
  let ?G = "\<lambda>\<omega>. \<lambda>i\<in>I. g i (\<omega> i)" and ?H = "\<lambda>\<omega>. \<lambda>i\<in>I. h i (\<omega> i)"
  have Gm: "?G \<in> Pi\<^sub>M I N \<rightarrow>\<^sub>M Pi\<^sub>M I S"
  proof (rule measurable_restrict)
    fix i assume i: "i \<in> I"
    show "(\<lambda>\<omega>. g i (\<omega> i)) \<in> Pi\<^sub>M I N \<rightarrow>\<^sub>M S i"
      by (rule measurable_compose[OF
          measurable_component_singleton[OF i, where M = N] g[OF i]])
  qed
  have Hm: "?H \<in> Pi\<^sub>M I N \<rightarrow>\<^sub>M Pi\<^sub>M I S'"
  proof (rule measurable_restrict)
    fix i assume i: "i \<in> I"
    show "(\<lambda>\<omega>. h i (\<omega> i)) \<in> Pi\<^sub>M I N \<rightarrow>\<^sub>M S' i"
      by (rule measurable_compose[OF
          measurable_component_singleton[OF i, where M = N] h[OF i]])
  qed
  \<comment> \<open>rectangle preimages generate the two @{text \<sigma>}-algebras\<close>
  define E1 where "E1 = {?G -` Pi\<^sub>E I A \<inter> space (Pi\<^sub>M I N) |
      A. \<forall>i. A i \<in> sets (S i)}"
  define E2 where "E2 = {?H -` Pi\<^sub>E I B \<inter> space (Pi\<^sub>M I N) |
      B. \<forall>i. B i \<in> sets (S' i)}"
  have rect_a: "?G -` Pi\<^sub>E I A \<inter> space (Pi\<^sub>M I N)
      = Pi\<^sub>E I (\<lambda>i. (\<lambda>x. g i x) -` A i \<inter> space (N i))"
    if A: "\<And>i. i \<in> I \<Longrightarrow> A i \<in> sets (S i)" for A
    by (auto simp: space_PiM PiE_iff extensional_def)
  have rect_b: "?H -` Pi\<^sub>E I B \<inter> space (Pi\<^sub>M I N)
      = Pi\<^sub>E I (\<lambda>i. (\<lambda>x. h i x) -` B i \<inter> space (N i))"
    if B: "\<And>i. i \<in> I \<Longrightarrow> B i \<in> sets (S' i)" for B
    by (auto simp: space_PiM PiE_iff extensional_def)
  have fact_ab: "P.prob (a \<inter> b) = P.prob a * P.prob b"
    if a: "a \<in> E1" and b: "b \<in> E2" for a b
  proof -
    from a obtain A where A: "\<And>i. A i \<in> sets (S i)"
      and a_def: "a = ?G -` Pi\<^sub>E I A \<inter> space (Pi\<^sub>M I N)"
      by (auto simp: E1_def)
    from b obtain B where B: "\<And>i. B i \<in> sets (S' i)"
      and b_def: "b = ?H -` Pi\<^sub>E I B \<inter> space (Pi\<^sub>M I N)"
      by (auto simp: E2_def)
    define Cg where "Cg = (\<lambda>i. (\<lambda>x. g i x) -` A i \<inter> space (N i))"
    define Ch where "Ch = (\<lambda>i. (\<lambda>x. h i x) -` B i \<inter> space (N i))"
    have Cg_sets: "\<And>i. i \<in> I \<Longrightarrow> Cg i \<in> sets (N i)"
      unfolding Cg_def by (intro measurable_sets[OF g A])
    have Ch_sets: "\<And>i. i \<in> I \<Longrightarrow> Ch i \<in> sets (N i)"
      unfolding Ch_def by (intro measurable_sets[OF h B])
    have a_rect: "a = Pi\<^sub>E I Cg"
      unfolding a_def Cg_def by (rule rect_a) (rule A)
    have b_rect: "b = Pi\<^sub>E I Ch"
      unfolding b_def Ch_def by (rule rect_b) (rule B)
    have ab_rect: "a \<inter> b = Pi\<^sub>E I (\<lambda>i. Cg i \<inter> Ch i)"
      unfolding a_rect b_rect by (rule PiE_Int)
    have fact_i: "measure (N i) (Cg i \<inter> Ch i)
        = measure (N i) (Cg i) * measure (N i) (Ch i)"
      if i: "i \<in> I" for i
    proof -
      interpret Ni: prob_space "N i" by (rule prob)
      have "(\<lambda>x. (g i x, h i x)) -` (A i \<times> B i) \<inter> space (N i)
          = Cg i \<inter> Ch i"
        by (auto simp: Cg_def Ch_def)
      then show ?thesis
        using Ni.indep_varD[OF ind[OF i] A B]
        by (simp add: Cg_def Ch_def)
    qed
    have prob_rect: "P.prob (Pi\<^sub>E I C) = (\<Prod>i\<in>I. measure (N i) (C i))"
      if C: "\<And>i. i \<in> I \<Longrightarrow> C i \<in> sets (N i)" for C
    proof -
      interpret Ni: prob_space "N i" for i by (rule prob)
      have "emeasure (Pi\<^sub>M I N) (Pi\<^sub>E I C)
          = (\<Prod>i\<in>I. emeasure (N i) (C i))"
        by (rule PSF.emeasure_PiM[OF fin C])
      also have "\<dots> = ennreal (\<Prod>i\<in>I. measure (N i) (C i))"
        by (simp add: Ni.emeasure_eq_measure prod_ennreal)
      finally show ?thesis
        by (simp add: P.emeasure_eq_measure measure_nonneg prod_nonneg)
    qed
    have "P.prob (a \<inter> b) = (\<Prod>i\<in>I. measure (N i) (Cg i \<inter> Ch i))"
      unfolding ab_rect
      by (intro prob_rect) (auto intro: Cg_sets Ch_sets)
    also have "\<dots> = (\<Prod>i\<in>I. measure (N i) (Cg i) * measure (N i) (Ch i))"
      by (intro prod.cong refl fact_i)
    also have "\<dots> = (\<Prod>i\<in>I. measure (N i) (Cg i))
        * (\<Prod>i\<in>I. measure (N i) (Ch i))"
      by (rule prod.distrib)
    also have "\<dots> = P.prob a * P.prob b"
      unfolding a_rect b_rect
      by (simp add: prob_rect[OF Cg_sets] prob_rect[OF Ch_sets])
    finally show ?thesis .
  qed
  have E1_events: "E1 \<subseteq> P.events"
    unfolding E1_def
    by (auto intro!: measurable_sets[OF Gm] sets_PiM_I_finite[OF fin])
  have E2_events: "E2 \<subseteq> P.events"
    unfolding E2_def
    by (auto intro!: measurable_sets[OF Hm] sets_PiM_I_finite[OF fin])
  have E1_Int: "Int_stable E1"
  proof (rule Int_stableI)
    fix a b assume "a \<in> E1" "b \<in> E1"
    then obtain A B where A: "\<forall>i. A i \<in> sets (S i)" "\<forall>i. B i \<in> sets (S i)"
      and "a = ?G -` Pi\<^sub>E I A \<inter> space (Pi\<^sub>M I N)"
        "b = ?G -` Pi\<^sub>E I B \<inter> space (Pi\<^sub>M I N)"
      by (auto simp: E1_def)
    then have "a \<inter> b = ?G -` Pi\<^sub>E I (\<lambda>i. A i \<inter> B i) \<inter> space (Pi\<^sub>M I N)"
      by (auto simp: PiE_Int)
    then show "a \<inter> b \<in> E1"
      using A unfolding E1_def by (intro CollectI exI[of _ "\<lambda>i. A i \<inter> B i"]) auto
  qed
  have E2_Int: "Int_stable E2"
  proof (rule Int_stableI)
    fix a b assume "a \<in> E2" "b \<in> E2"
    then obtain A B where A: "\<forall>i. A i \<in> sets (S' i)" "\<forall>i. B i \<in> sets (S' i)"
      and "a = ?H -` Pi\<^sub>E I A \<inter> space (Pi\<^sub>M I N)"
        "b = ?H -` Pi\<^sub>E I B \<inter> space (Pi\<^sub>M I N)"
      by (auto simp: E2_def)
    then have "a \<inter> b = ?H -` Pi\<^sub>E I (\<lambda>i. A i \<inter> B i) \<inter> space (Pi\<^sub>M I N)"
      by (auto simp: PiE_Int)
    then show "a \<inter> b \<in> E2"
      using A unfolding E2_def by (intro CollectI exI[of _ "\<lambda>i. A i \<inter> B i"]) auto
  qed
  have "P.indep_set E1 E2"
    by (rule P.indep_setI[OF E1_events E2_events fact_ab])
  then have "P.indep_sets (case_bool E1 E2) UNIV"
    unfolding P.indep_set_def .
  then have "P.indep_sets (\<lambda>b. sigma_sets (space (Pi\<^sub>M I N))
      (case_bool E1 E2 b)) UNIV"
    by (rule P.indep_sets_sigma) (auto split: bool.split
        simp: E1_Int E2_Int)
  then have sig: "P.indep_set (sigma_sets (space (Pi\<^sub>M I N)) E1)
      (sigma_sets (space (Pi\<^sub>M I N)) E2)"
    unfolding P.indep_set_def
    by (rule P.indep_sets_cong[THEN iffD1, OF refl, rotated])
      (auto split: bool.split)
  \<comment> \<open>the rectangle preimages generate the full vimage @{text \<sigma>}-algebras\<close>
  have gen: "sigma_sets (space (Pi\<^sub>M I N))
      {F -` X \<inter> space (Pi\<^sub>M I N) |X. X \<in> sets (Pi\<^sub>M I T)}
      \<subseteq> sigma_sets (space (Pi\<^sub>M I N)) E"
    if Fm: "F \<in> Pi\<^sub>M I N \<rightarrow>\<^sub>M Pi\<^sub>M I T"
      and Emem: "\<And>A. (\<forall>i. A i \<in> sets (T i)) \<Longrightarrow>
        F -` Pi\<^sub>E I A \<inter> space (Pi\<^sub>M I N) \<in> E"
    for F :: "('i \<Rightarrow> 'b) \<Rightarrow> 'i \<Rightarrow> 'e" and T :: "'i \<Rightarrow> 'e measure" and E
  proof -
    have Fsp: "F \<in> space (Pi\<^sub>M I N) \<rightarrow> space (Pi\<^sub>M I T)"
      using measurable_space[OF Fm] by auto
    have "{F -` X \<inter> space (Pi\<^sub>M I N) |X. X \<in> sets (Pi\<^sub>M I T)}
        = {F -` X \<inter> space (Pi\<^sub>M I N) |X. X \<in> sigma_sets (space (Pi\<^sub>M I T))
            {Pi\<^sub>E I A |A. (\<forall>i. A i \<in> sets (T i)) \<and>
              finite {i. A i \<noteq> space (T i)}}}"
      by (simp add: sets_PiM_finite space_PiM)
    also have "\<dots> = sigma_sets (space (Pi\<^sub>M I N))
        {F -` X \<inter> space (Pi\<^sub>M I N) |X. X \<in> {Pi\<^sub>E I A |A.
          (\<forall>i. A i \<in> sets (T i)) \<and> finite {i. A i \<noteq> space (T i)}}}"
      by (rule sigma_sets_vimage_commute[OF Fsp])
    also have "\<dots> \<subseteq> sigma_sets (space (Pi\<^sub>M I N)) E"
    proof (rule sigma_sets_mono)
      show "{F -` X \<inter> space (Pi\<^sub>M I N) |X. X \<in> {Pi\<^sub>E I A |A.
          (\<forall>i. A i \<in> sets (T i)) \<and> finite {i. A i \<noteq> space (T i)}}}
          \<subseteq> sigma_sets (space (Pi\<^sub>M I N)) E"
        by (auto intro!: sigma_sets.Basic Emem)
    qed
    finally have fam: "{F -` X \<inter> space (Pi\<^sub>M I N) |X. X \<in> sets (Pi\<^sub>M I T)}
        \<subseteq> sigma_sets (space (Pi\<^sub>M I N)) E" .
    show ?thesis
      by (rule sigma_sets_mono[OF fam])
  qed
  have genG: "sigma_sets (space (Pi\<^sub>M I N))
      {?G -` X \<inter> space (Pi\<^sub>M I N) |X. X \<in> sets (Pi\<^sub>M I S)}
      \<subseteq> sigma_sets (space (Pi\<^sub>M I N)) E1"
    by (intro gen[OF Gm]) (auto simp: E1_def)
  have genH: "sigma_sets (space (Pi\<^sub>M I N))
      {?H -` X \<inter> space (Pi\<^sub>M I N) |X. X \<in> sets (Pi\<^sub>M I S')}
      \<subseteq> sigma_sets (space (Pi\<^sub>M I N)) E2"
    by (intro gen[OF Hm]) (auto simp: E2_def)
  have main: "P.indep_set
      (sigma_sets (space (Pi\<^sub>M I N))
        {?G -` X \<inter> space (Pi\<^sub>M I N) |X. X \<in> sets (Pi\<^sub>M I S)})
      (sigma_sets (space (Pi\<^sub>M I N))
        {?H -` X \<inter> space (Pi\<^sub>M I N) |X. X \<in> sets (Pi\<^sub>M I S')})"
  proof -
    have "P.indep_sets (case_bool
        (sigma_sets (space (Pi\<^sub>M I N)) E1)
        (sigma_sets (space (Pi\<^sub>M I N)) E2)) UNIV"
      using sig unfolding P.indep_set_def .
    then have "P.indep_sets (case_bool
        (sigma_sets (space (Pi\<^sub>M I N))
          {?G -` X \<inter> space (Pi\<^sub>M I N) |X. X \<in> sets (Pi\<^sub>M I S)})
        (sigma_sets (space (Pi\<^sub>M I N))
          {?H -` X \<inter> space (Pi\<^sub>M I N) |X. X \<in> sets (Pi\<^sub>M I S')})) UNIV"
      by (rule P.indep_sets_mono_sets)
        (auto split: bool.split simp: genG genH)
    then show ?thesis
      unfolding P.indep_set_def .
  qed
  show ?thesis
    unfolding P.indep_var_eq
    using Gm Hm main by blast
qed

section \<open>The past and an increment of the Wiener measure are independent\<close>

text \<open>The finite past and an increment of the Wiener measure are
  independent.  Since @{const prob_space.indep_var} forces both variables
  to take values in a common type, the increment is encoded as a
  one-point function.\<close>

lemma wiener_pre_past_increment_indep:
  assumes U: "finite U" "U \<subseteq> {0..s}" and s: "0 \<le> s" and st: "s < t"
  shows "W.indep_var (Pi\<^sub>M U (\<lambda>_. borel)) (\<lambda>\<omega>. restrict \<omega> U)
    (Pi\<^sub>M {t} (\<lambda>_. borel)) (\<lambda>\<omega>. \<lambda>u\<in>{t}. \<omega> t - \<omega> s)"
proof -
  define J where "J = U \<union> {s, t}"
  have finJ: "finite J" using U by (simp add: J_def)
  have J0: "J \<subseteq> {0..}" using U s st by (auto simp: J_def)
  have sJ: "s \<in> J" and tJ: "t \<in> J" and UJ: "U \<subseteq> J"
    by (auto simp: J_def)
  define grp1 where "grp1 = {v \<in> J. v \<le> s}"
  define grp2 where "grp2 = {v \<in> J. s < v}"
  have grp1_eq: "grp1 = U \<union> {s}"
    using U st by (auto simp: grp1_def J_def)
  have grp2_eq: "grp2 = {t}"
    using U st by (auto simp: grp2_def J_def)
  interpret IP: prob_space "inc_prod 0 J" by simp
  \<comment> \<open>the coordinates of the increment product are independent\<close>
  interpret PPS: product_prob_space
    "\<lambda>u. gauss_measure (u - prevt 0 J u)" J
    by (intro product_prob_space.intro product_sigma_finite.intro
        product_prob_space_axioms.intro sigma_finite_gauss_measure
        prob_space_gauss_measure)
  have coords: "IP.indep_vars (\<lambda>_. borel) (\<lambda>u w. w u) J"
  proof -
    have "prob_space.indep_vars (Pi\<^sub>M J (\<lambda>u. gauss_measure (u - prevt 0 J u)))
        (\<lambda>u. gauss_measure (u - prevt 0 J u)) (\<lambda>u w. w u) J"
      using finJ sJ by (intro PPS.indep_vars_PiM_coordinate) auto
    then have "IP.indep_vars (\<lambda>u. gauss_measure (u - prevt 0 J u))
        (\<lambda>u w. w u) J"
      by (simp add: inc_prod_def)
    then show ?thesis
      by (rule IP.indep_vars_cong_sets[rotated]) simp
  qed
  \<comment> \<open>group them into past and future coordinates\<close>
  have grouped: "IP.indep_var
      (Pi\<^sub>M grp1 (\<lambda>_. borel)) (\<lambda>w. restrict w grp1)
      (Pi\<^sub>M grp2 (\<lambda>_. borel)) (\<lambda>w. restrict w grp2)"
  proof -
    have disj: "grp1 \<inter> grp2 = {}"
      by (auto simp: grp1_def grp2_def)
    have s1: "grp1 \<subseteq> J" and s2: "grp2 \<subseteq> J"
      by (auto simp: grp1_def grp2_def)
    show ?thesis
      using IP.indep_var_restrict[OF coords disj s1 s2] by simp
  qed
  \<comment> \<open>past values and the increment are functions of the two groups\<close>
  define ph1 where "ph1 = (\<lambda>h :: real \<Rightarrow> real.
      \<lambda>u\<in>U. \<Sum>v\<in>{v \<in> grp1. v \<le> u}. h v)"
  define ph2 where "ph2 = (\<lambda>h :: real \<Rightarrow> real. \<lambda>u\<in>{t}. h t)"
  have ph1m: "ph1 \<in> Pi\<^sub>M grp1 (\<lambda>_. borel) \<rightarrow>\<^sub>M Pi\<^sub>M U (\<lambda>_. (borel :: real measure))"
    unfolding ph1_def
    by (intro measurable_restrict borel_measurable_sum
        measurable_component_singleton) auto
  have ph2m: "ph2 \<in> Pi\<^sub>M grp2 (\<lambda>_. borel) \<rightarrow>\<^sub>M Pi\<^sub>M {t} (\<lambda>_. (borel :: real measure))"
    unfolding ph2_def grp2_eq
    by (intro measurable_restrict measurable_component_singleton) simp
  have comp_ind: "IP.indep_var (Pi\<^sub>M U (\<lambda>_. borel))
      (\<lambda>w. ph1 (restrict w grp1)) (Pi\<^sub>M {t} (\<lambda>_. borel))
      (\<lambda>w. ph2 (restrict w grp2))"
    using IP.indep_var_compose[OF grouped ph1m ph2m]
    by (simp add: comp_def)
  \<comment> \<open>identify the composed maps with restriction/increment after csum\<close>
  have csum_val: "csum J w u = (\<Sum>v\<in>{v \<in> J. v \<le> u}. w v)"
    if "u \<in> J" for w u
    using that by (simp add: csum_def)
  have past_eq: "(\<lambda>w. ph1 (restrict w grp1))
      = (\<lambda>w. restrict (csum J w) U)"
  proof
    fix w :: "real \<Rightarrow> real"
    show "ph1 (restrict w grp1) = restrict (csum J w) U"
      unfolding ph1_def
    proof (rule restrict_ext)
      fix u assume u: "u \<in> U"
      have uJ: "u \<in> J" using u UJ by blast
      have us: "u \<le> s" using u U by auto
      have seteq: "{v \<in> grp1. v \<le> u} = {v \<in> J. v \<le> u}"
        using us by (auto simp: grp1_def)
      have "(\<Sum>v\<in>{v \<in> grp1. v \<le> u}. restrict w grp1 v)
          = (\<Sum>v\<in>{v \<in> grp1. v \<le> u}. w v)"
        by (intro sum.cong refl) (auto simp: grp1_def)
      then show "(\<Sum>v\<in>{v \<in> grp1. v \<le> u}. restrict w grp1 v)
          = csum J w u"
        by (simp add: csum_val[OF uJ] seteq)
    qed
  qed
  have inc_eq: "(\<lambda>w. ph2 (restrict w grp2))
      = (\<lambda>w. \<lambda>u\<in>{t}. csum J w t - csum J w s)"
  proof
    fix w :: "real \<Rightarrow> real"
    have subs: "{v \<in> J. v \<le> s} \<subseteq> {v \<in> J. v \<le> t}"
      using st by auto
    have ddiff: "{v \<in> J. v \<le> t} - {v \<in> J. v \<le> s} = {t}"
      using U st tJ by (auto simp: J_def)
    have "csum J w t - csum J w s
        = (\<Sum>v\<in>{v \<in> J. v \<le> t}. w v) - (\<Sum>v\<in>{v \<in> J. v \<le> s}. w v)"
      by (simp add: csum_val[OF tJ] csum_val[OF sJ])
    also have "\<dots> = (\<Sum>v\<in>{v \<in> J. v \<le> t} - {v \<in> J. v \<le> s}. w v)"
      using finJ subs by (subst sum_diff) auto
    also have "\<dots> = w t"
      unfolding ddiff by simp
    finally have wt: "csum J w t - csum J w s = w t" .
    have "restrict w grp2 t = w t"
      using st tJ by (simp add: grp2_def)
    then show "ph2 (restrict w grp2) = (\<lambda>u\<in>{t}. csum J w t - csum J w s)"
      by (simp add: ph2_def wt)
  qed
  have over_inc: "IP.indep_var (Pi\<^sub>M U (\<lambda>_. borel))
      (\<lambda>w. restrict (csum J w) U) (Pi\<^sub>M {t} (\<lambda>_. borel))
      (\<lambda>w. \<lambda>u\<in>{t}. csum J w t - csum J w s)"
    using comp_ind unfolding past_eq inc_eq .
  \<comment> \<open>transport along csum to the finite-dimensional distribution\<close>
  have restrU: "(\<lambda>h. restrict h U)
      \<in> Pi\<^sub>M J (\<lambda>_. borel) \<rightarrow>\<^sub>M Pi\<^sub>M U (\<lambda>_. (borel :: real measure))"
    by (rule measurable_restrict_subset[OF UJ])
  have DJ: "(\<lambda>h. \<lambda>u\<in>{t}. h t - h s)
      \<in> Pi\<^sub>M J (\<lambda>_. borel) \<rightarrow>\<^sub>M Pi\<^sub>M {t} (\<lambda>_. (borel :: real measure))"
    using sJ tJ
    by (intro measurable_restrict borel_measurable_diff
        measurable_component_singleton)
  have iff1: "prob_space.indep_var (distr (inc_prod 0 J)
        (Pi\<^sub>M J (\<lambda>_. borel)) (csum J))
      (Pi\<^sub>M U (\<lambda>_. borel)) (\<lambda>h. restrict h U)
      (Pi\<^sub>M {t} (\<lambda>_. borel)) (\<lambda>h. \<lambda>u\<in>{t}. h t - h s)
      \<longleftrightarrow> IP.indep_var (Pi\<^sub>M U (\<lambda>_. borel)) (\<lambda>w. restrict (csum J w) U)
        (Pi\<^sub>M {t} (\<lambda>_. borel)) (\<lambda>w. \<lambda>u\<in>{t}. csum J w t - csum J w s)"
    by (rule indep_var_distr_iff[OF prob_space_inc_prod
        measurable_csum_inc_prod restrU DJ])
  have over_fdd: "prob_space.indep_var (bm_fdd J)
      (Pi\<^sub>M U (\<lambda>_. borel)) (\<lambda>h. restrict h U)
      (Pi\<^sub>M {t} (\<lambda>_. borel)) (\<lambda>h. \<lambda>u\<in>{t}. h t - h s)"
    using iff1 over_inc by (simp add: bm_fdd_def)
  \<comment> \<open>transport along the marginal map to the Wiener measure\<close>
  have iff2: "prob_space.indep_var (distr wiener_pre
        (Pi\<^sub>M J (\<lambda>_. borel)) (\<lambda>f. restrict f J))
      (Pi\<^sub>M U (\<lambda>_. borel)) (\<lambda>h. restrict h U)
      (Pi\<^sub>M {t} (\<lambda>_. borel)) (\<lambda>h. \<lambda>u\<in>{t}. h t - h s)
      \<longleftrightarrow> W.indep_var (Pi\<^sub>M U (\<lambda>_. borel))
        (\<lambda>\<omega>. restrict (restrict \<omega> J) U)
        (Pi\<^sub>M {t} (\<lambda>_. borel))
        (\<lambda>\<omega>. \<lambda>u\<in>{t}. restrict \<omega> J t - restrict \<omega> J s)"
    by (rule indep_var_distr_iff[OF prob_space_wiener_pre
        measurable_restrict_wiener_pre[OF J0] restrU DJ])
  have "W.indep_var (Pi\<^sub>M U (\<lambda>_. borel))
      (\<lambda>\<omega>. restrict (restrict \<omega> J) U)
      (Pi\<^sub>M {t} (\<lambda>_. borel))
      (\<lambda>\<omega>. \<lambda>u\<in>{t}. restrict \<omega> J t - restrict \<omega> J s)"
    using over_fdd iff2 by (simp add: wiener_pre_marginal[OF finJ J0])
  moreover have "(\<lambda>\<omega> :: real \<Rightarrow> real. restrict (restrict \<omega> J) U)
      = (\<lambda>\<omega>. restrict \<omega> U)"
    using UJ by (auto simp: restrict_def fun_eq_iff)
  moreover have "(\<lambda>\<omega> :: real \<Rightarrow> real. \<lambda>u\<in>{t}. restrict \<omega> J t - restrict \<omega> J s)
      = (\<lambda>\<omega>. \<lambda>u\<in>{t}. \<omega> t - \<omega> s)"
    using sJ tJ by (auto simp: restrict_def fun_eq_iff)
  ultimately show ?thesis by simp
qed

section \<open>The product Brownian model\<close>

definition bm_paths :: "('n::finite \<Rightarrow> real \<Rightarrow> real) measure" where
  "bm_paths = Pi\<^sub>M UNIV (\<lambda>_. wiener_pre)"

lemma prob_space_bm_paths [intro, simp]: "prob_space bm_paths"
  unfolding bm_paths_def
  by (intro prob_space_PiM prob_space_wiener_pre)

interpretation BMP: prob_space "bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure"
  by simp

interpretation BMC: product_prob_space "\<lambda>_ :: 'n::finite. wiener_pre" UNIV
  by (intro product_prob_space.intro product_sigma_finite.intro
      product_prob_space_axioms.intro prob_space_imp_sigma_finite
      prob_space_wiener_pre)

lemma bm_paths_component:
  "distr (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure) wiener_pre
    (\<lambda>\<omega>. \<omega> i) = wiener_pre"
  unfolding bm_paths_def by (rule BMC.PiM_component) simp

lemma measurable_bm_coordinate [measurable]:
  assumes u: "u \<in> {0..}"
  shows "(\<lambda>\<omega>. \<omega> i u) \<in> (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure)
    \<rightarrow>\<^sub>M (borel :: real measure)"
proof -
  have "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i)
      \<in> Pi\<^sub>M UNIV (\<lambda>_. wiener_pre) \<rightarrow>\<^sub>M wiener_pre"
    by (rule measurable_component_singleton) simp
  then show ?thesis
    unfolding bm_paths_def
    by (rule measurable_compose[OF _ measurable_coord[OF u]])
qed

section \<open>Gaussian first and second moments\<close>

lemma gauss_measure_mean:
  shows gauss_measure_mean_integrable:
    "integrable (gauss_measure v) (\<lambda>y. y)"
    and gauss_measure_mean_integral:
    "(\<integral>y. y \<partial>gauss_measure v) = 0"
proof -
  have both: "integrable (gauss_measure v) (\<lambda>y. y)
      \<and> (\<integral>y. y \<partial>gauss_measure v) = 0"
  proof (cases "v \<le> 0")
    case True
    then have g: "gauss_measure v = return borel 0"
      by (simp add: gauss_measure_def)
    have "integrable (return borel (0 :: real)) (\<lambda>y. y)"
      by (auto simp: integrable_iff_bounded nn_integral_return)
    moreover have "(\<integral>y. y \<partial>return borel (0 :: real)) = 0"
      by (subst integral_return) auto
    ultimately show ?thesis by (simp add: g)
  next
    case False
    then have v: "0 < v" by simp
    have "has_bochner_integral lborel
        (\<lambda>x. normal_density 0 (sqrt v) x * (x - 0) ^ (2 * 0 + 1)) 0"
      using normal_moment_odd[of "sqrt v" 0 0] v by simp
    then have "has_bochner_integral lborel
        (\<lambda>x. normal_density 0 (sqrt v) x * x) 0"
      by simp
    then have "has_bochner_integral
        (density lborel (normal_density 0 (sqrt v))) (\<lambda>y. y) 0"
      by (subst has_bochner_integral_density)
        (auto simp: normal_density_nonneg mult_ac)
    then have "has_bochner_integral (gauss_measure v) (\<lambda>y. y) 0"
      using v by (simp add: gauss_measure_pos)
    then show ?thesis
      by (auto intro: integrable.intros has_bochner_integral_integral_eq)
  qed
  from both show "integrable (gauss_measure v) (\<lambda>y. y)"
    and "(\<integral>y. y \<partial>gauss_measure v) = 0" by auto
qed

lemma gauss_measure_snd_moment:
  assumes v: "0 \<le> v"
  shows gauss_measure_snd_moment_integrable:
    "integrable (gauss_measure v) (\<lambda>y. y\<^sup>2)"
    and gauss_measure_snd_moment_integral:
    "(\<integral>y. y\<^sup>2 \<partial>gauss_measure v) = v"
proof -
  have both: "integrable (gauss_measure v) (\<lambda>y. y\<^sup>2)
      \<and> (\<integral>y. y\<^sup>2 \<partial>gauss_measure v) = v"
  proof (cases "v = 0")
    case True
    have "integrable (return borel (0 :: real)) (\<lambda>y. y\<^sup>2)"
      by (auto simp: integrable_iff_bounded nn_integral_return)
    moreover have "(\<integral>y. y\<^sup>2 \<partial>return borel (0 :: real)) = 0"
      by (subst integral_return) auto
    ultimately show ?thesis
      by (simp add: True gauss_measure_zero)
  next
    case False
    with v have v': "0 < v" by simp
    have "has_bochner_integral (gauss_measure v) (\<lambda>x. x ^ (2 * 1))
        (fact (2 * 1) / (2 ^ 1 * fact 1) * v ^ 1)"
      by (rule gauss_measure_moment_even[OF v'])
    then have "has_bochner_integral (gauss_measure v) (\<lambda>y. y\<^sup>2) v"
      by simp
    then show ?thesis
      by (auto intro: integrable.intros has_bochner_integral_integral_eq)
  qed
  from both show "integrable (gauss_measure v) (\<lambda>y. y\<^sup>2)"
    and "(\<integral>y. y\<^sup>2 \<partial>gauss_measure v) = v" by auto
qed

lemma gauss_shifted_square:
  assumes v: "0 \<le> v"
  shows gauss_shifted_square_integrable:
    "integrable (gauss_measure v) (\<lambda>y. (c + y)\<^sup>2)"
    and gauss_shifted_square_integral:
    "(\<integral>y. (c + y)\<^sup>2 \<partial>gauss_measure v) = c\<^sup>2 + v"
proof -
  interpret G: prob_space "gauss_measure v" by simp
  note mean_int = gauss_measure_mean_integrable[of v]
  note mean_val = gauss_measure_mean_integral[of v]
  note sq_int = gauss_measure_snd_moment_integrable[OF v]
  note sq_val = gauss_measure_snd_moment_integral[OF v]
  have expand: "\<And>y :: real. (c + y)\<^sup>2 = c\<^sup>2 + ((2 * c) * y + y\<^sup>2)"
    by (simp add: power2_eq_square field_simps)
  have int_lin: "integrable (gauss_measure v) (\<lambda>y. (2 * c) * y)"
    by (intro integrable_mult_right mean_int)
  have int_rest: "integrable (gauss_measure v) (\<lambda>y. (2 * c) * y + y\<^sup>2)"
    by (intro Bochner_Integration.integrable_add int_lin sq_int)
  show "integrable (gauss_measure v) (\<lambda>y. (c + y)\<^sup>2)"
    unfolding expand
    by (intro Bochner_Integration.integrable_add int_rest
        G.integrable_const)
  have pu: "G.prob UNIV = 1"
    using G.prob_space by simp
  have e2: "(\<integral>y. (2 * c) * y + y\<^sup>2 \<partial>gauss_measure v) = v"
  proof -
    have "(\<integral>y. (2 * c) * y + y\<^sup>2 \<partial>gauss_measure v)
        = (\<integral>y. (2 * c) * y \<partial>gauss_measure v) + (\<integral>y. y\<^sup>2 \<partial>gauss_measure v)"
      by (rule Bochner_Integration.integral_add[OF int_lin sq_int])
    then show ?thesis
      by (simp add: mean_val sq_val)
  qed
  show "(\<integral>y. (c + y)\<^sup>2 \<partial>gauss_measure v) = c\<^sup>2 + v"
    unfolding expand
    by (subst Bochner_Integration.integral_add[OF G.integrable_const
        int_rest]) (simp add: pu e2)
qed

section \<open>Coordinate moments of the product model\<close>

lemma wiener_pre_coord':
  assumes u: "0 \<le> u"
  shows "distr wiener_pre borel (\<lambda>\<omega>. \<omega> u) = gauss_measure u"
proof -
  have ae: "AE \<omega> in wiener_pre. \<omega> u = \<omega> u - \<omega> 0"
    using wiener_pre_start by eventually_elim simp
  have m1: "(\<lambda>\<omega>. \<omega> u) \<in> wiener_pre \<rightarrow>\<^sub>M (borel :: real measure)"
    using u by (intro measurable_coord) simp
  have m2: "(\<lambda>\<omega>. \<omega> u - \<omega> 0) \<in> wiener_pre \<rightarrow>\<^sub>M (borel :: real measure)"
    using u by (intro borel_measurable_diff measurable_coord) simp_all
  have "distr wiener_pre borel (\<lambda>\<omega>. \<omega> u)
      = distr wiener_pre borel (\<lambda>\<omega>. \<omega> u - \<omega> 0)"
    by (rule distr_cong_AE[OF refl refl ae m1 m2])
  also have "\<dots> = gauss_measure (u - 0)"
    by (rule wiener_pre_increment[OF order_refl u])
  finally show ?thesis by simp
qed

lemma bm_coordinate_distr:
  assumes u: "0 \<le> u"
  shows "distr (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure) borel
    (\<lambda>\<omega>. \<omega> i u) = gauss_measure u"
proof -
  have cu: "(\<lambda>\<omega>. \<omega> u) \<in> wiener_pre \<rightarrow>\<^sub>M (borel :: real measure)"
    using u by (intro measurable_coord) simp
  have ci: "(\<lambda>\<omega>. \<omega> i) \<in> (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      \<rightarrow>\<^sub>M wiener_pre"
    unfolding bm_paths_def
    by (rule measurable_component_singleton) simp
  have "distr (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) borel (\<lambda>\<omega>. \<omega> i u)
      = distr (distr bm_paths wiener_pre (\<lambda>\<omega>. \<omega> i)) borel (\<lambda>\<omega>. \<omega> u)"
    by (subst distr_distr[OF cu ci]) (simp add: comp_def)
  also have "\<dots> = distr wiener_pre borel (\<lambda>\<omega>. \<omega> u)"
    by (simp add: bm_paths_component)
  also have "\<dots> = gauss_measure u"
    by (rule wiener_pre_coord'[OF u])
  finally show ?thesis .
qed

lemma bm_coordinate_sq:
  assumes u: "0 \<le> u"
  shows bm_coordinate_sq_integrable:
    "integrable (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>\<omega>. (c + \<omega> i u)\<^sup>2)"
    and bm_coordinate_sq_integral:
    "(\<integral>\<omega>. (c + \<omega> i u)\<^sup>2 \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      = c\<^sup>2 + u"
proof -
  have m: "(\<lambda>\<omega>. \<omega> i u) \<in> (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      \<rightarrow>\<^sub>M (borel :: real measure)"
    using u by (intro measurable_bm_coordinate) simp
  have sq_meas: "(\<lambda>y :: real. (c + y)\<^sup>2) \<in> borel_measurable borel"
    by measurable
  have "integrable (distr (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) borel
      (\<lambda>\<omega>. \<omega> i u)) (\<lambda>y. (c + y)\<^sup>2)"
    unfolding bm_coordinate_distr[OF u]
    by (rule gauss_shifted_square_integrable[OF u])
  then show "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>\<omega>. (c + \<omega> i u)\<^sup>2)"
    by (rule integrable_distr[OF m])
  have "(\<integral>\<omega>. (c + \<omega> i u)\<^sup>2 \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      = (\<integral>y. (c + y)\<^sup>2 \<partial>distr bm_paths borel (\<lambda>\<omega>. \<omega> i u))"
    by (rule integral_distr[OF m sq_meas, symmetric])
  also have "\<dots> = c\<^sup>2 + u"
    unfolding bm_coordinate_distr[OF u]
    by (rule gauss_shifted_square_integral[OF u])
  finally show "(\<integral>\<omega>. (c + \<omega> i u)\<^sup>2
      \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)) = c\<^sup>2 + u" .
qed

section \<open>The market process\<close>

lemma measurable_vec_components [measurable]:
  fixes f :: "'i::finite \<Rightarrow> 'a \<Rightarrow> real"
  assumes "\<And>i. (\<lambda>x. f i x) \<in> borel_measurable M"
  shows "(\<lambda>x. (\<chi> i. f i x) :: real^'i) \<in> borel_measurable M"
proof (subst borel_measurable_euclidean_space, safe)
  fix b :: "real^'i" assume "b \<in> Basis"
  then obtain i where b: "b = axis i 1"
    by (auto simp: Basis_vec_def Basis_real_def)
  show "(\<lambda>x. ((\<chi> i. f i x) :: real^'i) \<bullet> b) \<in> borel_measurable M"
    unfolding b by (simp add: inner_axis assms)
qed

definition bmX :: "real^'n::finite \<Rightarrow> real \<Rightarrow> ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real^'n"
  where "bmX x0 t \<omega> = x0 + (\<chi> i. \<omega> i t)"

lemma measurable_bmX [measurable]:
  assumes "t \<in> {0..}"
  shows "bmX x0 t \<in> bm_paths \<rightarrow>\<^sub>M (borel :: (real^'n::finite) measure)"
  unfolding bmX_def
  by (intro borel_measurable_add borel_measurable_const
      measurable_vec_components measurable_bm_coordinate[OF assms])

lemma bmX_start:
  fixes x0 :: "real^'n::finite"
  shows "AE \<omega> in bm_paths. bmX x0 0 \<omega> = x0"
proof -
  have coord0: "AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure). \<omega> i 0 = 0"
    for i :: 'n
  proof -
    have ci: "(\<lambda>\<omega>. \<omega> i) \<in> (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
        \<rightarrow>\<^sub>M wiener_pre"
      unfolding bm_paths_def by (intro measurable_component_singleton) simp
    have c0: "(\<lambda>p. p (0 :: real)) \<in> wiener_pre \<rightarrow>\<^sub>M (borel :: real measure)"
      by (rule measurable_coord) simp
    have pred: "{p \<in> space wiener_pre. p 0 = 0} \<in> sets wiener_pre"
    proof -
      have "{p \<in> space wiener_pre. p 0 = 0}
          = (\<lambda>p. p (0 :: real)) -` {0} \<inter> space wiener_pre"
        by auto
      then show ?thesis
        using measurable_sets[OF c0, of "{0}"] by simp
    qed
    have pred': "{p \<in> space wiener_pre. p 0 = 0}
        \<in> sets (Pi\<^sub>M {0..} (\<lambda>_. borel :: real measure))"
      using pred unfolding sets_wiener_pre .
    have "AE p in distr (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
        wiener_pre (\<lambda>\<omega>. \<omega> i). p 0 = 0"
      unfolding bm_paths_component by (rule wiener_pre_start)
    then show ?thesis
      by (subst (asm) AE_distr_iff) (auto intro: ci pred')
  qed
  have "AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
      \<forall>i\<in>(UNIV :: 'n set). \<omega> i 0 = 0"
    by (subst AE_ball_countable)
      (auto intro: coord0 simp: countable_finite)
  then show ?thesis
    unfolding bmX_def
  proof eventually_elim
    case (elim \<omega>)
    then show ?case
      by (simp add: vec_eq_iff)
  qed
qed

section \<open>The Dynkin identity for a deterministic time\<close>

lemma trace_mat1: "trace (mat 1 :: real^'n::finite^'n) = real CARD('n)"
  by (simp add: trace_def mat_def)

lemma bmX_sq:
  fixes x0 :: "real^'n::finite"
  assumes u: "0 \<le> u"
  shows bmX_sq_integrable:
    "integrable bm_paths (\<lambda>\<omega>. bmX x0 u \<omega> \<bullet> bmX x0 u \<omega>)"
    and bmX_sq_integral:
    "(\<integral>\<omega>. bmX x0 u \<omega> \<bullet> bmX x0 u \<omega> \<partial>bm_paths)
      = x0 \<bullet> x0 + real CARD('n) * u"
proof -
  have expand: "bmX x0 u \<omega> \<bullet> bmX x0 u \<omega>
      = (\<Sum>i\<in>UNIV. (x0 $ i + \<omega> i u)\<^sup>2)" for \<omega> :: "'n \<Rightarrow> real \<Rightarrow> real"
    by (simp add: bmX_def inner_vec_def power2_eq_square)
  show "integrable bm_paths (\<lambda>\<omega>. bmX x0 u \<omega> \<bullet> bmX x0 u \<omega>)"
    unfolding expand
    by (intro Bochner_Integration.integrable_sum
        bm_coordinate_sq_integrable[OF u])
  have "(\<integral>\<omega>. bmX x0 u \<omega> \<bullet> bmX x0 u \<omega> \<partial>bm_paths)
      = (\<Sum>i\<in>UNIV. \<integral>\<omega>. (x0 $ i + \<omega> i u)\<^sup>2 \<partial>bm_paths)"
    unfolding expand
    by (intro Bochner_Integration.integral_sum
        bm_coordinate_sq_integrable[OF u])
  also have "\<dots> = (\<Sum>i\<in>(UNIV :: 'n set). (x0 $ i)\<^sup>2 + u)"
    by (intro sum.cong refl bm_coordinate_sq_integral[OF u])
  also have "\<dots> = (\<Sum>i\<in>(UNIV :: 'n set). (x0 $ i)\<^sup>2) + real CARD('n) * u"
    by (simp add: sum.distrib)
  also have "(\<Sum>i\<in>(UNIV :: 'n set). (x0 $ i)\<^sup>2) = x0 \<bullet> x0"
    by (simp add: inner_vec_def power2_eq_square)
  finally show "(\<integral>\<omega>. bmX x0 u \<omega> \<bullet> bmX x0 u \<omega> \<partial>bm_paths)
      = x0 \<bullet> x0 + real CARD('n) * u" .
qed

lemma bm_compensator_const:
  assumes u: "0 \<le> u"
  shows "set_lebesgue_integral lborel {0..u}
      (\<lambda>_. trace (mat 1 :: real^'n::finite^'n))
    = real CARD('n) * u"
proof -
  have "set_lebesgue_integral lborel {0..u}
      (\<lambda>_. trace (mat 1 :: real^'n^'n)) = u * trace (mat 1 :: real^'n^'n)"
    using u by (subst set_integral_const) (auto simp: emeasure_lborel_Icc)
  then show ?thesis
    by (simp add: trace_mat1 mult_ac)
qed

section \<open>Past and increments of the market are independent\<close>

lemma bm_paths_past_increment_indep:
  fixes U :: "real set"
  assumes U: "finite U" "U \<subseteq> {0..s}" and s: "0 \<le> s" and st: "s < t"
  shows "BMP.indep_var
      (Pi\<^sub>M (UNIV :: 'n::finite set) (\<lambda>_. Pi\<^sub>M U (\<lambda>_. borel)))
      (\<lambda>\<omega>. \<lambda>i\<in>UNIV. restrict (\<omega> i) U)
      (Pi\<^sub>M (UNIV :: 'n set) (\<lambda>_. Pi\<^sub>M {t} (\<lambda>_. borel)))
      (\<lambda>\<omega>. \<lambda>i\<in>UNIV. \<lambda>u\<in>{t}. \<omega> i t - \<omega> i s)"
proof -
  have gU: "(\<lambda>\<omega>. restrict \<omega> U)
      \<in> wiener_pre \<rightarrow>\<^sub>M Pi\<^sub>M U (\<lambda>_. (borel :: real measure))"
  proof (rule measurable_restrict)
    fix u assume "u \<in> U"
    then show "(\<lambda>\<omega>. \<omega> u) \<in> wiener_pre \<rightarrow>\<^sub>M borel"
      using U s by (intro measurable_coord) auto
  qed
  have hI: "(\<lambda>\<omega>. \<lambda>u\<in>{t}. \<omega> t - \<omega> s)
      \<in> wiener_pre \<rightarrow>\<^sub>M Pi\<^sub>M {t} (\<lambda>_. (borel :: real measure))"
    using s st
    by (intro measurable_restrict borel_measurable_diff measurable_coord) auto
  show ?thesis
    unfolding bm_paths_def
    by (rule indep_var_PiM_components[where g = "\<lambda>_ \<omega>. restrict \<omega> U"
        and h = "\<lambda>_ \<omega>. \<lambda>u\<in>{t}. \<omega> t - \<omega> s"
        and N = "\<lambda>_. wiener_pre"])
      (auto intro!: prob_space_wiener_pre gU hI
        wiener_pre_past_increment_indep[OF U s st])
qed

section \<open>Increments are independent of the natural filtration\<close>

lemma bmX_increment_eq:
  "(\<lambda>\<omega>. bmX x0 t \<omega> - bmX x0 s \<omega>)
    = (\<lambda>\<omega> :: 'n::finite \<Rightarrow> real \<Rightarrow> real. \<chi> i. \<omega> i t - \<omega> i s)"
  by (auto simp: bmX_def vec_eq_iff fun_eq_iff)

lemma bm_filtration_increment_indep:
  fixes x0 :: "real^'n::finite"
  assumes s: "0 \<le> s" and st: "s < t"
  shows "BMP.indep_set
    (natural_filtration (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0
      (bmX x0) s)
    (vimage_algebra (space (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      (\<lambda>\<omega>. bmX x0 t \<omega> - bmX x0 s \<omega>) borel)"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  define D where "D = (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<chi> i. \<omega> i t - \<omega> i s)"
  define G1 where "G1 = {(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real.
      \<lambda>u\<in>V. bmX x0 u \<omega>) -` B \<inter> space ?M | V B.
      finite V \<and> V \<noteq> {} \<and> V \<subseteq> {0..s}
      \<and> B \<in> sets (Pi\<^sub>M V (\<lambda>_. borel :: (real^'n) measure))}"
  define G2 where "G2 = {D -` C \<inter> space ?M | C.
      C \<in> sets (borel :: (real^'n) measure)}"
  have Xvec_meas: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<lambda>u\<in>V. bmX x0 u \<omega>)
      \<in> ?M \<rightarrow>\<^sub>M Pi\<^sub>M V (\<lambda>_. borel :: (real^'n) measure)"
    if V: "V \<subseteq> {0..s}" for V
  proof (rule measurable_restrict)
    fix u assume "u \<in> V"
    then have "u \<in> {0..}" using V s by auto
    then show "bmX x0 u \<in> ?M \<rightarrow>\<^sub>M borel"
      by (rule measurable_bmX)
  qed
  have D_meas: "D \<in> ?M \<rightarrow>\<^sub>M (borel :: (real^'n) measure)"
    unfolding D_def
    using s st
    by (intro measurable_vec_components borel_measurable_diff
        measurable_bm_coordinate) auto
  \<comment> \<open>the finite-dimensional independence, composed to the market process\<close>
  have Xvec_ind: "BMP.indep_var
      (Pi\<^sub>M V (\<lambda>_. borel :: (real^'n) measure)) (\<lambda>\<omega>. \<lambda>u\<in>V. bmX x0 u \<omega>)
      (Pi\<^sub>M {t} (\<lambda>_. borel :: (real^'n) measure)) (\<lambda>\<omega>. \<lambda>u\<in>{t}. D \<omega>)"
    if V: "finite V" "V \<noteq> {}" "V \<subseteq> {0..s}" for V
  proof -
    note base = bm_paths_past_increment_indep[OF V(1,3) s st]
    define F1 where "F1 = (\<lambda>p :: 'n \<Rightarrow> real \<Rightarrow> real.
        \<lambda>u\<in>V. x0 + (\<chi> i. p i u))"
    define F2 where "F2 = (\<lambda>q :: 'n \<Rightarrow> real \<Rightarrow> real.
        \<lambda>u\<in>{t}. 0 *\<^sub>R x0 + (\<chi> i. q i t))"
    have cV: "(\<lambda>p :: 'n \<Rightarrow> real \<Rightarrow> real. p i)
        \<in> Pi\<^sub>M (UNIV :: 'n set) (\<lambda>_. Pi\<^sub>M V (\<lambda>_. borel))
        \<rightarrow>\<^sub>M Pi\<^sub>M V (\<lambda>_. (borel :: real measure))" for i
      by (rule measurable_component_singleton) simp
    have ct: "(\<lambda>p :: 'n \<Rightarrow> real \<Rightarrow> real. p i)
        \<in> Pi\<^sub>M (UNIV :: 'n set) (\<lambda>_. Pi\<^sub>M {t} (\<lambda>_. borel))
        \<rightarrow>\<^sub>M Pi\<^sub>M {t} (\<lambda>_. (borel :: real measure))" for i
      by (rule measurable_component_singleton) simp
    have F1m: "F1 \<in> Pi\<^sub>M (UNIV :: 'n set) (\<lambda>_. Pi\<^sub>M V (\<lambda>_. borel))
        \<rightarrow>\<^sub>M Pi\<^sub>M V (\<lambda>_. borel :: (real^'n) measure)"
      unfolding F1_def
    proof (rule measurable_restrict)
      fix u assume u: "u \<in> V"
      have hu: "(\<lambda>h :: real \<Rightarrow> real. h u)
          \<in> Pi\<^sub>M V (\<lambda>_. borel) \<rightarrow>\<^sub>M (borel :: real measure)"
        by (rule measurable_component_singleton[OF u])
      show "(\<lambda>p. x0 + (\<chi> i. p i u))
          \<in> Pi\<^sub>M (UNIV :: 'n set) (\<lambda>_. Pi\<^sub>M V (\<lambda>_. borel)) \<rightarrow>\<^sub>M borel"
        by (intro borel_measurable_add borel_measurable_const
            measurable_vec_components measurable_compose[OF cV hu])
    qed
    have F2m: "F2 \<in> Pi\<^sub>M (UNIV :: 'n set) (\<lambda>_. Pi\<^sub>M {t} (\<lambda>_. borel))
        \<rightarrow>\<^sub>M Pi\<^sub>M {t} (\<lambda>_. borel :: (real^'n) measure)"
      unfolding F2_def
    proof (rule measurable_restrict)
      fix u assume "u \<in> {t}"
      have ht: "(\<lambda>h :: real \<Rightarrow> real. h t)
          \<in> Pi\<^sub>M {t} (\<lambda>_. borel) \<rightarrow>\<^sub>M (borel :: real measure)"
        by (rule measurable_component_singleton) simp
      show "(\<lambda>q. 0 *\<^sub>R x0 + (\<chi> i. q i t))
          \<in> Pi\<^sub>M (UNIV :: 'n set) (\<lambda>_. Pi\<^sub>M {t} (\<lambda>_. borel)) \<rightarrow>\<^sub>M borel"
        by (intro borel_measurable_add borel_measurable_const
            measurable_vec_components measurable_compose[OF ct ht])
    qed
    have cmp1: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<lambda>u\<in>V. bmX x0 u \<omega>)
        = (\<lambda>\<omega>. F1 (\<lambda>i\<in>UNIV. restrict (\<omega> i) V))"
      by (auto simp: F1_def bmX_def fun_eq_iff restrict_def vec_eq_iff)
    have cmp2: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<lambda>u\<in>{t}. D \<omega>)
        = (\<lambda>\<omega>. F2 (\<lambda>i\<in>UNIV. \<lambda>u\<in>{t}. \<omega> i t - \<omega> i s))"
      by (auto simp: F2_def D_def fun_eq_iff restrict_def vec_eq_iff)
    show ?thesis
      unfolding cmp1 cmp2
      using BMP.indep_var_compose[OF base F1m F2m]
      by (simp add: comp_def)
  qed
  have Dvec_eq: "D -` C \<inter> space ?M
      = (\<lambda>\<omega>. \<lambda>u\<in>{t}. D \<omega>) -`
        ((\<lambda>h. h t) -` C \<inter> space (Pi\<^sub>M {t} (\<lambda>_. borel :: (real^'n) measure)))
        \<inter> space ?M"
    for C :: "(real^'n) set"
    by (auto simp: space_PiM PiE_iff extensional_def)
  have Dvec_set: "(\<lambda>h. h t) -` C
      \<inter> space (Pi\<^sub>M {t} (\<lambda>_. borel :: (real^'n) measure))
      \<in> sets (Pi\<^sub>M {t} (\<lambda>_. borel :: (real^'n) measure))"
    if that: "C \<in> sets (borel :: (real^'n) measure)" for C
  proof -
    have "(\<lambda>h :: real \<Rightarrow> real^'n. h t)
        \<in> Pi\<^sub>M {t} (\<lambda>_. borel) \<rightarrow>\<^sub>M (borel :: (real^'n) measure)"
      by (rule measurable_component_singleton) simp
    from measurable_sets[OF this that] show ?thesis .
  qed
  \<comment> \<open>pairwise factorization on the generators\<close>
  have fact_ab: "BMP.prob (a \<inter> b) = BMP.prob a * BMP.prob b"
    if a: "a \<in> G1" and b: "b \<in> G2" for a b
  proof -
    from a obtain V B where V: "finite V" "V \<noteq> {}" "V \<subseteq> {0..s}"
      and B: "B \<in> sets (Pi\<^sub>M V (\<lambda>_. borel :: (real^'n) measure))"
      and a_def: "a = (\<lambda>\<omega>. \<lambda>u\<in>V. bmX x0 u \<omega>) -` B \<inter> space ?M"
      by (auto simp: G1_def)
    from b obtain C where C: "C \<in> sets (borel :: (real^'n) measure)"
      and b_def: "b = D -` C \<inter> space ?M"
      by (auto simp: G2_def)
    have "BMP.indep_set
        (sigma_sets (space ?M) {(\<lambda>\<omega>. \<lambda>u\<in>V. bmX x0 u \<omega>) -` X' \<inter> space ?M
          |X'. X' \<in> sets (Pi\<^sub>M V (\<lambda>_. borel :: (real^'n) measure))})
        (sigma_sets (space ?M) {(\<lambda>\<omega>. \<lambda>u\<in>{t}. D \<omega>) -` X' \<inter> space ?M
          |X'. X' \<in> sets (Pi\<^sub>M {t} (\<lambda>_. borel :: (real^'n) measure))})"
      using Xvec_ind[OF V] unfolding BMP.indep_var_eq by blast
    moreover have "a \<in> sigma_sets (space ?M)
        {(\<lambda>\<omega>. \<lambda>u\<in>V. bmX x0 u \<omega>) -` X' \<inter> space ?M
          |X'. X' \<in> sets (Pi\<^sub>M V (\<lambda>_. borel :: (real^'n) measure))}"
      unfolding a_def using B by (intro sigma_sets.Basic) auto
    moreover have "b \<in> sigma_sets (space ?M)
        {(\<lambda>\<omega>. \<lambda>u\<in>{t}. D \<omega>) -` X' \<inter> space ?M
          |X'. X' \<in> sets (Pi\<^sub>M {t} (\<lambda>_. borel :: (real^'n) measure))}"
    proof -
      have "b \<in> {(\<lambda>\<omega>. \<lambda>u\<in>{t}. D \<omega>) -` X' \<inter> space ?M
          |X'. X' \<in> sets (Pi\<^sub>M {t} (\<lambda>_. borel :: (real^'n) measure))}"
        unfolding b_def Dvec_eq[of C]
        using Dvec_set[OF C] by blast
      then show ?thesis by (rule sigma_sets.Basic)
    qed
    ultimately show ?thesis
      by (rule BMP.indep_setD)
  qed
  have G1_events: "G1 \<subseteq> BMP.events"
    unfolding G1_def
    by (auto intro!: measurable_sets[OF Xvec_meas])
  have G2_events: "G2 \<subseteq> BMP.events"
    unfolding G2_def
    by (auto intro!: measurable_sets[OF D_meas])
  have G1_Int: "Int_stable G1"
  proof (rule Int_stableI)
    fix a b assume "a \<in> G1" "b \<in> G1"
    then obtain V1 B1 V2 B2 where
      V1: "finite V1" "V1 \<noteq> {}" "V1 \<subseteq> {0..s}"
      and B1: "B1 \<in> sets (Pi\<^sub>M V1 (\<lambda>_. borel :: (real^'n) measure))"
      and a_def: "a = (\<lambda>\<omega>. \<lambda>u\<in>V1. bmX x0 u \<omega>) -` B1 \<inter> space ?M"
      and V2: "finite V2" "V2 \<noteq> {}" "V2 \<subseteq> {0..s}"
      and B2: "B2 \<in> sets (Pi\<^sub>M V2 (\<lambda>_. borel :: (real^'n) measure))"
      and b_def: "b = (\<lambda>\<omega>. \<lambda>u\<in>V2. bmX x0 u \<omega>) -` B2 \<inter> space ?M"
      by (auto simp: G1_def)
    define V where "V = V1 \<union> V2"
    have V: "finite V" "V \<noteq> {}" "V \<subseteq> {0..s}"
      using V1 V2 by (auto simp: V_def)
    have sub1: "V1 \<subseteq> V" and sub2: "V2 \<subseteq> V" by (auto simp: V_def)
    define B where "B = ((\<lambda>h. restrict h V1) -` B1
        \<inter> space (Pi\<^sub>M V (\<lambda>_. borel :: (real^'n) measure)))
        \<inter> ((\<lambda>h. restrict h V2) -` B2
        \<inter> space (Pi\<^sub>M V (\<lambda>_. borel :: (real^'n) measure)))"
    have Bs: "B \<in> sets (Pi\<^sub>M V (\<lambda>_. borel :: (real^'n) measure))"
      unfolding B_def
      by (intro sets.Int
          measurable_sets[OF measurable_restrict_subset[OF sub1] B1]
          measurable_sets[OF measurable_restrict_subset[OF sub2] B2])
    have iv1: "V \<inter> V1 = V1" and iv2: "V \<inter> V2 = V2"
      using sub1 sub2 by auto
    have restr_eval: "restrict (\<lambda>u\<in>V. bmX x0 u \<omega>) V1 = (\<lambda>u\<in>V1. bmX x0 u \<omega>)"
      "restrict (\<lambda>u\<in>V. bmX x0 u \<omega>) V2 = (\<lambda>u\<in>V2. bmX x0 u \<omega>)"
      for \<omega> using sub1 sub2 by (auto simp: restrict_def fun_eq_iff)
    have sp: "(\<lambda>u\<in>V. bmX x0 u \<omega>)
        \<in> space (Pi\<^sub>M V (\<lambda>_. borel :: (real^'n) measure))" for \<omega>
      by (auto simp: space_PiM PiE_iff extensional_def)
    have "a \<inter> b = (\<lambda>\<omega>. \<lambda>u\<in>V. bmX x0 u \<omega>) -` B \<inter> space ?M"
      unfolding a_def b_def B_def
      by (auto simp: restr_eval sp iv1 iv2)
    then show "a \<inter> b \<in> G1"
      unfolding G1_def using V Bs by blast
  qed
  have G2_Int: "Int_stable G2"
  proof (rule Int_stableI)
    fix a b assume "a \<in> G2" "b \<in> G2"
    then obtain C1 C2 where C: "C1 \<in> sets (borel :: (real^'n) measure)"
      "C2 \<in> sets (borel :: (real^'n) measure)"
      and ab: "a = D -` C1 \<inter> space ?M" "b = D -` C2 \<inter> space ?M"
      by (auto simp: G2_def)
    have "a \<inter> b = D -` (C1 \<inter> C2) \<inter> space ?M"
      unfolding ab by auto
    then show "a \<inter> b \<in> G2"
      unfolding G2_def using C by blast
  qed
  have "BMP.indep_set G1 G2"
    by (rule BMP.indep_setI[OF G1_events G2_events fact_ab])
  then have "BMP.indep_sets (case_bool G1 G2) UNIV"
    unfolding BMP.indep_set_def .
  then have "BMP.indep_sets (\<lambda>b. sigma_sets (space ?M)
      (case_bool G1 G2 b)) UNIV"
    by (rule BMP.indep_sets_sigma)
      (auto split: bool.split simp: G1_Int G2_Int)
  then have sig: "BMP.indep_set (sigma_sets (space ?M) G1)
      (sigma_sets (space ?M) G2)"
    unfolding BMP.indep_set_def
    by (rule BMP.indep_sets_cong[THEN iffD1, OF refl, rotated])
      (auto split: bool.split)
  \<comment> \<open>the natural filtration is generated by @{text G1}\<close>
  have E1G1: "(\<Union>u\<in>{0..s}. {bmX x0 u -` A \<inter> space ?M | A. A \<in> sets borel})
      \<subseteq> G1"
  proof safe
    fix u A assume u: "u \<in> {0..s}"
      and A: "A \<in> sets (borel :: (real^'n) measure)"
    have hu: "(\<lambda>h :: real \<Rightarrow> real^'n. h u)
        \<in> Pi\<^sub>M {u} (\<lambda>_. borel) \<rightarrow>\<^sub>M (borel :: (real^'n) measure)"
      by (rule measurable_component_singleton) simp
    define B where "B = (\<lambda>h. h u) -` A
        \<inter> space (Pi\<^sub>M {u} (\<lambda>_. borel :: (real^'n) measure))"
    have Bs: "B \<in> sets (Pi\<^sub>M {u} (\<lambda>_. borel :: (real^'n) measure))"
      unfolding B_def by (rule measurable_sets[OF hu A])
    have eq: "bmX x0 u -` A \<inter> space ?M
        = (\<lambda>\<omega>. \<lambda>u'\<in>{u}. bmX x0 u' \<omega>) -` B \<inter> space ?M"
      unfolding B_def by (auto simp: space_PiM PiE_iff extensional_def)
    have "(\<lambda>\<omega>. \<lambda>u'\<in>{u}. bmX x0 u' \<omega>) -` B \<inter> space ?M \<in> G1"
      unfolding G1_def using u Bs by blast
    then show "bmX x0 u -` A \<inter> space ?M \<in> G1"
      unfolding eq .
  qed
  have F_sub: "sets (natural_filtration ?M 0 (bmX x0) s)
      \<subseteq> sigma_sets (space ?M) G1"
  proof -
    have "sets (natural_filtration ?M 0 (bmX x0) s)
        = sigma_sets (space ?M) (\<Union>u\<in>{0..s}.
          {bmX x0 u -` A \<inter> space ?M | A. A \<in> sets borel})"
      by (rule sets_natural_filtration)
    also have "\<dots> \<subseteq> sigma_sets (space ?M) G1"
      using E1G1 by (intro sigma_sets_mono) (auto intro: sigma_sets.Basic)
    finally show ?thesis .
  qed
  have D_sub: "sets (vimage_algebra (space ?M)
      (\<lambda>\<omega>. bmX x0 t \<omega> - bmX x0 s \<omega>) borel) \<subseteq> sigma_sets (space ?M) G2"
  proof -
    have "{(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<chi> i. \<omega> i t - \<omega> i s) -` A
        \<inter> space ?M |A. A \<in> sets borel} \<subseteq> G2"
      by (auto simp: G2_def D_def)
    then show ?thesis
      unfolding sets_vimage_algebra bmX_increment_eq
      by (intro sigma_sets_mono) (auto intro: sigma_sets.Basic)
  qed
  have "BMP.indep_sets (case_bool (sigma_sets (space ?M) G1)
      (sigma_sets (space ?M) G2)) UNIV"
    using sig unfolding BMP.indep_set_def .
  then have "BMP.indep_sets (case_bool
      (sets (natural_filtration ?M 0 (bmX x0) s))
      (sets (vimage_algebra (space ?M)
        (\<lambda>\<omega>. bmX x0 t \<omega> - bmX x0 s \<omega>) borel))) UNIV"
    by (rule BMP.indep_sets_mono_sets)
      (auto split: bool.split simp: F_sub D_sub)
  then show ?thesis
    unfolding BMP.indep_set_def .
qed

section \<open>Coordinate means and vector integrability\<close>

lemma bm_coordinate_mean:
  assumes u: "0 \<le> u"
  shows bm_coordinate_mean_integrable:
    "integrable (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>\<omega>. \<omega> i u)"
    and bm_coordinate_mean_integral:
    "(\<integral>\<omega>. \<omega> i u \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)) = 0"
proof -
  have m: "(\<lambda>\<omega>. \<omega> i u) \<in> (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      \<rightarrow>\<^sub>M (borel :: real measure)"
    using u by (intro measurable_bm_coordinate) simp
  have idm: "(\<lambda>y :: real. y) \<in> borel_measurable borel"
    by (rule measurable_ident_sets) simp
  have "integrable (distr (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) borel
      (\<lambda>\<omega>. \<omega> i u)) (\<lambda>y. y)"
    unfolding bm_coordinate_distr[OF u]
    by (rule gauss_measure_mean_integrable)
  then show "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>\<omega>. \<omega> i u)"
    by (rule integrable_distr[OF m])
  have "(\<integral>\<omega>. \<omega> i u \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      = (\<integral>y. y \<partial>distr bm_paths borel (\<lambda>\<omega>. \<omega> i u))"
    by (rule integral_distr[OF m idm, symmetric])
  also have "\<dots> = 0"
    unfolding bm_coordinate_distr[OF u]
    by (rule gauss_measure_mean_integral)
  finally show "(\<integral>\<omega>. \<omega> i u
      \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)) = 0" .
qed

lemma integrable_vec_components:
  fixes f :: "'i::finite \<Rightarrow> 'a \<Rightarrow> real"
  assumes f: "\<And>i. integrable M (f i)"
  shows "integrable M (\<lambda>x. (\<chi> i. f i x) :: real^'i)"
proof -
  have comp: "(\<Sum>k\<in>(UNIV :: 'i set). f k x * axis k 1 $ j) = f j x"
    for x j
  proof -
    have "(\<Sum>k\<in>(UNIV :: 'i set). f k x * axis k 1 $ j)
        = (\<Sum>k\<in>(UNIV :: 'i set). if k = j then f k x else 0)"
      by (intro sum.cong refl) (simp add: axis_def)
    also have "\<dots> = f j x"
      by (simp add: sum.delta)
    finally show ?thesis .
  qed
  have eq: "(\<lambda>x. (\<chi> i. f i x) :: real^'i)
      = (\<lambda>x. \<Sum>i\<in>UNIV. f i x *\<^sub>R axis i 1)"
    by (simp add: fun_eq_iff vec_eq_iff comp)
  show ?thesis
    unfolding eq
    by (intro Bochner_Integration.integrable_sum integrable_scaleR_left f)
qed

lemma bmX_integrable:
  fixes x0 :: "real^'n::finite"
  assumes u: "0 \<le> u"
  shows "integrable bm_paths (bmX x0 u)"
proof -
  have eq: "bmX x0 u = (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<chi> i. x0 $ i + \<omega> i u)"
    by (simp add: bmX_def fun_eq_iff vec_eq_iff)
  show ?thesis
    unfolding eq
    by (intro integrable_vec_components Bochner_Integration.integrable_add
        BMP.integrable_const bm_coordinate_mean_integrable[OF u])
qed

lemma bm_increment_component:
  assumes s: "0 \<le> s" and t: "0 \<le> t"
  shows bm_increment_component_integrable:
    "integrable (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>\<omega>. \<omega> i t - \<omega> i s)"
    and bm_increment_component_integral:
    "(\<integral>\<omega>. \<omega> i t - \<omega> i s
      \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)) = 0"
proof -
  show "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>\<omega>. \<omega> i t - \<omega> i s)"
    by (intro Bochner_Integration.integrable_diff
        bm_coordinate_mean_integrable s t)
  show "(\<integral>\<omega>. \<omega> i t - \<omega> i s
      \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)) = 0"
    by (subst Bochner_Integration.integral_diff)
      (simp_all add: bm_coordinate_mean_integrable
        bm_coordinate_mean_integral s t)
qed

section \<open>The increment has zero conditional expectation\<close>

lemma bm_indicator_increment_indep_var:
  fixes x0 :: "real^'n::finite"
  assumes s: "0 \<le> s" and st: "s < t"
    and A: "A \<in> sets (natural_filtration
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0 (bmX x0) s)"
  shows "BMP.indep_var borel (indicator A :: ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real)
    borel (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s)"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "natural_filtration ?M 0 (bmX x0) s"
  let ?D = "\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. bmX x0 t \<omega> - bmX x0 s \<omega>"
  let ?V = "vimage_algebra (space ?M) ?D borel"
  interpret SP: stochastic_process ?M 0 "bmX x0"
    by unfold_locales (intro measurable_bmX, simp)
  have subalg: "subalgebra ?M ?F"
    by (rule SP.subalgebra_natural_filtration)
  have A_M: "A \<in> sets ?M"
    using A subalg by (auto simp: subalgebra_def)
  have base: "BMP.indep_set (sets ?F) (sets ?V)"
    by (rule bm_filtration_increment_indep[OF s st])
  have ind_meas_F: "(indicator A :: _ \<Rightarrow> real) \<in> borel_measurable ?F"
    by (rule borel_measurable_indicator[OF A])
  have L: "sigma_sets (space ?M)
      {(indicator A :: _ \<Rightarrow> real) -` B \<inter> space ?M |B. B \<in> sets borel}
      \<subseteq> sets ?F"
  proof -
    have gen: "{(indicator A :: _ \<Rightarrow> real) -` B \<inter> space ?M
        |B. B \<in> sets borel} \<subseteq> sets ?F"
    proof safe
      fix B :: "real set" assume B: "B \<in> sets borel"
      have "(indicator A :: _ \<Rightarrow> real) -` B \<inter> space ?F \<in> sets ?F"
        by (rule measurable_sets[OF ind_meas_F B])
      then show "(indicator A :: _ \<Rightarrow> real) -` B \<inter> space ?M \<in> sets ?F"
        by simp
    qed
    show ?thesis
      using sets.sigma_sets_subset[OF gen] by simp
  qed
  have nth_meas: "(\<lambda>v :: real^'n. v $ i) \<in> borel_measurable borel"
  proof -
    have "(\<lambda>v :: real^'n. v $ i) = (\<lambda>v. inner v (axis i 1))"
      by (simp add: fun_eq_iff cart_eq_inner_axis)
    then show ?thesis
      by simp
  qed
  have Dcomp: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s)
      = (\<lambda>\<omega>. ?D \<omega> $ i)"
    by (simp add: fun_eq_iff bmX_def)
  have R: "sigma_sets (space ?M)
      {(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s) -` B \<inter> space ?M
        |B. B \<in> sets borel} \<subseteq> sets ?V"
  proof -
    have gen: "{(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s) -` B
        \<inter> space ?M |B. B \<in> sets borel} \<subseteq> sets ?V"
    proof safe
      fix B :: "real set" assume B: "B \<in> sets borel"
      have Ci: "(\<lambda>v :: real^'n. v $ i) -` B \<in> sets borel"
        using measurable_sets[OF nth_meas B] by simp
      have veq: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s) -` B
          \<inter> space ?M
          = ?D -` ((\<lambda>v. v $ i) -` B) \<inter> space ?M"
        unfolding Dcomp by auto
      have "?D -` ((\<lambda>v. v $ i) -` B) \<inter> space ?M
          \<in> {?D -` C \<inter> space ?M |C. C \<in> sets borel}"
        using Ci by blast
      then have "?D -` ((\<lambda>v. v $ i) -` B) \<inter> space ?M
          \<in> sigma_sets (space ?M) {?D -` C \<inter> space ?M |C. C \<in> sets borel}"
        by (rule sigma_sets.Basic)
      then show "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s) -` B
          \<inter> space ?M \<in> sets ?V"
        unfolding veq sets_vimage_algebra .
    qed
    show ?thesis
      using sets.sigma_sets_subset[OF gen] by simp
  qed
  show ?thesis
    unfolding BMP.indep_var_eq
  proof (intro conjI)
    show "(indicator A :: _ \<Rightarrow> real) \<in> borel_measurable ?M"
      by (rule borel_measurable_indicator[OF A_M])
    show "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s)
        \<in> borel_measurable ?M"
      using s st
      by (intro borel_measurable_diff measurable_bm_coordinate) auto
    have "BMP.indep_sets (case_bool (sets ?F) (sets ?V)) UNIV"
      using base unfolding BMP.indep_set_def .
    then have "BMP.indep_sets (case_bool
        (sigma_sets (space ?M)
          {(indicator A :: _ \<Rightarrow> real) -` B \<inter> space ?M |B. B \<in> sets borel})
        (sigma_sets (space ?M)
          {(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s) -` B \<inter> space ?M
            |B. B \<in> sets borel})) UNIV"
      by (rule BMP.indep_sets_mono_sets)
        (auto split: bool.split simp: L R)
    then show "BMP.indep_set
        (sigma_sets (space ?M)
          {(indicator A :: _ \<Rightarrow> real) -` B \<inter> space ?M |B. B \<in> sets borel})
        (sigma_sets (space ?M)
          {(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s) -` B \<inter> space ?M
            |B. B \<in> sets borel})"
      unfolding BMP.indep_set_def .
  qed
qed

lemma bmX_increment_set_integral_zero:
  fixes x0 :: "real^'n::finite"
  assumes s: "0 \<le> s" and st: "s \<le> t"
    and A: "A \<in> sets (natural_filtration
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0 (bmX x0) s)"
  shows "(\<integral>\<omega>. indicator A \<omega> *\<^sub>R (bmX x0 t \<omega> - bmX x0 s \<omega>)
      \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)) = 0"
proof (cases "s = t")
  case True
  then show ?thesis by simp
next
  case False
  with st have st': "s < t" by simp
  have t0: "0 \<le> t" using s st by simp
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "natural_filtration ?M 0 (bmX x0) s"
  let ?D = "\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. bmX x0 t \<omega> - bmX x0 s \<omega>"
  interpret SP: stochastic_process ?M 0 "bmX x0"
    by unfold_locales (intro measurable_bmX, simp)
  have subalg: "subalgebra ?M ?F"
    by (rule SP.subalgebra_natural_filtration)
  have A_M: "A \<in> sets ?M"
    using A subalg by (auto simp: subalgebra_def)
  have D_int: "integrable ?M ?D"
    by (intro Bochner_Integration.integrable_diff bmX_integrable s t0)
  have setD_int: "integrable ?M (\<lambda>\<omega>. indicator A \<omega> *\<^sub>R ?D \<omega>)"
    by (rule integrable_mult_indicator[OF A_M D_int])
  have indA_int: "integrable ?M (indicator A :: _ \<Rightarrow> real)"
  proof (rule BMP.integrable_const_bound[where B = 1])
    show "AE \<omega> in ?M. norm (indicator A \<omega> :: real) \<le> 1"
      by (intro AE_I2) (simp add: indicator_def)
    show "(indicator A :: _ \<Rightarrow> real) \<in> borel_measurable ?M"
      by (rule borel_measurable_indicator[OF A_M])
  qed
  have comp0: "(\<integral>\<omega>. indicator A \<omega> *\<^sub>R ?D \<omega> \<partial>?M) $ i = 0" for i
  proof -
    have inc_int: "integrable ?M
        (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s)"
      by (rule bm_increment_component_integrable[OF s t0])
    have "(\<integral>\<omega>. indicator A \<omega> *\<^sub>R ?D \<omega> \<partial>?M) $ i
        = (\<integral>\<omega>. (indicator A \<omega> *\<^sub>R ?D \<omega>) $ i \<partial>?M)"
      by (rule integral_bounded_linear
          [OF bounded_linear_vec_nth setD_int, symmetric])
    also have "\<dots> = (\<integral>\<omega>. indicator A \<omega> * (\<omega> i t - \<omega> i s) \<partial>?M)"
      by (intro Bochner_Integration.integral_cong refl)
        (simp add: bmX_def)
    also have "\<dots> = (\<integral>\<omega>. indicator A \<omega> \<partial>?M)
        * (\<integral>\<omega>. \<omega> i t - \<omega> i s \<partial>?M)"
      by (rule BMP.indep_var_lebesgue_integral
          [OF bm_indicator_increment_indep_var[OF s st' A]
            indA_int inc_int])
    also have "\<dots> = 0"
      by (simp add: bm_increment_component_integral[OF s t0])
    finally show ?thesis .
  qed
  show ?thesis
    using comp0 by (simp add: vec_eq_iff)
qed

lemma bmX_has_cond_exp:
  fixes x0 :: "real^'n::finite"
  assumes s: "0 \<le> s" and st: "s \<le> t"
  shows "has_cond_exp (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (bmX x0) s) (bmX x0 t) (bmX x0 s)"
proof (rule has_cond_expI')
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "natural_filtration ?M 0 (bmX x0) s"
  have t0: "0 \<le> t" using s st by simp
  interpret SP: stochastic_process ?M 0 "bmX x0"
    by unfold_locales (intro measurable_bmX, simp)
  have subalg: "subalgebra ?M ?F"
    by (rule SP.subalgebra_natural_filtration)
  show "integrable ?M (bmX x0 t)"
    by (rule bmX_integrable[OF t0])
  show "integrable ?M (bmX x0 s)"
    by (rule bmX_integrable[OF s])
  show "bmX x0 s \<in> borel_measurable ?F"
    by (rule adapted_process.adapted
        [OF SP.adapted_process_natural_filtration s])
  fix A assume A: "A \<in> sets ?F"
  have A_M: "A \<in> sets ?M"
    using A subalg by (auto simp: subalgebra_def)
  have int_s: "integrable ?M (\<lambda>\<omega>. indicator A \<omega> *\<^sub>R bmX x0 s \<omega>)"
    by (rule integrable_mult_indicator[OF A_M bmX_integrable[OF s]])
  have int_D: "integrable ?M
      (\<lambda>\<omega>. indicator A \<omega> *\<^sub>R (bmX x0 t \<omega> - bmX x0 s \<omega>))"
    by (intro integrable_mult_indicator[OF A_M]
        Bochner_Integration.integrable_diff bmX_integrable s t0)
  have "(\<integral>\<omega> \<in> A. bmX x0 t \<omega> \<partial>?M)
      = (\<integral>\<omega>. indicator A \<omega> *\<^sub>R bmX x0 t \<omega> \<partial>?M)"
    unfolding set_lebesgue_integral_def ..
  also have "\<dots> = (\<integral>\<omega>. indicator A \<omega> *\<^sub>R bmX x0 s \<omega>
      + indicator A \<omega> *\<^sub>R (bmX x0 t \<omega> - bmX x0 s \<omega>) \<partial>?M)"
    by (intro Bochner_Integration.integral_cong refl)
      (simp add: scaleR_add_right scaleR_diff_right)
  also have "\<dots> = (\<integral>\<omega>. indicator A \<omega> *\<^sub>R bmX x0 s \<omega> \<partial>?M)
      + (\<integral>\<omega>. indicator A \<omega> *\<^sub>R (bmX x0 t \<omega> - bmX x0 s \<omega>) \<partial>?M)"
    by (rule Bochner_Integration.integral_add[OF int_s int_D])
  also have "\<dots> = (\<integral>\<omega>. indicator A \<omega> *\<^sub>R bmX x0 s \<omega> \<partial>?M)"
    by (simp add: bmX_increment_set_integral_zero[OF s st A])
  also have "\<dots> = (\<integral>\<omega> \<in> A. bmX x0 s \<omega> \<partial>?M)"
    unfolding set_lebesgue_integral_def ..
  finally show "(\<integral>\<omega> \<in> A. bmX x0 t \<omega> \<partial>?M)
      = (\<integral>\<omega> \<in> A. bmX x0 s \<omega> \<partial>?M)" .
qed

section \<open>The market is a martingale\<close>

theorem martingale_bmX:
  fixes x0 :: "real^'n::finite"
  shows "martingale (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (bmX x0)) 0 (bmX x0)"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "natural_filtration ?M 0 (bmX x0)"
  interpret SP: stochastic_process ?M 0 "bmX x0"
    by unfold_locales (intro measurable_bmX, simp)
  have fm: "finite_measure ?M"
    by (rule finite_measureI) (simp add: BMP.emeasure_space_1)
  have sfs: "sigma_finite_subalgebra ?M (?F i)" for i
    by (intro finite_measure_subalgebra_is_sigma_finite
        finite_measure_subalgebra.intro
        finite_measure_subalgebra_axioms.intro
        fm SP.subalgebra_natural_filtration)
  show ?thesis
  proof (intro martingale.intro martingale_axioms.intro)
    show "sigma_finite_filtered_measure ?M ?F 0"
      by (intro sigma_finite_filtered_measure.intro
          sigma_finite_filtered_measure_axioms.intro
          SP.filtered_measure_natural_filtration sfs)
    show "adapted_process ?M ?F 0 (bmX x0)"
      by (rule SP.adapted_process_natural_filtration)
    show "\<And>i. 0 \<le> i \<Longrightarrow> integrable ?M (bmX x0 i)"
      by (rule bmX_integrable)
    fix i j :: real assume ij: "0 \<le> i" "i \<le> j"
    interpret S: sigma_finite_subalgebra ?M "?F i"
      by (rule sfs)
    show "AE \<xi> in ?M. bmX x0 i \<xi> = cond_exp ?M (?F i) (bmX x0 j) \<xi>"
      by (rule S.has_cond_exp_charact(2)
          [OF bmX_has_cond_exp[OF ij], THEN AE_symmetric])
  qed
qed

section \<open>The Brownian market is sufficiently volatile\<close>

text \<open>The main theorem of this theory: the axiomatized market class
  \<open>\<P>\<^sub>x\<close> of Relative\_Arbitrage\_Stochastic is inhabited.  The
  \<open>n\<close>-dimensional Brownian market started at \<open>x0\<close>, with constant
  covariation \<open>mat 1\<close> and any deterministic horizon, satisfies every
  assumption of the locale --- in particular the martingale-problem
  identity \<open>dynkin_quadratic\<close> is here a theorem, not an axiom.\<close>



section \<open>Ito's formula for the square: the compensated square is a martingale\<close>

text \<open>The martingale-problem identity used above is the \<^emph>\<open>expectation\<close>
  form of Ito's formula for the test function \<open>|x|\<^sup>2\<close>.  Its process form,

    \<open>Z t = |B t|\<^sup>2 - int_0^t tr(mat 1) ds\<close> is a martingale,

  is proved in this section.  It is what the locales of Ito\_Market take as
  their hypothesis, so it shows that the martingale problem in process form
  is inhabited as well.  Everything rests on the independence of the
  increment from the past, generalised here from indicators of past events
  to arbitrary past-measurable factors.\<close>

lemma bm_meas_increment_indep_var:
  fixes x0 :: "real^'n::finite"
  assumes s: "0 \<le> s" and st: "s < t"
    and g_meas: "g \<in> borel_measurable (natural_filtration
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0 (bmX x0) s)"
  shows "BMP.indep_var borel (g :: ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real)
    borel (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s)"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "natural_filtration ?M 0 (bmX x0) s"
  let ?D = "\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. bmX x0 t \<omega> - bmX x0 s \<omega>"
  let ?V = "vimage_algebra (space ?M) ?D borel"
  interpret SP: stochastic_process ?M 0 "bmX x0"
    by unfold_locales (intro measurable_bmX, simp)
  have subalg: "subalgebra ?M ?F"
    by (rule SP.subalgebra_natural_filtration)
  have g_M: "g \<in> borel_measurable ?M"
    by (rule measurable_from_subalg[OF subalg g_meas])
  have base: "BMP.indep_set (sets ?F) (sets ?V)"
    by (rule bm_filtration_increment_indep[OF s st])
  have L: "sigma_sets (space ?M) {g -` B \<inter> space ?M |B. B \<in> sets borel}
      \<subseteq> sets ?F"
  proof -
    have gen: "{g -` B \<inter> space ?M |B. B \<in> sets borel} \<subseteq> sets ?F"
    proof safe
      fix B :: "real set" assume B: "B \<in> sets borel"
      have "g -` B \<inter> space ?F \<in> sets ?F"
        by (rule measurable_sets[OF g_meas B])
      then show "g -` B \<inter> space ?M \<in> sets ?F"
        using subalg by (simp add: subalgebra_def)
    qed
    show ?thesis
      using sets.sigma_sets_subset[OF gen] by simp
  qed
  have nth_meas: "(\<lambda>v :: real^'n. v $ i) \<in> borel_measurable borel"
  proof -
    have "(\<lambda>v :: real^'n. v $ i) = (\<lambda>v. inner v (axis i 1))"
      by (simp add: fun_eq_iff cart_eq_inner_axis)
    then show ?thesis
      by simp
  qed
  have Dcomp: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s)
      = (\<lambda>\<omega>. ?D \<omega> $ i)"
    by (simp add: fun_eq_iff bmX_def)
  have R: "sigma_sets (space ?M)
      {(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s) -` B \<inter> space ?M
        |B. B \<in> sets borel} \<subseteq> sets ?V"
  proof -
    have gen: "{(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s) -` B
        \<inter> space ?M |B. B \<in> sets borel} \<subseteq> sets ?V"
    proof safe
      fix B :: "real set" assume B: "B \<in> sets borel"
      have Ci: "(\<lambda>v :: real^'n. v $ i) -` B \<in> sets borel"
        using measurable_sets[OF nth_meas B] by simp
      have veq: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s) -` B
          \<inter> space ?M
          = ?D -` ((\<lambda>v. v $ i) -` B) \<inter> space ?M"
        unfolding Dcomp by auto
      have "?D -` ((\<lambda>v. v $ i) -` B) \<inter> space ?M
          \<in> {?D -` C \<inter> space ?M |C. C \<in> sets borel}"
        using Ci by blast
      then have "?D -` ((\<lambda>v. v $ i) -` B) \<inter> space ?M
          \<in> sigma_sets (space ?M) {?D -` C \<inter> space ?M |C. C \<in> sets borel}"
        by (rule sigma_sets.Basic)
      then show "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s) -` B
          \<inter> space ?M \<in> sets ?V"
        unfolding veq sets_vimage_algebra .
    qed
    show ?thesis
      using sets.sigma_sets_subset[OF gen] by simp
  qed
  show ?thesis
    unfolding BMP.indep_var_eq
  proof (intro conjI)
    show "g \<in> borel_measurable ?M"
      by (rule g_M)
    show "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s)
        \<in> borel_measurable ?M"
      using s st
      by (intro borel_measurable_diff measurable_bm_coordinate) auto
    have "BMP.indep_sets (case_bool (sets ?F) (sets ?V)) UNIV"
      using base unfolding BMP.indep_set_def .
    then have "BMP.indep_sets (case_bool
        (sigma_sets (space ?M) {g -` B \<inter> space ?M |B. B \<in> sets borel})
        (sigma_sets (space ?M)
          {(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s) -` B \<inter> space ?M
            |B. B \<in> sets borel})) UNIV"
      by (rule BMP.indep_sets_mono_sets)
        (auto split: bool.split simp: L R)
    then show "BMP.indep_set
        (sigma_sets (space ?M) {g -` B \<inter> space ?M |B. B \<in> sets borel})
        (sigma_sets (space ?M)
          {(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s) -` B \<inter> space ?M
            |B. B \<in> sets borel})"
      unfolding BMP.indep_set_def .
  qed
qed

lemma bm_meas_increment_product:
  fixes x0 :: "real^'n::finite"
  assumes s: "0 \<le> s" and st: "s \<le> t"
    and g_meas: "g \<in> borel_measurable (natural_filtration
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0 (bmX x0) s)"
    and g_int: "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) g"
  shows bm_meas_increment_product_integrable:
    "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>\<omega>. g \<omega> * (\<omega> i t - \<omega> i s))"
    and bm_meas_increment_product_zero:
    "(\<integral>\<omega>. g \<omega> * (\<omega> i t - \<omega> i s)
      \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)) = 0"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  have t0: "0 \<le> t" using s st by simp
  show "integrable ?M (\<lambda>\<omega>. g \<omega> * (\<omega> i t - \<omega> i s))"
  proof (cases "s = t")
    case True
    then show ?thesis by simp
  next
    case False
    with st have st': "s < t" by simp
    show ?thesis
      by (rule BMP.indep_var_integrable
          [OF bm_meas_increment_indep_var[OF s st' g_meas] g_int
            bm_increment_component_integrable[OF s t0]])
  qed
  show "(\<integral>\<omega>. g \<omega> * (\<omega> i t - \<omega> i s) \<partial>?M) = 0"
  proof (cases "s = t")
    case True
    then show ?thesis by simp
  next
    case False
    with st have st': "s < t" by simp
    have "(\<integral>\<omega>. g \<omega> * (\<omega> i t - \<omega> i s) \<partial>?M)
        = (\<integral>\<omega>. g \<omega> \<partial>?M) * (\<integral>\<omega>. \<omega> i t - \<omega> i s \<partial>?M)"
      by (rule BMP.indep_var_lebesgue_integral
          [OF bm_meas_increment_indep_var[OF s st' g_meas] g_int
            bm_increment_component_integrable[OF s t0]])
    also have "\<dots> = 0"
      by (simp add: bm_increment_component_integral[OF s t0])
    finally show ?thesis .
  qed
qed

lemma bm_coordinate_measurable_F:
  fixes x0 :: "real^'n::finite"
  assumes s: "0 \<le> s"
  shows "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i s) \<in> borel_measurable
    (natural_filtration (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0
      (bmX x0) s)"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "natural_filtration ?M 0 (bmX x0) s"
  interpret SP: stochastic_process ?M 0 "bmX x0"
    by unfold_locales (intro measurable_bmX, simp)
  interpret AP: adapted_process ?M "natural_filtration ?M 0 (bmX x0)" 0
    "bmX x0"
    by (rule SP.adapted_process_natural_filtration)
  have X_F: "bmX x0 s \<in> borel_measurable ?F"
    by (intro AP.adaptedD s order.refl)
  have nth_meas: "(\<lambda>v :: real^'n. v $ i) \<in> borel_measurable borel"
  proof -
    have "(\<lambda>v :: real^'n. v $ i) = (\<lambda>v. inner v (axis i 1))"
      by (simp add: fun_eq_iff cart_eq_inner_axis)
    then show ?thesis by simp
  qed
  have comp_F: "(\<lambda>\<omega>. bmX x0 s \<omega> $ i) \<in> borel_measurable ?F"
    by (rule measurable_compose[OF X_F nth_meas])
  have eq: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i s)
      = (\<lambda>\<omega>. bmX x0 s \<omega> $ i - x0 $ i)"
    by (simp add: fun_eq_iff bmX_def)
  show ?thesis
    unfolding eq using comp_F by simp
qed

lemma bm_increment_sq:
  fixes x0 :: "real^'n::finite"
  assumes s: "0 \<le> s" and st: "s \<le> t"
  shows bm_increment_sq_integrable:
    "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>\<omega>. (\<omega> i t - \<omega> i s)\<^sup>2)"
    and bm_increment_sq_integral:
    "(\<integral>\<omega>. (\<omega> i t - \<omega> i s)\<^sup>2
      \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)) = t - s"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  have t0: "0 \<le> t" using s st by simp
  have sq_t: "integrable ?M (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. (\<omega> i t)\<^sup>2)"
    using bm_coordinate_sq_integrable[OF t0, of 0 i] by simp
  have sq_s: "integrable ?M (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. (\<omega> i s)\<^sup>2)"
    using bm_coordinate_sq_integrable[OF s, of 0 i] by simp
  have sq_t_val: "(\<integral>\<omega>. (\<omega> i t)\<^sup>2 \<partial>?M) = t"
    using bm_coordinate_sq_integral[OF t0, of 0 i] by simp
  have sq_s_val: "(\<integral>\<omega>. (\<omega> i s)\<^sup>2 \<partial>?M) = s"
    using bm_coordinate_sq_integral[OF s, of 0 i] by simp
  have cross_int: "integrable ?M
      (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i s * (\<omega> i t - \<omega> i s))"
    by (rule bm_meas_increment_product_integrable
        [OF s st bm_coordinate_measurable_F[OF s]
          bm_coordinate_mean_integrable[OF s]])
  have cross_val: "(\<integral>\<omega>. \<omega> i s * (\<omega> i t - \<omega> i s) \<partial>?M) = 0"
    by (rule bm_meas_increment_product_zero
        [OF s st bm_coordinate_measurable_F[OF s]
          bm_coordinate_mean_integrable[OF s]])
  have decomp: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. (\<omega> i t - \<omega> i s)\<^sup>2)
      = (\<lambda>\<omega>. (\<omega> i t)\<^sup>2 - (\<omega> i s)\<^sup>2
            - 2 * (\<omega> i s * (\<omega> i t - \<omega> i s)))"
    by (simp add: fun_eq_iff power2_eq_square algebra_simps)
  have int': "integrable ?M (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real.
      (\<omega> i t)\<^sup>2 - (\<omega> i s)\<^sup>2 - 2 * (\<omega> i s * (\<omega> i t - \<omega> i s)))"
    by (intro Bochner_Integration.integrable_diff sq_t sq_s
        integrable_mult_right cross_int)
  show "integrable ?M (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. (\<omega> i t - \<omega> i s)\<^sup>2)"
    unfolding decomp by (rule int')
  have step1: "(\<integral>\<omega>. (\<omega> i t)\<^sup>2 - (\<omega> i s)\<^sup>2 \<partial>?M)
      = (\<integral>\<omega>. (\<omega> i t)\<^sup>2 \<partial>?M) - (\<integral>\<omega>. (\<omega> i s)\<^sup>2 \<partial>?M)"
    by (intro Bochner_Integration.integral_diff sq_t sq_s)
  have step2: "(\<integral>\<omega>. 2 * (\<omega> i s * (\<omega> i t - \<omega> i s)) \<partial>?M) = 0"
    using cross_int cross_val by simp
  have "(\<integral>\<omega>. (\<omega> i t - \<omega> i s)\<^sup>2 \<partial>?M)
      = (\<integral>\<omega>. (\<omega> i t)\<^sup>2 - (\<omega> i s)\<^sup>2
            - 2 * (\<omega> i s * (\<omega> i t - \<omega> i s)) \<partial>?M)"
    unfolding decomp ..
  also have "\<dots> = (\<integral>\<omega>. (\<omega> i t)\<^sup>2 - (\<omega> i s)\<^sup>2 \<partial>?M)
      - (\<integral>\<omega>. 2 * (\<omega> i s * (\<omega> i t - \<omega> i s)) \<partial>?M)"
    by (intro Bochner_Integration.integral_diff
        Bochner_Integration.integrable_diff sq_t sq_s
        integrable_mult_right cross_int)
  also have "\<dots> = t - s"
    using step1 step2 by (simp add: sq_t_val sq_s_val)
  finally show "(\<integral>\<omega>. (\<omega> i t - \<omega> i s)\<^sup>2 \<partial>?M) = t - s" .
qed

section \<open>The compensated square has constant set integrals\<close>

lemma bm_indicator_coord_sq_integrable:
  assumes u: "0 \<le> u" and A: "A \<in> sets (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure)"
  shows "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (\<lambda>\<omega>. indicator A \<omega> * (c + \<omega> i u)\<^sup>2)"
proof -
  have "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>\<omega>. indicator A \<omega> *\<^sub>R (c + \<omega> i u)\<^sup>2)"
    by (intro integrable_mult_indicator A bm_coordinate_sq_integrable[OF u])
  then show ?thesis by simp
qed

lemma bm_indicator_int:
  assumes A: "A \<in> sets (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure)"
  shows bm_indicator_integrable:
    "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (indicator A :: ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real)"
    and bm_indicator_integral:
    "(\<integral>\<omega>. indicator A \<omega>
      \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)) = BMP.prob A"
proof -
  show "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (indicator A :: ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real)"
  proof (rule BMP.integrable_const_bound[where B = 1])
    show "AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
        norm (indicator A \<omega> :: real) \<le> 1"
      by (intro AE_I2) (simp add: indicator_def)
    show "(indicator A :: ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real)
        \<in> borel_measurable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)"
      by (rule borel_measurable_indicator[OF A])
  qed
  have ins: "A \<inter> space (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) = A"
    using A sets.sets_into_space by blast
  show "(\<integral>\<omega>. indicator A \<omega>
      \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)) = BMP.prob A"
    using ins by simp
qed

text \<open>One coordinate at a time: the conditional second moment increases by
  exactly the elapsed time.\<close>

lemma bm_set_integral_coord_sq_eq:
  fixes x0 :: "real^'n::finite"
  assumes s: "0 \<le> s" and st: "s \<le> t"
    and A: "A \<in> sets (natural_filtration
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0 (bmX x0) s)"
  shows "(\<integral>\<omega>. indicator A \<omega> * (x0 $ i + \<omega> i t)\<^sup>2
        \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      = (\<integral>\<omega>. indicator A \<omega> * (x0 $ i + \<omega> i s)\<^sup>2
        \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
        + (t - s) * BMP.prob A"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "natural_filtration ?M 0 (bmX x0) s"
  let ?d = "\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s"
  let ?g = "\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real.
    indicator A \<omega> * (x0 $ i + \<omega> i s)"
  interpret SP: stochastic_process ?M 0 "bmX x0"
    by unfold_locales (intro measurable_bmX, simp)
  have subalg: "subalgebra ?M ?F"
    by (rule SP.subalgebra_natural_filtration)
  have A_M: "A \<in> sets ?M"
    using A subalg by (auto simp: subalgebra_def)
  have ind_F: "(indicator A :: ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real)
      \<in> borel_measurable ?F"
    by (rule borel_measurable_indicator[OF A])
  have ind_int: "integrable ?M (indicator A :: ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real)"
    by (rule bm_indicator_integrable[OF A_M])
  have ind_val: "(\<integral>\<omega>. indicator A \<omega> \<partial>?M) = BMP.prob A"
    by (rule bm_indicator_integral[OF A_M])
  have ins: "A \<inter> space ?M = A"
    using A_M sets.sets_into_space by blast
  have g_F: "?g \<in> borel_measurable ?F"
  proof -
    have c1: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i s) \<in> borel_measurable ?F"
      by (rule bm_coordinate_measurable_F[OF s])
    show ?thesis
      by (intro borel_measurable_times ind_F borel_measurable_add
          borel_measurable_const c1)
  qed
  have coord_int: "integrable ?M
      (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. x0 $ i + \<omega> i s)"
    by (intro Bochner_Integration.integrable_add BMP.integrable_const
        bm_coordinate_mean_integrable[OF s])
  have g_int: "integrable ?M ?g"
  proof -
    have "integrable ?M (\<lambda>\<omega>. indicator A \<omega> *\<^sub>R (x0 $ i + \<omega> i s))"
      by (intro integrable_mult_indicator A_M coord_int)
    then show ?thesis by simp
  qed
  have cross_int: "integrable ?M (\<lambda>\<omega>. ?g \<omega> * ?d \<omega>)"
    by (rule bm_meas_increment_product_integrable[OF s st g_F g_int])
  have cross_val: "(\<integral>\<omega>. ?g \<omega> * ?d \<omega> \<partial>?M) = 0"
    by (rule bm_meas_increment_product_zero[OF s st g_F g_int])
  have inc_sq_int: "integrable ?M (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. (?d \<omega>)\<^sup>2)"
    by (rule bm_increment_sq_integrable[OF s st])
  have sq_int: "integrable ?M (\<lambda>\<omega>. indicator A \<omega> * (?d \<omega>)\<^sup>2)"
  proof -
    have "integrable ?M (\<lambda>\<omega>. indicator A \<omega> *\<^sub>R (?d \<omega>)\<^sup>2)"
      by (intro integrable_mult_indicator A_M inc_sq_int)
    then show ?thesis by simp
  qed
  have sq_val: "(\<integral>\<omega>. indicator A \<omega> * (?d \<omega>)\<^sup>2 \<partial>?M)
      = BMP.prob A * (t - s)"
  proof (cases "s = t")
    case True
    then show ?thesis by simp
  next
    case False
    with st have st': "s < t" by simp
    have base: "BMP.indep_var borel
        (indicator A :: ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real) borel ?d"
      by (rule bm_meas_increment_indep_var[OF s st' ind_F])
    have "BMP.indep_var borel
        ((\<lambda>x :: real. x) \<circ> (indicator A :: ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real))
        borel ((\<lambda>x :: real. x\<^sup>2) \<circ> ?d)"
      by (rule BMP.indep_var_compose[OF base]) simp_all
    then have indep2: "BMP.indep_var borel
        (indicator A :: ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real)
        borel (\<lambda>\<omega>. (?d \<omega>)\<^sup>2)"
      by (simp add: comp_def)
    have "(\<integral>\<omega>. indicator A \<omega> * (?d \<omega>)\<^sup>2 \<partial>?M)
        = (\<integral>\<omega>. indicator A \<omega> \<partial>?M) * (\<integral>\<omega>. (?d \<omega>)\<^sup>2 \<partial>?M)"
      by (rule BMP.indep_var_lebesgue_integral[OF indep2 ind_int inc_sq_int])
    also have "\<dots> = BMP.prob A * (t - s)"
      by (simp add: ind_val ins bm_increment_sq_integral[OF s st])
    finally show ?thesis .
  qed
  have decomp: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real.
        indicator A \<omega> * (x0 $ i + \<omega> i t)\<^sup>2)
      = (\<lambda>\<omega>. indicator A \<omega> * (x0 $ i + \<omega> i s)\<^sup>2
          + 2 * (?g \<omega> * ?d \<omega>) + indicator A \<omega> * (?d \<omega>)\<^sup>2)"
    by (simp add: fun_eq_iff power2_eq_square algebra_simps)
  have int_s: "integrable ?M
      (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. indicator A \<omega> * (x0 $ i + \<omega> i s)\<^sup>2)"
    by (rule bm_indicator_coord_sq_integrable[OF s A_M])
  have inner_split: "(\<integral>\<omega>. indicator A \<omega> * (x0 $ i + \<omega> i s)\<^sup>2
        + 2 * (?g \<omega> * ?d \<omega>) \<partial>?M)
      = (\<integral>\<omega>. indicator A \<omega> * (x0 $ i + \<omega> i s)\<^sup>2 \<partial>?M)
        + (\<integral>\<omega>. 2 * (?g \<omega> * ?d \<omega>) \<partial>?M)"
    by (intro Bochner_Integration.integral_add int_s integrable_mult_right
        cross_int)
  have cross2_val: "(\<integral>\<omega>. 2 * (?g \<omega> * ?d \<omega>) \<partial>?M) = 0"
    using cross_int cross_val by simp
  have "(\<integral>\<omega>. indicator A \<omega> * (x0 $ i + \<omega> i t)\<^sup>2 \<partial>?M)
      = (\<integral>\<omega>. indicator A \<omega> * (x0 $ i + \<omega> i s)\<^sup>2
          + 2 * (?g \<omega> * ?d \<omega>) + indicator A \<omega> * (?d \<omega>)\<^sup>2 \<partial>?M)"
    unfolding decomp ..
  also have "\<dots> = (\<integral>\<omega>. indicator A \<omega> * (x0 $ i + \<omega> i s)\<^sup>2
          + 2 * (?g \<omega> * ?d \<omega>) \<partial>?M)
      + (\<integral>\<omega>. indicator A \<omega> * (?d \<omega>)\<^sup>2 \<partial>?M)"
    by (intro Bochner_Integration.integral_add
        Bochner_Integration.integrable_add int_s integrable_mult_right
        cross_int sq_int)
  also have "\<dots> = (\<integral>\<omega>. indicator A \<omega> * (x0 $ i + \<omega> i s)\<^sup>2 \<partial>?M)
      + (t - s) * BMP.prob A"
    using inner_split cross2_val sq_val by (simp add: mult_ac)
  finally show ?thesis .
qed

text \<open>Summing the coordinates: the compensated square has equal set
  integrals over events of the past.\<close>

lemma bm_indicator_sq_sum:
  fixes x0 :: "real^'n::finite"
  shows "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real.
      indicator A \<omega> * (bmX x0 u \<omega> \<bullet> bmX x0 u \<omega>))
    = (\<lambda>\<omega>. \<Sum>i\<in>(UNIV :: 'n set). indicator A \<omega> * (x0 $ i + \<omega> i u)\<^sup>2)"
  by (simp add: fun_eq_iff inner_vec_def bmX_def power2_eq_square
      sum_distrib_left)

lemma bm_indicator_sq_integrable:
  fixes x0 :: "real^'n::finite"
  assumes u: "0 \<le> u"
    and A: "A \<in> sets (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)"
  shows "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (\<lambda>\<omega>. indicator A \<omega> * (bmX x0 u \<omega> \<bullet> bmX x0 u \<omega>))"
  unfolding bm_indicator_sq_sum
  by (intro Bochner_Integration.integrable_sum
      bm_indicator_coord_sq_integrable[OF u A])

lemma bm_set_integral_sq_eq:
  fixes x0 :: "real^'n::finite"
  assumes s: "0 \<le> s" and st: "s \<le> t"
    and A: "A \<in> sets (natural_filtration
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0 (bmX x0) s)"
  shows "(\<integral>\<omega>. indicator A \<omega> * (bmX x0 t \<omega> \<bullet> bmX x0 t \<omega>)
        \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      = (\<integral>\<omega>. indicator A \<omega> * (bmX x0 s \<omega> \<bullet> bmX x0 s \<omega>)
        \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
        + real CARD('n) * (t - s) * BMP.prob A"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  interpret SP: stochastic_process ?M 0 "bmX x0"
    by unfold_locales (intro measurable_bmX, simp)
  have A_M: "A \<in> sets ?M"
    using A SP.subalgebra_natural_filtration by (auto simp: subalgebra_def)
  have t0: "0 \<le> t" using s st by simp
  have "(\<integral>\<omega>. indicator A \<omega> * (bmX x0 t \<omega> \<bullet> bmX x0 t \<omega>) \<partial>?M)
      = (\<Sum>i\<in>(UNIV :: 'n set).
          (\<integral>\<omega>. indicator A \<omega> * (x0 $ i + \<omega> i t)\<^sup>2 \<partial>?M))"
    unfolding bm_indicator_sq_sum
    by (intro Bochner_Integration.integral_sum
        bm_indicator_coord_sq_integrable[OF t0 A_M])
  also have "\<dots> = (\<Sum>i\<in>(UNIV :: 'n set).
      (\<integral>\<omega>. indicator A \<omega> * (x0 $ i + \<omega> i s)\<^sup>2 \<partial>?M)
        + (t - s) * BMP.prob A)"
    by (intro sum.cong refl bm_set_integral_coord_sq_eq[OF s st A])
  also have "\<dots> = (\<Sum>i\<in>(UNIV :: 'n set).
      (\<integral>\<omega>. indicator A \<omega> * (x0 $ i + \<omega> i s)\<^sup>2 \<partial>?M))
      + real CARD('n) * ((t - s) * BMP.prob A)"
    by (simp add: sum.distrib)
  also have "(\<Sum>i\<in>(UNIV :: 'n set).
      (\<integral>\<omega>. indicator A \<omega> * (x0 $ i + \<omega> i s)\<^sup>2 \<partial>?M))
      = (\<integral>\<omega>. indicator A \<omega> * (bmX x0 s \<omega> \<bullet> bmX x0 s \<omega>) \<partial>?M)"
    unfolding bm_indicator_sq_sum
    by (intro Bochner_Integration.integral_sum[symmetric]
        bm_indicator_coord_sq_integrable[OF s A_M])
  finally show ?thesis
    by (simp add: mult_ac)
qed

section \<open>The compensated square is a martingale\<close>

theorem martingale_bm_square:
  fixes x0 :: "real^'n::finite"
  shows "martingale (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (bmX x0)) 0
    (\<lambda>t \<omega>. bmX x0 t \<omega> \<bullet> bmX x0 t \<omega>
      - set_lebesgue_integral lborel {0..t}
          (\<lambda>s. trace (mat 1 :: real^'n^'n)))"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "natural_filtration ?M 0 (bmX x0)"
  let ?Z = "\<lambda>t \<omega>. bmX x0 t \<omega> \<bullet> bmX x0 t \<omega>
    - set_lebesgue_integral lborel {0..t} (\<lambda>s. trace (mat 1 :: real^'n^'n))"
  interpret SP: stochastic_process ?M 0 "bmX x0"
    by unfold_locales (intro measurable_bmX, simp)
  interpret AP: adapted_process ?M ?F 0 "bmX x0"
    by (rule SP.adapted_process_natural_filtration)
  have fm: "finite_measure ?M"
    by (rule finite_measureI) (simp add: BMP.emeasure_space_1)
  have sfs: "sigma_finite_subalgebra ?M (?F i)" for i
    by (intro finite_measure_subalgebra_is_sigma_finite
        finite_measure_subalgebra.intro
        finite_measure_subalgebra_axioms.intro
        fm SP.subalgebra_natural_filtration)
  have sff: "sigma_finite_filtered_measure ?M ?F 0"
    by (intro sigma_finite_filtered_measure.intro
        sigma_finite_filtered_measure_axioms.intro
        SP.filtered_measure_natural_filtration sfs)
  interpret SFF: sigma_finite_filtered_measure ?M ?F 0
    by (rule sff)
  have Zmeas: "?Z u \<in> borel_measurable (?F u)" if u: "0 \<le> u" for u
  proof -
    have X_F: "bmX x0 u \<in> borel_measurable (?F u)"
      by (intro AP.adaptedD u order.refl)
    have "(\<lambda>\<omega>. bmX x0 u \<omega> \<bullet> bmX x0 u \<omega>) \<in> borel_measurable (?F u)"
      by (intro borel_measurable_inner X_F)
    then show ?thesis
      by (intro borel_measurable_diff borel_measurable_const)
  qed
  have Zint: "integrable ?M (?Z u)" if u: "0 \<le> u" for u
    by (intro Bochner_Integration.integrable_diff bmX_sq_integrable[OF u]
        BMP.integrable_const)
  have ap: "adapted_process ?M ?F 0 ?Z"
    by (intro adapted_process.intro[OF SP.filtered_measure_natural_filtration]
        adapted_process_axioms.intro Zmeas)
  show ?thesis
  proof (rule SFF.martingale_of_set_integral_eq[OF ap])
    show "\<And>i. 0 \<le> i \<Longrightarrow> integrable ?M (?Z i)"
      by (rule Zint)
    fix A and u v :: real
    assume u: "0 \<le> u" and uv: "u \<le> v" and A: "A \<in> sets (?F u)"
    have v: "0 \<le> v" using u uv by simp
    have A_M: "A \<in> sets ?M"
      using A SP.subalgebra_natural_filtration by (auto simp: subalgebra_def)
    have ind_int: "integrable ?M
        (indicator A :: ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real)"
      by (rule bm_indicator_integrable[OF A_M])
    have ind_val: "(\<integral>\<omega>. indicator A \<omega> \<partial>?M) = BMP.prob A"
      by (rule bm_indicator_integral[OF A_M])
    have ins: "A \<inter> space ?M = A"
      using A_M sets.sets_into_space by blast
    have cst: "(\<integral>\<omega>. indicator A \<omega> * c \<partial>?M) = BMP.prob A * c" for c :: real
    proof -
      have "(\<integral>\<omega>. indicator A \<omega> * c \<partial>?M)
          = (\<integral>\<omega>. indicator A \<omega> \<partial>?M) * c"
        using ind_int by simp
      then show ?thesis
        by (simp add: ind_val ins)
    qed
    have split: "set_lebesgue_integral ?M A (?Z w)
        = (\<integral>\<omega>. indicator A \<omega> * (bmX x0 w \<omega> \<bullet> bmX x0 w \<omega>) \<partial>?M)
          - BMP.prob A * (real CARD('n) * w)" if w: "0 \<le> w" for w
    proof -
      have comp: "set_lebesgue_integral lborel {0..w}
          (\<lambda>s. trace (mat 1 :: real^'n^'n)) = real CARD('n) * w"
        by (rule bm_compensator_const[OF w])
      have comp': "(LBINT x. indicat_real {0..w} x
            *\<^sub>R trace (mat 1 :: real^'n^'n)) = real CARD('n) * w"
        using comp unfolding set_lebesgue_integral_def .
      have i1: "integrable ?M
          (\<lambda>\<omega>. indicator A \<omega> * (bmX x0 w \<omega> \<bullet> bmX x0 w \<omega>))"
        by (rule bm_indicator_sq_integrable[OF w A_M])
      have i2: "integrable ?M
          (\<lambda>\<omega>. indicator A \<omega> * (real CARD('n) * w))"
        by (intro integrable_mult_left ind_int)
      have "set_lebesgue_integral ?M A (?Z w)
          = (\<integral>\<omega>. indicator A \<omega> * (bmX x0 w \<omega> \<bullet> bmX x0 w \<omega>)
              - indicator A \<omega> * (real CARD('n) * w) \<partial>?M)"
        unfolding set_lebesgue_integral_def
        by (intro Bochner_Integration.integral_cong refl)
          (simp add: comp' trace_mat1 w algebra_simps)
      also have "\<dots> = (\<integral>\<omega>. indicator A \<omega>
            * (bmX x0 w \<omega> \<bullet> bmX x0 w \<omega>) \<partial>?M)
          - (\<integral>\<omega>. indicator A \<omega> * (real CARD('n) * w) \<partial>?M)"
        by (intro Bochner_Integration.integral_diff i1 i2)
      also have "\<dots> = (\<integral>\<omega>. indicator A \<omega>
            * (bmX x0 w \<omega> \<bullet> bmX x0 w \<omega>) \<partial>?M)
          - BMP.prob A * (real CARD('n) * w)"
        by (simp add: cst ins)
      finally show ?thesis .
    qed
    have vsplit: "set_lebesgue_integral ?M A (?Z v)
        = (\<integral>\<omega>. indicator A \<omega> * (bmX x0 v \<omega> \<bullet> bmX x0 v \<omega>) \<partial>?M)
          - BMP.prob A * (real CARD('n) * v)"
      by (rule split[OF v])
    have usplit: "set_lebesgue_integral ?M A (?Z u)
        = (\<integral>\<omega>. indicator A \<omega> * (bmX x0 u \<omega> \<bullet> bmX x0 u \<omega>) \<partial>?M)
          - BMP.prob A * (real CARD('n) * u)"
      by (rule split[OF u])
    have vu: "(\<integral>\<omega>. indicator A \<omega> * (bmX x0 v \<omega> \<bullet> bmX x0 v \<omega>) \<partial>?M)
        = (\<integral>\<omega>. indicator A \<omega> * (bmX x0 u \<omega> \<bullet> bmX x0 u \<omega>) \<partial>?M)
          + real CARD('n) * (v - u) * BMP.prob A"
      by (rule bm_set_integral_sq_eq[OF u uv A])
    show "set_lebesgue_integral ?M A (?Z u)
        = set_lebesgue_integral ?M A (?Z v)"
      unfolding usplit vsplit vu by (simp add: algebra_simps)
  qed
qed

text \<open>Consequently the process form of the martingale problem is
  inhabited: with \<open>acov = mat 1\<close> the process of \<open>ito_Z\<close> is exactly \<open>?Z\<close>
  above, so \<open>martingale_bm_square\<close> discharges the hypothesis
  \<open>Z_martingale\<close> of \<open>ito_const_horizon_market\<close>.  The instantiation
  itself belongs to Ito\_Market, which imports this theory's ambient
  definitions.\<close>

section \<open>The compensated square of a SINGLE coordinate is a martingale\<close>

text \<open>
  \<open>martingale_bm_square\<close> above compensates the squared NORM by the trace. That is
  what \<open>ito_Z\<close> and \<open>dynkin_quadratic\<close> speak about, and it is all the market
  locales currently demand.

  It is not enough for Lemma 2.2 of arXiv:2512.17702. The tightness chain
  (\<open>Path_Tightness.tight_on_set_path_laws_vec\<close> \<open>\<leftarrow>\<close>
  \<open>Increment_Moments.fourth_moment_bound_bounded\<close> \<open>\<leftarrow>\<close>
  \<open>Stopped_Localization.stopped_covariation\<close>) needs a fourth-moment bound on each
  COORDINATE separately, hence the compensated square of each coordinate must be
  a martingale in its own right. A trace identity does not give the coordinate
  ones, so this has to be proved.

  It costs little: \<open>bm_set_integral_coord_sq_eq\<close> is already the per-coordinate
  increment identity that \<open>bm_set_integral_sq_eq\<close> sums up. The proof below is the
  proof of \<open>martingale_bm_square\<close> with the sum removed --- the compensator drops
  from \<open>CARD('n) * w\<close> to \<open>w\<close>, since \<open>mat 1 $ i $ i = 1\<close>.
\<close>

lemma bm_compensator_coord:
  assumes u: "0 \<le> u"
  shows "set_lebesgue_integral lborel {0..u}
      (\<lambda>_. (mat 1 :: real^'n::finite^'n) $ i $ i) = u"
proof -
  have "set_lebesgue_integral lborel {0..u}
      (\<lambda>_. (mat 1 :: real^'n^'n) $ i $ i)
      = u * ((mat 1 :: real^'n^'n) $ i $ i)"
    using u by (subst set_integral_const) (auto simp: emeasure_lborel_Icc)
  then show ?thesis by (simp add: mat_def)
qed

theorem martingale_bm_coord_square:
  fixes x0 :: "real^'n::finite"
  shows "martingale (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (bmX x0)) 0
    (\<lambda>t \<omega>. (bmX x0 t \<omega> $ i)\<^sup>2
      - set_lebesgue_integral lborel {0..t}
          (\<lambda>s. (mat 1 :: real^'n^'n) $ i $ i))"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "natural_filtration ?M 0 (bmX x0)"
  let ?Z = "\<lambda>t \<omega>. (bmX x0 t \<omega> $ i)\<^sup>2
    - set_lebesgue_integral lborel {0..t}
        (\<lambda>s. (mat 1 :: real^'n^'n) $ i $ i)"
  interpret SP: stochastic_process ?M 0 "bmX x0"
    by unfold_locales (intro measurable_bmX, simp)
  interpret AP: adapted_process ?M ?F 0 "bmX x0"
    by (rule SP.adapted_process_natural_filtration)
  have fm: "finite_measure ?M"
    by (rule finite_measureI) (simp add: BMP.emeasure_space_1)
  have sfs: "sigma_finite_subalgebra ?M (?F j)" for j
    by (intro finite_measure_subalgebra_is_sigma_finite
        finite_measure_subalgebra.intro
        finite_measure_subalgebra_axioms.intro
        fm SP.subalgebra_natural_filtration)
  have sff: "sigma_finite_filtered_measure ?M ?F 0"
    by (intro sigma_finite_filtered_measure.intro
        sigma_finite_filtered_measure_axioms.intro
        SP.filtered_measure_natural_filtration sfs)
  interpret SFF: sigma_finite_filtered_measure ?M ?F 0
    by (rule sff)
  have coord: "bmX x0 w \<omega> $ i = x0 $ i + \<omega> i w" for w \<omega>
    by (simp add: bmX_def)
  have Zmeas: "?Z u \<in> borel_measurable (?F u)" if u: "0 \<le> u" for u
  proof -
    have X_F: "bmX x0 u \<in> borel_measurable (?F u)"
      by (intro AP.adaptedD u order.refl)
    have cnt: "continuous_on UNIV (\<lambda>x :: real^'n. x $ i)"
      by (intro linear_continuous_on bounded_linear_vec_nth)
    have prj: "(\<lambda>x :: real^'n. x $ i) \<in> borel_measurable borel"
      by (rule borel_measurable_continuous_onI[OF cnt])
    have "(\<lambda>\<omega>. bmX x0 u \<omega> $ i) \<in> borel_measurable (?F u)"
      by (rule measurable_compose[OF X_F prj])
    hence "(\<lambda>\<omega>. (bmX x0 u \<omega> $ i)\<^sup>2) \<in> borel_measurable (?F u)"
      by (intro borel_measurable_power)
    then show ?thesis
      by (intro borel_measurable_diff borel_measurable_const)
  qed
  have Zint: "integrable ?M (?Z u)" if u: "0 \<le> u" for u
    unfolding coord
    by (intro Bochner_Integration.integrable_diff
        bm_coordinate_sq_integrable[OF u] BMP.integrable_const)
  have ap: "adapted_process ?M ?F 0 ?Z"
    by (intro adapted_process.intro[OF SP.filtered_measure_natural_filtration]
        adapted_process_axioms.intro Zmeas)
  show ?thesis
  proof (rule SFF.martingale_of_set_integral_eq[OF ap])
    show "\<And>j. 0 \<le> j \<Longrightarrow> integrable ?M (?Z j)"
      by (rule Zint)
    fix A and u v :: real
    assume u: "0 \<le> u" and uv: "u \<le> v" and A: "A \<in> sets (?F u)"
    have v: "0 \<le> v" using u uv by simp
    have A_M: "A \<in> sets ?M"
      using A SP.subalgebra_natural_filtration by (auto simp: subalgebra_def)
    have ind_int: "integrable ?M
        (indicator A :: ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real)"
      by (rule bm_indicator_integrable[OF A_M])
    have ind_val: "(\<integral>\<omega>. indicator A \<omega> \<partial>?M) = BMP.prob A"
      by (rule bm_indicator_integral[OF A_M])
    have ins: "A \<inter> space ?M = A"
      using A_M sets.sets_into_space by blast
    have cst: "(\<integral>\<omega>. indicator A \<omega> * c \<partial>?M) = BMP.prob A * c" for c :: real
    proof -
      have "(\<integral>\<omega>. indicator A \<omega> * c \<partial>?M) = (\<integral>\<omega>. indicator A \<omega> \<partial>?M) * c"
        using ind_int by simp
      then show ?thesis by (simp add: ind_val ins)
    qed
    have split: "set_lebesgue_integral ?M A (?Z w)
        = (\<integral>\<omega>. indicator A \<omega> * (x0 $ i + \<omega> i w)\<^sup>2 \<partial>?M) - BMP.prob A * w"
      if w: "0 \<le> w" for w
    proof -
      have comp: "set_lebesgue_integral lborel {0..w}
          (\<lambda>s. (mat 1 :: real^'n^'n) $ i $ i) = w"
        by (rule bm_compensator_coord[OF w])
      have i1: "integrable ?M (\<lambda>\<omega>. indicator A \<omega> * (x0 $ i + \<omega> i w)\<^sup>2)"
        by (rule bm_indicator_coord_sq_integrable[OF w A_M])
      have i2: "integrable ?M (\<lambda>\<omega>. indicator A \<omega> * w)"
        by (intro integrable_mult_left ind_int)
      have "set_lebesgue_integral ?M A (?Z w)
          = (\<integral>\<omega>. indicator A \<omega> * (x0 $ i + \<omega> i w)\<^sup>2
              - indicator A \<omega> * w \<partial>?M)"
        unfolding set_lebesgue_integral_def
        by (intro Bochner_Integration.integral_cong refl)
          (simp add: comp coord mat_def w algebra_simps)
      also have "\<dots> = (\<integral>\<omega>. indicator A \<omega> * (x0 $ i + \<omega> i w)\<^sup>2 \<partial>?M)
          - (\<integral>\<omega>. indicator A \<omega> * w \<partial>?M)"
        by (intro Bochner_Integration.integral_diff i1 i2)
      also have "\<dots> = (\<integral>\<omega>. indicator A \<omega> * (x0 $ i + \<omega> i w)\<^sup>2 \<partial>?M)
          - BMP.prob A * w"
        by (simp add: cst ins)
      finally show ?thesis .
    qed
    have vu: "(\<integral>\<omega>. indicator A \<omega> * (x0 $ i + \<omega> i v)\<^sup>2 \<partial>?M)
        = (\<integral>\<omega>. indicator A \<omega> * (x0 $ i + \<omega> i u)\<^sup>2 \<partial>?M)
          + (v - u) * BMP.prob A"
      by (rule bm_set_integral_coord_sq_eq[OF u uv A])
    show "set_lebesgue_integral ?M A (?Z u)
        = set_lebesgue_integral ?M A (?Z v)"
      unfolding split[OF u] split[OF v] vu by (simp add: algebra_simps)
  qed
qed

theorem Brownian_market_sufficiently_volatile:
  fixes x0 :: "real^'n::finite"
  assumes k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L" and c: "0 \<le> c"
    and K: "AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
      \<forall>s. 0 \<le> s \<longrightarrow> s \<le> c \<longrightarrow> bmX x0 s \<omega> \<in> K"
  shows "sufficiently_volatile_market
    (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (bmX x0)) (bmX x0)
    (\<lambda>_ _. mat 1) k L K x0 (\<lambda>_. c)"
proof (intro sufficiently_volatile_market.intro
    sufficiently_volatile_market_axioms.intro)
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  show "martingale ?M (natural_filtration ?M 0 (bmX x0)) 0 (bmX x0)"
    by (rule martingale_bmX)
  show "prob_space ?M" by simp
  show "1 \<le> k" "k < CARD('n)" "1 \<le> L" by fact+
  show "AE \<omega> in ?M. bmX x0 0 \<omega> = x0" by (rule bmX_start)
  show "AE \<omega> in ?M. 0 \<le> c" using c by simp
  show "(\<lambda>_. c) \<in> borel_measurable ?M" by simp
  show "AE \<omega> in ?M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> c \<longrightarrow> bmX x0 s \<omega> \<in> K"
    by (rule K)
  have psd1: "psd (mat 1 :: real^'n^'n)"
    by (simp add: psd_def)
  show "AE \<omega> in ?M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> c \<longrightarrow> psd (mat 1 :: real^'n^'n)"
    using psd1 by simp
  have elb: "eigen_lb (mat 1 :: real^'n^'n) (CARD('n) - k)"
    unfolding eigen_lb_def
  proof (intro exI[of _ UNIV] conjI)
    show "subspace (UNIV :: (real^'n) set)" by simp
    show "CARD('n) - k \<le> dim (UNIV :: (real^'n) set)" by simp
    show "\<forall>x\<in>(UNIV :: (real^'n) set). x \<bullet> x \<le> x \<bullet> (mat 1 *v x)"
      by simp
  qed
  show "AE \<omega> in ?M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> c \<longrightarrow>
      eigen_lb (mat 1 :: real^'n^'n) (CARD('n) - k)"
    using elb by simp
  have eub: "eigen_ub (mat 1 :: real^'n^'n) L"
  proof -
    have "x \<bullet> x \<le> L * (x \<bullet> x)" for x :: "real^'n"
      using mult_right_mono[OF L inner_ge_zero] by simp
    then show ?thesis
      by (simp add: eigen_ub_def)
  qed
  show "AE \<omega> in ?M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> c \<longrightarrow>
      eigen_ub (mat 1 :: real^'n^'n) L"
    using eub by simp
  have ti: "set_integrable lborel {0..t}
      (\<lambda>s. trace (mat 1 :: real^'n^'n))" for t :: real
  proof -
    have "integrable lborel
        (\<lambda>s. indicator {0..t} s *\<^sub>R trace (mat 1 :: real^'n^'n))"
    proof (intro integrable_scaleR_left integrable_real_indicator)
      show "{0..t} \<in> sets lborel"
        unfolding sets_lborel
        by (intro borel_closed closed_atLeastAtMost)
      show "emeasure lborel {0..t} < \<infinity>"
        by (simp add: emeasure_lborel_Icc_eq)
    qed
    then show ?thesis
      unfolding set_integrable_def .
  qed
  show "AE \<omega> in ?M. \<forall>t :: real. 0 \<le> t \<longrightarrow>
      set_integrable lborel {0..t} (\<lambda>s. trace (mat 1 :: real^'n^'n))"
    using ti by (intro AE_I2) blast
  show "\<And>t. 0 \<le> t \<Longrightarrow> integrable ?M
      (\<lambda>\<omega>. bmX x0 (min t c) \<omega> \<bullet> bmX x0 (min t c) \<omega>)"
    using c by (intro bmX_sq_integrable) simp
  show "\<And>t. 0 \<le> t \<Longrightarrow> integrable ?M
      (\<lambda>\<omega>. set_lebesgue_integral lborel {0..min t c}
        (\<lambda>s. trace (mat 1 :: real^'n^'n)))"
    by (rule BMP.integrable_const)
  show "(\<integral>\<omega>. bmX x0 (min t c) \<omega> \<bullet> bmX x0 (min t c) \<omega> \<partial>?M)
      - (\<integral>\<omega>. set_lebesgue_integral lborel {0..min t c}
          (\<lambda>s. trace (mat 1 :: real^'n^'n)) \<partial>?M) = x0 \<bullet> x0"
    if t: "0 \<le> t" for t
  proof -
    have u: "0 \<le> min t c" using t c by simp
    have 1: "(\<integral>\<omega>. bmX x0 (min t c) \<omega> \<bullet> bmX x0 (min t c) \<omega> \<partial>?M)
        = x0 \<bullet> x0 + real CARD('n) * min t c"
      by (rule bmX_sq_integral[OF u])
    have 2: "set_lebesgue_integral lborel {0..min t c}
        (\<lambda>s. trace (mat 1 :: real^'n^'n)) = real CARD('n) * min t c"
      by (rule bm_compensator_const[OF u])
    show ?thesis
      unfolding 1 2 by (simp add: BMP.prob_space)
  qed
  show "martingale ?M (natural_filtration ?M 0 (bmX x0)) 0
      (coord_Z (bmX x0) (\<lambda>_ _. mat 1) i)" for i
    unfolding coord_Z_def by (rule martingale_bm_coord_square)
qed

section \<open>A concrete instance: the class \<open>\<P>\<^sub>x\<close> is inhabited\<close>

text \<open>Specialising the theorem above to the planar market with
  \<open>k = L = 1\<close>, horizon \<open>1\<close> and start \<open>0\<close> discharges all its side
  conditions numerically, so the following statement has no hypotheses
  whatsoever: the axiomatised market class of
  Relative\_Arbitrage\_Stochastic is non-vacuous.\<close>

theorem sufficiently_volatile_market_nonvacuous:
  "sufficiently_volatile_market
    (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (bmX 0)) (bmX (0 :: real^2))
    (\<lambda>_ _. mat 1) 1 1 UNIV 0 (\<lambda>_. 1)"
  by (rule Brownian_market_sufficiently_volatile) simp_all

interpretation BM2: sufficiently_volatile_market
    "bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure"
    "natural_filtration bm_paths 0 (bmX 0)" "bmX (0 :: real^2)"
    "\<lambda>_ _. mat 1" 1 1 UNIV 0 "\<lambda>_. 1"
  by (rule sufficiently_volatile_market_nonvacuous)

text \<open>With the interpretation in place, the locale's facts are ordinary
  theorems about the Brownian market.  In particular the
  martingale-problem identity --- an \<^emph>\<open>assumption\<close> of the locale, here a
  consequence of the construction --- yields a closed numerical
  statement with no hypotheses: planar Brownian motion started at the
  origin has expected squared norm \<open>2\<close> at time \<open>1\<close>.\<close>

corollary bm2_expected_square:
  "(\<integral>\<omega>. bmX (0 :: real^2) 1 \<omega> \<bullet> bmX 0 1 \<omega>
      \<partial>(bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure)) = 2"
proof -
  have comp: "set_lebesgue_integral lborel {0..(1 :: real)}
      (\<lambda>s. trace (mat 1 :: real^2^2)) = 2"
    by (subst bm_compensator_const) simp_all
  show ?thesis
    using BM2.dynkin_quadratic[of 1]
    by (simp add: BMP.prob_space comp)
qed

text \<open>The exit-time bound \<open>E[\<tau>] \<le> v(x0)\<close> of Example 3.1 is available
  inside the locale as \<open>expected_exit_time_bound\<close>, but instantiating it
  non-degenerately requires \<open>K = cball 0 r\<close> together with the first exit
  time of the ball; that is a genuine stopping time of the continuous
  modification and hence belongs to the quadratic-variation phase.\<close>

end
