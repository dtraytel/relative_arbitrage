section \<open>Criteria for integrability, and two lattice helpers\<close>

(*<*)
theory Integrability_Criteria
  imports Martingale_Algebra "HOL-Probability.Probability"
begin

(*>*)

text \<open>
  Small, frequently needed criteria that neither HOL-Probability nor the
  AFP's \<open>Martingales\<close> states: when a square-integrable or boundedly
  measurable function is integrable, when a clamped or tail-truncated one
  is, integrability and integrals under a scalar multiple, positivity of an
  integral from almost-everywhere positivity, two set integrals over
  degenerate sets, the exponential time integral, and independence read
  through a distribution or through the components of a product measure.

  Two facts about \<open>ennreal\<close> suprema and about shifting and scaling an
  infimum of reals come along, because the same arguments need them and
  they have nowhere better to live.
\<close>

lemma cInf_mult_pos:
  fixes A :: "real set"
  assumes c0: "0 < c" and ne: "A \<noteq> {}" and bdd: "bdd_below A"
  shows "Inf ((\<lambda>t. c * t) ` A) = c * Inf A"
proof -
  obtain m where m: "\<And>a. a \<in> A \<Longrightarrow> m \<le> a"
    using bdd unfolding bdd_below_def by blast
  have bddI: "bdd_below ((\<lambda>t. c * t) ` A)"
  proof (rule bdd_belowI[of _ "c * m"])
    fix t assume "t \<in> (\<lambda>t. c * t) ` A"
    then obtain a where aA: "a \<in> A" and ta: "t = c * a" by auto
    show "c * m \<le> t" unfolding ta using m[OF aA] c0 by (simp add: mult_left_mono)
  qed
  have neI: "(\<lambda>t. c * t) ` A \<noteq> {}" using ne by auto
  have ge: "c * Inf A \<le> Inf ((\<lambda>t. c * t) ` A)"
  proof (rule cInf_greatest[OF neI])
    fix t assume "t \<in> (\<lambda>t. c * t) ` A"
    then obtain a where aA: "a \<in> A" and ta: "t = c * a" by auto
    have "Inf A \<le> a" by (rule cInf_lower[OF aA bdd])
    then show "c * Inf A \<le> t" unfolding ta using c0 by (simp add: mult_left_mono)
  qed
  have "Inf ((\<lambda>t. c * t) ` A) / c \<le> Inf A"
  proof (rule cInf_greatest[OF ne])
    fix a assume aA: "a \<in> A"
    have "Inf ((\<lambda>t. c * t) ` A) \<le> c * a"
      by (rule cInf_lower[OF _ bddI]) (use aA in auto)
    then show "Inf ((\<lambda>t. c * t) ` A) / c \<le> a"
      using c0 by (simp add: divide_le_eq mult.commute)
  qed
  then have le: "Inf ((\<lambda>t. c * t) ` A) \<le> c * Inf A"
    using c0 by (simp add: divide_le_eq mult.commute)
  show ?thesis using ge le by linarith
qed

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
        by (simp add: P.emeasure_eq_measure prod_nonneg)
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
        by (auto intro!: Emem)
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

lemma set_integral_lborel_singleton [simp]:
  fixes f :: "real \<Rightarrow> real"
  shows "set_lebesgue_integral lborel {c} f = 0"
proof -
  have "AE s in lborel. indicat_real {c} s *\<^sub>R f s = 0"
    using AE_lborel_singleton[of c] by auto
  then show ?thesis
    unfolding set_lebesgue_integral_def by (rule integral_eq_zero_AE)
qed

text \<open>The market stopping at time \<open>0\<close>: constant state \<open>x0\<close>, horizon \<open>0\<close>,
  covariance \<open>mat 1\<close> at the single instant \<open>s = 0\<close> and \<open>0\<close> afterwards.
  The eigenvalue constraints are imposed only on \<open>[0, tau] = {0}\<close>, where
  \<open>mat 1\<close> satisfies them; the compensator integrals vanish since the
  covariance is supported on a Lebesgue-null set.\<close>

lemma set_integral_at_origin:
  fixes c t :: real
  shows "set_integrable lborel {0..t} (\<lambda>s. if s = 0 then c else 0)"
    and "set_lebesgue_integral lborel {0..t} (\<lambda>s. if s = 0 then c else 0) = 0"
proof -
  have m: "(\<lambda>s :: real. indicator {0..t} s *\<^sub>R (if s = 0 then c else 0))
      \<in> borel_measurable lborel"
    by measurable
  have ae: "AE s in lborel.
      indicator {0..t} s *\<^sub>R (if s = 0 then c else 0) = (0 :: real)"
    using AE_lborel_singleton[of 0] by eventually_elim auto
  have "integrable lborel
      (\<lambda>s :: real. indicator {0..t} s *\<^sub>R (if s = 0 then c else 0))"
    using integrable_cong_AE[OF m borel_measurable_const ae] by simp
  then show "set_integrable lborel {0..t} (\<lambda>s. if s = 0 then c else 0)"
    unfolding set_integrable_def .
  show "set_lebesgue_integral lborel {0..t}
      (\<lambda>s. if s = 0 then c else 0) = 0"
    unfolding set_lebesgue_integral_def
    using integral_cong_AE[OF m borel_measurable_const ae] by simp
qed

text \<open>LR, proof of Lemma 2.1 of \<^cite>\<open>LaiShkolnikovSoner\<close>: with \<open>f\<^sub>\<lambda>(P) = -(1/\<lambda>) ln E\<^sub>P[e\<^sup>-\<^sup>\<lambda>\<^sup>\<tau>]\<close>, the
  essential infimum of a time bounded in \<open>[0, T]\<close> is \<open>inf\<^sub>\<lambda> f\<^sub>\<lambda>\<close>.  Each
  \<open>f\<^sub>\<lambda>\<close> dominates the essential infimum (Jensen-free: the a.s. lower
  bound passes through the decreasing exponential), and as \<open>\<lambda> \<rightarrow> \<infinity>\<close>
  the transform concentrates at the essential infimum.\<close>

lemma exp_neg_time_integrable:
  fixes tau :: "'a \<Rightarrow> real" and l :: real
  assumes M: "prob_space M" and meas: "tau \<in> borel_measurable M"
    and nn: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> 0 \<le> tau \<omega>"
    and lam: "0 \<le> l"
  shows "integrable M (\<lambda>\<omega>. exp (- l * tau \<omega>))"
proof -
  interpret prob_space M by fact
  have m: "(\<lambda>\<omega>. exp (- l * tau \<omega>)) \<in> borel_measurable M"
    using meas by measurable
  have b: "norm (exp (- l * tau \<omega>)) \<le> 1" if w: "\<omega> \<in> space M" for \<omega>
    using nn[OF w] lam
    by (simp add: abs_of_pos)
  show ?thesis
    by (rule integrable_const_bound[where B = 1])
      (use m b in \<open>auto\<close>)
qed

lemma exp_neg_time_integral_lower:
  fixes tau :: "'a \<Rightarrow> real" and l T :: real
  assumes M: "prob_space M" and meas: "tau \<in> borel_measurable M"
    and nn: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> 0 \<le> tau \<omega>"
    and le: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> tau \<omega> \<le> T"
    and lam: "0 \<le> l"
  shows "exp (- l * T) \<le> (\<integral>\<omega>. exp (- l * tau \<omega>) \<partial>M)"
proof -
  interpret prob_space M by fact
  have "exp (- l * T) = (\<integral>\<omega>. exp (- l * T) \<partial>M)"
    by (simp add: prob_space)
  also have "\<dots> \<le> (\<integral>\<omega>. exp (- l * tau \<omega>) \<partial>M)"
  proof (rule Bochner_Integration.integral_mono)
    show "integrable M (\<lambda>\<omega>. exp (- l * T))"
      by (rule integrable_const)
    show "integrable M (\<lambda>\<omega>. exp (- l * tau \<omega>))"
      by (rule exp_neg_time_integrable[OF M meas nn lam])
    show "exp (- l * T) \<le> exp (- l * tau \<omega>)"
      if w: "\<omega> \<in> space M" for \<omega>
    proof -
      have "l * tau \<omega> \<le> l * T"
        by (rule mult_left_mono[OF le[OF w] lam])
      then show ?thesis by simp
    qed
  qed
  finally show ?thesis .
qed

text \<open>The transfer theorem \<open>weak_conv_integral_of_L2_bound\<close> asks for a
  battery of integrability facts under every approximating law and under
  the limit.  All of them follow from one input: a bound on the second
  moment of the coordinate, which the members have by
  a second-moment bound in the application and which the limit inherits because
  \<open>\<omega> \<mapsto> (X\<^sub>u $ i)\<^sup>2\<close> is continuous and nonnegative
  (\<open>Path_Space.weak_conv_on_nn_integral_le\<close>).  This subsection therefore
  works with a bare pair law with an \<open>L\<^sup>2\<close> bound and never mentions the
  class.\<close>

lemma integrable_of_sq_integrable:
  fixes f :: "'a \<Rightarrow> real"
  assumes fm: "finite_measure N" and m: "f \<in> borel_measurable N"
    and sq: "integrable N (\<lambda>\<omega>. (f \<omega>)\<^sup>2)"
  shows "integrable N f"
proof (rule Bochner_Integration.integrable_bound)
  show "integrable N (\<lambda>\<omega>. 1 + (f \<omega>)\<^sup>2)"
    by (intro Bochner_Integration.integrable_add
        finite_measure.integrable_const[OF fm] sq)
  show "f \<in> borel_measurable N" by (rule m)
  show "AE \<omega> in N. norm (f \<omega>) \<le> norm (1 + (f \<omega>)\<^sup>2)"
  proof (intro AE_I2)
    fix \<omega>
    have nn: "(0::real) \<le> (1 - \<bar>f \<omega>\<bar>)\<^sup>2" by simp
    have exp: "(1 - \<bar>f \<omega>\<bar>)\<^sup>2 = 1 - 2 * \<bar>f \<omega>\<bar> + (f \<omega>)\<^sup>2"
      by (simp add: power2_diff)
    have "\<bar>f \<omega>\<bar> \<le> 1 + (f \<omega>)\<^sup>2"
      using nn abs_ge_zero[of "f \<omega>"] unfolding exp by linarith
    then show "norm (f \<omega>) \<le> norm (1 + (f \<omega>)\<^sup>2)" by simp
  qed
qed

text \<open>\<open>weak_conv_integral_of_L2_bound\<close> asks, besides the \<open>L\<^sup>2\<close> bound
  itself, for integrability of the clamped and of the tail-truncated
  integrand under every law involved.  Neither depends on the path space:
  a clamp is bounded, and a tail truncation is dominated by \<open>\<bar>f\<bar>\<close>.\<close>

lemma bounded_measurable_integrable:
  fixes g :: "'a \<Rightarrow> real"
  assumes P: "finite_measure N" and m: "g \<in> borel_measurable N"
    and b: "\<And>w. \<bar>g w\<bar> \<le> D"
  shows "integrable N g"
  by (rule finite_measure.integrable_const_bound[OF P _ m]) (use b in auto)

lemma clamp_integrable:
  fixes f :: "'a \<Rightarrow> real"
  assumes P: "finite_measure N" and m: "f \<in> borel_measurable N"
  shows "integrable N (\<lambda>w. max (- R) (min R (f w)))"
proof (rule bounded_measurable_integrable[OF P])
  show "(\<lambda>w. max (- R) (min R (f w))) \<in> borel_measurable N"
    using m by measurable
  show "\<And>w. \<bar>max (- R) (min R (f w))\<bar> \<le> \<bar>R\<bar>" by auto
qed

lemma tail_indicator_measurable:
  fixes f :: "'a \<Rightarrow> real"
  assumes m: "f \<in> borel_measurable N"
  shows "(\<lambda>w. \<bar>f w\<bar> * indicat_real {z. R < \<bar>z\<bar>} (f w)) \<in> borel_measurable N"
proof -
  have os: "open {z::real. R < \<bar>z\<bar>}"
    by (intro open_Collect_less continuous_intros)
  have "{z::real. R < \<bar>z\<bar>} \<in> sets borel" by (rule borel_open[OF os])
  note this[measurable] m[measurable]
  show ?thesis by measurable
qed

lemma tail_integrable:
  fixes f :: "'a \<Rightarrow> real"
  assumes int: "integrable N f"
  shows "integrable N (\<lambda>w. \<bar>f w\<bar> * indicat_real {z. R < \<bar>z\<bar>} (f w))"
proof (rule Bochner_Integration.integrable_bound
    [OF Bochner_Integration.integrable_abs[OF int]])
  show "(\<lambda>w. \<bar>f w\<bar> * indicat_real {z. R < \<bar>z\<bar>} (f w)) \<in> borel_measurable N"
    by (rule tail_indicator_measurable[OF borel_measurable_integrable[OF int]])
  show "AE w in N. norm (\<bar>f w\<bar> * indicat_real {z. R < \<bar>z\<bar>} (f w)) \<le> norm \<bar>f w\<bar>"
    by (intro AE_I2) (auto simp: indicator_def)
qed

lemma ennreal_Sup_image:
  fixes S :: "real set" and B :: real
  assumes ne: "S \<noteq> {}" and bnd: "\<And>s. s \<in> S \<Longrightarrow> 0 \<le> s \<and> s \<le> B"
  shows "Sup (ennreal ` S) = ennreal (Sup S)"
proof -
  have bdd: "bdd_above S" using bnd by (intro bdd_aboveI[of _ B]) auto
  have le1: "Sup (ennreal ` S) \<le> ennreal (Sup S)"
  proof (rule Sup_least)
    fix e assume "e \<in> ennreal ` S"
    then obtain s where s: "s \<in> S" and e: "e = ennreal s" by blast
    have "s \<le> Sup S" using s bdd by (rule cSup_upper)
    then show "e \<le> ennreal (Sup S)" unfolding e by (rule ennreal_leI)
  qed
  have leB: "Sup (ennreal ` S) \<le> ennreal B"
    by (rule Sup_least) (use bnd in \<open>auto intro: ennreal_leI\<close>)
  have fin: "Sup (ennreal ` S) < \<top>"
    using leB ennreal_less_top by (rule order_le_less_trans)
  have "Sup S \<le> enn2real (Sup (ennreal ` S))"
  proof (rule cSup_least[OF ne])
    fix s assume s: "s \<in> S"
    have "ennreal s \<le> Sup (ennreal ` S)" using s by (intro Sup_upper) auto
    also have "\<dots> = ennreal (enn2real (Sup (ennreal ` S)))"
      using fin by simp
    finally show "s \<le> enn2real (Sup (ennreal ` S))" by simp
  qed
  then have "ennreal (Sup S) \<le> ennreal (enn2real (Sup (ennreal ` S)))"
    by (rule ennreal_leI)
  then have le2: "ennreal (Sup S) \<le> Sup (ennreal ` S)"
    using fin by simp
  from le1 le2 show ?thesis by simp
qed

lemma ennreal_min_eq: "ennreal (min a b) = min (ennreal a) (ennreal b)"
proof (cases "a \<le> b")
  case True
  then have "ennreal a \<le> ennreal b" by (rule ennreal_leI)
  with True show ?thesis by (simp add: min_def)
next
  case False
  then have "ennreal b \<le> ennreal a" by (simp add: ennreal_leI)
  with False show ?thesis by (simp add: min_def)
qed

text \<open>This section builds the ingredients for the conditioning statement
  isolated in \<open>d\<close>: the exit time splits at
  \<open>r\<close> on the survival event, and the rebased future the rebased future is a measurable
  map of path spaces.\<close>

lemma cInf_shift_real:
  fixes S :: "real set"
  assumes ne: "S \<noteq> {}" and bdd: "bdd_below S"
  shows "Inf ((\<lambda>s. r + s) ` S) = r + Inf S"
proof -
  obtain m where m: "\<And>s. s \<in> S \<Longrightarrow> m \<le> s" using bdd by (auto simp: bdd_below_def)
  have neI: "(\<lambda>s. r + s) ` S \<noteq> {}" using ne by blast
  have bddI: "bdd_below ((\<lambda>s. r + s) ` S)"
    by (rule bdd_belowI[of _ "r + m"]) (use m in auto)
  show ?thesis
  proof (rule antisym)
    have "Inf ((\<lambda>s. r + s) ` S) - r \<le> s" if s: "s \<in> S" for s
    proof -
      have "Inf ((\<lambda>s. r + s) ` S) \<le> r + s"
        using s by (intro cInf_lower[OF _ bddI]) blast
      then show ?thesis by simp
    qed
    then have "Inf ((\<lambda>s. r + s) ` S) - r \<le> Inf S" by (intro cInf_greatest[OF ne])
    then show "Inf ((\<lambda>s. r + s) ` S) \<le> r + Inf S" by simp
    show "r + Inf S \<le> Inf ((\<lambda>s. r + s) ` S)"
    proof (rule cInf_greatest[OF neI])
      fix z assume "z \<in> (\<lambda>s. r + s) ` S"
      then obtain s where s: "s \<in> S" "z = r + s" by blast
      then show "r + Inf S \<le> z" using cInf_lower[OF s(1) bdd] by simp
    qed
  qed
qed

text \<open>The two ingredients \<open>e\<close> needs on
  the way to clause (iv): a product is integrable as soon as both squares
  are, and the cross term of \<open>d\<close> is a
  matrix martingale, entry by entry.\<close>

lemma integrable_mult_of_sq:
  fixes f g :: "'a \<Rightarrow> real"
  assumes fm: "f \<in> borel_measurable M" and gm: "g \<in> borel_measurable M"
    and f2: "integrable M (\<lambda>\<omega>. (f \<omega>)\<^sup>2)" and g2: "integrable M (\<lambda>\<omega>. (g \<omega>)\<^sup>2)"
  shows "integrable M (\<lambda>\<omega>. f \<omega> * g \<omega>)"
proof -
  have b: "integrable M (\<lambda>\<omega>. ((f \<omega>)\<^sup>2 + (g \<omega>)\<^sup>2) / 2)" using f2 g2 by simp
  have pm: "(\<lambda>\<omega>. f \<omega> * g \<omega>) \<in> borel_measurable M" using fm gm by simp
  have ae: "AE \<omega> in M. norm (f \<omega> * g \<omega>) \<le> norm (((f \<omega>)\<^sup>2 + (g \<omega>)\<^sup>2) / 2)"
  proof (rule AE_I2)
    fix \<omega>
    have "(0::real) \<le> (\<bar>f \<omega>\<bar> - \<bar>g \<omega>\<bar>)\<^sup>2" by simp
    also have "(\<bar>f \<omega>\<bar> - \<bar>g \<omega>\<bar>)\<^sup>2 = (f \<omega>)\<^sup>2 - 2 * (\<bar>f \<omega>\<bar> * \<bar>g \<omega>\<bar>) + (g \<omega>)\<^sup>2"
      by (simp add: power2_diff)
    finally have le: "2 * (\<bar>f \<omega>\<bar> * \<bar>g \<omega>\<bar>) \<le> (f \<omega>)\<^sup>2 + (g \<omega>)\<^sup>2" by simp
    have nn: "(0::real) \<le> ((f \<omega>)\<^sup>2 + (g \<omega>)\<^sup>2) / 2" by simp
    show "norm (f \<omega> * g \<omega>) \<le> norm (((f \<omega>)\<^sup>2 + (g \<omega>)\<^sup>2) / 2)"
      using le nn by (simp add: abs_mult)
  qed
  show ?thesis by (rule Bochner_Integration.integrable_bound[OF b pm ae])
qed

text \<open>Two tiny facts used throughout the localisation: multiplying by a real
  constant passes through integrability and the integral.\<close>

lemma integrable_cmult:
  fixes g :: "'a \<Rightarrow> real"
  assumes g: "integrable N g"
  shows "integrable N (\<lambda>\<omega>. c * g \<omega>)"
proof -
  have bl: "bounded_linear (\<lambda>r :: real. c * r)"
    unfolding linear_conv_bounded_linear[symmetric]
    by (intro linearI) (auto simp: algebra_simps)
  show ?thesis by (rule integrable_bounded_linear[OF bl g])
qed

lemma integral_cmult:
  fixes g :: "'a \<Rightarrow> real"
  assumes g: "integrable N g"
  shows "(\<integral>\<omega>. c * g \<omega> \<partial>N) = c * (\<integral>\<omega>. g \<omega> \<partial>N)"
proof -
  have bl: "bounded_linear (\<lambda>r :: real. c * r)"
    unfolding linear_conv_bounded_linear[symmetric]
    by (intro linearI) (auto simp: algebra_simps)
  show ?thesis by (rule integral_of_bounded_linear[OF bl g])
qed

lemma integral_pos_of_AE_pos:
  fixes f :: "'a \<Rightarrow> real"
  assumes PP: "prob_space N" and im: "integrable N f"
    and pos: "AE \<omega> in N. 0 < f \<omega>"
  shows "0 < (\<integral>\<omega>. f \<omega> \<partial>N)"
proof -
  interpret prob_space N by (rule PP)
  have fm: "f \<in> borel_measurable N" by (rule borel_measurable_integrable[OF im])
  define A where "A n = {\<omega> \<in> space N. 1 / real (Suc n) < f \<omega>}" for n
  have Am: "A n \<in> sets N" for n
    unfolding A_def using fm by measurable
  have un: "(\<Union>n. A n) = {\<omega> \<in> space N. 0 < f \<omega>}"
  proof (rule set_eqI)
    fix \<omega>
    show "\<omega> \<in> (\<Union>n. A n) \<longleftrightarrow> \<omega> \<in> {\<omega> \<in> space N. 0 < f \<omega>}"
    proof
      assume "\<omega> \<in> (\<Union>n. A n)"
      then obtain n where an: "\<omega> \<in> A n" by blast
      have h1: "\<omega> \<in> space N" and h2: "1 / real (Suc n) < f \<omega>"
        using an unfolding A_def by auto
      have p0: "0 < 1 / real (Suc n)" by simp
      have "0 < f \<omega>" by (rule less_trans[OF p0 h2])
      with h1 show "\<omega> \<in> {\<omega> \<in> space N. 0 < f \<omega>}" by simp
    next
      assume "\<omega> \<in> {\<omega> \<in> space N. 0 < f \<omega>}"
      then obtain n where "inverse (real (Suc n)) < f \<omega>"
        using reals_Archimedean[of "f \<omega>"] by auto
      then show "\<omega> \<in> (\<Union>n. A n)"
        using \<open>\<omega> \<in> {\<omega> \<in> space N. 0 < f \<omega>}\<close>
        unfolding A_def by (auto simp: inverse_eq_divide)
    qed
  qed
  have Um: "{\<omega> \<in> space N. 0 < f \<omega>} \<in> sets N" using fm by measurable
  have inA: "AE \<omega> in N. \<omega> \<in> {\<omega> \<in> space N. 0 < f \<omega>}"
    using pos AE_space by eventually_elim simp
  have p1: "prob {\<omega> \<in> space N. 0 < f \<omega>} = 1"
    using AE_in_set_eq_1[OF Um] inA by simp
  have ex: "\<exists>n. 0 < prob (A n)"
  proof (rule ccontr)
    assume "\<not> (\<exists>n. 0 < prob (A n))"
    then have z: "\<And>n. prob (A n) = 0"
      using measure_nonneg[of N] by (metis order.antisym not_le)
    have null: "A n \<in> null_sets N" for n
      using z Am by (intro null_setsI) (simp add: emeasure_eq_measure)
    have "(\<Union>n. A n) \<in> null_sets N" by (rule null_sets_UN) (rule null)
    then have "prob (\<Union>n. A n) = 0"
      by (simp add: measure_eq_0_null_sets)
    with p1 un show False by simp
  qed
  then obtain n where pn: "0 < prob (A n)" by blast
  have iind: "integrable N (\<lambda>\<omega>. indicat_real (A n) \<omega> * (1 / real (Suc n)))"
  proof -
    have "integrable N (indicat_real (A n))"
      by (rule integrable_real_indicator[OF Am]) (simp add: emeasure_eq_measure)
    then have "integrable N (\<lambda>\<omega>. (1 / real (Suc n)) * indicat_real (A n) \<omega>)"
      by (rule integrable_cmult)
    then show ?thesis by (simp add: ac_simps)
  qed
  have lb: "(\<integral>\<omega>. indicat_real (A n) \<omega> * (1 / real (Suc n)) \<partial>N)
      \<le> (\<integral>\<omega>. f \<omega> \<partial>N)"
  proof (rule integral_mono_AE[OF iind im])
    show "AE \<omega> in N. indicat_real (A n) \<omega> * (1 / real (Suc n)) \<le> f \<omega>"
      using pos
    proof (rule eventually_mono)
      fix \<omega> assume f0: "0 < f \<omega>"
      show "indicat_real (A n) \<omega> * (1 / real (Suc n)) \<le> f \<omega>"
      proof (cases "\<omega> \<in> A n")
        case True
        then have "1 / real (Suc n) < f \<omega>" unfolding A_def by simp
        with True show ?thesis by (simp add: indicator_def)
      next
        case False
        then show ?thesis using f0 by (simp add: indicator_def)
      qed
    qed
  qed
  have ind_int: "(\<integral>\<omega>. indicat_real (A n) \<omega> * (1 / real (Suc n)) \<partial>N)
      = prob (A n) * (1 / real (Suc n))"
  proof -
    have "(\<integral>\<omega>. indicat_real (A n) \<omega> * (1 / real (Suc n)) \<partial>N)
        = (1 / real (Suc n)) * (\<integral>\<omega>. indicat_real (A n) \<omega> \<partial>N)"
      using integral_cmult[of N "indicat_real (A n)" "1 / real (Suc n)"]
        integrable_real_indicator[OF Am]
      by (simp add: ac_simps emeasure_eq_measure)
    also have "(\<integral>\<omega>. indicat_real (A n) \<omega> \<partial>N) = prob (A n)"
      using Am by simp
    finally show ?thesis by (simp add: ac_simps)
  qed
  have "0 < prob (A n) * (1 / real (Suc n))" using pn by simp
  with lb ind_int show ?thesis by simp
qed

(*<*)
end
(*>*)
