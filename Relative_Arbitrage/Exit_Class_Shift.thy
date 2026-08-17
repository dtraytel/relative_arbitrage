section \<open>Shift equivariance, and upper semicontinuity of the value function\<close>

(*<*)
theory Exit_Class_Shift
  imports Exit_Class_Tightness
    "Continuous_Time_Martingales.Integrability_Criteria"
begin

(*>*)

section \<open>The shift structure of the class (Larsson--Ruf Prop. 2.2(ii))\<close>

text \<open>Every member started at \<open>x\<close> is the \<open>x\<close>-translate of a member started
  at \<open>0\<close>.  This turns the value function into a supremum over a fixed
  family, the shape Berge's theorem needs.  The translation must
  \<open>restrict\<close>, because points of the capped path space are extensional on
  \<open>{0..T}\<close>.\<close>

definition pshift :: "real \<Rightarrow> real^'n::finite \<Rightarrow> 'n pairpath \<Rightarrow> 'n pairpath"
  where "pshift T x \<omega> = restrict (\<lambda>t. (x + fst (\<omega> t), snd (\<omega> t))) {0..T}"

lemma pshift_apply: "t \<in> {0..T} \<Longrightarrow> pshift T x \<omega> t = (x + fst (\<omega> t), snd (\<omega> t))"
  by (simp add: pshift_def)

lemma pshift_fst: "t \<in> {0..T} \<Longrightarrow> fst (pshift T x \<omega> t) = x + fst (\<omega> t)"
  by (simp add: pshift_def)

lemma pshift_snd: "t \<in> {0..T} \<Longrightarrow> snd (pshift T x \<omega> t) = snd (\<omega> t)"
  by (simp add: pshift_def)

lemma pshift_outside: "t \<notin> {0..T} \<Longrightarrow> pshift T x \<omega> t = undefined"
  by (auto simp: pshift_def)

lemma mspace_path_restrict_self:
  fixes \<omega> :: "real \<Rightarrow> 'b::polish_space"
  assumes w: "\<omega> \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric)"
  shows "restrict \<omega> {0..T} = \<omega>"
proof -
  \<comment> \<open>unfolding \<open>path_metric_def\<close> INSIDE a simp call does not terminate here;
      the extensionality has to be extracted by hand.\<close>
  have "\<omega> \<in> mspace (cfunspace (top_of_set {0..T}) (euclidean_metric :: 'b metric))"
    using w unfolding path_metric_def .
  then have "\<omega> \<in> extensional (topspace (top_of_set ({0..T} :: real set)))"
    unfolding mspace_cfunspace by blast
  then have e: "\<omega> \<in> extensional {0..T}" by simp
  show ?thesis
  proof (rule ext)
    fix t :: real
    show "restrict \<omega> {0..T} t = \<omega> t"
    proof (cases "t \<in> {0..T}")
      case True then show ?thesis by simp
    next
      case False
      then have "\<omega> t = undefined" using extensional_arb[OF e] by simp
      with False show ?thesis by simp
    qed
  qed
qed

lemma pshift_in_mspace:
  fixes \<omega> :: "'n::finite pairpath"
  assumes w: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
  shows "pshift T x \<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
proof -
  have c: "continuous_on {0..T} \<omega>" by (rule mspace_path_metricD[OF w])
  have "continuous_on {0..T} (\<lambda>t. (x + fst (\<omega> t), snd (\<omega> t)))"
    by (intro continuous_intros c)
  then show ?thesis unfolding pshift_def by (rule mspace_path_metricI)
qed

lemma pshift_zero:
  fixes \<omega> :: "'n::finite pairpath"
  assumes w: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
  shows "pshift T 0 \<omega> = \<omega>"
proof -
  have "pshift T 0 \<omega> = restrict \<omega> {0..T}"
    unfolding pshift_def by simp
  also have "\<dots> = \<omega>" by (rule mspace_path_restrict_self[OF w])
  finally show ?thesis .
qed

lemma pshift_pshift:
  fixes \<omega> :: "'n::finite pairpath"
  shows "pshift T y (pshift T x \<omega>) = pshift T (y + x) \<omega>"
  by (rule ext) (simp add: pshift_def add.assoc)

lemma pshift_inverse:
  fixes \<omega> :: "'n::finite pairpath"
  assumes w: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
  shows "pshift T (- x) (pshift T x \<omega>) = \<omega>"
  using pshift_pshift[of T "- x" x \<omega>] pshift_zero[OF w] by simp

lemma Lipschitz_pshift:
  fixes x :: "real^'n::finite"
  assumes T: "0 \<le> T"
  shows "Lipschitz_continuous_map (path_metric T :: ('n pairpath) metric)
      (path_metric T :: ('n pairpath) metric) (pshift T x)"
  unfolding Lipschitz_continuous_map_def
proof (intro conjI)
  show "pshift T x \<in> mspace (path_metric T :: ('n pairpath) metric)
      \<rightarrow> mspace (path_metric T :: ('n pairpath) metric)"
    by (intro funcsetI pshift_in_mspace)
  have key: "mdist (path_metric T) (pshift T x f) (pshift T x g)
      \<le> 1 * mdist (path_metric T) f g"
    if f: "f \<in> mspace (path_metric T :: ('n pairpath) metric)"
      and g: "g \<in> mspace (path_metric T :: ('n pairpath) metric)" for f g
  proof -
    have sf: "pshift T x f \<in> mspace (path_metric T :: ('n pairpath) metric)"
      by (rule pshift_in_mspace[OF f])
    have sg: "pshift T x g \<in> mspace (path_metric T :: ('n pairpath) metric)"
      by (rule pshift_in_mspace[OF g])
    have pw: "\<forall>t\<in>{0..T}. dist (f t) (g t) \<le> mdist (path_metric T) f g"
      using path_mdist_le_iff_all[OF T f g] by blast
    have pws: "dist (pshift T x f t) (pshift T x g t)
        \<le> mdist (path_metric T) f g" if t: "t \<in> {0..T}" for t
    proof -
      have "dist (pshift T x f t) (pshift T x g t)
          = dist (x + fst (f t), snd (f t)) (x + fst (g t), snd (g t))"
        using t by (simp add: pshift_def)
      also have "\<dots> = dist (f t) (g t)"
        by (simp add: dist_prod_def dist_norm)
      finally show ?thesis using bspec[OF pw t] by simp
    qed
    have "mdist (path_metric T) (pshift T x f) (pshift T x g)
        \<le> mdist (path_metric T) f g"
      using path_mdist_le_iff_all[OF T sf sg] pws by blast
    then show ?thesis by simp
  qed
  show "\<exists>B. \<forall>f\<in>mspace (path_metric T :: ('n pairpath) metric).
      \<forall>g\<in>mspace (path_metric T :: ('n pairpath) metric).
        mdist (path_metric T) (pshift T x f) (pshift T x g)
          \<le> B * mdist (path_metric T) f g"
    by (intro exI[of _ 1] ballI key)
qed

lemma pshift_measurable:
  fixes x :: "real^'n::finite"
  assumes T: "0 \<le> T"
  shows "pshift T x
      \<in> borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))
        \<rightarrow>\<^sub>M borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  by (intro continuous_map_measurable Lipschitz_continuous_imp_continuous_map
      Lipschitz_pshift[OF T])

text \<open>The shift is measurable for the natural filtration too, at every
  level: it changes values, not times.  This is what lets the martingale
  clauses be transported --- the past of the shifted path is the shifted
  past.\<close>

lemma pshift_filtration_measurable:
  fixes Q :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes setsQ: "sets Q = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
  shows "pshift T x \<in> natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v) u
      \<rightarrow>\<^sub>M natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v) u"
proof -
  let ?F = "natural_filtration Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) u"
  have spQ: "space Q = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsQ])
  have spF: "space ?F = space Q" by simp
  show ?thesis
  proof (rule measurable_sigma_sets[OF sets_natural_filtration])
    show "(\<Union>i\<in>{0..u}. {(\<lambda>\<omega> :: 'n pairpath. \<omega> i) -` A \<inter> space Q | A. A \<in> sets borel})
        \<subseteq> Pow (space Q)"
      by auto
    show "pshift T x \<in> space ?F \<rightarrow> space Q"
      using spQ spF by (auto intro: pshift_in_mspace)
    fix y
    assume "y \<in> (\<Union>i\<in>{0..u}.
        {(\<lambda>\<omega> :: 'n pairpath. \<omega> i) -` A \<inter> space Q | A. A \<in> sets borel})"
    then obtain i A where i: "i \<in> {0..u}" and A: "A \<in> sets borel"
      and y: "y = (\<lambda>\<omega> :: 'n pairpath. \<omega> i) -` A \<inter> space Q" by blast
    have shim: "pshift T x \<omega> \<in> space Q" if "\<omega> \<in> space Q" for \<omega>
      using that spQ by (simp add: pshift_in_mspace)
    show "pshift T x -` y \<inter> space ?F \<in> sets ?F"
    proof (cases "i \<in> {0..T}")
      case True
      define g where "g = (\<lambda>p :: (real^'n) \<times> (real^'n^'n). (x + fst p, snd p))"
      have gb: "g \<in> borel_measurable borel"
        unfolding g_def
        by (intro borel_measurable_continuous_onI continuous_intros)
      have gA: "g -` A \<in> sets borel"
        using measurable_sets[OF gb A] by simp
      have "pshift T x -` y \<inter> space ?F
          = (\<lambda>\<omega> :: 'n pairpath. \<omega> i) -` (g -` A) \<inter> space Q"
        using True y spF shim by (auto simp: pshift_apply g_def)
      moreover have "(\<lambda>\<omega> :: 'n pairpath. \<omega> i) -` (g -` A) \<inter> space Q \<in> sets ?F"
        unfolding sets_natural_filtration
        by (rule sigma_sets.Basic)
          (use i gA in \<open>auto intro!: bexI[of _ i] exI[of _ "g -` A"]\<close>)
      ultimately show ?thesis by simp
    next
      case False
      show ?thesis
      proof (cases "undefined \<in> A")
        case inA: True
        have "pshift T x -` y \<inter> space ?F = space ?F"
        proof
          show "pshift T x -` y \<inter> space ?F \<subseteq> space ?F" by blast
          show "space ?F \<subseteq> pshift T x -` y \<inter> space ?F"
          proof
            fix \<omega> :: "'n pairpath" assume w: "\<omega> \<in> space ?F"
            then have wq: "\<omega> \<in> space Q" using spF by simp
            have "pshift T x \<omega> i = undefined"
              by (rule pshift_outside[OF False])
            then show "\<omega> \<in> pshift T x -` y \<inter> space ?F"
              using inA w shim[OF wq] spF y by auto
          qed
        qed
        then show ?thesis using sets.top[of ?F] by simp
      next
        case notinA: False
        have "pshift T x -` y \<inter> space ?F = {}"
        proof (rule ccontr)
          assume "pshift T x -` y \<inter> space ?F \<noteq> {}"
          then obtain \<omega> :: "'n pairpath" where "pshift T x \<omega> \<in> y" by blast
          then have "pshift T x \<omega> i \<in> A" using y by blast
          moreover have "pshift T x \<omega> i = undefined"
            by (rule pshift_outside[OF False])
          ultimately show False using notinA by simp
        qed
        then show ?thesis by simp
      qed
    qed
  qed
qed

subsection \<open>The shifted law\<close>

definition pshift_law ::
  "real \<Rightarrow> real^'n::finite \<Rightarrow> ('n pairpath) measure \<Rightarrow> ('n pairpath) measure"
  where "pshift_law T x Q = distr Q
     (borel_of (mtopology_of (path_metric T :: ('n pairpath) metric)))
     (pshift T x)"

lemma sets_pshift_law[simp]:
  "sets (pshift_law T x Q)
     = sets (borel_of (mtopology_of (path_metric T :: ('n::finite pairpath) metric)))"
  unfolding pshift_law_def by simp

lemma space_pshift_law:
  "space (pshift_law T x Q)
     = mspace (path_metric T :: ('n::finite pairpath) metric)"
  unfolding pshift_law_def by (simp add: space_borel_of)

lemma prob_space_pshift_law:
  fixes Q :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T: "0 \<le> T" and prob: "prob_space Q"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "prob_space (pshift_law T x Q)"
proof -
  interpret P: prob_space Q by (rule prob)
  have m: "pshift T x \<in> Q \<rightarrow>\<^sub>M borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric))"
    using pshift_measurable[OF T] measurable_cong_sets[OF setsQ refl] by blast
  show ?thesis unfolding pshift_law_def by (rule P.prob_space_distr[OF m])
qed

lemma natural_filtration_pshift_law:
  fixes Q :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes setsQ: "sets Q = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
  shows "natural_filtration (pshift_law T x Q) 0 (\<lambda>v \<omega>. \<omega> v)
       = natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v)"
  unfolding natural_filtration_def
  using space_of_path_sets[OF setsQ] space_pshift_law[of T x Q] by simp

text \<open>The martingale property transports.  Everything is arranged so that
  the filtration does not move (\<open>natural_filtration_pshift_law\<close>): only the
  measure and the process change, and they change by the same shift, so
  the set-integral identity is the one \<open>Q\<close> already satisfies over the
  shifted event.\<close>

lemma martingale_pshift_law:
  fixes Q :: "('n::finite pairpath) measure" and x :: "real^'n"
    and Z :: "real \<Rightarrow> 'n pairpath \<Rightarrow> 'b::{banach,second_countable_topology}"
  assumes T: "0 \<le> T" and prob: "prob_space Q"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Zm: "\<And>u. 0 \<le> u \<Longrightarrow>
        Z u \<in> borel_measurable (natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v) u)"
    and mg: "martingale Q (natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v)) 0
        (\<lambda>u \<omega>. Z u (pshift T x \<omega>))"
  shows "martingale (pshift_law T x Q)
      (natural_filtration (pshift_law T x Q) 0 (\<lambda>v \<omega>. \<omega> v)) 0 Z"
proof -
  let ?Q' = "pshift_law T x Q"
  let ?F = "natural_filtration Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  interpret MG: martingale Q ?F 0 "\<lambda>u \<omega>. Z u (pshift T x \<omega>)" by (rule mg)
  have FF: "natural_filtration ?Q' 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) = ?F"
    by (rule natural_filtration_pshift_law[OF setsQ])
  have spQ: "space Q = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsQ])
  have spQ': "space ?Q' = space Q" using spQ by (simp add: space_pshift_law)
  have setsQ': "sets ?Q' = sets ?B" by simp
  have prob': "prob_space ?Q'" by (rule prob_space_pshift_law[OF T prob setsQ])
  have fin': "finite_measure ?Q'" using prob' by (simp add: prob_space_def)
  have shm: "pshift T x \<in> Q \<rightarrow>\<^sub>M ?B"
    using pshift_measurable[OF T] measurable_cong_sets[OF setsQ refl] by blast
  have SP: "Stochastic_Process.stochastic_process ?Q' (0::real)
      (\<lambda>u \<omega> :: 'n pairpath. \<omega> u)"
    by unfold_locales (rule pair_law_eval_measurable[OF sets_pshift_law])
  interpret SF: finite_filtered_measure ?Q' ?F 0
    using Stochastic_Process.stochastic_process.finite_filtered_measure_natural_filtration
      [OF SP fin'] unfolding FF .
  have ZB: "Z w \<in> borel_measurable ?B" if w: "0 \<le> w" for w
  proof -
    have "Z w \<in> borel_measurable ?Q'"
      by (rule measurable_from_subalg[OF SF.subalgebras[OF w] Zm[OF w]])
    then show ?thesis using measurable_cong_sets[OF setsQ' refl] by blast
  qed
  show ?thesis
    unfolding FF
  proof (rule SF.martingale_of_set_integral_eq)
    show "adapted_process ?Q' ?F 0 Z"
    proof (unfold_locales)
      fix u :: real assume u: "0 \<le> u"
      show "Z u \<in> borel_measurable (?F u)" by (rule Zm[OF u])
    qed
    show "integrable ?Q' (Z u)" if u: "0 \<le> u" for u
    proof -
      have "integrable ?Q' (Z u) \<longleftrightarrow> integrable Q (\<lambda>\<omega>. Z u (pshift T x \<omega>))"
        unfolding pshift_law_def by (rule integrable_distr_eq[OF shm ZB[OF u]])
      then show ?thesis using MG.integrable[OF u] by simp
    qed
    fix A and u v :: real
    assume A: "A \<in> ?F u" and uv: "0 \<le> u" "u \<le> v"
    have v0: "0 \<le> v" using uv by simp
    have AB: "A \<in> sets ?B"
      using A SF.subalgebras[OF uv(1)] setsQ' by (auto simp: subalgebra_def)
    have pA: "pshift T x -` A \<inter> space Q \<in> ?F u"
      using measurable_sets[OF pshift_filtration_measurable[OF setsQ] A] by simp
    have key: "set_lebesgue_integral ?Q' A (Z w)
        = set_lebesgue_integral Q (pshift T x -` A \<inter> space Q)
            (\<lambda>\<omega>. Z w (pshift T x \<omega>))" if w: "0 \<le> w" for w
    proof -
      have gb: "(\<lambda>\<omega> :: 'n pairpath. indicat_real A \<omega> *\<^sub>R Z w \<omega>)
          \<in> borel_measurable ?B"
        using AB ZB[OF w] by measurable
      have "set_lebesgue_integral ?Q' A (Z w)
          = (\<integral>\<omega>. indicat_real A \<omega> *\<^sub>R Z w \<omega> \<partial>?Q')"
        unfolding set_lebesgue_integral_def ..
      also have "\<dots> = (\<integral>\<omega>. indicat_real A (pshift T x \<omega>)
              *\<^sub>R Z w (pshift T x \<omega>) \<partial>Q)"
        unfolding pshift_law_def by (rule integral_distr[OF shm gb])
      also have "\<dots> = (\<integral>\<omega>. indicat_real (pshift T x -` A \<inter> space Q) \<omega>
              *\<^sub>R Z w (pshift T x \<omega>) \<partial>Q)"
        by (rule Bochner_Integration.integral_cong) (auto simp: indicator_def)
      finally show ?thesis unfolding set_lebesgue_integral_def .
    qed
    show "set_lebesgue_integral ?Q' A (Z u) = set_lebesgue_integral ?Q' A (Z v)"
      unfolding key[OF uv(1)] key[OF v0]
      by (rule MG.set_integral_eq[OF pA uv(1) uv(2)])
  qed
qed

text \<open>\<open>martingale_add\<close>, \<open>martingale_add_const\<close> and \<open>martingale_cong_ge\<close>
  live in @{theory Continuous_Time_Martingales.Martingale_Algebra}.\<close>

subsection \<open>Almost-sure statements transport through the shift\<close>

text \<open>The shift is a bijection of the path space with measurable inverse,
  so a null set for \<open>Q\<close> has a null image --- which is what lets the two
  almost-sure clauses of (1.7) be transported without any measurability
  hypothesis on the property itself.\<close>

lemma AE_pshift_law:
  fixes Q :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T: "0 \<le> T"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and ae: "AE \<omega> in Q. P (pshift T x \<omega>)"
  shows "AE \<omega> in pshift_law T x Q. P \<omega>"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have spQ: "space Q = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsQ])
  have spQ': "space (pshift_law T x Q) = space Q"
    using spQ by (simp add: space_pshift_law)
  have shm: "pshift T x \<in> Q \<rightarrow>\<^sub>M ?B"
    using pshift_measurable[OF T] measurable_cong_sets[OF setsQ refl] by blast
  have shmQ: "pshift T (- x) \<in> Q \<rightarrow>\<^sub>M Q"
    using pshift_measurable[OF T] measurable_cong_sets[OF setsQ setsQ] by blast
  obtain N1 where N1: "{\<omega> \<in> space Q. \<not> P (pshift T x \<omega>)} \<subseteq> N1"
    and N1z: "emeasure Q N1 = 0" and N1s: "N1 \<in> sets Q"
    by (rule AE_E[OF ae])
  define B where "B = pshift T (- x) -` N1 \<inter> space Q"
  have Bs: "B \<in> sets Q" unfolding B_def by (rule measurable_sets[OF shmQ N1s])
  have pre: "pshift T x -` B \<inter> space Q = N1 \<inter> space Q"
  proof
    show "pshift T x -` B \<inter> space Q \<subseteq> N1 \<inter> space Q"
    proof
      fix \<omega> :: "'n pairpath"
      assume "\<omega> \<in> pshift T x -` B \<inter> space Q"
      then have w: "\<omega> \<in> space Q" and n: "pshift T (- x) (pshift T x \<omega>) \<in> N1"
        unfolding B_def by auto
      have "pshift T (- x) (pshift T x \<omega>) = \<omega>"
        using w spQ by (simp add: pshift_inverse)
      with n w show "\<omega> \<in> N1 \<inter> space Q" by simp
    qed
    show "N1 \<inter> space Q \<subseteq> pshift T x -` B \<inter> space Q"
    proof
      fix \<omega> :: "'n pairpath" assume "\<omega> \<in> N1 \<inter> space Q"
      then have n: "\<omega> \<in> N1" and w: "\<omega> \<in> space Q" by auto
      have e: "pshift T (- x) (pshift T x \<omega>) = \<omega>"
        using w spQ by (simp add: pshift_inverse)
      have "pshift T x \<omega> \<in> space Q" using w spQ by (simp add: pshift_in_mspace)
      then show "\<omega> \<in> pshift T x -` B \<inter> space Q"
        unfolding B_def using n w e by simp
    qed
  qed
  have "emeasure (pshift_law T x Q) B = emeasure Q (pshift T x -` B \<inter> space Q)"
    unfolding pshift_law_def
    by (rule emeasure_distr[OF shm]) (use Bs setsQ in simp)
  also have "\<dots> = emeasure Q (N1 \<inter> space Q)" using pre by simp
  also have "\<dots> = 0"
    using N1z sets.sets_into_space[OF N1s] by (simp add: Int_absorb2)
  finally have Bnull: "emeasure (pshift_law T x Q) B = 0" .
  have sub: "{\<omega> \<in> space (pshift_law T x Q). \<not> P \<omega>} \<subseteq> B"
  proof
    fix \<omega>' :: "'n pairpath"
    assume "\<omega>' \<in> {\<omega> \<in> space (pshift_law T x Q). \<not> P \<omega>}"
    then have w': "\<omega>' \<in> space Q" and nP: "\<not> P \<omega>'" using spQ' by auto
    have wm: "\<omega>' \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using w' spQ by simp
    have e: "pshift T x (pshift T (- x) \<omega>') = \<omega>'"
      using pshift_pshift[of T x "- x" \<omega>'] pshift_zero[OF wm] by simp
    have "pshift T (- x) \<omega>' \<in> space Q"
      using wm spQ by (simp add: pshift_in_mspace)
    then have "pshift T (- x) \<omega>' \<in> N1" using N1 nP e by auto
    then show "\<omega>' \<in> B" unfolding B_def using w' by simp
  qed
  have Bn: "B \<in> null_sets (pshift_law T x Q)"
    using Bs Bnull setsQ by (simp add: null_sets_def)
  show ?thesis
    unfolding eventually_ae_filter using sub Bn by blast
qed

subsection \<open>The class is shift-equivariant\<close>

text \<open>The one algebraic input: translating \<open>X\<close> splits the compensated
  process into itself, a term linear in \<open>X\<close>, and a constant --- so it stays
  a martingale.\<close>

lemma comp_shift_split:
  fixes x v :: "real^'n::finite" and w :: "real^'n^'n"
  shows "outerp x + ((outerp v - w) + (\<chi> i j. x $ i * v $ j + v $ i * x $ j))
       = outerp (x + v) - w"
  by (simp add: outerp_def vec_eq_iff algebra_simps)

text \<open>\<open>bounded_linear_cross\<close> lives in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


theorem exit_class_pshift:
  fixes Q :: "('n::finite pairpath) measure" and x x0 :: "real^'n"
  assumes T: "0 \<le> T" and Q: "Q \<in> exit_class k L T x0"
  shows "pshift_law T x Q \<in> exit_class k L T (x + x0)"
proof -
  let ?F = "natural_filtration Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?cross = "\<lambda>v :: real^'n. (\<chi> i j. x $ i * v $ j + v $ i * x $ j) :: real^'n^'n"
  have prob: "prob_space Q" by (rule exit_class_prob[OF Q])
  have setsQ: "sets Q = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    by (rule exit_class_sets[OF Q])
  have finQ: "finite_measure Q" using prob by (simp add: prob_space_def)
  have SP: "Stochastic_Process.stochastic_process Q (0::real)
      (\<lambda>u \<omega> :: 'n pairpath. \<omega> u)"
    by unfold_locales (rule pair_law_eval_measurable[OF setsQ])
  have ffm: "finite_filtered_measure Q ?F 0"
    by (rule Stochastic_Process.stochastic_process.finite_filtered_measure_natural_filtration
        [OF SP finQ])
  have minI: "min u T \<in> {0..T}" if "0 \<le> u" for u using that T by simp
  have mX: "martingale Q ?F 0 (\<lambda>u \<omega>. fst (\<omega> (min u T)))"
    by (rule exit_class_X_martingale[OF Q])
  interpret MX: martingale Q ?F 0 "\<lambda>u \<omega> :: 'n pairpath. fst (\<omega> (min u T))"
    by (rule mX)
  \<comment> \<open>the two almost-sure clauses\<close>
  have st: "AE \<omega> in Q. fst (\<omega> 0) = x0 \<and> snd (\<omega> 0) = 0"
    using Q unfolding exit_class_def by blast
  have st': "AE \<omega> in pshift_law T x Q. fst (\<omega> 0) = x + x0 \<and> snd (\<omega> 0) = 0"
  proof (rule AE_pshift_law[OF T setsQ])
    show "AE \<omega> in Q. fst (pshift T x \<omega> 0) = x + x0
        \<and> snd (pshift T x \<omega> 0) = 0"
    proof (rule eventually_mono[OF st])
      fix \<omega> :: "'n pairpath"
      assume "fst (\<omega> 0) = x0 \<and> snd (\<omega> 0) = 0"
      then show "fst (pshift T x \<omega> 0) = x + x0 \<and> snd (pshift T x \<omega> 0) = 0"
        using T by (simp add: pshift_fst pshift_snd)
    qed
  qed
  have dq: "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
    using Q unfolding exit_class_def by blast
  have dq': "AE \<omega> in pshift_law T x Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
  proof (rule AE_pshift_law[OF T setsQ])
    show "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (pshift T x \<omega> t) - snd (pshift T x \<omega> s))
          \<in> sconstraint k L"
    proof (rule eventually_mono[OF dq])
      fix \<omega> :: "'n pairpath"
      assume q: "\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
          (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
      show "\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
          (1 / (t - s)) *\<^sub>R (snd (pshift T x \<omega> t) - snd (pshift T x \<omega> s))
            \<in> sconstraint k L"
      proof (intro allI impI)
        fix s t :: real
        assume s: "0 \<le> s" and stt: "s < t" and tT: "t \<le> T"
        have sI: "s \<in> {0..T}" using s stt tT by simp
        have tI: "t \<in> {0..T}" using s stt tT by simp
        show "(1 / (t - s)) *\<^sub>R (snd (pshift T x \<omega> t) - snd (pshift T x \<omega> s))
            \<in> sconstraint k L"
          using q s stt tT by (simp add: pshift_snd[OF sI] pshift_snd[OF tI])
      qed
    qed
  qed
  \<comment> \<open>the two martingale clauses\<close>
  have Zm: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min u T))) \<in> borel_measurable (?F u)"
    if u: "0 \<le> u" for u by (rule MX.adapted[OF u])
  have mgX: "martingale Q ?F 0 (\<lambda>u \<omega>. fst (pshift T x \<omega> (min u T)))"
  proof (rule martingale_cong_ge[OF martingale_add_const[OF ffm mX, of x]])
    fix u :: real assume u: "0 \<le> u"
    show "(\<lambda>\<omega> :: 'n pairpath. x + fst (\<omega> (min u T)))
        = (\<lambda>\<omega>. fst (pshift T x \<omega> (min u T)))"
      by (rule ext) (simp add: pshift_fst[OF minI[OF u]])
  qed
  have Xshift: "martingale (pshift_law T x Q)
      (natural_filtration (pshift_law T x Q) 0 (\<lambda>v \<omega>. \<omega> v)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u T)))"
    by (rule martingale_pshift_law[OF T prob setsQ Zm mgX])
  have mC: "martingale Q ?F 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T)))"
    by (rule exit_class_compensated_martingale[OF Q])
  interpret MC: martingale Q ?F 0
      "\<lambda>u \<omega> :: 'n pairpath. outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T))"
    by (rule mC)
  have mCross: "martingale Q ?F 0 (\<lambda>u \<omega>. ?cross (fst (\<omega> (min u T))))"
    by (rule martingale_bounded_linear_image[OF bounded_linear_cross mX])
  have sum2: "martingale Q ?F 0 (\<lambda>u \<omega>. outerp x
      + ((outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T)))
         + ?cross (fst (\<omega> (min u T)))))"
    by (rule martingale_add_const[OF ffm martingale_add[OF mC mCross]])
  have ZmC: "(\<lambda>\<omega> :: 'n pairpath.
      outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T)))
        \<in> borel_measurable (?F u)"
    if u: "0 \<le> u" for u by (rule MC.adapted[OF u])
  have mgC: "martingale Q ?F 0 (\<lambda>u \<omega>.
      outerp (fst (pshift T x \<omega> (min u T))) - snd (pshift T x \<omega> (min u T)))"
  proof (rule martingale_cong_ge[OF sum2])
    fix u :: real assume u: "0 \<le> u"
    show "(\<lambda>\<omega> :: 'n pairpath. outerp x
        + ((outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T)))
           + ?cross (fst (\<omega> (min u T)))))
        = (\<lambda>\<omega>. outerp (fst (pshift T x \<omega> (min u T)))
           - snd (pshift T x \<omega> (min u T)))"
      by (rule ext)
        (simp add: pshift_fst[OF minI[OF u]] pshift_snd[OF minI[OF u]]
          comp_shift_split)
  qed
  have Cshift: "martingale (pshift_law T x Q)
      (natural_filtration (pshift_law T x Q) 0 (\<lambda>v \<omega>. \<omega> v)) 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T)))"
    by (rule martingale_pshift_law[OF T prob setsQ ZmC mgC])
  show ?thesis
    unfolding exit_class_def
  proof (intro CollectI conjI)
    show "prob_space (pshift_law T x Q)"
      by (rule prob_space_pshift_law[OF T prob setsQ])
    show "sets (pshift_law T x Q) = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))" by simp
    show "AE \<omega> in pshift_law T x Q. fst (\<omega> 0) = x + x0 \<and> snd (\<omega> 0) = 0"
      by (rule st')
    show "AE \<omega> in pshift_law T x Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
      by (rule dq')
    show "martingale (pshift_law T x Q)
        (natural_filtration (pshift_law T x Q) 0 (\<lambda>t \<omega>. \<omega> t)) 0
        (\<lambda>t \<omega>. fst (\<omega> (min t T)))" by (rule Xshift)
    show "martingale (pshift_law T x Q)
        (natural_filtration (pshift_law T x Q) 0 (\<lambda>t \<omega>. \<omega> t)) 0
        (\<lambda>t \<omega>. outerp (fst (\<omega> (min t T))) - snd (\<omega> (min t T)))"
      by (rule Cshift)
  qed
qed

text \<open>Larsson--Ruf Prop. 2.2(ii) for the paper's class, in the form the
  value function needs: the class at \<open>x\<close> is the \<open>x\<close>-translate of the class
  at \<open>0\<close>.  The reverse inclusion is the same theorem at \<open>-x\<close>, plus the fact
  that the two push-forwards compose to the identity.\<close>

corollary exit_class_shift_image:
  fixes x :: "real^'n::finite"
  assumes T: "0 \<le> T"
  shows "exit_class k L T x = pshift_law T x ` exit_class k L T 0"
proof
  show "pshift_law T x ` exit_class k L T 0 \<subseteq> exit_class k L T x"
  proof
    fix R :: "('n pairpath) measure"
    assume "R \<in> pshift_law T x ` exit_class k L T 0"
    then obtain Q0 where Q0: "Q0 \<in> exit_class k L T 0"
      and R: "R = pshift_law T x Q0" by blast
    have "pshift_law T x Q0 \<in> exit_class k L T (x + 0)"
      by (rule exit_class_pshift[OF T Q0])
    then show "R \<in> exit_class k L T x" using R by simp
  qed
  show "exit_class k L T x \<subseteq> pshift_law T x ` exit_class k L T 0"
  proof
    fix Q :: "('n pairpath) measure"
    assume Q: "Q \<in> exit_class k L T x"
    let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
    have setsQ: "sets Q = sets ?B" by (rule exit_class_sets[OF Q])
    have spQ: "space Q = mspace (path_metric T :: ('n pairpath) metric)"
      by (rule space_of_path_sets[OF setsQ])
    have mem0: "pshift_law T (- x) Q \<in> exit_class k L T 0"
      using exit_class_pshift[OF T Q, of "- x"] by simp
    have shm: "pshift T (- x) \<in> Q \<rightarrow>\<^sub>M ?B"
      using pshift_measurable[OF T] measurable_cong_sets[OF setsQ refl] by blast
    have shm2: "pshift T x \<in> ?B \<rightarrow>\<^sub>M ?B" by (rule pshift_measurable[OF T])
    have "pshift_law T x (pshift_law T (- x) Q)
        = distr Q ?B (pshift T x \<circ> pshift T (- x))"
      unfolding pshift_law_def by (rule distr_distr[OF shm2 shm])
    also have "\<dots> = distr Q ?B (\<lambda>\<omega>. \<omega>)"
    proof (rule distr_cong)
      show "Q = Q" ..
      show "sets ?B = sets ?B" ..
      fix \<omega> :: "'n pairpath" assume "\<omega> \<in> space Q"
      then have wm: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
        using spQ by simp
      show "(pshift T x \<circ> pshift T (- x)) \<omega> = \<omega>"
        using pshift_pshift[of T x "- x" \<omega>] pshift_zero[OF wm] by simp
    qed
    also have "\<dots> = Q" by (rule distr_id2[OF setsQ[symmetric]])
    finally have "pshift_law T x (pshift_law T (- x) Q) = Q" .
    with mem0 show "Q \<in> pshift_law T x ` exit_class k L T 0" by force
  qed
qed

section \<open>The value function of Eq. (1.6) is upper semicontinuous\<close>

subsection \<open>The shift is an involution on laws\<close>

lemma pshift_law_compose:
  fixes Q :: "('n::finite pairpath) measure" and x y :: "real^'n"
  assumes T: "0 \<le> T"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "pshift_law T y (pshift_law T x Q) = pshift_law T (y + x) Q"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have shx: "pshift T x \<in> Q \<rightarrow>\<^sub>M ?B"
    using pshift_measurable[OF T] measurable_cong_sets[OF setsQ refl] by blast
  have shy: "pshift T y \<in> ?B \<rightarrow>\<^sub>M ?B" by (rule pshift_measurable[OF T])
  have "pshift_law T y (pshift_law T x Q) = distr Q ?B (pshift T y \<circ> pshift T x)"
    unfolding pshift_law_def by (rule distr_distr[OF shy shx])
  also have "\<dots> = distr Q ?B (pshift T (y + x))"
    by (rule distr_cong) (auto simp: pshift_pshift)
  finally show ?thesis unfolding pshift_law_def .
qed

lemma pshift_law_zero:
  fixes Q :: "('n::finite pairpath) measure"
  assumes setsQ: "sets Q = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
  shows "pshift_law T 0 Q = Q"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have spQ: "space Q = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsQ])
  have "pshift_law T 0 Q = distr Q ?B (\<lambda>\<omega>. \<omega>)"
    unfolding pshift_law_def
    by (rule distr_cong) (use spQ in \<open>auto simp: pshift_zero\<close>)
  also have "\<dots> = Q" by (rule distr_id2[OF setsQ[symmetric]])
  finally show ?thesis .
qed

text \<open>Hence the almost-sure transfer is an equivalence, not just an
  implication: apply it at \<open>-x\<close> to the shifted law.\<close>

lemma AE_pshift_law_iff:
  fixes Q :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T: "0 \<le> T"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "(AE \<omega> in pshift_law T x Q. P \<omega>)
       \<longleftrightarrow> (AE \<omega> in Q. P (pshift T x \<omega>))"
proof
  assume "AE \<omega> in Q. P (pshift T x \<omega>)"
  then show "AE \<omega> in pshift_law T x Q. P \<omega>"
    by (rule AE_pshift_law[OF T setsQ])
next
  let ?Q' = "pshift_law T x Q"
  assume h: "AE \<omega> in ?Q'. P \<omega>"
  have setsQ': "sets ?Q' = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))" by simp
  have spQ': "space ?Q' = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_pshift_law)
  have id': "AE \<omega> in ?Q'. pshift T x (pshift T (- x) \<omega>) = \<omega>"
  proof (rule AE_I2)
    fix \<omega> :: "'n pairpath" assume "\<omega> \<in> space ?Q'"
    then have wm: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using spQ' by simp
    show "pshift T x (pshift T (- x) \<omega>) = \<omega>"
      using pshift_pshift[of T x "- x" \<omega>] pshift_zero[OF wm] by simp
  qed
  have h2: "AE \<omega> in ?Q'. P (pshift T x (pshift T (- x) \<omega>))"
    using h id' by eventually_elim simp
  have step: "AE \<omega> in pshift_law T (- x) ?Q'. P (pshift T x \<omega>)"
    by (rule AE_pshift_law[OF T setsQ' h2])
  \<comment> \<open>the measure INSIDE an \<open>AE\<close> cannot be rewritten by simp; \<open>unfolding\<close>
      acts on the chained fact and does it.\<close>
  have eqQ: "pshift_law T (- x) ?Q' = Q"
    using pshift_law_compose[OF T setsQ, of "- x"] pshift_law_zero[OF setsQ]
    by simp
  show "AE \<omega> in Q. P (pshift T x \<omega>)" using step unfolding eqQ .
qed

lemma ess_inf_time_pshift_law:
  fixes Q :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T: "0 \<le> T"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "ess_inf_time (pshift_law T x Q) g
       = ess_inf_time Q (\<lambda>\<omega>. g (pshift T x \<omega>))"
proof -
  have "{c. AE \<omega> in pshift_law T x Q. c \<le> ennreal (g \<omega>)}
      = {c. AE \<omega> in Q. c \<le> ennreal (g (pshift T x \<omega>))}"
    by (intro Collect_cong) (rule AE_pshift_law_iff[OF T setsQ])
  then show ?thesis unfolding ess_inf_time_def by simp
qed

subsection \<open>The exit functional of (1.6) is the shifted exit time\<close>

text \<open>Both sides are the same infimum: the times range over \<open>{0..T}\<close>, and
  there \<open>fst (pshift T x \<omega> r) = x + fst (\<omega> r) = fst ((x,0) + \<omega> r)\<close>.  No
  path-space membership is needed.\<close>

lemma pexit_pshift_eq_etime:
  fixes \<omega> :: "'n::finite pairpath" and K :: "(real^'n) set" and x :: "real^'n"
  shows "pexit T K (\<lambda>t. fst (pshift T x \<omega> t))
       = etime T {p :: (real^'n) \<times> (real^'n^'n). fst p \<in> - K}
           (\<lambda>s w. (x, 0) + w s) \<omega>"
proof -
  have "{r. 0 \<le> r \<and> r \<le> T \<and> fst (pshift T x \<omega> r) \<in> - K}
      = {r. 0 \<le> r \<and> r \<le> T
            \<and> (x, 0) + \<omega> r \<in> {p :: (real^'n) \<times> (real^'n^'n). fst p \<in> - K}}"
    by (auto simp: pshift_fst)
  then show ?thesis unfolding pexit_def etime_def by simp
qed

subsection \<open>Turning a supremum of \<open>ennreal\<close>s into a supremum of reals\<close>

text \<open>\<open>ennreal_Sup_image\<close> lives in @{theory Continuous_Time_Martingales.Integrability_Criteria}.\<close>


subsection \<open>Eq. (1.6) as a shifted supremum over the class at \<open>0\<close>\<close>

theorem exit_val_eq_vshift_sup:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
  \<comment> \<open>the \<open>0\<close> MUST be annotated: without it the class in the assumption
      elaborates at a fresh type variable and \<open>rule ne\<close> silently fails.\<close>
  assumes T: "0 \<le> T" and ne: "exit_class k L T (0 :: real^'n) \<noteq> {}"
  shows "exit_val k L T K x
      = ennreal (Sup (vshift T {p :: (real^'n) \<times> (real^'n^'n). fst p \<in> - K} (x, 0)
          ` exit_class k L T 0))"
proof -
  let ?A = "{p :: (real^'n) \<times> (real^'n^'n). fst p \<in> - K}"
  let ?C = "exit_class k L T 0"
  let ?g = "\<lambda>\<omega> :: 'n pairpath. pexit T K (\<lambda>t. fst (\<omega> t))"
  have setsQ: "sets Q = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))" if "Q \<in> ?C" for Q
    by (rule exit_class_sets[OF that])
  have probQ: "prob_space Q" if "Q \<in> ?C" for Q :: "('n pairpath) measure"
    by (rule exit_class_prob[OF that])
  have key: "ess_inf_time (pshift_law T x Q) ?g = ennreal (vshift T ?A (x, 0) Q)"
    if Q: "Q \<in> ?C" for Q
  proof -
    have "ess_inf_time (pshift_law T x Q) ?g
        = ess_inf_time Q (\<lambda>\<omega>. ?g (pshift T x \<omega>))"
      by (rule ess_inf_time_pshift_law[OF T setsQ[OF Q]])
    also have "\<dots> = ess_inf_time Q (etime T ?A (\<lambda>s w. (x, 0) + w s))"
      by (rule arg_cong[where f = "ess_inf_time Q"])
        (rule ext, rule pexit_pshift_eq_etime)
    finally have e: "ess_inf_time (pshift_law T x Q) ?g
        = ess_inf_time Q (etime T ?A (\<lambda>s w. (x, 0) + w s))" .
    have le: "ess_inf_time Q (etime T ?A (\<lambda>s w. (x, 0) + w s)) \<le> ennreal T"
      by (rule ess_inf_time_le_const[OF probQ[OF Q]]) (rule etime_le_T[OF T])
    have fin: "ess_inf_time Q (etime T ?A (\<lambda>s w. (x, 0) + w s)) < \<top>"
      using le ennreal_less_top by (rule order_le_less_trans)
    show ?thesis unfolding e vshift_def using fin by simp
  qed
  have img: "exit_class k L T x = pshift_law T x ` ?C"
    by (rule exit_class_shift_image[OF T])
  have "exit_val k L T K x
      = Sup ((\<lambda>Q. ess_inf_time Q ?g) ` (pshift_law T x ` ?C))"
    unfolding exit_val_def img ..
  also have "\<dots> = Sup ((\<lambda>Q. ess_inf_time (pshift_law T x Q) ?g) ` ?C)"
    by (simp add: image_image)
  also have "\<dots> = Sup ((\<lambda>Q. ennreal (vshift T ?A (x, 0) Q)) ` ?C)"
    using key by (intro arg_cong[where f = Sup] image_cong refl)
  also have "\<dots> = Sup (ennreal ` (vshift T ?A (x, 0) ` ?C))"
    by (simp add: image_image)
  also have "\<dots> = ennreal (Sup (vshift T ?A (x, 0) ` ?C))"
  proof (rule ennreal_Sup_image[where B = T])
    show "vshift T ?A (x, 0) ` ?C \<noteq> {}"
      unfolding image_is_empty by (rule ne)
    fix s :: real assume "s \<in> vshift T ?A (x, 0) ` ?C"
    then obtain Q where Q: "Q \<in> ?C" and s: "s = vshift T ?A (x, 0) Q" by blast
    have "0 \<le> s" unfolding s vshift_def by simp
    moreover have "s \<le> T" unfolding s by (rule vshift_le[OF T probQ[OF Q]])
    ultimately show "0 \<le> s \<and> s \<le> T" by blast
  qed
  finally show ?thesis .
qed

subsection \<open>Clause (1) of Theorem 1.1, for the paper's own value function\<close>

text \<open>\<open>exit_val\<close> is Eq. (1.6): the supremum, over the class (1.7) started at
  \<open>x\<close>, of the essential infimum of the exit time from \<open>K\<close>.  Upper
  semicontinuity in \<open>x\<close> is exactly clause (1).  The class is sequentially
  compact and shift-equivariant (Prop. 2.2(ii)), so Berge applies through
  \<open>Exit_Time_Semicontinuity.vshift_sup_usc_of_seq_compact\<close>, whose remaining
  hypothesis, nonemptiness of the class at \<open>0\<close>, is supplied by a separate
  construction.\<close>

theorem exit_val_usc:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n" and b :: ennreal
  assumes T: "0 < T" and L: "0 \<le> L" and K: "closed K"
    and ne: "exit_class k L T (0 :: real^'n) \<noteq> {}"
    and lt: "exit_val k L T K x < b"
  shows "eventually (\<lambda>y. exit_val k L T K y < b) (nhds x)"
proof -
  let ?A = "{p :: (real^'n) \<times> (real^'n^'n). fst p \<in> - K}"
  let ?C = "exit_class k L T (0 :: real^'n)"
  let ?S = "\<lambda>y :: real^'n. Sup (vshift T ?A (y, 0) ` ?C)"
  let ?e = "\<lambda>y :: real^'n. (y, 0 :: real^'n^'n)"
  have T0: "0 \<le> T" using T by simp
  have Aopen: "open ?A"
  proof -
    have e: "?A = (fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n) -` (- K)" by auto
    show ?thesis unfolding e by (rule open_vimage_fst[OF open_Compl[OF K]])
  qed
  have probQ: "prob_space Q" if "Q \<in> ?C" for Q :: "('n pairpath) measure"
    by (rule exit_class_prob[OF that])
  have eqv: "exit_val k L T K y = ennreal (?S y)" for y :: "real^'n"
    by (rule exit_val_eq_vshift_sup[OF T0 ne])
  have bdd: "bdd_above (vshift T ?A (y, 0) ` ?C)" for y :: "real^'n"
    by (rule bdd_aboveI[of _ T]) (auto intro: vshift_le[OF T0] probQ)
  have S0: "0 \<le> ?S y" for y :: "real^'n"
  proof -
    from ne obtain Q0 :: "('n pairpath) measure" where Q0: "Q0 \<in> ?C" by auto
    have "0 \<le> vshift T ?A (y, 0) Q0" unfolding vshift_def by simp
    also have "\<dots> \<le> ?S y" using Q0 bdd by (intro cSup_upper) auto
    finally show ?thesis .
  qed
  have usc: "eventually (\<lambda>z. Sup (vshift T ?A z ` ?C) < c) (nhds (?e x))"
    if c: "?S x < c" for c :: real
  proof (rule vshift_sup_usc_of_seq_compact[OF T0 Aopen])
    show "?C \<noteq> {}" by (rule ne)
    show "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))" if "Q \<in> ?C" for Q
      by (rule exit_class_sets[OF that])
    show "prob_space Q" if "Q \<in> ?C" for Q by (rule probQ[OF that])
    show "\<exists>Lm r. Lm \<in> ?C \<and> strict_mono r \<and> weak_conv_on (\<sigma> \<circ> r) Lm sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
      if "range \<sigma> \<subseteq> ?C" for \<sigma> :: "nat \<Rightarrow> ('n pairpath) measure"
    proof -
      have mem: "\<sigma> m \<in> ?C" for m using that by auto
      have ex: "\<exists>a Q. strict_mono a \<and> Q \<in> ?C \<and> weak_conv_on (\<sigma> \<circ> a) Q sequentially
          (mtopology_of (path_metric T :: ('n pairpath) metric))"
        by (rule exit_class_convergent_subsequence[OF T L mem])
      obtain a where ea: "\<exists>Q. strict_mono a \<and> Q \<in> ?C
          \<and> weak_conv_on (\<sigma> \<circ> a) Q sequentially
              (mtopology_of (path_metric T :: ('n pairpath) metric))"
        using ex by (rule exE)
      obtain Q where h: "strict_mono a \<and> Q \<in> ?C
          \<and> weak_conv_on (\<sigma> \<circ> a) Q sequentially
              (mtopology_of (path_metric T :: ('n pairpath) metric))"
        using ea by (rule exE)
      show ?thesis
        by (rule exI[of _ Q], rule exI[of _ a]) (use h in simp)
    qed
    show "?S x < c" by (rule c)
  qed
  obtain c :: real where cS: "?S x < c" and cb: "ennreal c \<le> b"
  proof (cases "b = \<top>")
    case True
    show thesis by (rule that[of "?S x + 1"]) (simp_all add: True)
  next
    case False
    then have blt: "b < \<top>" by (simp add: less_top)
    have bb: "b = ennreal (enn2real b)" using blt by simp
    have "ennreal (?S x) < b" using lt eqv by simp
    then have "ennreal (?S x) < ennreal (enn2real b)" using bb by simp
    \<comment> \<open>\<open>ennreal_less_iff\<close> carries its nonnegativity on the LEFT argument.\<close>
    then have "?S x < enn2real b"
      using S0[of x] by (simp add: ennreal_less_iff)
    then show thesis by (rule that) (use bb in simp)
  qed
  from usc[OF cS] obtain U where U: "open U" and xU: "?e x \<in> U"
    and UP: "\<And>z. z \<in> U \<Longrightarrow> Sup (vshift T ?A z ` ?C) < c"
    unfolding eventually_nhds by blast
  show ?thesis
    unfolding eventually_nhds
  proof (intro exI[of _ "?e -` U"] conjI ballI)
    show "open (?e -` U)"
      by (rule open_vimage[OF U]) (intro continuous_intros)
    show "x \<in> ?e -` U" using xU by simp
    fix y :: "real^'n" assume y: "y \<in> ?e -` U"
    have "?S y < c" using UP[of "?e y"] y by simp
    then have "ennreal (?S y) < ennreal c"
      using S0[of y] by (simp add: ennreal_less_iff)
    also have "\<dots> \<le> b" by (rule cb)
    finally show "exit_val k L T K y < b" using eqv[of y] by simp
  qed
qed


(*<*)
end
(*>*)
