
(*<*)
theory Semidirect_Kernels
  imports "Martingales.Martingale" "HOL-Probability.Probability"
begin

(*>*)

text \<open>
  The Giry monad's semidirect product \<open>ksemi M N Kr\<close>: run a base measure
  \<open>M\<close>, then continue with the law a kernel \<open>Kr\<close> picks at the point reached.
  Its \<open>sets\<close> agree with the ordinary product \<open>M \<Otimes>\<^sub>M N\<close> (so measurability
  already proved for the product transfers verbatim), it is a probability
  space when \<open>M\<close> is, and its almost-sure and nonnegative, bounded and
  past-bounded integrals disintegrate.  What it does not satisfy is Fubini
  --- the order of integration cannot be swapped.
\<close>

section \<open>The semidirect product\<close>

definition ksemi :: "'a measure \<Rightarrow> 'b measure \<Rightarrow> ('a \<Rightarrow> 'b measure) \<Rightarrow> ('a \<times> 'b) measure"
  where "ksemi M N Kr = M \<bind> (\<lambda>\<omega>. distr (Kr \<omega>) (M \<Otimes>\<^sub>M N) (Pair \<omega>))"

lemma ksemi_sets_kernel:
  assumes K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N" and w: "\<omega> \<in> space M"
  shows "sets (Kr \<omega>) = sets N" and "prob_space (Kr \<omega>)"
  using measurable_space[OF K w] by (auto simp: space_prob_algebra)

lemma ksemi_Pair_measurable:
  assumes K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N" and w: "\<omega> \<in> space M"
  shows "Pair \<omega> \<in> Kr \<omega> \<rightarrow>\<^sub>M M \<Otimes>\<^sub>M N"
  using measurable_Pair1'[OF w, of N]
    measurable_cong_sets[OF ksemi_sets_kernel(1)[OF K w] refl] by blast

lemma ksemi_kernel_measurable:
  assumes K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N"
  shows "(\<lambda>\<omega>. distr (Kr \<omega>) (M \<Otimes>\<^sub>M N) (Pair \<omega>)) \<in> M \<rightarrow>\<^sub>M subprob_algebra (M \<Otimes>\<^sub>M N)"
proof (rule measurable_distr2[where M = N])
  show "case_prod Pair \<in> M \<Otimes>\<^sub>M N \<rightarrow>\<^sub>M M \<Otimes>\<^sub>M N" by simp
  show "Kr \<in> M \<rightarrow>\<^sub>M subprob_algebra N" by (rule measurable_prob_algebraD[OF K])
qed

lemma sets_ksemi[measurable_cong]:
  assumes K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N" and ne: "space M \<noteq> {}"
  shows "sets (ksemi M N Kr) = sets (M \<Otimes>\<^sub>M N)"
  unfolding ksemi_def
  by (rule sets_bind[OF _ ne]) (simp add: ksemi_sets_kernel(1)[OF K])

lemma space_ksemi:
  assumes K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N" and ne: "space M \<noteq> {}"
  shows "space (ksemi M N Kr) = space (M \<Otimes>\<^sub>M N)"
  by (rule sets_eq_imp_space_eq[OF sets_ksemi[OF K ne]])

lemma prob_space_ksemi:
  assumes P: "prob_space M" and K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N"
  shows "prob_space (ksemi M N Kr)"
proof -
  interpret PM: prob_space M by (rule P)
  have "AE \<omega> in M. prob_space (distr (Kr \<omega>) (M \<Otimes>\<^sub>M N) (Pair \<omega>))"
  proof (rule AE_I2)
    fix \<omega> assume w: "\<omega> \<in> space M"
    show "prob_space (distr (Kr \<omega>) (M \<Otimes>\<^sub>M N) (Pair \<omega>))"
      by (rule prob_space.prob_space_distr
          [OF ksemi_sets_kernel(2)[OF K w] ksemi_Pair_measurable[OF K w]])
  qed
  from PM.prob_space_bind[OF this ksemi_kernel_measurable[OF K]]
  show ?thesis unfolding ksemi_def .
qed

lemma AE_ksemi:
  assumes K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N"
    and P: "{p \<in> space (M \<Otimes>\<^sub>M N). P p} \<in> sets (M \<Otimes>\<^sub>M N)"
  shows "(AE p in ksemi M N Kr. P p) \<longleftrightarrow> (AE \<omega> in M. AE \<omega>' in Kr \<omega>. P (\<omega>, \<omega>'))"
proof -
  have Pp: "Measurable.pred (M \<Otimes>\<^sub>M N) P" using P by (simp add: pred_def)
  have inner: "(AE p in distr (Kr \<omega>) (M \<Otimes>\<^sub>M N) (Pair \<omega>). P p)
      \<longleftrightarrow> (AE \<omega>' in Kr \<omega>. P (\<omega>, \<omega>'))" if w: "\<omega> \<in> space M" for \<omega>
    using AE_distr_iff[OF ksemi_Pair_measurable[OF K w] P] by simp
  have "(AE p in ksemi M N Kr. P p)
      \<longleftrightarrow> (AE \<omega> in M. AE p in distr (Kr \<omega>) (M \<Otimes>\<^sub>M N) (Pair \<omega>). P p)"
    unfolding ksemi_def by (rule AE_bind[OF ksemi_kernel_measurable[OF K] Pp])
  also have "\<dots> \<longleftrightarrow> (AE \<omega> in M. AE \<omega>' in Kr \<omega>. P (\<omega>, \<omega>'))"
    by (rule AE_cong) (simp add: inner)
  finally show ?thesis .
qed

lemma nn_integral_ksemi:
  assumes K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N"
    and g: "g \<in> borel_measurable (M \<Otimes>\<^sub>M N)"
  shows "(\<integral>\<^sup>+p. g p \<partial>(ksemi M N Kr)) = (\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+\<omega>'. g (\<omega>, \<omega>') \<partial>(Kr \<omega>)) \<partial>M)"
proof -
  have inner: "(\<integral>\<^sup>+p. g p \<partial>(distr (Kr \<omega>) (M \<Otimes>\<^sub>M N) (Pair \<omega>)))
      = (\<integral>\<^sup>+\<omega>'. g (\<omega>, \<omega>') \<partial>(Kr \<omega>))" if w: "\<omega> \<in> space M" for \<omega>
  proof -
    have gm: "g \<in> borel_measurable (distr (Kr \<omega>) (M \<Otimes>\<^sub>M N) (Pair \<omega>))"
      using g by simp
    show ?thesis
      by (rule nn_integral_distr[OF ksemi_Pair_measurable[OF K w] gm])
  qed
  have "(\<integral>\<^sup>+p. g p \<partial>(ksemi M N Kr))
      = (\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+p. g p \<partial>(distr (Kr \<omega>) (M \<Otimes>\<^sub>M N) (Pair \<omega>))) \<partial>M)"
    unfolding ksemi_def
    by (rule nn_integral_bind[OF g ksemi_kernel_measurable[OF K]])
  also have "\<dots> = (\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+\<omega>'. g (\<omega>, \<omega>') \<partial>(Kr \<omega>)) \<partial>M)"
    by (rule nn_integral_cong) (simp add: inner)
  finally show ?thesis .
qed

text \<open>The bounded disintegration.  This is the case the distribution's
  \<open>integral_bind\<close> does cover.\<close>

lemma integral_ksemi_bounded:
  fixes g :: "'a \<times> 'b \<Rightarrow> real"
  assumes PM: "prob_space M"
    and K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N"
    and gm: "g \<in> borel_measurable (M \<Otimes>\<^sub>M N)"
    and gb: "\<And>p. p \<in> space (M \<Otimes>\<^sub>M N) \<Longrightarrow> \<bar>g p\<bar> \<le> B"
  shows "(\<integral>p. g p \<partial>(ksemi M N Kr)) = (\<integral>\<omega>. (\<integral>\<omega>'. g (\<omega>, \<omega>') \<partial>(Kr \<omega>)) \<partial>M)"
proof -
  interpret PM: prob_space M by (rule PM)
  let ?f = "\<lambda>\<omega>. distr (Kr \<omega>) (M \<Otimes>\<^sub>M N) (Pair \<omega>)"
  have fm: "?f \<in> M \<rightarrow>\<^sub>M subprob_algebra (M \<Otimes>\<^sub>M N)"
    by (rule ksemi_kernel_measurable[OF K])
  have gb': "\<bar>g p\<bar> \<le> B" if "p \<in> space (M \<Otimes>\<^sub>M N)" for p by (rule gb[OF that])
  have ae: "AE \<omega> in M. emeasure (?f \<omega>) (space (?f \<omega>)) \<le> ennreal 1"
  proof (rule AE_I2)
    fix \<omega> assume w: "\<omega> \<in> space M"
    have "prob_space (?f \<omega>)"
      by (rule prob_space.prob_space_distr
          [OF ksemi_sets_kernel(2)[OF K w] ksemi_Pair_measurable[OF K w]])
    then have "emeasure (?f \<omega>) (space (?f \<omega>)) = 1"
      by (rule prob_space.emeasure_space_1)
    then show "emeasure (?f \<omega>) (space (?f \<omega>)) \<le> ennreal 1" by simp
  qed
  have "(\<integral>p. g p \<partial>(ksemi M N Kr)) = (\<integral>\<omega>. (\<integral>p. g p \<partial>(?f \<omega>)) \<partial>M)"
    unfolding ksemi_def
    by (rule integral_bind[OF gm gb' fm PM.finite_measure_axioms ae])
  also have "\<dots> = (\<integral>\<omega>. (\<integral>\<omega>'. g (\<omega>, \<omega>') \<partial>(Kr \<omega>)) \<partial>M)"
  proof (rule Bochner_Integration.integral_cong[OF refl])
    fix \<omega> assume w: "\<omega> \<in> space M"
    show "(\<integral>p. g p \<partial>(?f \<omega>)) = (\<integral>\<omega>'. g (\<omega>, \<omega>') \<partial>(Kr \<omega>))"
      by (rule integral_distr[OF ksemi_Pair_measurable[OF K w] gm])
  qed
  finally show ?thesis .
qed

lemma integral_ksemi_measurable:
  fixes g :: "'a \<times> 'b \<Rightarrow> real"
  assumes K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N" and gm: "g \<in> borel_measurable (M \<Otimes>\<^sub>M N)"
  shows "(\<lambda>\<omega>. (\<integral>\<omega>'. g (\<omega>, \<omega>') \<partial>(Kr \<omega>))) \<in> borel_measurable M"
proof -
  let ?f = "\<lambda>\<omega>. distr (Kr \<omega>) (M \<Otimes>\<^sub>M N) (Pair \<omega>)"
  have "(\<lambda>\<omega>. (\<integral>p. g p \<partial>(?f \<omega>))) \<in> borel_measurable M"
    using measurable_compose[OF ksemi_kernel_measurable[OF K]
        integral_measurable_subprob_algebra[OF gm]] .
  moreover have "(\<integral>p. g p \<partial>(?f \<omega>)) = (\<integral>\<omega>'. g (\<omega>, \<omega>') \<partial>(Kr \<omega>))"
    if w: "\<omega> \<in> space M" for \<omega>
  proof -
    show ?thesis by (rule integral_distr[OF ksemi_Pair_measurable[OF K w] gm])
  qed
  ultimately show ?thesis by (simp cong: measurable_cong)
qed

section \<open>Measurable and integrable kernel integrals\<close>

text \<open>The map \<open>\<omega> \<mapsto> \<integral> h d(Kr \<omega>)\<close> is measurable when the integrand does not
  depend on \<open>\<omega>\<close>.\<close>

lemma measurable_integral_kernel:
  fixes h :: "'b \<Rightarrow> 'c::{banach,second_countable_topology}"
  assumes K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N" and hm: "h \<in> borel_measurable N"
  shows "(\<lambda>\<omega>. \<integral>\<omega>'. h \<omega>' \<partial>(Kr \<omega>)) \<in> borel_measurable M"
  by (rule measurable_compose[OF measurable_prob_algebraD[OF K]
      integral_measurable_subprob_algebra[OF hm]])

text \<open>The general case: the inner integral is measurable in the base point
  even when the integrand \<open>g \<omega>\<close> itself depends on \<open>\<omega>\<close>; this is the curried
  form of @{thm [source] integral_ksemi_measurable}, and the integrability
  hypothesis is not needed.\<close>

lemma integral_kernel_measurable:
  fixes g :: "'a \<Rightarrow> 'b \<Rightarrow> real"
  assumes K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N"
    and gm: "(\<lambda>p. g (fst p) (snd p)) \<in> borel_measurable (M \<Otimes>\<^sub>M N)"
    and gi: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> integrable (Kr \<omega>) (g \<omega>)"
  shows "(\<lambda>\<omega>. \<integral>\<omega>'. g \<omega> \<omega>' \<partial>(Kr \<omega>)) \<in> borel_measurable M"
  using integral_ksemi_measurable[OF K gm] by simp

text \<open>Integrability from an integrable bound on the inner integral, itself
  possibly a function of the base point.\<close>

lemma integrable_ksemi_of_past_bound:
  fixes g :: "'a \<times> 'b \<Rightarrow> 'c::{banach,second_countable_topology}"
  assumes K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N" and ne: "space M \<noteq> {}"
    and gm: "g \<in> borel_measurable (M \<Otimes>\<^sub>M N)"
    and hi: "integrable M h"
    and bnd: "\<And>\<omega>. \<omega> \<in> space M
      \<Longrightarrow> (\<integral>\<^sup>+\<omega>'. ennreal (norm (g (\<omega>, \<omega>'))) \<partial>(Kr \<omega>)) \<le> ennreal (h \<omega>)"
  shows "integrable (ksemi M N Kr) g"
proof -
  have setsS: "sets (ksemi M N Kr) = sets (M \<Otimes>\<^sub>M N)"
    by (rule sets_ksemi[OF K ne])
  have gmS: "g \<in> borel_measurable (ksemi M N Kr)"
    using gm measurable_cong_sets[OF setsS refl] by blast
  have gabs: "(\<lambda>p. ennreal (norm (g p))) \<in> borel_measurable (M \<Otimes>\<^sub>M N)"
    using gm by measurable
  have "(\<integral>\<^sup>+p. ennreal (norm (g p)) \<partial>(ksemi M N Kr))
      = (\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+\<omega>'. ennreal (norm (g (\<omega>, \<omega>'))) \<partial>(Kr \<omega>)) \<partial>M)"
    using nn_integral_ksemi[OF K gabs] by simp
  also have "\<dots> \<le> (\<integral>\<^sup>+\<omega>. ennreal (norm (h \<omega>)) \<partial>M)"
  proof (rule nn_integral_mono_AE)
    show "AE \<omega> in M.
        (\<integral>\<^sup>+\<omega>'. ennreal (norm (g (\<omega>, \<omega>'))) \<partial>(Kr \<omega>)) \<le> ennreal (norm (h \<omega>))"
    proof (rule eventually_mono[OF AE_space])
      fix \<omega> assume w: "\<omega> \<in> space M"
      have "(\<integral>\<^sup>+\<omega>'. ennreal (norm (g (\<omega>, \<omega>'))) \<partial>(Kr \<omega>)) \<le> ennreal (h \<omega>)"
        by (rule bnd[OF w])
      also have "\<dots> \<le> ennreal (norm (h \<omega>))" by (intro ennreal_leI) simp
      finally show "(\<integral>\<^sup>+\<omega>'. ennreal (norm (g (\<omega>, \<omega>'))) \<partial>(Kr \<omega>))
          \<le> ennreal (norm (h \<omega>))" .
    qed
  qed
  also have "\<dots> < \<top>" using hi by (simp add: integrable_iff_bounded)
  finally show ?thesis using gmS by (simp add: integrable_iff_bounded)
qed

section \<open>Rectangles, sections and pushforwards\<close>

text \<open>The almost-sure transfer through a semidirect product: an
  almost-sure property of the pushforward of a semidirect product (or of a
  product) is an almost-sure property of the first factor, then of the second.\<close>

lemma AE_distr_ksemi_iff:
  assumes K: "Kr \<in> Q \<rightarrow>\<^sub>M prob_algebra N" and ne: "space Q \<noteq> {}"
    and gm: "g \<in> Q \<Otimes>\<^sub>M N \<rightarrow>\<^sub>M B" and Phi: "{\<omega> \<in> space B. \<Phi> \<omega>} \<in> sets B"
  shows "(AE \<omega> in distr (ksemi Q N Kr) B g. \<Phi> \<omega>)
      \<longleftrightarrow> (AE p in Q. AE w in Kr p. \<Phi> (g (p, w)))"
proof -
  have gm': "g \<in> ksemi Q N Kr \<rightarrow>\<^sub>M B"
    using gm measurable_cong_sets[OF sets_ksemi[OF K ne] refl] by blast
  have "{p \<in> space (Q \<Otimes>\<^sub>M N). \<Phi> (g p)} = g -` {\<omega> \<in> space B. \<Phi> \<omega>} \<inter> space (Q \<Otimes>\<^sub>M N)"
    using measurable_space[OF gm] by auto
  then have meas: "{p \<in> space (Q \<Otimes>\<^sub>M N). \<Phi> (g p)} \<in> sets (Q \<Otimes>\<^sub>M N)"
    using measurable_sets[OF gm Phi] by simp
  show ?thesis
    by (subst AE_distr_iff[OF gm' Phi]) (rule AE_ksemi[OF K meas])
qed

lemma AE_distr_ksemi_imp:
  assumes K: "Kr \<in> Q \<rightarrow>\<^sub>M prob_algebra N" and ne: "space Q \<noteq> {}"
    and gm: "g \<in> Q \<Otimes>\<^sub>M N \<rightarrow>\<^sub>M B" and Phi: "{\<omega> \<in> space B. \<Phi> \<omega>} \<in> sets B"
    and A: "AE \<omega> in Q. A \<omega>" and Bw: "\<And>\<omega>. \<omega> \<in> space Q \<Longrightarrow> AE w in Kr \<omega>. Bp \<omega> w"
    and imp: "\<And>\<omega> w. \<omega> \<in> space Q \<Longrightarrow> w \<in> space N \<Longrightarrow> A \<omega> \<Longrightarrow> Bp \<omega> w
        \<Longrightarrow> \<Phi> (g (\<omega>, w))"
  shows "AE \<omega> in distr (ksemi Q N Kr) B g. \<Phi> \<omega>"
  unfolding AE_distr_ksemi_iff[OF K ne gm Phi]
  using A AE_space
proof eventually_elim
  case (elim \<omega>)
  note Aw = elim(1) and wQ = elim(2)
  have sp: "space (Kr \<omega>) = space N"
    by (rule sets_eq_imp_space_eq[OF ksemi_sets_kernel(1)[OF K wQ]])
  from Bw[OF wQ] AE_space show ?case
  proof eventually_elim
    case (elim w)
    show ?case by (rule imp[OF wQ elim(2)[unfolded sp] Aw elim(1)])
  qed
qed

text \<open>On a rectangle the semidirect product integrates the kernel's mass of the
  second side over the first.\<close>

lemma emeasure_ksemi_rect:
  assumes K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N" and ne: "space M \<noteq> {}"
    and A: "A \<in> sets M" and B: "B \<in> sets N"
  shows "emeasure (ksemi M N Kr) (A \<times> B) = (\<integral>\<^sup>+\<omega>\<in>A. emeasure (Kr \<omega>) B \<partial>M)"
proof -
  have rect: "A \<times> B \<in> sets (M \<Otimes>\<^sub>M N)" using A B by simp
  have "emeasure (ksemi M N Kr) (A \<times> B)
      = (\<integral>\<^sup>+\<omega>. emeasure (distr (Kr \<omega>) (M \<Otimes>\<^sub>M N) (Pair \<omega>)) (A \<times> B) \<partial>M)"
    unfolding ksemi_def
    by (rule emeasure_bind[OF ne ksemi_kernel_measurable[OF K] rect])
  also have "\<dots> = (\<integral>\<^sup>+\<omega>. indicator A \<omega> * emeasure (Kr \<omega>) B \<partial>M)"
  proof (rule nn_integral_cong)
    fix \<omega> assume w: "\<omega> \<in> space M"
    have sK: "sets (Kr \<omega>) = sets N" by (rule ksemi_sets_kernel(1)[OF K w])
    have spK: "space (Kr \<omega>) = space N" by (rule sets_eq_imp_space_eq[OF sK])
    have "emeasure (distr (Kr \<omega>) (M \<Otimes>\<^sub>M N) (Pair \<omega>)) (A \<times> B)
        = emeasure (Kr \<omega>) (Pair \<omega> -` (A \<times> B) \<inter> space (Kr \<omega>))"
      by (rule emeasure_distr[OF ksemi_Pair_measurable[OF K w] rect])
    also have "\<dots> = indicator A \<omega> * emeasure (Kr \<omega>) B"
    proof (cases "\<omega> \<in> A")
      case True
      have "Pair \<omega> -` (A \<times> B) \<inter> space (Kr \<omega>) = B"
        using True B sets.sets_into_space[OF B] by (auto simp: spK)
      then show ?thesis using True by simp
    next
      case False
      have "Pair \<omega> -` (A \<times> B) \<inter> space (Kr \<omega>) = {}" using False by auto
      then show ?thesis using False by simp
    qed
    finally show "emeasure (distr (Kr \<omega>) (M \<Otimes>\<^sub>M N) (Pair \<omega>)) (A \<times> B)
        = indicator A \<omega> * emeasure (Kr \<omega>) B" .
  qed
  finally show ?thesis by (simp add: nn_integral_set_ennreal mult.commute)
qed

text \<open>Almost every section of a function integrable for the semidirect product is
  integrable for the kernel.\<close>

lemma AE_integrable_ksemi_section:
  fixes g :: "'a \<times> 'b \<Rightarrow> 'c::{banach,second_countable_topology}"
  assumes K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N"
    and gm: "g \<in> borel_measurable (M \<Otimes>\<^sub>M N)"
    and gi: "integrable (ksemi M N Kr) g"
    and ne: "space M \<noteq> {}"
  shows "AE \<omega> in M. integrable (Kr \<omega>) (\<lambda>\<omega>'. g (\<omega>, \<omega>'))"
proof -
  have gabs: "(\<lambda>p. ennreal (norm (g p))) \<in> borel_measurable (M \<Otimes>\<^sub>M N)"
    using gm by measurable
  have fin: "(\<integral>\<^sup>+p. ennreal (norm (g p)) \<partial>(ksemi M N Kr)) < \<top>"
    using gi by (simp add: integrable_iff_bounded)
  have split: "(\<integral>\<^sup>+p. ennreal (norm (g p)) \<partial>(ksemi M N Kr))
      = (\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+\<omega>'. ennreal (norm (g (\<omega>, \<omega>'))) \<partial>(Kr \<omega>)) \<partial>M)"
    by (rule nn_integral_ksemi[OF K gabs])
  have minner: "(\<lambda>\<omega>. \<integral>\<^sup>+\<omega>'. ennreal (norm (g (\<omega>, \<omega>'))) \<partial>(Kr \<omega>))
      \<in> borel_measurable M"
  proof (rule nn_integral_measurable_subprob_algebra2)
    show "(\<lambda>(x, y). ennreal (norm (g (x, y)))) \<in> borel_measurable (M \<Otimes>\<^sub>M N)"
      using gabs by (simp add: case_prod_unfold)
    show "Kr \<in> M \<rightarrow>\<^sub>M subprob_algebra N" by (rule measurable_prob_algebraD[OF K])
  qed
  have fin': "(\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+\<omega>'. ennreal (norm (g (\<omega>, \<omega>'))) \<partial>(Kr \<omega>)) \<partial>M) \<noteq> \<infinity>"
    using fin split by (simp add: less_top)
  have aefin: "AE \<omega> in M. (\<integral>\<^sup>+\<omega>'. ennreal (norm (g (\<omega>, \<omega>'))) \<partial>(Kr \<omega>)) \<noteq> \<infinity>"
    by (rule nn_integral_PInf_AE[OF minner fin'])
  have "AE \<omega> in M. \<omega> \<in> space M" by (rule AE_I2) simp
  with aefin show ?thesis
  proof eventually_elim
    fix \<omega> assume z: "(\<integral>\<^sup>+\<omega>'. ennreal (norm (g (\<omega>, \<omega>'))) \<partial>(Kr \<omega>)) \<noteq> \<infinity>"
      and w: "\<omega> \<in> space M"
    have sec: "(\<lambda>\<omega>'. g (\<omega>, \<omega>')) \<in> borel_measurable (Kr \<omega>)"
      by (rule measurable_compose[OF ksemi_Pair_measurable[OF K w] gm])
    show "integrable (Kr \<omega>) (\<lambda>\<omega>'. g (\<omega>, \<omega>'))"
      using sec z by (simp add: integrable_iff_bounded less_top)
  qed
qed

text \<open>When the semidirect product is the pushforward of a measure \<open>P\<close>, a
  rectangle-cut function is integrable as soon as the second factor is
  integrable under \<open>P\<close>.\<close>

lemma integrable_ksemi_of_distr_rect:
  fixes h :: "'b \<Rightarrow> real"
  assumes eq: "ksemi M N Kr = distr P (M \<Otimes>\<^sub>M N) \<phi>"
    and phim: "\<phi> \<in> P \<rightarrow>\<^sub>M M \<Otimes>\<^sub>M N"
    and hm: "h \<in> borel_measurable N"
    and A: "A \<in> sets M" and A': "A' \<in> sets N"
    and hi: "integrable P (\<lambda>\<omega>. h (snd (\<phi> \<omega>)))"
  shows "integrable (ksemi M N Kr)
      (\<lambda>p. indicator A (fst p) * (indicator A' (snd p) * h (snd p)))"
proof -
  let ?g = "\<lambda>p :: 'a \<times> 'b.
      indicator A (fst p) * (indicator A' (snd p) * h (snd p))"
  have gm: "?g \<in> borel_measurable (M \<Otimes>\<^sub>M N)" using A A' hm by measurable
  have comp: "integrable P (\<lambda>\<omega>. ?g (\<phi> \<omega>))"
  proof (rule Bochner_Integration.integrable_bound[OF hi])
    show "(\<lambda>\<omega>. ?g (\<phi> \<omega>)) \<in> borel_measurable P"
      by (rule measurable_compose[OF phim gm])
    show "AE \<omega> in P. norm (?g (\<phi> \<omega>)) \<le> norm (h (snd (\<phi> \<omega>)))"
      by (rule AE_I2) (auto simp: indicator_def abs_mult)
  qed
  have "integrable (distr P (M \<Otimes>\<^sub>M N) \<phi>) ?g"
    using comp by (simp add: integrable_distr_eq[OF phim gm])
  then show ?thesis unfolding eq .
qed

text \<open>The outer integral of the kernel integral is
  dominated by the \<open>ksemi\<close> integral of \<open>|h|\<close>, because the section integral is
  almost surely bounded in norm by the section's own nonnegative integral,
  where @{thm [source] AE_integrable_ksemi_section} earns its keep.\<close>

lemma integrable_kernel_integral:
  fixes h :: "'b \<Rightarrow> real"
  assumes K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N" and ne: "space M \<noteq> {}"
    and hm: "h \<in> borel_measurable N"
    and A': "A' \<in> sets N"
    and hi: "integrable (ksemi M N Kr) (\<lambda>p. h (snd p))"
  shows "integrable M (\<lambda>\<omega>. \<integral>\<omega>'. indicator A' \<omega>' * h \<omega>' \<partial>(Kr \<omega>))"
proof -
  have hm2: "(\<lambda>p :: 'a \<times> 'b. h (snd p)) \<in> borel_measurable (M \<Otimes>\<^sub>M N)"
    using hm by measurable
  have hm': "(\<lambda>\<omega>'. indicator A' \<omega>' * h \<omega>') \<in> borel_measurable N"
    using hm A' by measurable
  have fmeas: "(\<lambda>\<omega>. \<integral>\<omega>'. indicator A' \<omega>' * h \<omega>' \<partial>(Kr \<omega>)) \<in> borel_measurable M"
    by (rule measurable_integral_kernel[OF K hm'])
  have aei: "AE \<omega> in M. integrable (Kr \<omega>) h"
    using AE_integrable_ksemi_section[OF K hm2 hi ne] by simp
  have "AE \<omega> in M. \<omega> \<in> space M" by (rule AE_I2) simp
  with aei have bnd: "AE \<omega> in M.
      ennreal (norm (\<integral>\<omega>'. indicator A' \<omega>' * h \<omega>' \<partial>(Kr \<omega>)))
        \<le> (\<integral>\<^sup>+\<omega>'. ennreal (norm (h \<omega>')) \<partial>(Kr \<omega>))"
  proof eventually_elim
    fix \<omega> assume i: "integrable (Kr \<omega>) h" and w: "\<omega> \<in> space M"
    have sK: "sets (Kr \<omega>) = sets N" by (rule ksemi_sets_kernel(1)[OF K w])
    have AK: "A' \<in> sets (Kr \<omega>)" using A' sK by simp
    have i2: "integrable (Kr \<omega>) (\<lambda>\<omega>'. indicator A' \<omega>' * h \<omega>')"
      using integrable_mult_indicator[OF AK i] by simp
    have "ennreal (norm (\<integral>\<omega>'. indicator A' \<omega>' * h \<omega>' \<partial>(Kr \<omega>)))
        \<le> (\<integral>\<^sup>+\<omega>'. ennreal (norm (indicator A' \<omega>' * h \<omega>')) \<partial>(Kr \<omega>))"
      by (rule integral_norm_bound_ennreal[OF i2])
    also have "\<dots> \<le> (\<integral>\<^sup>+\<omega>'. ennreal (norm (h \<omega>')) \<partial>(Kr \<omega>))"
      by (intro nn_integral_mono ennreal_leI) (simp add: indicator_def abs_mult)
    finally show "ennreal (norm (\<integral>\<omega>'. indicator A' \<omega>' * h \<omega>' \<partial>(Kr \<omega>)))
        \<le> (\<integral>\<^sup>+\<omega>'. ennreal (norm (h \<omega>')) \<partial>(Kr \<omega>))" .
  qed
  have "(\<integral>\<^sup>+\<omega>. ennreal (norm (\<integral>\<omega>'. indicator A' \<omega>' * h \<omega>' \<partial>(Kr \<omega>))) \<partial>M)
      \<le> (\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+\<omega>'. ennreal (norm (h \<omega>')) \<partial>(Kr \<omega>)) \<partial>M)"
    by (rule nn_integral_mono_AE[OF bnd])
  also have "\<dots> = (\<integral>\<^sup>+p. ennreal (norm (h (snd p))) \<partial>(ksemi M N Kr))"
  proof -
    have gmm: "(\<lambda>p :: 'a \<times> 'b. ennreal (norm (h (snd p))))
        \<in> borel_measurable (M \<Otimes>\<^sub>M N)" using hm2 by measurable
    show "(\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+\<omega>'. ennreal (norm (h \<omega>')) \<partial>(Kr \<omega>)) \<partial>M)
        = (\<integral>\<^sup>+p. ennreal (norm (h (snd p))) \<partial>(ksemi M N Kr))"
      using nn_integral_ksemi[OF K gmm] by simp
  qed
  also have "\<dots> < \<top>" using hi by (simp add: integrable_iff_bounded)
  finally show ?thesis using fmeas by (simp add: integrable_iff_bounded)
qed

text \<open>The rectangle integral over the semidirect product
  is a single set integral over \<open>P\<close>, the two indicators combining into the
  indicator of \<open>\<phi> \<^sup>-\<^sup>1 (A \<times> A')\<close>.  That set is where the martingale property
  of \<open>P\<close> is applied, so this lemma is the bridge from the kernel back to the
  original law.\<close>

lemma integral_ksemi_rect_of_set_integral:
  fixes h :: "'b \<Rightarrow> real"
  assumes eq: "ksemi M N Kr = distr P (M \<Otimes>\<^sub>M N) \<phi>"
    and phim: "\<phi> \<in> P \<rightarrow>\<^sub>M M \<Otimes>\<^sub>M N"
    and hm: "h \<in> borel_measurable N"
    and A: "A \<in> sets M" and A': "A' \<in> sets N"
  shows "(\<integral>p. indicator A (fst p) * (indicator A' (snd p) * h (snd p))
        \<partial>(ksemi M N Kr))
      = set_lebesgue_integral P (\<phi> -` (A \<times> A') \<inter> space P)
          (\<lambda>\<omega>. h (snd (\<phi> \<omega>)))"
proof -
  let ?g = "\<lambda>p :: 'a \<times> 'b.
      indicator A (fst p) * (indicator A' (snd p) * h (snd p))"
  have gm: "?g \<in> borel_measurable (M \<Otimes>\<^sub>M N)" using A A' hm by measurable
  have "(\<integral>p. ?g p \<partial>(ksemi M N Kr)) = (\<integral>p. ?g p \<partial>(distr P (M \<Otimes>\<^sub>M N) \<phi>))"
    unfolding eq ..
  also have "\<dots> = (\<integral>\<omega>. ?g (\<phi> \<omega>) \<partial>P)" by (rule integral_distr[OF phim gm])
  also have "\<dots> = (\<integral>\<omega>. indicator (\<phi> -` (A \<times> A') \<inter> space P) \<omega> * h (snd (\<phi> \<omega>)) \<partial>P)"
  proof (rule Bochner_Integration.integral_cong[OF refl])
    fix \<omega> assume "\<omega> \<in> space P"
    then show "?g (\<phi> \<omega>)
        = indicator (\<phi> -` (A \<times> A') \<inter> space P) \<omega> * h (snd (\<phi> \<omega>))"
      by (auto simp: indicator_def mem_Times_iff)
  qed
  also have "\<dots> = set_lebesgue_integral P (\<phi> -` (A \<times> A') \<inter> space P)
      (\<lambda>\<omega>. h (snd (\<phi> \<omega>)))"
    unfolding set_lebesgue_integral_def by simp
  finally show ?thesis .
qed

(*<*)
end
(*>*)
