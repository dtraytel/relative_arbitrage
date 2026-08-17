
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
  even when the integrand \<open>g \<omega>\<close> itself depends on \<open>\<omega>\<close>.\<close>

lemma integral_kernel_measurable:
  fixes g :: "'a \<Rightarrow> 'b \<Rightarrow> real"
  assumes K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N"
    and gm: "(\<lambda>p. g (fst p) (snd p)) \<in> borel_measurable (M \<Otimes>\<^sub>M N)"
    and gi: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> integrable (Kr \<omega>) (g \<omega>)"
  shows "(\<lambda>\<omega>. \<integral>\<omega>'. g \<omega> \<omega>' \<partial>(Kr \<omega>)) \<in> borel_measurable M"
proof -
  define A where "A \<omega> = (\<integral>\<^sup>+\<omega>'. ennreal (g \<omega> \<omega>') \<partial>(Kr \<omega>))" for \<omega>
  define B where "B \<omega> = (\<integral>\<^sup>+\<omega>'. ennreal (- g \<omega> \<omega>') \<partial>(Kr \<omega>))" for \<omega>
  have Ksub: "Kr \<in> M \<rightarrow>\<^sub>M subprob_algebra N"
    by (rule measurable_prob_algebraD[OF K])
  have mA: "A \<in> borel_measurable M"
    unfolding A_def
    by (rule nn_integral_measurable_subprob_algebra2[OF _ Ksub])
       (use gm in \<open>simp add: case_prod_unfold\<close>)
  have mB: "B \<in> borel_measurable M"
    unfolding B_def
    by (rule nn_integral_measurable_subprob_algebra2[OF _ Ksub])
       (use gm in \<open>simp add: case_prod_unfold\<close>)
  have mAB: "(\<lambda>\<omega>. enn2real (A \<omega>) - enn2real (B \<omega>)) \<in> borel_measurable M"
    using mA mB by measurable
  show ?thesis
  proof (subst measurable_cong)
    fix \<omega> assume w: "\<omega> \<in> space M"
    show "(\<integral>\<omega>'. g \<omega> \<omega>' \<partial>(Kr \<omega>)) = enn2real (A \<omega>) - enn2real (B \<omega>)"
      unfolding A_def B_def by (rule real_lebesgue_integral_def[OF gi[OF w]])
  next
    show "(\<lambda>\<omega>. enn2real (A \<omega>) - enn2real (B \<omega>)) \<in> borel_measurable M"
      by (rule mAB)
  qed
qed

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

section \<open>Mixing two kernels on an event\<close>

text \<open>Optimal on a chosen event, the other kernel elsewhere.  Measurability
  is @{thm [source] measurable_If}.\<close>

lemma kernel_mix_measurable:
  assumes A: "A \<in> sets G"
    and K1: "\<kappa>1 \<in> G \<rightarrow>\<^sub>M prob_algebra N" and K2: "\<kappa>2 \<in> G \<rightarrow>\<^sub>M prob_algebra N"
  shows "(\<lambda>p. if p \<in> A then \<kappa>1 p else \<kappa>2 p) \<in> G \<rightarrow>\<^sub>M prob_algebra N"
proof (rule measurable_If[OF K1 K2])
  have "{p \<in> space G. p \<in> A} = A" using A sets.sets_into_space by auto
  then show "{p \<in> space G. p \<in> A} \<in> sets G" using A by simp
qed

(*<*)
end
(*>*)
