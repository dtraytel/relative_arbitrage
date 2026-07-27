section \<open>Sampling a continuous-time martingale along a partition\<close>

text \<open>
  Layer 2 of open task 15 (continuous-time stochastic integration). Neither the
  Isabelle distribution nor the AFP contains any stochastic integral, Ito formula
  or Doob-Meyer decomposition -- checked: no \<open>Ito\<close>, \<open>stochastic_integral\<close> or
  \<open>Doob_Meyer\<close> in either, and the AFP's \<open>Stochastic_Matrices\<close> is linear algebra --
  so this has to be built.

  The observation that organises the construction: for a SIMPLE predictable
  integrand, subordinate to a monotone partition \<open>t :: nat => real\<close>, the
  stochastic integral is literally a discrete martingale transform of the SAMPLED
  process \<open>%k. X (t k)\<close> along the SAMPLED filtration \<open>%k. F (t k)\<close>. So the
  discrete theory already developed in \<open>Quadratic_Variation\<close> and
  \<open>Stochastic_Integral\<close> (\<open>mtrans\<close>, \<open>martingale_mtrans\<close>, \<open>qvar\<close>) can be reused
  wholesale, provided we first know that sampling a martingale gives a
  martingale. That bridge is what this theory supplies.

  AFP \<open>Martingales\<close> is index-generic: \<open>filtered_measure\<close> fixes an arbitrary
  order-topology index and the entry provides \<open>real_filtered_measure\<close>. That is
  what makes the statement expressible at all.

  Note this text block sits BEFORE the theory header, so it must not use
  antiquotations -- there is no theory context yet in which to elaborate them.
\<close>
theory Sampled_Martingale
  imports "Martingales.Martingale"
begin

theorem martingale_sampled:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> 'b::{second_countable_topology,banach}"
    and t :: "nat \<Rightarrow> real"
  assumes X: "martingale M F (0::real) X"
    and t0: "\<And>k. 0 \<le> t k" and tmono: "mono t"
  shows "martingale M (\<lambda>k. F (t k)) (0::nat) (\<lambda>k. X (t k))"
proof -
  interpret X: martingale M F "0::real" X by (rule X)
  have sf: "sigma_finite_subalgebra M (F (t 0))"
    using t0 by (rule X.sigma_finite_subalgebra_F)
  show ?thesis
  proof (unfold_locales)
    show "subalgebra M (F (t i))" for i :: nat
      using t0 by (rule X.subalgebras)
    show "sets (F (t i)) \<subseteq> sets (F (t j))"
      if "(0::nat) \<le> i" "i \<le> j" for i j :: nat
      using t0 monoD[OF tmono that(2)] by (rule X.sets_F_mono)
    show "subalgebra M (F (t 0))"
      by (rule sigma_finite_subalgebra.subalg[OF sf])
    show "\<exists>A. countable A \<and> A \<subseteq> sets (restr_to_subalg M (F (t 0)))
              \<and> \<Union> A = space (restr_to_subalg M (F (t 0)))
              \<and> (\<forall>a\<in>A. emeasure (restr_to_subalg M (F (t 0))) a \<noteq> \<infinity>)"
      by (rule sigma_finite_measure.sigma_finite_countable
                 [OF sigma_finite_subalgebra.sigma_fin_subalg[OF sf]])
    show "X (t i) \<in> borel_measurable (F (t i))" for i :: nat
      using t0 by (rule X.adapted)
    show "integrable M (X (t i))" for i :: nat
      using t0 by (rule X.integrable)
    show "AE \<xi> in M. X (t i) \<xi> = cond_exp M (F (t i)) (X (t j)) \<xi>"
      if "(0::nat) \<le> i" "i \<le> j" for i j :: nat
      using t0 monoD[OF tmono that(2)] by (rule X.martingale_property)
  qed
qed
text \<open>
  The sampled filtration is a @{term nat}-indexed filtered measure, which is the
  interface the repository's discrete development (@{text Quadratic_Variation},
  @{text Stochastic_Integral}) is stated over.
\<close>

corollary nat_filtered_of_sampled:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> 'b::{second_countable_topology,banach}"
  assumes X: "martingale M F (0::real) X"
    and t0: "\<And>k. 0 \<le> t k" and tmono: "mono t"
  shows "nat_sigma_finite_filtered_measure M (\<lambda>k. F (t k))"
proof -
  interpret S: martingale M "\<lambda>k. F (t k)" "0::nat" "\<lambda>k. X (t k)"
    by (rule martingale_sampled[OF X t0 tmono])
  show ?thesis by unfold_locales
qed

text \<open>
  The case actually used to build the integral by refinement: a uniform
  partition of mesh @{term dt}.
\<close>

corollary martingale_sampled_uniform:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> 'b::{second_countable_topology,banach}"
  assumes X: "martingale M F (0::real) X" and dt: "0 \<le> dt"
  shows "martingale M (\<lambda>k. F (real k * dt)) (0::nat) (\<lambda>k. X (real k * dt))"
proof (rule martingale_sampled[OF X])
  show "0 \<le> real k * dt" for k using dt by simp
  show "mono (\<lambda>k::nat. real k * dt)"
    using dt by (intro monoI mult_right_mono) auto
qed

subsection \<open>Reducing the compensated-square martingale property to the covariation hypothesis\<close>

text \<open>
  This is the shape of the \<open>Z_martingale\<close> assumption in
  \<open>locale ito_volatile_market\<close>: with \<open>S t = X t \<bullet> X t\<close> and
  \<open>A t = integral_{0..t} (trace o acov)\<close>, that assumption says exactly that
  \<open>S - A\<close> is a martingale. It is NOT derivable from the other assumptions of that
  locale, because \<open>acov\<close> enters as a free parameter constrained only by
  positive-semidefiniteness, the eigenvalue bounds and integrability -- nothing
  there ties it to the covariation of @{term X}. Confirmed against the paper: the
  condition \<open>d<X_i,X_j>(t)/dt IN S\<close> is imposed as part of the DEFINITION of the
  admissible family, so it is data rather than something to be constructed, and no
  Doob-Meyer decomposition is involved.

  What can be done, and is done here, is to reduce that assumption to the
  covariation condition in its primitive conditional form: \<open>S - A\<close> is a martingale
  as soon as the conditional expectation of an increment of @{term S} agrees with
  that of the corresponding increment of @{term A}. Combined with
  \<open>cond_exp_increment_sq\<close> of \<open>Sampled_Quadratic_Variation\<close> (which cannot be cited
  as an antiquotation here, since that theory sits ABOVE this one in the import
  order), the increment of @{term Sq} is a
  conditional VARIANCE, so the hypothesis below is precisely the statement that
  @{term A} is the compensator -- i.e. the paper's own defining condition, with no
  martingale property assumed of the compensated process itself.
\<close>

theorem martingale_of_cond_increment:
  fixes Sq A :: "real \<Rightarrow> 'a \<Rightarrow> real"
  assumes sfm: "sigma_finite_filtered_measure M F (0::real)"
    and adapted: "adapted_process M F (0::real) (\<lambda>t \<omega>. Sq t \<omega> - A t \<omega>)"
    and Sint: "\<And>t. 0 \<le> t \<Longrightarrow> integrable M (Sq t)"
    and Aint: "\<And>t. 0 \<le> t \<Longrightarrow> integrable M (A t)"
    and cov: "\<And>s u. 0 \<le> s \<Longrightarrow> s \<le> u \<Longrightarrow>
        AE \<omega> in M. cond_exp M (F s) (\<lambda>\<omega>. Sq u \<omega> - Sq s \<omega>) \<omega>
                   = cond_exp M (F s) (\<lambda>\<omega>. A u \<omega> - A s \<omega>) \<omega>"
  shows "martingale M F 0 (\<lambda>t \<omega>. Sq t \<omega> - A t \<omega>)"
proof (rule sigma_finite_filtered_measure.martingale_of_cond_exp_diff_eq_zero
             [OF sfm adapted])
  show "integrable M (\<lambda>\<omega>. Sq i \<omega> - A i \<omega>)" if "0 \<le> i" for i
    using Sint[OF that] Aint[OF that] by simp
next
  fix i j :: real assume ij: "0 \<le> i" "i \<le> j"
  then have j: "0 \<le> j" by simp
  have sfsub: "sigma_finite_subalgebra M (F i)"
    using ij by (intro sigma_finite_filtered_measure.sigma_finite_subalgebra_F[OF sfm])
  have iS: "integrable M (\<lambda>\<omega>. Sq j \<omega> - Sq i \<omega>)"
    using Sint[OF j] Sint[OF ij(1)] by simp
  have iA: "integrable M (\<lambda>\<omega>. A j \<omega> - A i \<omega>)"
    using Aint[OF j] Aint[OF ij(1)] by simp
  have rearr: "(\<lambda>\<omega>. (Sq j \<omega> - A j \<omega>) - (Sq i \<omega> - A i \<omega>))
               = (\<lambda>\<omega>. (Sq j \<omega> - Sq i \<omega>) - (A j \<omega> - A i \<omega>))"
    by (simp add: algebra_simps)
  have "AE \<omega> in M.
      cond_exp M (F i) (\<lambda>\<omega>. (Sq j \<omega> - Sq i \<omega>) - (A j \<omega> - A i \<omega>)) \<omega>
        = cond_exp M (F i) (\<lambda>\<omega>. Sq j \<omega> - Sq i \<omega>) \<omega>
          - cond_exp M (F i) (\<lambda>\<omega>. A j \<omega> - A i \<omega>) \<omega>"
    by (rule sigma_finite_subalgebra.cond_exp_diff[OF sfsub iS iA])
  with cov[OF ij]
  show "AE \<omega> in M.
      cond_exp M (F i) (\<lambda>\<xi>. (Sq j \<xi> - A j \<xi>) - (Sq i \<xi> - A i \<xi>)) \<omega> = 0"
    unfolding rearr by auto
qed

end
