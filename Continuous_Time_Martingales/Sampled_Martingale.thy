section \<open>Sampling a continuous-time martingale along a partition\<close>

(*<*)
theory Sampled_Martingale
  imports "Martingales.Martingale"
begin

(*>*)

text \<open>
  A continuous-time martingale sampled along a monotone partition
  \<open>t :: nat \<Rightarrow> real\<close> of nonnegative times is a discrete-time martingale for
  the sampled filtration \<open>\<lambda>k. F (t k)\<close>.  This is the bridge through which
  the discrete-time theory of \<open>Quadratic_Variation\<close> (the quadratic
  variation \<open>qvar\<close>, the compensated square, the Dynkin identity) applies to
  a continuous-time martingale along any partition.

  The AFP entry \<open>Martingales\<close> is index-generic: \<open>filtered_measure\<close> fixes an
  arbitrary order-topology index and the entry provides
  \<open>real_filtered_measure\<close>.  That is what makes the statement expressible.
\<close>
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
  The sampled filtration is a @{typ nat}-indexed filtered measure, the
  interface over which the discrete-time development
  (\<open>Quadratic_Variation\<close>) is stated.
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

(*<*)
end
(*>*)
