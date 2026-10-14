section \<open>Criteria for integrability\<close>

(*<*)
theory Integrability_Criteria
  imports "HOL-Probability.Probability"
begin

(*>*)

text \<open>
  Small, frequently needed criteria that neither HOL-Probability nor the
  AFP's \<open>Martingales\<close> states: when a clamped or tail-truncated function
  is integrable, and positivity of an integral from almost-everywhere
  positivity.
\<close>

text \<open>\<open>weak_conv_integral_of_L2_bound\<close> asks, besides the \<open>L\<^sup>2\<close> bound
  itself, for integrability of the clamped and of the tail-truncated
  integrand under every law involved.  Neither depends on the path space:
  a clamp is bounded, and a tail truncation is dominated by \<open>\<bar>f\<bar>\<close>.\<close>

lemma clamp_integrable:
  fixes f :: "'a \<Rightarrow> real"
  assumes P: "finite_measure N" and m: "f \<in> borel_measurable N"
  shows "integrable N (\<lambda>w. max (- R) (min R (f w)))"
proof (rule finite_measure.integrable_const_bound[OF P, where B = "\<bar>R\<bar>"])
  show "(\<lambda>w. max (- R) (min R (f w))) \<in> borel_measurable N"
    using m by measurable
qed (auto intro: AE_I2)

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

lemma integral_pos_of_AE_pos:
  fixes f :: "'a \<Rightarrow> real"
  assumes PP: "prob_space N" and im: "integrable N f"
    and pos: "AE \<omega> in N. 0 < f \<omega>"
  shows "0 < (\<integral>\<omega>. f \<omega> \<partial>N)"
proof -
  have nn: "AE \<omega> in N. 0 \<le> f \<omega>" using pos by eventually_elim simp
  have "(\<integral>\<omega>. f \<omega> \<partial>N) \<noteq> 0"
  proof
    assume "(\<integral>\<omega>. f \<omega> \<partial>N) = 0"
    with pos have "AE \<omega> in N. False"
      unfolding integral_nonneg_eq_0_iff_AE[OF im nn] by eventually_elim simp
    then show False using prob_space.AE_False[OF PP] by simp
  qed
  with integral_nonneg_AE[OF nn] show ?thesis by simp
qed

(*<*)
end
(*>*)
