section \<open>Tail bounds from the fourth-moment estimate\<close>

(*<*)
theory Increment_Tails
  imports Increment_Moments
begin

(*>*)

text \<open>
  The quantitative tail estimates that turn Eq. (2.7) into tightness. The
  AFP's Kolmogorov-Chentsov theorem produces a continuous modification but
  not the tail bound on the modulus of continuity that Lemma 2.2 of
  \<^cite>\<open>LaiShkolnikovSoner\<close> needs; that bound is assembled here from Markov's
  inequality and a union bound over one partition level. The chaining over
  dyadic levels is the following step.
\<close>
subsection \<open>Markov's inequality at the fourth power\<close>

lemma abs_pow4: "\<bar>x::real\<bar>^4 = x^4"
proof -
  have "\<bar>x\<bar>^4 = (\<bar>x\<bar>\<^sup>2)\<^sup>2" by algebra
  also have "\<dots> = (x\<^sup>2)\<^sup>2" by simp
  also have "\<dots> = x^4" by algebra
  finally show ?thesis .
qed

lemma fourth_moment_tail:
  fixes f :: "'a \<Rightarrow> real"
  assumes P: "prob_space M"
    and fm[measurable]: "f \<in> borel_measurable M"
    and f4: "integrable M (\<lambda>\<omega>. (f \<omega>)^4)"
    and l: "0 < l"
  shows "measure M {\<omega> \<in> space M. l \<le> \<bar>f \<omega>\<bar>} \<le> (\<integral>\<omega>. (f \<omega>)^4 \<partial>M) / l^4"
proof -
  have seteq: "{\<omega> \<in> space M. l \<le> \<bar>f \<omega>\<bar>} = {\<omega> \<in> space M. l^4 \<le> (f \<omega>)^4}"
  proof (intro Collect_cong conj_cong refl iffI)
    fix \<omega>
    assume "l \<le> \<bar>f \<omega>\<bar>"
    hence "l^4 \<le> \<bar>f \<omega>\<bar>^4" using l by (intro power_mono) simp_all
    thus "l^4 \<le> (f \<omega>)^4" by (simp add: abs_pow4)
  next
    fix \<omega>
    assume "l^4 \<le> (f \<omega>)^4"
    hence h4: "l ^ Suc 3 \<le> \<bar>f \<omega>\<bar> ^ Suc 3"
      by (simp add: abs_pow4 eval_nat_numeral)
    show "l \<le> \<bar>f \<omega>\<bar>" by (rule power_le_imp_le_base[OF h4 abs_ge_zero])
  qed
  have l4: "0 < l^4" using l by simp
  have "measure M {\<omega> \<in> space M. l^4 \<le> (f \<omega>)^4} \<le> (\<integral>\<omega>. (f \<omega>)^4 \<partial>M) / l^4"
  proof (rule integral_Markov_inequality_measure)
    show "integrable M (\<lambda>\<omega>. (f \<omega>)^4)" by (rule f4)
    show "space M \<in> sets M" by (rule sets.top)
    show "AE \<omega> in M. 0 \<le> (f \<omega>)^4" by (intro AE_I2 pow4_nonneg)
    show "0 < l^4" by (rule l4)
  qed
  thus ?thesis by (simp add: seteq)
qed

subsection \<open>The tail bound at one partition level\<close>

text \<open>
  The union bound over the increments of the \<open>m\<close>-th uniform partition. The
  bound decays like \<open>1 / Suc m\<close>: refining the partition by a factor halves
  the tail, which is what makes the dyadic chaining sum converge.
\<close>

(*<*)
end
(*>*)
