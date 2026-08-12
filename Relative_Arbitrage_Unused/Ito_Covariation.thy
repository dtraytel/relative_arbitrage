section \<open>The compensated-square martingale property from the covariation hypothesis\<close>

text \<open>
  This theory turns the \<open>Z_martingale\<close> assumption of \<open>locale ito_volatile_market\<close>
  into a THEOREM, derived from the paper's own defining hypothesis.

  Why this is the right thing to do, rather than trying to prove \<open>Z_martingale\<close>
  from the rest of that locale: in \<open>ito_volatile_market\<close> the process \<open>acov\<close> is a
  FREE PARAMETER, constrained only by \<open>acov_psd\<close>, \<open>acov_eigen_lb\<close>,
  \<open>acov_eigen_ub\<close> and \<open>acov_trace_integrable\<close>. None of those ties \<open>acov\<close> to the
  covariation of \<open>X\<close>, so \<open>Z_martingale\<close> is not a consequence of them -- it is
  itself the formal content of the condition \<open>d<X_i,X_j>(t)/dt = a(t)\<close>.

  Checked against arXiv:2512.17702: that condition is imposed as part of the
  DEFINITION of the admissible family of laws (Eqs. (1.6)-(1.8)), and the \<open>d/dt\<close>
  notation carries absolute continuity of the covariation. So it is data, not
  something to be constructed, and no Doob-Meyer decomposition is involved.

  What is achieved here is therefore a reduction: \<open>Z_martingale\<close> follows from the
  covariation condition stated in its primitive CONDITIONAL form, with nothing
  assumed about the compensated process itself beyond adaptedness and
  integrability. Together with \<open>cond_exp_increment_sq\<close> of
  \<open>Sampled_Quadratic_Variation\<close> -- which identifies the conditional expectation of
  a squared increment with a conditional variance -- the hypothesis below is
  exactly the paper's defining condition.

  The import is \<open>Ito_Market\<close> together with \<open>Sampled_Martingale\<close>. Their only common
  ancestor is the session theory \<open>Martingales.Martingale\<close>, so this is not a
  diamond over a draft theory.
\<close>

theory Ito_Covariation
  imports "Relative_Arbitrage.Ito_Market" "Martingale_Sampling.Sampled_Martingale"
begin

text \<open>
  The covariation condition, in conditional form: the conditional expectation of an
  increment of \<open>|X|\<^sup>2\<close> agrees with that of the corresponding increment of
  \<open>\<integral> trace (acov)\<close>.
\<close>

definition cond_covariation ::
  "'a measure \<Rightarrow> (real \<Rightarrow> 'a measure)
     \<Rightarrow> (real \<Rightarrow> 'a \<Rightarrow> real^'n::finite) \<Rightarrow> (real \<Rightarrow> 'a \<Rightarrow> real^'n^'n) \<Rightarrow> bool"
  where
  "cond_covariation M F X acov \<longleftrightarrow>
     (\<forall>s u. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow>
        (AE \<omega> in M.
           cond_exp M (F s) (\<lambda>\<omega>. X u \<omega> \<bullet> X u \<omega> - X s \<omega> \<bullet> X s \<omega>) \<omega>
             = cond_exp M (F s)
                 (\<lambda>\<omega>. set_lebesgue_integral lborel {0..u} (\<lambda>r. trace (acov r \<omega>))
                      - set_lebesgue_integral lborel {0..s}
                          (\<lambda>r. trace (acov r \<omega>))) \<omega>))"

lemma cond_covariationD:
  assumes "cond_covariation M F X acov" and "0 \<le> s" and "s \<le> u"
  shows "AE \<omega> in M.
           cond_exp M (F s) (\<lambda>\<omega>. X u \<omega> \<bullet> X u \<omega> - X s \<omega> \<bullet> X s \<omega>) \<omega>
             = cond_exp M (F s)
                 (\<lambda>\<omega>. set_lebesgue_integral lborel {0..u} (\<lambda>r. trace (acov r \<omega>))
                      - set_lebesgue_integral lborel {0..s}
                          (\<lambda>r. trace (acov r \<omega>))) \<omega>"
  using assms unfolding cond_covariation_def by blast

text \<open>
  The reduction. This is exactly \<open>martingale_of_cond_increment\<close> instantiated at
  \<open>Sq t \<omega> = X t \<omega> \<bullet> X t \<omega>\<close> and
  \<open>A t \<omega> = \<integral>\<^bsub>{0..t}\<^esub> trace (acov \<cdot> \<omega>)\<close>, whose difference is \<open>ito_Z X acov\<close>.
\<close>

theorem Z_martingale_of_cond_covariation:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real^'n::finite"
    and acov :: "real \<Rightarrow> 'a \<Rightarrow> real^'n^'n"
  assumes sfm: "sigma_finite_filtered_measure M F (0::real)"
    and adapted: "adapted_process M F (0::real) (ito_Z X acov)"
    and sq_int: "\<And>t. 0 \<le> t \<Longrightarrow> integrable M (\<lambda>\<omega>. X t \<omega> \<bullet> X t \<omega>)"
    and comp_int: "\<And>t. 0 \<le> t \<Longrightarrow> integrable M
        (\<lambda>\<omega>. set_lebesgue_integral lborel {0..t} (\<lambda>r. trace (acov r \<omega>)))"
    and cov: "cond_covariation M F X acov"
  shows "martingale M F 0 (ito_Z X acov)"
proof -
  have ad: "adapted_process M F (0::real)
      (\<lambda>t \<omega>. X t \<omega> \<bullet> X t \<omega>
              - set_lebesgue_integral lborel {0..t} (\<lambda>r. trace (acov r \<omega>)))"
    using adapted unfolding ito_Z_def .
  have "martingale M F 0
      (\<lambda>t \<omega>. X t \<omega> \<bullet> X t \<omega>
              - set_lebesgue_integral lborel {0..t} (\<lambda>r. trace (acov r \<omega>)))"
  proof (rule martingale_of_cond_increment[OF sfm ad])
    show "integrable M (\<lambda>\<omega>. X t \<omega> \<bullet> X t \<omega>)" if "0 \<le> t" for t
      by (rule sq_int[OF that])
    show "integrable M
        (\<lambda>\<omega>. set_lebesgue_integral lborel {0..t} (\<lambda>r. trace (acov r \<omega>)))"
      if "0 \<le> t" for t
      by (rule comp_int[OF that])
    show "AE \<omega> in M.
        cond_exp M (F s) (\<lambda>\<omega>. X u \<omega> \<bullet> X u \<omega> - X s \<omega> \<bullet> X s \<omega>) \<omega>
          = cond_exp M (F s)
              (\<lambda>\<omega>. set_lebesgue_integral lborel {0..u} (\<lambda>r. trace (acov r \<omega>))
                   - set_lebesgue_integral lborel {0..s}
                       (\<lambda>r. trace (acov r \<omega>))) \<omega>"
      if "0 \<le> s" "s \<le> u" for s u
      by (rule cond_covariationD[OF cov that])
  qed
  thus ?thesis unfolding ito_Z_def .
qed

end
