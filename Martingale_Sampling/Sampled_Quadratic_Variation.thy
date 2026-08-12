section \<open>Quadratic variation of a continuous-time martingale along a partition\<close>

(*<*)
theory Sampled_Quadratic_Variation
  imports Quadratic_Variation Sampled_Martingale
begin

(*>*)

text \<open>
  The sampling bridge of @{theory Martingale_Sampling.Sampled_Martingale} turns a real-indexed
  martingale into a nat-indexed one; this theory uses that to discharge the
  three obligations of the locale \<open>sq_int_martingale\<close> for the sampled
  process, and thereby transfers the whole discrete quadratic-variation
  theory of @{theory Martingale_Sampling.Quadratic_Variation} to continuous time along an arbitrary
  monotone partition.

  The two results that matter downstream are the discrete Ito formula for the
  square function (\<open>qvar_compensates\<close>) and the energy identity
  (\<open>expectation_sq_qvar\<close>). Transferred, they say: along any partition of a
  continuous-time martingale, the compensated square is a martingale, and the
  second moment grows exactly by the expected sum of squared increments. The
  latter is the second-moment input that Eq. (2.7) of arXiv:2512.17702 needs,
  and the former is the quadratic Ito formula that the \<open>Z_martingale\<close> assumption
  of \<open>ito_volatile_market\<close> currently postulates.\<close>
subsection \<open>The sampled process is a square-integrable discrete martingale\<close>

theorem sq_int_martingale_sampled:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real" and t :: "nat \<Rightarrow> real"
  assumes X: "martingale M F (0::real) X"
    and t0: "\<And>k. 0 \<le> t k" and tmono: "mono t"
    and sq: "\<And>u. 0 \<le> u \<Longrightarrow> integrable M (\<lambda>\<omega>. (X u \<omega>)\<^sup>2)"
  shows "sq_int_martingale M (\<lambda>k. F (t k)) (\<lambda>k. X (t k))"
proof (intro sq_int_martingale.intro sq_int_martingale_axioms.intro)
  show "nat_sigma_finite_filtered_measure M (\<lambda>k. F (t k))"
    by (rule nat_filtered_of_sampled[OF X t0 tmono])
  show "martingale M (\<lambda>k. F (t k)) 0 (\<lambda>k. X (t k))"
    by (rule martingale_sampled[OF X t0 tmono])
  show "integrable M (\<lambda>\<omega>. (X (t n) \<omega>)\<^sup>2)" for n
    by (rule sq[OF t0])
qed

subsection \<open>The transferred results\<close>

text \<open>
  The quadratic variation of the sampled process along the partition, written out
  as the sum of squared increments over the partition intervals.
\<close>

lemma qvar_sampled_eq:
  "qvar (\<lambda>k. X (t k)) n \<omega>
     = (\<Sum>k<n. (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2)"
  by (simp add: qvar_def)

text \<open>
  The quadratic Ito formula, in continuous time along a partition: the
  compensated square of the sampled martingale is a martingale.
\<close>

theorem qvar_compensates_sampled:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real" and t :: "nat \<Rightarrow> real"
  assumes X: "martingale M F (0::real) X"
    and t0: "\<And>k. 0 \<le> t k" and tmono: "mono t"
    and sq: "\<And>u. 0 \<le> u \<Longrightarrow> integrable M (\<lambda>\<omega>. (X u \<omega>)\<^sup>2)"
  shows "martingale M (\<lambda>k. F (t k)) 0
           (\<lambda>n \<omega>. (X (t n) \<omega>)\<^sup>2
                    - (\<Sum>k<n. (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2))"
proof -
  interpret S: sq_int_martingale M "\<lambda>k. F (t k)" "\<lambda>k. X (t k)"
    by (rule sq_int_martingale_sampled[OF X t0 tmono sq])
  have "martingale M (\<lambda>k. F (t k)) 0
          (\<lambda>n \<omega>. (X (t n) \<omega>)\<^sup>2 - qvar (\<lambda>k. X (t k)) n \<omega>)"
    by (rule S.qvar_compensates)
  thus ?thesis by (simp add: qvar_sampled_eq)
qed

text \<open>
  The energy identity: along any partition, the second moment of a
  continuous-time martingale grows exactly by the expected sum of squared
  increments. This is the second-moment input of Eq. (2.7).
\<close>

theorem expectation_sq_sampled:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real" and t :: "nat \<Rightarrow> real"
  assumes X: "martingale M F (0::real) X"
    and t0: "\<And>k. 0 \<le> t k" and tmono: "mono t"
    and sq: "\<And>u. 0 \<le> u \<Longrightarrow> integrable M (\<lambda>\<omega>. (X u \<omega>)\<^sup>2)"
  shows "(\<integral>\<omega>. (X (t n) \<omega>)\<^sup>2 \<partial>M)
           = (\<integral>\<omega>. (X (t 0) \<omega>)\<^sup>2 \<partial>M)
             + (\<integral>\<omega>. (\<Sum>k<n. (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2) \<partial>M)"
proof -
  interpret S: sq_int_martingale M "\<lambda>k. F (t k)" "\<lambda>k. X (t k)"
    by (rule sq_int_martingale_sampled[OF X t0 tmono sq])
  have "(\<integral>\<omega>. (X (t n) \<omega>)\<^sup>2 \<partial>M)
          = (\<integral>\<omega>. (X (t 0) \<omega>)\<^sup>2 \<partial>M)
            + (\<integral>\<omega>. qvar (\<lambda>k. X (t k)) n \<omega> \<partial>M)"
    by (rule S.expectation_sq_qvar)
  thus ?thesis by (simp add: qvar_sampled_eq)
qed

subsection \<open>The conditional increment identity\<close>

text \<open>
  Specialising the partition to the two points @{term s} and @{term u} turns
  the energy identity into its conditional form: the conditional variance of
  an increment is the increment of the conditional second moment. This is
  the identity that connects a martingale to its covariation without any
  reference to a stochastic integral.
\<close>

theorem cond_exp_increment_sq:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real"
  assumes X: "martingale M F (0::real) X"
    and sq: "\<And>v. 0 \<le> v \<Longrightarrow> integrable M (\<lambda>\<omega>. (X v \<omega>)\<^sup>2)"
    and s: "0 \<le> s" and su: "s \<le> u"
  shows "AE \<omega> in M. cond_exp M (F s) (\<lambda>\<omega>. (X u \<omega> - X s \<omega>)\<^sup>2) \<omega>
                     = cond_exp M (F s) (\<lambda>\<omega>. (X u \<omega>)\<^sup>2) \<omega> - (X s \<omega>)\<^sup>2"
proof -
  define t where "t = (\<lambda>k::nat. if k = 0 then s else u)"
  have t0: "0 \<le> t k" for k unfolding t_def using s su by simp
  have tmono: "mono t"
  proof (rule monoI)
    fix k l :: nat assume "k \<le> l"
    thus "t k \<le> t l" unfolding t_def using su by (cases "k = 0"; cases "l = 0") auto
  qed
  text \<open>Note @{term "Suc 0"} rather than @{term "1::nat"}: simp normalises the
    literal, so an instance stated with \<open>1\<close> would not fire.\<close>
  have t_0: "t 0 = s" and t_1: "t (Suc 0) = u" unfolding t_def by simp_all

  interpret S: sq_int_martingale M "\<lambda>k. F (t k)" "\<lambda>k. X (t k)"
    by (rule sq_int_martingale_sampled[OF X t0 tmono sq])
  interpret Q: martingale M "\<lambda>k. F (t k)" 0
      "\<lambda>n \<omega>. (X (t n) \<omega>)\<^sup>2 - qvar (\<lambda>k. X (t k)) n \<omega>"
    by (rule S.qvar_compensates)

  have qint: "integrable M (\<lambda>\<omega>. qvar (\<lambda>k. X (t k)) (Suc 0) \<omega>)"
    by (rule S.qvar_integrable)
  have q1: "qvar (\<lambda>k. X (t k)) (Suc 0) \<omega> = (X u \<omega> - X s \<omega>)\<^sup>2" for \<omega>
    by (simp add: qvar_def t_0 t_1)
  have dint: "integrable M (\<lambda>\<omega>. (X u \<omega> - X s \<omega>)\<^sup>2)"
    using qint by (simp add: q1)

  have mart: "AE \<omega> in M.
      (X (t 0) \<omega>)\<^sup>2 - qvar (\<lambda>k. X (t k)) 0 \<omega>
        = cond_exp M (F (t 0))
            (\<lambda>\<omega>. (X (t (Suc 0)) \<omega>)\<^sup>2 - qvar (\<lambda>k. X (t k)) (Suc 0) \<omega>) \<omega>"
    by (rule Q.martingale_property) auto
  have lhs: "AE \<omega> in M. (X s \<omega>)\<^sup>2
      = cond_exp M (F s) (\<lambda>\<omega>. (X u \<omega>)\<^sup>2 - (X u \<omega> - X s \<omega>)\<^sup>2) \<omega>"
    using mart by (simp add: t_0 t_1 q1)

  have sfs: "sigma_finite_subalgebra M (F s)"
    using S.sigma_finite_subalgebra_F[OF order_refl] by (simp add: t_0)
  have split: "AE \<omega> in M.
      cond_exp M (F s) (\<lambda>\<omega>. (X u \<omega>)\<^sup>2 - (X u \<omega> - X s \<omega>)\<^sup>2) \<omega>
        = cond_exp M (F s) (\<lambda>\<omega>. (X u \<omega>)\<^sup>2) \<omega>
          - cond_exp M (F s) (\<lambda>\<omega>. (X u \<omega> - X s \<omega>)\<^sup>2) \<omega>"
    by (rule sigma_finite_subalgebra.cond_exp_diff
              [OF sfs sq[OF order_trans[OF s su]] dint])

  from lhs split show ?thesis by auto
qed


(*<*)
end
(*>*)
