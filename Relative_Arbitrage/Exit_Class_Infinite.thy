section \<open>The paper's class and value function on the half-line\<close>

(*<*)
theory Exit_Class_Infinite
  imports
    "Covariation_Constrained_Martingales.Covariation_Class_Infinite" Exit_Class
begin
(*>*)

text \<open>Eq. (1.6)--(1.7) of \<^cite>\<open>LaiShkolnikovSoner\<close> without the horizon cap is the
  class @{const icovariation_class} on the half-line at the constraint set \<open>sconstraint k L\<close>.\<close>

subsection \<open>The paper's class on the half-line\<close>

definition iexit_class ::
  "nat \<Rightarrow> real \<Rightarrow> real^'n::finite \<Rightarrow> (('n pairpath) measure) set"
  where
  "iexit_class k L x = {P.
     prob_space P \<and>
     sets P = sets (ipath_space :: ('n pairpath) measure) \<and>
     (AE \<omega> in P. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0) \<and>
     (AE \<omega> in P. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L) \<and>
     martingale P (natural_filtration P 0 (\<lambda>t \<omega>. \<omega> t)) 0
       (\<lambda>t \<omega>. fst (\<omega> t)) \<and>
     martingale P (natural_filtration P 0 (\<lambda>t \<omega>. \<omega> t)) 0
       (\<lambda>t \<omega>. outerp (fst (\<omega> t)) - snd (\<omega> t))}"

definition iexit_val ::
  "nat \<Rightarrow> real \<Rightarrow> (real^'n::finite) set \<Rightarrow> real^'n \<Rightarrow> ennreal"
  where
  "iexit_val k L K x =
     Sup ((\<lambda>Q. ess_inf Q (\<lambda>\<omega>. iexit K (\<lambda>t. fst (\<omega> t)))) ` iexit_class k L x)"

theorem iexit_class_eq_icovariation:
  "iexit_class k L x = icovariation_class (sconstraint k L) x"
  by (simp add: iexit_class_def icovariation_class_def)

theorem iexit_val_eq_icovariation_val:
  "iexit_val k L K x = icovariation_val (sconstraint k L) K x"
  by (simp add: iexit_val_def icovariation_val_def iexit_class_eq_icovariation)

text \<open>For the paper's constraint set the rate \<open>\<sigma> = I\<close> is admissible for
  \<open>L \<ge> 1\<close> and the trace is at least \<open>n - k\<close>
  (@{thm [source] sconstraint_trace_ge}).\<close>

corollary iexit_val_eq_exit_val_ball:
  fixes K :: "(real^'n::finite) set" and rK :: real
  assumes k: "k < CARD('n)" and L: "1 \<le> L" and Kc: "closed K"
    and KB: "K \<subseteq> cball 0 rK"
    and big: "rK * rK / real (CARD('n) - k) < T"
  shows "iexit_val k L K x = exit_val k L T K x"
  unfolding iexit_val_eq_icovariation_val exit_val_eq_covariation_val
  by (rule icovariation_val_eq_covariation_val_ball[OF closed_sconstraint sconstraint_convex
        mat_1_rate_in_sconstraint[OF L] sconstraint_trace_bounds[OF k order_trans[OF zero_le_one L]]
        Kc KB big])

corollary iexit_val_eq_exit_val_horizon:
  fixes K :: "(real^'n::finite) set" and rK :: real
  assumes k: "k < CARD('n)" and L: "1 \<le> L" and Kc: "closed K"
    and KB: "K \<subseteq> cball 0 rK"
  obtains T where "0 < T" and "rK * rK / real (CARD('n) - k) < T"
    and "2 * (rK * rK) / real (CARD('n) - k) < T"
    and "iexit_val k L K = exit_val k L T K"
proof -
  obtain T where T: "0 < T" "rK * rK / real (CARD('n) - k) < T"
      "2 * (rK * rK) / real (CARD('n) - k) < T"
    and eq: "icovariation_val (sconstraint k L) K = covariation_val (sconstraint k L) T K"
    by (rule icovariation_val_eq_covariation_val_horizon[OF closed_sconstraint
          sconstraint_convex mat_1_rate_in_sconstraint[OF L]
          sconstraint_trace_bounds[OF k order_trans[OF zero_le_one L]] Kc KB])
  have "iexit_val k L K = exit_val k L T K"
    using eq by (simp add: fun_eq_iff iexit_val_eq_icovariation_val exit_val_eq_covariation_val)
  then show ?thesis by (rule that[OF T])
qed

(*<*)
end
(*>*)
