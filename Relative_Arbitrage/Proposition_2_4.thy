section \<open>Proposition 2.4: the dynamic programming equality, with attainment\<close>

(*<*)
theory Proposition_2_4
  imports "Covariation_Constrained_Martingales.Dynamic_Programming_Principle" Control_Problem
begin
(*>*)

text \<open>Proposition 2.4 of \<^cite>\<open>LaiShkolnikovSoner\<close>, Eq. (2.9), for the
  horizon-\<open>T\<close> value \<open>exit_val\<close>: at a deterministic time \<open>0 \<le> r < T\<close>
  (\<open>exit_val_dpp\<close>) and at a path stopping time \<open>\<theta>\<close> with values in
  \<open>[0,T]\<close> (\<open>exit_val_dpp_time\<close>).  Every optimiser of the value function
  attains the supremum, so the supremum is a maximum.

  Both summands are read off the first piece: \<open>\<theta> \<and> \<tau>\<^sub>K\<close> is the exit time
  capped at \<open>\<theta>\<close>, and the indicator \<open>1\<^bsub>{\<theta> \<le> \<tau>\<^sub>K}\<^esub>\<close> is
  \<open>pexit \<theta> K \<dots> = \<theta> \<and> fst (\<omega> \<theta>) \<in> K\<close>, exact for the capped exit time and
  needing no path continuity.

  Each statement is the case \<open>S = sconstraint k L\<close> of the dynamic
  programming principle for an abstract constraint set, in
  @{theory Covariation_Constrained_Martingales.Dynamic_Programming_Principle}.

  What is not proved here.  The paper states (2.9) for \<open>v\<close> on \<open>[0,\<infinity>)\<close> at
  arbitrary stopping times of the natural filtration of \<open>X\<close>.  The transfer
  needs the identification of \<open>v\<close> with \<open>exit_val\<close> at large horizons, the
  transport of essential infima between the two classes, Galmarino's test for
  the coordinate filtration on continuous paths, and a limit argument for
  unbounded \<open>\<theta>\<close>.\<close>

lemma exit_val_dpp_ess_inf_mono_time:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and P :: "('n pairpath) measure" and \<theta> :: "'n pairpath \<Rightarrow> real"
  assumes T0: "0 \<le> T" and L1: "1 \<le> L" and Kc: "closed K"
    and P: "P \<in> exit_class k L T x"
    and th0: "\<And>\<omega>. 0 \<le> \<theta> \<omega>" and thT: "\<And>\<omega>. \<theta> \<omega> \<le> T"
  shows "ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))
      \<le> ess_inf_time P (\<lambda>\<omega>. pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
          + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
             then enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0))"
  unfolding exit_class_eq_covariation exit_val_eq_covariation_val
  by (rule covariation_val_dpp_ess_inf_mono_time[OF T0 sconstraint_bounds[OF order_trans[OF zero_le_one L1]]
        closed_sconstraint sconstraint_convex mat_1_rate_in_sconstraint[OF L1] Kc
        P[unfolded exit_class_eq_covariation] th0 thT])

theorem exit_val_dpp_le_time:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and \<theta> :: "'n pairpath \<Rightarrow> real"
  assumes T0: "0 \<le> T" and L1: "1 \<le> L" and Kc: "closed K"
    and th0: "\<And>\<omega>. 0 \<le> \<theta> \<omega>" and thT: "\<And>\<omega>. \<theta> \<omega> \<le> T"
  shows "exit_val k L T K x
      \<le> (SUP P \<in> exit_class k L T x. ess_inf_time P
          (\<lambda>\<omega>. pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
            + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
               then enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0)))"
  unfolding exit_class_eq_covariation exit_val_eq_covariation_val
  by (rule covariation_val_dpp_le_time[OF T0 sconstraint_bounds[OF order_trans[OF zero_le_one L1]]
        closed_sconstraint sconstraint_convex mat_1_rate_in_sconstraint[OF L1] Kc th0 thT])

lemma exit_val_dpp_ess_inf_mono:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and P :: "('n pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T" and L1: "1 \<le> L" and Kc: "closed K"
    and P: "P \<in> exit_class k L T x"
  shows "ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))
      \<le> ess_inf_time P (\<lambda>\<omega>. pexit r K (\<lambda>t. fst (\<omega> t))
          + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
             then enn2real (exit_val k L (T - r) K (fst (\<omega> r))) else 0))"
  unfolding exit_class_eq_covariation exit_val_eq_covariation_val
  by (rule covariation_val_dpp_ess_inf_mono[OF r rT sconstraint_bounds[OF order_trans[OF zero_le_one L1]]
        closed_sconstraint sconstraint_convex mat_1_rate_in_sconstraint[OF L1] Kc
        P[unfolded exit_class_eq_covariation]])

theorem exit_val_dpp:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
  assumes r: "0 \<le> r" and rT: "r < T" and L1: "1 \<le> L" and Kc: "closed K"
  shows "exit_val k L T K x
      = (SUP P \<in> exit_class k L T x. ess_inf_time P
          (\<lambda>\<omega>. pexit r K (\<lambda>t. fst (\<omega> t))
            + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
               then enn2real (exit_val k L (T - r) K (fst (\<omega> r))) else 0)))"
  unfolding exit_class_eq_covariation exit_val_eq_covariation_val
  by (rule covariation_val_dpp[OF r rT sconstraint_bounds[OF order_trans[OF zero_le_one L1]]
        closed_sconstraint sconstraint_convex mat_1_rate_in_sconstraint[OF L1] Kc])

theorem exit_val_dpp_optimizer:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and P :: "('n pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r < T" and L1: "1 \<le> L" and Kc: "closed K"
    and P: "P \<in> exit_class k L T x"
    and opt: "ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))) = exit_val k L T K x"
  shows "ess_inf_time P (\<lambda>\<omega>. pexit r K (\<lambda>t. fst (\<omega> t))
            + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
               then enn2real (exit_val k L (T - r) K (fst (\<omega> r))) else 0))
      = exit_val k L T K x"
  unfolding exit_class_eq_covariation exit_val_eq_covariation_val
  by (rule covariation_val_dpp_optimizer[OF r rT sconstraint_bounds[OF order_trans[OF zero_le_one L1]]
        closed_sconstraint sconstraint_convex mat_1_rate_in_sconstraint[OF L1] Kc
        P[unfolded exit_class_eq_covariation] opt[unfolded exit_val_eq_covariation_val]])

corollary exit_val_dpp_attained:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
  assumes r: "0 \<le> r" and rT: "r < T" and L1: "1 \<le> L" and Kc: "closed K"
  shows "\<exists>P \<in> exit_class k L T x.
      ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))) = exit_val k L T K x
    \<and> ess_inf_time P (\<lambda>\<omega>. pexit r K (\<lambda>t. fst (\<omega> t))
            + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
               then enn2real (exit_val k L (T - r) K (fst (\<omega> r))) else 0))
      = exit_val k L T K x"
  unfolding exit_class_eq_covariation exit_val_eq_covariation_val
  by (rule covariation_val_dpp_attained[OF r rT sconstraint_bounds[OF order_trans[OF zero_le_one L1]]
        closed_sconstraint sconstraint_convex mat_1_rate_in_sconstraint[OF L1] Kc])

theorem exit_val_dpp_time:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and \<theta> :: "'n pairpath \<Rightarrow> real"
  assumes T0: "0 < T" and L1: "1 \<le> L" and Kc: "closed K"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
  shows "exit_val k L T K x
      = (SUP P \<in> exit_class k L T x. ess_inf_time P
          (\<lambda>\<omega>. pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
            + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
               then enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0)))"
  unfolding exit_class_eq_covariation exit_val_eq_covariation_val
  by (rule covariation_val_dpp_time[OF T0 sconstraint_bounds[OF order_trans[OF zero_le_one L1]]
        closed_sconstraint sconstraint_convex mat_1_rate_in_sconstraint[OF L1] Kc st thM])

theorem exit_val_dpp_time_optimizer:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and \<theta> :: "'n pairpath \<Rightarrow> real" and P :: "('n pairpath) measure"
  assumes T0: "0 < T" and L1: "1 \<le> L" and Kc: "closed K"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
    and P: "P \<in> exit_class k L T x"
    and opt: "ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))) = exit_val k L T K x"
  shows "ess_inf_time P (\<lambda>\<omega>. pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
            + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
               then enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0))
      = exit_val k L T K x"
  unfolding exit_class_eq_covariation exit_val_eq_covariation_val
  by (rule covariation_val_dpp_time_optimizer[OF T0 sconstraint_bounds[OF order_trans[OF zero_le_one L1]]
        closed_sconstraint sconstraint_convex mat_1_rate_in_sconstraint[OF L1] Kc st thM
        P[unfolded exit_class_eq_covariation] opt[unfolded exit_val_eq_covariation_val]])

corollary exit_val_dpp_time_attained:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and \<theta> :: "'n pairpath \<Rightarrow> real"
  assumes T0: "0 < T" and L1: "1 \<le> L" and Kc: "closed K"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
  shows "\<exists>P \<in> exit_class k L T x.
      ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))) = exit_val k L T K x
    \<and> ess_inf_time P (\<lambda>\<omega>. pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
            + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
               then enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0))
      = exit_val k L T K x"
  unfolding exit_class_eq_covariation exit_val_eq_covariation_val
  by (rule covariation_val_dpp_time_attained[OF T0 sconstraint_bounds[OF order_trans[OF zero_le_one L1]]
        closed_sconstraint sconstraint_convex mat_1_rate_in_sconstraint[OF L1] Kc st thM])

(*<*)
end
(*>*)
