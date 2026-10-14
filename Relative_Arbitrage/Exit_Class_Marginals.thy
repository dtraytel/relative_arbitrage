section \<open>The paper's class of laws of \<open>X\<close>\<close>

(*<*)
theory Exit_Class_Marginals
  imports
    "Covariation_Constrained_Martingales.Covariation_Class_Marginals" Exit_Class_Infinite
begin
(*>*)

text \<open>The paper's class \<open>P\<^sub>x\<close> of Eq. (1.7) and its value function (1.6) are
  the instance \<open>S = sconstraint k L\<close>.\<close>

definition xclass ::
  "nat \<Rightarrow> real \<Rightarrow> real^'n::finite \<Rightarrow> ((real \<Rightarrow> real^'n) measure) set"
  where
  "xclass k L x = {Q.
     prob_space Q \<and>
     sets Q = sets (ipath_space :: ((real \<Rightarrow> real^'n) measure)) \<and>
     (AE w in Q. w 0 = x) \<and>
     martingale Q (natural_filtration Q 0 (\<lambda>t w. w t)) 0 (\<lambda>t w. w t) \<and>
     (\<exists>A. (AE w in Q. A 0 w = 0) \<and>
          martingale Q (natural_filtration Q 0 (\<lambda>t w. w t)) 0
            (\<lambda>t w. outerp (w t) - A t w) \<and>
          (AE w in Q. density_cond (\<lambda>t. A t w) (sconstraint k L)))}"

definition xval ::
  "nat \<Rightarrow> real \<Rightarrow> (real^'n::finite) set \<Rightarrow> real^'n \<Rightarrow> ennreal"
  where
  "xval k L K x = Sup ((\<lambda>Q. ess_inf Q (iexit K)) ` xclass k L x)"

theorem xclass_eq_xcovariation:
  "xclass k L x = xcovariation_class (sconstraint k L) x"
  by (simp add: xclass_def xcovariation_class_def)

theorem xval_eq_xcovariation_val:
  "xval k L K x = xcovariation_val (sconstraint k L) K x"
  by (simp add: xval_def xcovariation_val_def xclass_eq_xcovariation)

subsection \<open>The paper's classes\<close>

text \<open>For \<open>S = sconstraint k L\<close> the entry bound is \<open>D = L\<close>
  (@{thm [source] sconstraint_psd_entry}).\<close>

theorem iexit_class_marginal_in_xclass:
  fixes P :: "('n::finite pairpath) measure"
  assumes P: "P \<in> iexit_class k L x" and L: "0 \<le> L"
  shows "ipath_law P (\<lambda>t \<omega>. fst (\<omega> t)) \<in> xclass k L x"
  unfolding xclass_eq_xcovariation
  by (rule icovariation_class_marginal_in_xcovariation_class[OF closed_sconstraint
        sconstraint_convex sconstraint_psd_entry(1) L sconstraint_psd_entry(2)
        P[unfolded iexit_class_eq_icovariation]])

theorem xclass_lift_in_iexit_class:
  fixes Q :: "((real \<Rightarrow> real^'n::finite) measure)"
  assumes Q: "Q \<in> xclass k L x" and L: "0 \<le> L"
  shows "ipath_law Q (\<lambda>t w. (w t, qvmata (4 * L) w t)) \<in> iexit_class k L x"
  unfolding iexit_class_eq_icovariation
  by (rule xcovariation_class_lift_in_icovariation_class[OF closed_sconstraint
        sconstraint_convex sconstraint_psd_entry(1) L sconstraint_psd_entry(2)
        Q[unfolded xclass_eq_xcovariation]])

theorem iexit_val_eq_xval:
  fixes K :: "(real^'n::finite) set"
  assumes K: "closed K" and L: "0 \<le> L"
  shows "iexit_val k L K x = (xval k L K x :: ennreal)"
  unfolding iexit_val_eq_icovariation_val xval_eq_xcovariation_val
  by (rule icovariation_val_eq_xcovariation_val[OF closed_sconstraint
        sconstraint_convex sconstraint_psd_entry(1) L sconstraint_psd_entry(2) K])

(*<*)
end
(*>*)
