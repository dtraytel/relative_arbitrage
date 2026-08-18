section \<open>The jet interface to Definition 3.1\<close>

(*<*)
theory Comparison_Jets
  imports "Second_Order_Viscosity_Analysis.Soft_Penalty" Operator_Envelope_Continuity
    "Continuous_Time_Martingales.Integrability_Criteria"
    "Second_Order_Viscosity_Analysis.Doubling_Of_Variables"
    "Semicontinuous_Analysis.Semicontinuity"
    "Symmetric_Matrix_Spectra.Matrix_Algebra"
begin

(*>*)

text \<open>\<open>Theorem_On_Sums\<close> and the theories below it develop the jet
  machinery independently of this development, directly over
  \<open>HOL-Analysis.Analysis\<close>.  This theory combines it with
  @{theory Relative_Arbitrage.Operator_Envelope_Continuity} to package the
  derivative facts into \<open>test_fun_at\<close>, and states Definition 3.1 with the
  paper's own \<open>C\<^sup>2\<close> test functions.\<close>

text \<open>\<open>Theorem_On_Sums\<close> and the theories below it develop the jet
  machinery independently of this development, directly over
  \<open>HOL-Analysis.Analysis\<close>.  This theory combines it with
  @{theory Relative_Arbitrage.Operator_Envelope_Continuity} to package the
  derivative facts into \<open>test_fun_at\<close>, and states Definition 3.1 with the
  paper's own \<open>C\<^sup>2\<close> test functions.\<close>

text \<open>@{theory Second_Order_Viscosity_Analysis.Theorem_On_Sums} and the theories
  below it develop the jet machinery
  independently of this development, directly over \<open>HOL-Analysis.Analysis\<close>.  This
  theory combines it with @{theory Relative_Arbitrage.Operator_Envelope_Continuity}
  to package the derivative facts into \<open>test_fun_at\<close> and discharge
  \<open>max_principle_boundary\<close>.\<close>

subsection \<open>A jet gives a test function\<close>










end
(*>*)
