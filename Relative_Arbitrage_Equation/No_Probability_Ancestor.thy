(*<*)
theory No_Probability_Ancestor
  imports
    Eigenvalue_Bound_Exact Comparison_Instance Subspace_Tangential_Field
begin

text \<open>Fails the build if a theory of a probability session, or of the paper
  session, becomes an ancestor of this session.\<close>

ML \<open>
  val forbidden = ["HOL-Probability", "Martingales", "Continuous_Time_Martingales",
    "Continuous_Path_Spaces", "Path_Space_Operations", "Wiener_Measure",
    "Relative_Arbitrage"];
  val ancestors = Theory.nodes_of \<^theory> |> map Context.theory_long_name;
  val _ = if exists (fn n => Long_Name.qualifier n = "Second_Order_Viscosity_Analysis") ancestors
    then () else error "ancestor check is vacuous";
  val bad = filter (member (op =) forbidden o Long_Name.qualifier) ancestors;
  val _ = if null bad then () else error ("probability ancestors: " ^ commas bad);
\<close>

end
(*>*)
