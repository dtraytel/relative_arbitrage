(*<*)
theory No_Probability_Or_Paper_Ancestor
  imports
    Comparison_Two_Domain
begin

text \<open>Fails the build if a theory of a probability session, of the equation
  session (the operator of the paper and its envelopes), or of the paper
  sessions becomes an ancestor of this session.\<close>

ML \<open>
  val forbidden = ["HOL-Probability", "Martingales", "Continuous_Time_Martingales",
    "Continuous_Path_Spaces", "Path_Space_Operations", "Wiener_Measure",
    "Covariation_Constrained_Martingales", "Relative_Arbitrage_Equation",
    "Relative_Arbitrage", "Relative_Arbitrage_Statement"];
  val ancestors = Theory.nodes_of \<^theory> |> map Context.theory_long_name;
  val _ = if exists (fn n => Long_Name.qualifier n = "Second_Order_Viscosity_Analysis") ancestors
      andalso exists (fn n => Long_Name.qualifier n = "Semicontinuous_Analysis") ancestors
    then () else error "ancestor check is vacuous";
  val bad = filter (member (op =) forbidden o Long_Name.qualifier) ancestors;
  val _ = if null bad then () else error ("forbidden ancestors: " ^ commas bad);
\<close>

end
(*>*)
