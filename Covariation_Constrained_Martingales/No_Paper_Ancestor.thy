(*<*)
theory No_Paper_Ancestor
  imports
    Dynamic_Programming_Principle Covariation_Class_Marginals
begin

text \<open>Fails the build if a theory of the viscosity library, of the equation
  or paper sessions, or of complex analysis becomes an ancestor of this
  session.\<close>

ML \<open>
  val forbidden = ["Second_Order_Viscosity_Analysis",
    "Relative_Arbitrage", "Relative_Arbitrage_Equation",
    "Relative_Arbitrage_Statement", "HOL-Complex_Analysis"];
  val ancestors = Theory.nodes_of \<^theory> |> map Context.theory_long_name;
  val _ = if exists (fn n => Long_Name.qualifier n = "Path_Space_Operations") ancestors
      andalso exists (fn n => Long_Name.qualifier n = "Wiener_Measure") ancestors
    then () else error "ancestor check is vacuous";
  val bad = filter (member (op =) forbidden o Long_Name.qualifier) ancestors;
  val _ = if null bad then () else error ("forbidden ancestors: " ^ commas bad);
\<close>

end
(*>*)
