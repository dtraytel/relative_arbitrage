(* Semantic analysis behind notes/REVIEW_3.md.  Not part of any session.
   Load it in a PIDE session whose base is Relative_Arbitrage_Statement
   (isabelle jedit -d . -l Relative_Arbitrage_Statement, or the PIDE MCP server);
   set OUT below to an existing directory.  It writes facts.tsv (every user fact
   with its theory, line, kind, whether the deliverables use it, its direct named
   dependencies and the constants of its statement), dep_thys.tsv, const_thys.tsv,
   user_consts.tsv, clones.tsv (higher-order matching against every proper fact
   in scope) and thy_parents.tsv.  The Python scripts beside it post-process them. *)
theory Review_Analysis
  imports "Relative_Arbitrage_Statement.Paper_Readings"
    "Second_Order_Viscosity_Analysis.Crandall_Ishii_Sums"
begin

thm theorem_1_1

ML \<open>
val roots0 = [@{thm theorem_1_1}, @{thm example_3_1_closed_form}];
val oras = Thm_Deps.all_oracles roots0;
writeln ("oracles: " ^ string_of_int (length oras));
\<close>

ML \<open>
structure A1 =
struct
val thy = @{theory};
val ctxt = @{context};
val outdir = "/tmp/review_3_out/";  (* OUT: must exist *)
val user_sessions = ["Symmetric_Matrix_Spectra","Semicontinuous_Analysis",
  "Second_Order_Viscosity_Analysis","Wiener_Measure","Continuous_Time_Martingales",
  "Continuous_Path_Spaces","Relative_Arbitrage","Relative_Arbitrage_Statement"];
fun sess_of_thyname s = hd (space_explode "." s);
fun is_user_thyname s = member (op =) user_sessions (sess_of_thyname s);

val facts = Global_Theory.facts_of thy;
val fspace = Facts.space_of facts;
fun fact_thy name = #theory_long_name (Name_Space.the_entry fspace name) handle ERROR _ => "?";
fun fact_line name = the_default 0 (Position.line_of (Name_Space.the_entry_pos fspace name)) handle ERROR _ => 0;

val transfer = Global_Theory.transfer_theories thy;
val all_facts = Facts.dest_static false [] facts |> map (apsnd (map transfer));
val user_facts = filter (fn (n, _) => is_user_thyname (fact_thy n)) all_facts;
fun proper (n, ths) = exists (fn th => #1 (Thm.derivation_name th) = n) ths;
val proper_user = filter proper user_facts;

(* The roots: every line of roots.txt (next to this file) that is not blank and
   does not start with '#' names a fact, or "Session.Theory.*" for every proper
   fact of that theory.  Dead-code passes run against these roots only. *)
val rootsfile = "/home/user/relative_arbitrage/notes/review_3/roots.txt";  (* ROOTS *)
val root_lines = File.read_lines (Path.explode rootsfile)
  |> map (fn l => (case space_explode "#" l of [] => "" | x :: _ => x) |> Symbol.trim_blanks)
  |> filter (fn l => l <> "");
fun expand l =
  if String.isSuffix ".*" l then
    let val th = String.substring (l, 0, size l - 2)
    in proper_user |> filter (fn (n, _) => fact_thy n = th) |> map #1 end
  else [l];
val root_names = maps expand root_lines |> distinct (op =);
val roots = maps (Global_Theory.get_thms thy) root_names;
val used = Proofterm.fold_body_thms
  (fn {thm_name = a, ...} => not (Thm_Name.is_empty a) ? Symtab.insert_set (#1 a))
  (Thm.proof_bodies_of roots) Symtab.empty;

fun direct_deps ths = Thm_Deps.thm_deps thy ths |> map (#1 o #2) |> distinct (op =);
fun kind_of ths = Thm.legacy_get_kind (hd ths);
val cspace = Sign.const_space thy;
fun const_thy c = #theory_long_name (Name_Space.the_entry cspace c) handle ERROR _ => "?";
end;

val _ = File.write (Path.explode (A1.outdir ^ "summary.txt"))
  ("roots: " ^ string_of_int (length A1.roots) ^ "\n" ^
   "oracles in the roots' proofs: " ^ string_of_int (length (Thm_Deps.all_oracles A1.roots)) ^ "\n" ^
   "user facts: " ^ string_of_int (length A1.proper_user) ^ "\n" ^
   "names in the closure of the roots: " ^ string_of_int (Symtab.size A1.used) ^ "\n");
val _ = writeln ("all facts: " ^ string_of_int (length A1.all_facts) ^ ", user facts: " ^
  string_of_int (length A1.user_facts) ^ ", proper user facts: " ^ string_of_int (length A1.proper_user) ^
  ", names in closure: " ^ string_of_int (Symtab.size A1.used));
\<close>

ML \<open>
local open A1 in
val _ =
  let
    val lines = proper_user |> map (fn (n, ths) =>
      let
        val t = fact_thy n
        val deps = direct_deps ths |> filter (fn d => d <> n)
        val consts = fold (Term.add_const_names o Thm.prop_of) ths []
      in
        space_implode "\t" [sess_of_thyname t, t, n, string_of_int (fact_line n), kind_of ths,
          if Symtab.defined used n then "USED" else "unused",
          space_implode " " deps, space_implode " " consts]
      end)
    val _ = File.write (Path.explode (outdir ^ "facts.tsv")) (cat_lines lines ^ "\n")
    val dep_names = fold (fn (_, ths) => fold (insert (op =)) (direct_deps ths)) proper_user []
    val _ = File.write (Path.explode (outdir ^ "dep_thys.tsv"))
      (cat_lines (map (fn d => d ^ "\t" ^ fact_thy d) dep_names) ^ "\n")
    val const_names = fold (fn (_, ths) => fold (Term.add_const_names o Thm.prop_of) ths) proper_user []
    val _ = File.write (Path.explode (outdir ^ "const_thys.tsv"))
      (cat_lines (map (fn c => c ^ "\t" ^ const_thy c) const_names) ^ "\n")
    val closure_consts = Proofterm.fold_body_thms
      (fn {prop, ...} => Term.add_const_names prop) (Thm.proof_bodies_of roots)
      (fold (Term.add_const_names o Thm.prop_of) roots [])
    val user_consts = #constants (Consts.dest (Sign.consts_of thy))
      |> map #1 |> filter (is_user_thyname o const_thy)
    val _ = File.write (Path.explode (outdir ^ "user_consts.tsv"))
      (cat_lines (map (fn c => c ^ "\t" ^ const_thy c ^ "\t" ^
         (if member (op =) closure_consts c then "USED" else "unused")) user_consts) ^ "\n")
  in writeln ("wrote facts.tsv: " ^ string_of_int (length lines) ^ " rows; user consts " ^
       string_of_int (length user_consts)) end
end
\<close>

ML \<open>
structure A2 =
struct
open A1
fun norm_thm th = (Object_Logic.rulify ctxt th handle THM _ => th)
  |> Thm.prop_of |> Envir.beta_eta_contract;
fun freeze t = t
  |> Term.map_aterms (fn Var ((x, i), T) => Free ("z_" ^ x ^ "_" ^ string_of_int i, T) | a => a)
  |> Term.map_types (Term.map_type_tvar (fn ((a, i), S) => TFree (a ^ "_" ^ string_of_int i, S)));
fun trivial_pat t =
  (case Logic.strip_imp_concl t of Var _ => true | _ $ Var _ => true | _ => false);
fun try_match pat obj =
  SOME (Pattern.match thy (pat, obj) (Vartab.empty, Vartab.empty))
    handle Pattern.MATCH => NONE | Pattern.Pattern => NONE | TYPE _ => NONE | TERM _ => NONE;
val all_proper = filter proper all_facts;
val gen_items = all_proper |> maps (fn (n, ths) =>
    map_index (fn (i, th) => (n, i, norm_thm th)) ths)
  |> filter (fn (_, _, p) => not (trivial_pat p) andalso
       subset (op =) (fold Term.add_var_names (Logic.strip_imp_prems p) [],
                      Term.add_var_names (Logic.strip_imp_concl p) []));
val net = fold (fn it as (_, _, p) => Net.insert_term (K false) (Logic.strip_imp_concl p, it))
  gen_items Net.empty;
fun premise_ok (tyenv, tenv) prems_g prems_u =
  let val inst = Envir.norm_term (Envir.Envir {maxidx = 1000, tenv = tenv, tyenv = tyenv})
  in forall (fn pg => exists (fn pu => (inst pg) aconv pu) prems_u) prems_g end;
fun clones_of (n, ths) =
  let
    val deps = direct_deps ths
    fun one (i, th) =
      let
        val pu0 = norm_thm th
        val pu = freeze pu0
        val cu = Logic.strip_imp_concl pu
        val prems_u = Logic.strip_imp_prems pu
      in
        Net.match_term net cu |> map_filter (fn (gn, gi, pg) =>
          if gn = n then NONE else
          (case try_match (Logic.strip_imp_concl pg) cu of
            NONE => NONE
          | SOME env =>
              if premise_ok env (Logic.strip_imp_prems pg) prems_u then
                let
                  val exact = is_some (try_match pg pu) andalso
                    length (Logic.strip_imp_prems pg) = length prems_u
                  val mutual = exact andalso is_some (try_match pu0 (freeze pg))
                in SOME (string_of_int i, gn, string_of_int gi,
                         if mutual then "EQUIV" else if exact then "INSTANCE" else "WEAKER-PREMS",
                         if member (op =) deps gn then "dep" else "nodep") end
              else NONE))
      end
  in maps one (map_index I ths) end;
end;
val _ = writeln ("indexed generalisers: " ^ string_of_int (length A2.gen_items));
\<close>

ML \<open>
local open A1 A2 in
val _ =
  let
    val clone_lines = proper_user |> maps (fn f as (n, _) =>
      map (fn (i, gn, gi, k, d) =>
        space_implode "\t" [fact_thy n, n, i, string_of_int (fact_line n), fact_thy gn, gn, gi, k, d,
          if is_user_thyname (fact_thy gn) then "user" else "lib",
          if Symtab.defined used n then "USED" else "unused"]) (clones_of f handle ERROR _ => []))
    val _ = File.write (Path.explode (outdir ^ "clones.tsv")) (cat_lines clone_lines ^ "\n")
  in writeln ("clone pairs: " ^ string_of_int (length clone_lines)) end
end
\<close>

ML \<open>
val _ =
  let
    val nodes = Theory.nodes_of @{theory}
    val lines = nodes |> map (fn t => Context.theory_long_name t ^ "\t" ^
      space_implode " " (map Context.theory_long_name (Theory.parents_of t)))
  in File.write (Path.explode (A1.outdir ^ "thy_parents.tsv")) (cat_lines lines ^ "\n");
     writeln ("theories: " ^ string_of_int (length lines)) end
\<close>

end
