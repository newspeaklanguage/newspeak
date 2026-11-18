(* Ground regressions over the actual upstream elaborated SpecTec definitions
   of Emmanuel. This is a test driver, not the normative semantics.

   Derived from formal-semantics/spectec/tools/regress.ml (Newspeak), with one
   extension: relation premises are solved MODE-DIRECTED. A relation's
   components left of its `=>` atom are inputs and must be ground; those to
   the right are outputs. A rule applies when its conclusion's inputs match,
   its premises hold in order (each premise may bind variables that later
   premises and the conclusion's outputs use), and its now-ground outputs
   match the caller's output pattern. All rules are tried, never first
   success: more than one solution is reported as overlapping derivations,
   so every regression also checks the determinism the LaTeX claims.
   Relations without `=>` have inputs only. Unresolved subgoals fail loudly. *)
open Util.Source
open Il.Ast

let failed message = failwith message

let () =
  try
    if Array.length Sys.argv < 3 then
      failed "usage: regress cases.tsv source.spectec ...";
    let files = Array.to_list Sys.argv |> List.tl |> List.tl in
    let el = List.concat_map Frontend.Parse.parse_file files in
    let il, elenv = Frontend.Elab.elab el in
    Il.Valid.valid il;
    let env = Il.Env.env_of_script il in
    let id name = name $ no_region in
    let expression text typ =
      Frontend.Elab.elab_exp elenv (Frontend.Parse.parse_exp text)
        (Frontend.Parse.parse_typ typ)
    in
    let ground exp = Il.Free.Set.is_empty (Il.Free.free_exp exp).varid in
    let rec normal exp = match exp.it with
      | BoolE _ | NumE _ | TextE _ -> true
      | ListE es | TupE es -> List.for_all normal es
      | OptE None -> true
      | OptE (Some e) | CaseE (_, e) | SubE (e, _, _) -> normal e
      | StrE fields -> List.for_all (fun (_, e) -> normal e) fields
      | _ -> false
    in
    let reduce = Il.Eval.reduce_exp env in
    (* As in the Newspeak driver: the pinned upstream matcher splits a
       known-suffix list at suffix length, not at total length minus suffix
       length (eval.ml, CatE right-ListE case). Emmanuel's mode stacks grow
       rightward, so correct just structural matching here. *)
    let rec match_value subst value pattern =
      let value = reduce value in
      let pattern = reduce (Il.Subst.subst_exp subst pattern) in
      match value.it, pattern.it with
      | ListE actual, CatE (prefix, ({it = ListE suffix; _} as tail))
          when List.length suffix <= List.length actual ->
        let left, right = Util.Lib.List.split
          (List.length actual - List.length suffix) actual in
        (match match_value subst {value with it = ListE left} prefix with
        | None -> None
        | Some subst -> match_value subst {value with it = ListE right} tail)
      | ListE actual, CatE (({it = ListE prefix; _} as head), tail)
          when List.length prefix <= List.length actual ->
        let left, right = Util.Lib.List.split (List.length prefix) actual in
        (match match_value subst {value with it = ListE left} head with
        | None -> None
        | Some subst -> match_value subst {value with it = ListE right} tail)
      | TupE actual, TupE expected | ListE actual, ListE expected ->
        match_values subst actual expected
      | StrE actual, StrE expected ->
        if List.length actual <> List.length expected ||
           not (List.for_all2 (fun (a, _) (b, _) -> Il.Eq.eq_atom a b) actual expected)
        then None else match_values subst (List.map snd actual) (List.map snd expected)
      | CaseE (op, actual), CaseE (op', expected) when Il.Eq.eq_mixop op op' ->
        match_value subst actual expected
      | _ -> Il.Eval.match_exp env subst value pattern
    and match_values subst actual expected =
      match actual, expected with
      | [], [] -> Some subst
      | actual :: rest, expected :: rest' ->
        (match match_value subst actual expected with
        | None -> None
        | Some subst -> match_values subst rest rest')
      | _ -> None
    in
    (* Number of relation components before the `=>` atom. *)
    let input_count mixop =
      let rec flat = function
        | Xl.Mixop.Arg _ -> [`Arg]
        | Xl.Mixop.Atom a -> [`Atom a]
        | Xl.Mixop.Brack (a, m, b) -> `Atom a :: flat m @ [`Atom b]
        | Xl.Mixop.Infix (m1, a, m2) -> flat m1 @ (`Atom a :: flat m2)
        | Xl.Mixop.Seq ms -> List.concat_map flat ms
      in
      let rec count n = function
        | [] -> None
        | `Atom a :: _ when a.it = Xl.Atom.Arrow2 -> Some n
        | `Atom _ :: rest -> count n rest
        | `Arg :: rest -> count (n + 1) rest
      in
      count 0 (flat mixop)
    in
    let components exp = match exp.it with TupE es -> es | _ -> [exp] in
    let split n exp =
      let es = components exp in
      match n with
      | None -> es, []
      | Some n -> Util.Lib.List.split n es
    in
    (* Solutions of a relation goal: substitutions for the goal's output
       variables. Raises on more than one solution. *)
    (* Goals are memoized by relation and printed query. Sibling rules such
       as Run-Step and Run-Step-Error share their premises, so without this
       the all-rules search is exponential in the input length. Memoizing a
       pure judgment does not change its solutions. *)
    let memo = Hashtbl.create 4096 in
    let rec solve fuel relation query =
      if fuel = 0 then failed "relation test exceeded depth 2000";
      let query = reduce query in
      let key = relation.it ^ "\000" ^ Il.Print.string_of_exp query in
      match Hashtbl.find_opt memo key with
      | Some solutions -> solutions
      | None ->
      let solutions = solve_uncached fuel relation query in
      Hashtbl.replace memo key solutions;
      solutions
    and solve_uncached fuel relation query =
      let _, mixop, _, rules = Il.Env.find_rel env relation in
      let n = input_count mixop in
      let inputs, outputs = split n query in
      if not (List.for_all ground inputs) then
        failed ("non-ground relation inputs: " ^ Il.Print.string_of_exp query);
      let solutions = List.concat_map (fun rule ->
        let RuleD (name, _, _, conclusion, premises) = rule.it in
        let c_inputs, c_outputs = split n conclusion in
        match match_values Il.Subst.empty inputs c_inputs with
        | None -> []
        | Some subst ->
          match check_prems fuel subst premises with
          | None -> []
          | Some subst ->
            let produced = List.map (fun e -> reduce (Il.Subst.subst_exp subst e)) c_outputs in
            if not (List.for_all ground produced) then
              failed (relation.it ^ "/" ^ name.it ^ ": unbound conclusion output");
            if Sys.getenv_opt "EMMANUEL_TEST_TRACE" = Some name.it then
              prerr_endline ("APPLY " ^ name.it ^ " " ^ Il.Print.string_of_exp query);
            match match_values Il.Subst.empty produced outputs with
            | None -> []
            | Some bound -> [(name.it, bound)]
      ) rules in
      (match solutions with
      | _ :: _ :: _ ->
        failed ("overlapping derivations (" ^
          String.concat ", " (List.map fst solutions) ^ ") for " ^
          relation.it ^ ": " ^ Il.Print.string_of_exp query)
      | _ -> ());
      List.map snd solutions
    and check_prems fuel subst = function
      | [] -> Some subst
      | premise :: rest ->
        let premise = Il.Subst.subst_prem subst premise in
        match premise.it with
        | IfPr exp ->
          (match (reduce exp).it with
          | BoolE true -> check_prems fuel subst rest
          | BoolE false -> None
          | CmpE (`EqOp, _, lhs, rhs) ->
            let value, pattern =
              if ground lhs && not (ground rhs) then lhs, rhs
              else if ground rhs && not (ground lhs) then rhs, lhs
              else failed ("unresolved equality: " ^ Il.Print.string_of_prem premise)
            in
            (match match_value Il.Subst.empty value pattern with
            | None -> None
            | Some bound -> check_prems fuel (Il.Subst.union subst bound) rest)
          | _ -> failed ("unresolved test guard: " ^ Il.Print.string_of_prem premise))
        | LetPr (_, pattern, value) ->
          (match match_value Il.Subst.empty value pattern with
          | None -> None
          | Some bound -> check_prems fuel (Il.Subst.union subst bound) rest)
        | RulePr (relation, [], _, query) ->
          (match solve (fuel - 1) relation query with
          | [] -> None
          | [bound] -> check_prems fuel (Il.Subst.union subst bound) rest
          | _ -> assert false)
        | _ -> failed ("unsupported test premise: " ^ Il.Print.string_of_prem premise)
    in
    let count = ref 0 in
    In_channel.with_open_text Sys.argv.(1) (fun input ->
      let rec next () =
        match In_channel.input_line input with
        | None -> ()
        | Some line when line = "" || line.[0] = '#' -> next ()
        | Some line ->
          (match String.split_on_char '\t' line with
          | [name; kind; typ; query; expected] ->
            let success =
              if kind = "value" then
                let actual = reduce (expression query typ) in
                let expected = reduce (expression expected typ) in
                if not (ground actual && normal actual) then
                  failed (name ^ ": unresolved function result: " ^ Il.Print.string_of_exp actual);
                if not (ground expected && normal expected) then
                  failed (name ^ ": unresolved expected value: " ^ Il.Print.string_of_exp expected);
                if not (Il.Eq.eq_exp actual expected) then
                  failed (name ^ ": expected " ^ Il.Print.string_of_exp expected ^
                    "; got " ^ Il.Print.string_of_exp actual);
                true
              else if kind = "relation" then
                let query = Frontend.Elab.elab_rel elenv
                  (Frontend.Parse.parse_exp query) (id typ) in
                if not (ground query) then
                  failed (name ^ ": relation tests must be ground");
                (solve 2000 (id typ) query <> []) = bool_of_string expected
              else failed ("unknown test kind: " ^ kind)
            in
            if not success then failed ("regression failed: " ^ name);
            incr count;
            Printf.printf "PASS %s\n%!" name
          | _ -> failed "expected five tab-separated test columns");
          next ()
      in next ()
    );
    Printf.printf "%d Emmanuel SpecTec regressions passed.\n" !count
  with
  | Util.Error.Error (at, message) -> Util.Error.print_error at message; exit 1
  | exn -> prerr_endline (Printexc.to_string exn); exit 1
