(* Ground regressions over the actual upstream elaborated SpecTec definitions.
   This is a test driver, not the normative semantics or a Rocq generator.
   It checks all rules, never first-success order. Its intentionally limited
   relation checker supports ground goals, guards, and binding premises only;
   unresolved existential subgoals fail loudly rather than being assumed. *)
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
    (* The pinned upstream matcher splits a known-suffix list at suffix length,
       not at total length minus suffix length (eval.ml, CatE right-ListE case).
       That prevents matching Newspeak's snoc stacks. Correct just structural
       matching here; do not patch the compiler or change normative stack order.
       Function evaluation remains upstream. resumeStack uses head recursion.
       This workaround is test infrastructure, not a Newspeak rule. *)
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
    let rec prove fuel relation query =
      if fuel = 0 then failed "ground relation test exceeded depth 100";
      let query = reduce query in
      if not (ground query) then
        failed ("unsupported existential test subgoal: " ^ Il.Print.string_of_exp query);
      let _, _, _, rules = Il.Env.find_rel env relation in
      List.fold_left (fun count rule ->
        let RuleD (name, _, _, conclusion, premises) = rule.it in
        if Sys.getenv_opt "NEWSPEAK_TEST_TRACE" = Some name.it then
          prerr_endline ("MATCH " ^ Il.Print.string_of_exp conclusion);
        match match_value Il.Subst.empty query conclusion with
        | None -> count
        | Some subst -> if check_prems fuel subst premises then count + 1 else count
      ) 0 rules
    and check_prems fuel subst = function
      | [] -> true
      | premise :: rest ->
        let premise = Il.Subst.subst_prem subst premise in
        match premise.it with
        | IfPr exp ->
          (match (reduce exp).it with
          | BoolE true -> check_prems fuel subst rest
          | BoolE false -> false
          | CmpE (`EqOp, _, lhs, rhs) ->
            let value, pattern =
              if ground lhs && not (ground rhs) then lhs, rhs
              else if ground rhs && not (ground lhs) then rhs, lhs
              else failed ("unresolved equality: " ^ Il.Print.string_of_prem premise)
            in
            (match match_value Il.Subst.empty value pattern with
            | None -> false
            | Some bound -> check_prems fuel (Il.Subst.union subst bound) rest)
          | _ -> failed ("unresolved test guard: " ^ Il.Print.string_of_prem premise))
        | LetPr (_, pattern, value) ->
          (match match_value Il.Subst.empty value pattern with
          | None -> false
          | Some bound -> check_prems fuel (Il.Subst.union subst bound) rest)
        | RulePr (relation, [], _, query) ->
          let count = prove (fuel - 1) relation query in
          if count > 1 then failed "overlapping derivations in a ground lookup test";
          count = 1 && check_prems fuel subst rest
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
                let derivations = prove 100 (id typ) query in
                if derivations > 1 then failed (name ^ ": multiple applicable rules");
                (derivations = 1) = bool_of_string expected
              else failed ("unknown test kind: " ^ kind)
            in
            if not success then failed ("regression failed: " ^ name);
            incr count;
            Printf.printf "PASS %s\n%!" name
          | _ -> failed "expected five tab-separated test columns");
          next ()
      in next ()
    );
    Printf.printf "%d SpecTec regressions passed.\n" !count
  with
  | Util.Error.Error (at, message) -> Util.Error.print_error at message; exit 1
  | exn -> prerr_endline (Printexc.to_string exn); exit 1
