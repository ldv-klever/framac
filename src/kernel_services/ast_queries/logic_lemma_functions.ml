(**************************************************************************)
(*                                                                        *)
(*  This file is part of Frama-C.                                         *)
(*                                                                        *)
(*  Copyright (C) 2007-2016                                               *)
(*    CEA (Commissariat à l'énergie atomique et aux énergies              *)
(*         alternatives)                                                  *)
(*                                                                        *)
(*  you can redistribute it and/or modify it under the terms of the GNU   *)
(*  Lesser General Public License as published by the Free Software       *)
(*  Foundation, version 2.1.                                              *)
(*                                                                        *)
(*  It is distributed in the hope that it will be useful,                 *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *)
(*  GNU Lesser General Public License for more details.                   *)
(*                                                                        *)
(*  See the GNU Lesser General Public License version 2.1                 *)
(*  for more details (enclosed in the file licenses/LGPLv2.1).            *)
(*                                                                        *)
(**************************************************************************)

open Cil
open Cil_types
open Cil_datatype
open Logic_const

open Extlib

(** Lemma-Functions **
 *
 * RATIONALE:
   * Some properties are hard to prove as lemmas (solvers don't solve them automatically).
   * It is often possible to prove them as ghost functions instead.
   * With this feature, you don't have to explicitly call these functions,
   * because it automatically generates axioms from them.
 *
 * DESIGN:
   * For every function marked annotated with 'lemmafn something' (a term is
   * required by the extension system, but we don't care which term it is here),
   * an axiom is generated of the form
   * 'exists (return value). * forall (arguments). precondition => * postconditions'.
   *
   * To prevent the axiom from proving the function itself,
   * the axiom is wrapped in an axiomatic with an extra dummy predicate,
   * which is then used in all functions defined below the lemma-function.
   *
   * Some restrictions for the functions: must assign and allocate nothing, must
   * have only one (default) behavior. (Actually the annotation is on the behavior.)
 *
 * TODO:
   * examples/tests: jessie/tests/bitvectors
   * verker strchrnul
   * benchmark forall/exists orders
   * support lemmafn pre ==> post;
 * *)

(** \result → result, where just 'result' is a variable under Exists *)
let replace_result result_var pred = Visitor.visitFramacPredicate (object
  inherit Visitor.frama_c_inplace

  method! vterm t =
    if is_result t then ChangeTo (tvar result_var)
    else DoChildren

  end) pred

(** \old(x) → x, error on other labels *)
let remove_old pred = Visitor.visitFramacPredicate (object
  inherit Visitor.frama_c_inplace

  method! vpredicate_node = function
    | Pat (p, lab) when lab = Logic_const.old_label -> ChangeTo p.pred_content
    | Pat (_, _) -> Kernel.fatal "unsupported label in lemma-function"
    | _ -> DoChildren

  method! vterm_node = function
    | Tat (t, lab) when lab = Logic_const.old_label -> ChangeTo t.term_node
    | Tat (_, _) -> Kernel.fatal "unsupported label in lemma-function"
    | _ -> DoChildren

  end) pred

(** Append \requires p(1) to a function's specification (to the default behavior) *)
let add_usage_of_pred f p =
  let app = papp (p, [], []) in
  match Cil.find_default_behavior @@ (Globals.Functions.find_by_name f.svar.vname).spec with
  | Some beh ->
    beh.b_requires <- (new_predicate app) :: beh.b_requires
  | None ->
      let beh = Cil.mk_behavior ~requires:[new_predicate app] ~post_cond:[] () in
      let my_kf = Globals.Functions.get f.svar in
      Annotations.add_behaviors Emitter.end_user my_kf [beh]

(** Error if a different label is found anywhere inside the predicate *)
let error_if_label_other_than good_l pred = Visitor.visitFramacPredicate (object
  inherit Visitor.frama_c_inplace

  method! vlogic_label l =
    if l <> good_l then Kernel.fatal "unsupported label in lemma-function"
    else DoChildren

  end) pred

(** Generate an axiom from a behavior *)
let lemma_for_behavior fvar args beh =
  let preconds = List.map (fun pred -> pred.ip_content)
    (List.append beh.b_requires beh.b_assumes) in
  let precond_pred = List.fold_left (fun a b -> pand (a, b)) ptrue preconds in
  let postconds = List.map (fun (kind, pred) ->
    if (kind = Exits) then
      Kernel.fatal "postcondition of unsupported kind Exits for lemma-function";
    pred.ip_content) beh.b_post_cond in
  let postcond_pred = List.fold_left (fun a b -> pand (a, b)) ptrue postconds in
  let arg_vars =
    List.map
      (fun vi ->
        let lv = cvar_to_lvar vi in
        lv, Cil_const.make_logic_var_quant lv.lv_name lv.lv_type)
    args
  in
  let precond_pred, postcond_pred =
    let update_vars =
      Visitor.visitFramacPredicate
        (object(self)
          inherit Visitor.frama_c_refresh (Project.current ())
          val var_map = List.fold_right (uncurry Logic_var.Map.add ) arg_vars Logic_var.Map.empty

          method! vlogic_var_use lv =
            try ChangeTo (Logic_var.Map.find lv var_map)
            with Not_found -> JustCopy
        end)
    in
    update_vars precond_pred, update_vars postcond_pred
  in
  (* not using the pimplies function to avoid collapsing to just "true" right here *)
  let impl_pred = unamed (Pimplies (precond_pred, postcond_pred)) in
  let pred_with_args = pforall (List.map snd arg_vars, impl_pred) in
  let pred_with_ret = match (cvar_to_lvar fvar).lv_type with
    | Ctype (TFun (ret_typ, _, _, _)) when ret_typ <> voidType ->
        let ret_var = Cil_const.make_logic_var_formal "result" (Ctype ret_typ) in
        pexists ([ret_var], replace_result ret_var pred_with_args)
    | _ -> pred_with_args in
  let pred_without_old = remove_old pred_with_ret
    |> error_if_label_other_than (BuiltinLabel Here) in
  let name = "LF__Lemma__" ^ fvar.vname in
  Dlemma (name, true, [BuiltinLabel Here], [], pred_without_old, [], fvar.vdecl)

(** Generate an axiomatic for a behavior (with the dummy predicate), registering globals *)
let axiomatic_for_behavior fvar args beh l =
  let lemma = lemma_for_behavior fvar args beh in
  let pred_name = "LF__Predicate__" ^ fvar.vname in
  let pred = { (Cil_const.make_logic_info pred_name) with
    l_profile = [];
    l_body = LBpred ptrue } in
  let pred_def = Dfun_or_pred (pred, l) in
  let axiomatic = Daxiomatic ("LF__Axiomatic__" ^ fvar.vname, [
      lemma;
      pred_def
    ], [], l) in
  Logic_utils.add_logic_function l pred;
  Annotations.add_global Emitter.end_user pred_def;
  Annotations.add_global Emitter.end_user axiomatic;
  (GAnnot (axiomatic, l), pred)
  (* axiomatic { lemma; pred = true }
   * function after axiomatic { requires pred }
   *)

(** If a functions is marked with the annotation,
 *  make sure the function is a valid lemma-function
 *  and return the default behavior *)
let check_annot_get_beh f =
  (match f.sspec.spec_terminates with
  | None -> ()
  | Some term_p when term_p.ip_content.pred_content = Ptrue -> ()
  | Some _ when f.sspec.spec_lemma -> Kernel.fatal "abrupt termination for lemma-functions is not allowed"
  | Some _ -> ());
  if (List.length f.sspec.spec_behavior = 1) then (
    let beh = (List.hd f.sspec.spec_behavior) in
    if f.sspec.spec_lemma then (
      if not (beh.b_name = default_behavior_name) then
        Kernel.fatal "behavior name for lemma-function is not default";
      if (beh.b_assigns = WritesAny) then
        beh.b_assigns <- Writes [];
      if (beh.b_assigns <> Writes []) then
        Kernel.fatal "lemma-function with non-empty \\assigns";
      if (beh.b_allocation = FreeAllocAny) then
        beh.b_allocation <- FreeAlloc ([], []);
      if (beh.b_allocation <> FreeAlloc ([], [])) then
        Kernel.fatal "lemma-function with non-empty \\allocates";
      Some beh
    ) else None
  ) else (
    List.iter (fun _beh ->
      if f.sspec.spec_lemma then
        Kernel.fatal "lemma-function with number of behaviors != 1"
    ) f.sspec.spec_behavior;
    None
  )

(** The main visitor for processing lemma-functions *)
class make_axioms_for_functions = object
  inherit Visitor.frama_c_inplace

  val mutable added_preds : logic_info list = []

  method! vglob_aux g =
    match g with
    | GFun (f, l) -> (
        List.iter (add_usage_of_pred f) added_preds;
        match check_annot_get_beh f with
        | Some beh ->
          let (axiomatic_ann, pred_name) = axiomatic_for_behavior f.svar f.sformals beh l in
          added_preds <- pred_name :: added_preds;
          ChangeTo [
            GFun (f, l);
            axiomatic_ann
          ]
        | None -> DoChildren
      )
    | _ -> DoChildren
end

let make_axioms_for_functions f = Visitor.visitFramacFile (new make_axioms_for_functions) f

(*
Local Variables:
compile-command: "make -C ../../.."
End:
*)
