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
open Logic_const
open Logic_typing

(** \result → result, where just 'result' is a variable under Exists *)
let replace_result result_var pred = Visitor.visitFramacPredicate (object
  inherit Visitor.frama_c_inplace

  method! vterm t =
    if is_result t then ChangeTo (tvar result_var)
    else DoChildren

  end) pred

let () = Logic_typing.register_behavior_extension
  "lemmafn" (fun ~typing_context ~loc l -> Ext_terms [tinteger 1])

let add_usage_of_pred f p =
  let app = papp (p, [], [tinteger 1]) in
  List.iter (fun beh ->
    beh.b_requires <- (Logic_const.new_predicate app) :: beh.b_requires
  ) f.sspec.spec_behavior

let lemma_for_behavior fvar args beh =
  let preconds = List.map (fun pred -> pred.ip_content)
    (List.append beh.b_requires beh.b_assumes) in
  let precond_pred = List.fold_left (fun a b -> pand (a, b)) ptrue preconds in
  let postconds = List.map (fun (kind, pred) ->
    if (kind = Exits) then
      Kernel.fatal "postcondition of unsupported kind Exits for lemma function";
    pred.ip_content) beh.b_post_cond in
  let postcond_pred = List.fold_left (fun a b -> pand (a, b)) ptrue postconds in
  let arg_vars = List.map cvar_to_lvar args in
  (* not using the pimplies function to avoid collapsing to just "true" right here *)
  let impl_pred = unamed (Pimplies (precond_pred, postcond_pred)) in
  let pred_with_args = pforall (arg_vars, impl_pred) in
  let pred_with_ret = match (cvar_to_lvar fvar).lv_type with
    | Ctype (TFun (ret_typ, _, _, _)) when ret_typ <> voidType ->
        let ret_var = Cil_const.make_logic_var_formal "result" (Ctype (ret_typ)) in
        pexists ([ret_var], replace_result ret_var pred_with_args)
    | _ -> pred_with_args in
  let name = "LF__Lemma__" ^ fvar.vname in
  Dlemma (name, false, [Logic_const.old_label], [], pred_with_ret, Cil_datatype.Location.unknown)

let axiomatic_for_behavior fvar args beh l =
  let lemma = lemma_for_behavior fvar args beh in
  let pred_name = "LF__Predicate__" ^ fvar.vname in
  let pred = { (Cil_const.make_logic_info pred_name) with
    l_profile = [Cil_const.make_logic_var_formal "x" Linteger];
    l_body = LBpred (ptrue) } in
  let pred_def = Dfun_or_pred (pred, l) in
  let axiomatic = Daxiomatic ("LF__Axiomatic__" ^ fvar.vname, [
      lemma;
      pred_def
    ], l) in
  Annotations.add_global Emitter.end_user pred_def;
  Annotations.add_global Emitter.end_user axiomatic;
  (GAnnot (axiomatic, l), pred)
  (* axiomatic { lemma; pred = true }
   * function after axiomatic { requires pred }
   *)

let beh_is_lemma beh =
  List.exists (fun (extname, _) -> extname = "lemmafn") beh.b_extended

let check_annot_get_beh f =
  if (List.length f.sspec.spec_behavior = 1) then (
    let beh = (List.hd f.sspec.spec_behavior) in
    if (beh_is_lemma beh) then (
      if not (beh.b_name = Cil.default_behavior_name) then
        Kernel.fatal "behavior name for lemma function does not match the default";
      if (beh.b_assigns <> Writes []) then
        Kernel.fatal "can't make a lemma for function with non-empty 'assigns'";
      if (beh.b_allocation <> FreeAlloc ([], [])) then
        Kernel.fatal "can't make a lemma for function with non-empty 'allocates'";
      Some(beh)
    ) else None
  ) else (
    List.iter (fun beh ->
      if (beh_is_lemma beh) then
        Kernel.fatal "number of behaviors is not 1, but asked for lemma function"
    ) f.sspec.spec_behavior;
    None
  )

class make_axioms_for_functions = object
  inherit Visitor.frama_c_inplace

  val mutable added_preds : Cil_types.logic_info list = []

  method! vglob_aux g =
    match g with
    | GFun(f, l) -> (
        List.iter (add_usage_of_pred f) added_preds;
        match check_annot_get_beh f with
        | Some(beh) ->
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
