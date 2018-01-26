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
open Cil_const
open Logic_const
open Annotations
open Visitor

let add_usage_of_pred f p =
  let app = papp (p, [], [tinteger 1]) in
  List.iter (fun beh ->
    beh.b_requires <- (Logic_const.new_predicate app) :: beh.b_requires
  ) f.sspec.spec_behavior

let lemma_for_behavior f beh =
    let arg_quants = List.map cvar_to_lvar f.sformals in
    let preconds = List.map (fun pred -> pred.ip_content)
      (List.append beh.b_requires beh.b_assumes) in
    let precond_pred = List.fold_left (fun a b -> pand (a, b)) ptrue preconds in
    let postconds = List.map (fun (kind, pred) ->
      if not (kind != Exits) then
        Kernel.fatal "postcondition of unsupported kind for lemma function";
      pred.ip_content) beh.b_post_cond in
    let postcond_pred = List.fold_left (fun a b -> pand (a, b)) ptrue postconds in
    let final_pred = pforall (arg_quants,
      (* not using the pimplies function to avoid collapsing
       * to just "true" right here *)
      unamed (Pimplies (precond_pred, postcond_pred))) in
    (* TODO: error when \old is used *)
    let name = "LF__Lemma__" ^ f.svar.vname in
    Dlemma (name, false, [Logic_const.old_label], [], final_pred, Cil_datatype.Location.unknown)

let lemma_for_func f l =
  (* Format.printf "\n\n||| lemma function %s\n" f.svar.vname;
  Format.printf "b %d\n" (List.length f.sspec.spec_behavior);
  List.iter (fun x -> Format.printf "b %s\n" x.b_name) f.sspec.spec_behavior; *)
  if not (List.length f.sspec.spec_behavior = 1) then
    Kernel.fatal "number of behaviors is not 1 for lemma function";
  let beh = (List.hd f.sspec.spec_behavior) in
  if not (beh.b_name = Cil.default_behavior_name) then
    Kernel.fatal "behavior name for lemma function does not match the default";
  if not (beh.b_assigns = Writes [] && beh.b_allocation = FreeAlloc ([], [])) then (
    Kernel.fatal "can't make a lemma for behavior";
  ) else (
    let lemma = lemma_for_behavior f beh in
    let pred_name = "LF__Predicate__" ^ f.svar.vname in
    let pred = { (Cil_const.make_logic_info pred_name) with
      l_profile = [Cil_const.make_logic_var_formal "x" Linteger];
      l_body = LBpred (ptrue) } in
    let pred_def = Dfun_or_pred (pred, l) in
    let axiomatic = Daxiomatic ("LF__Axiomatic__" ^ f.svar.vname, [
        lemma;
        pred_def
      ], l) in
    Annotations.add_global Emitter.end_user pred_def;
    Annotations.add_global Emitter.end_user axiomatic;
    (ChangeTo [
      GFun (f, l);
      GAnnot (axiomatic, l)
    ], pred)
  )
  (* axiomatic { lemma; pred = true }
   * function after axiomatic { requires pred }
   *)

class make_axioms_for_functions = object
  inherit Visitor.frama_c_inplace

  val mutable added_preds : Cil_types.logic_info list = []

  method! vglob_aux g =
    match g with
    | GFun(f, l) ->
        List.iter (add_usage_of_pred f) added_preds;
        (* TODO: if marked *)
        let (result, pred_name) = lemma_for_func f l in
        added_preds <- pred_name :: added_preds;
        result
    | _ -> DoChildren
end

let make_axioms_for_functions f = Visitor.visitFramacFile (new make_axioms_for_functions) f

(*
Local Variables:
compile-command: "make -C ../../.."
End:
*)
