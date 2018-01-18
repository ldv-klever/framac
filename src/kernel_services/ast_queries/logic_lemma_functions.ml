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

class make_axioms_for_functions = object
  inherit Cil.nopCilVisitor
  method! vfunc f =
    Format.printf "\n\n||| lemma function %s\n" f.svar.vname;
    let arg_quants = List.map cvar_to_lvar f.sformals in
    (* TODO: multiple behaviors *)
    let beh = (List.hd f.sspec.spec_behavior) in
    Format.printf "\n%a\n" Printer.pp_behavior beh;
    (* TODO: skip instead of crashing *)
    assert (beh.b_assigns = Writes []);
    assert (beh.b_allocation = FreeAlloc ([], []));
    let preconds = List.map (fun pred -> pred.ip_content)
      (List.append beh.b_requires beh.b_assumes) in
    let precond_pred = List.fold_left (fun a b -> pand (a, b)) ptrue preconds in
    (* TODO: termination_kind ??? *)
    let postconds = List.map (fun (_, pred) -> pred.ip_content) beh.b_post_cond in
    let postcond_pred = List.fold_left (fun a b -> pand (a, b)) ptrue postconds in
    let final_pred = pforall (arg_quants,
      (* not using the pimplies function to avoid collapsing
       * to just "true" right here *)
      unamed (Pimplies (precond_pred, postcond_pred))) in
    let name = "Lemma__Function__" ^ f.svar.vname ^ "__Behavior__" ^ beh.b_name in
    let lemma = Dlemma (name, true, [], [], final_pred, Cil_datatype.Location.unknown) in
    Format.printf "\n%a\n" Printer.pp_global_annotation lemma;
    (* TODO: save it *)
    DoChildren
end

let make_axioms_for_functions f = Cil.visitCilFileSameGlobals (new make_axioms_for_functions) f

(*
Local Variables:
compile-command: "make -C ../../.."
End:
*)
