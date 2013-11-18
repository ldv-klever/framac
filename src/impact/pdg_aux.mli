(**************************************************************************)
(*                                                                        *)
(*  This file is part of Frama-C.                                         *)
(*                                                                        *)
(*  Copyright (C) 2007-2013                                               *)
(*    CEA (Commissariat � l'�nergie atomique et aux �nergies              *)
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

open Cil_types

(** Useful functions that are not directly accessible through the other
    Pdg modules. *)


(** [all_call_input_nodes caller callee call_stmt] find all the nodes
    above [call_stmt] in the pdg of [caller] that define the inputs
    of [callee]. Each input node in [callee] is returned with the set
    of nodes that define it in [caller]. The zones potentially not
    defined in [caller] are skipped, as they are not useful for an impact
    analysis *)
val all_call_input_nodes:
  Db.Pdg.t ->  kernel_function * Db.Pdg.t -> stmt ->
  (PdgTypes.Node.t * PdgTypes.NodeSet.t) list


val all_call_out_nodes :
  Db.Pdg.t ->  (*kernel_function *) Db.Pdg.t -> stmt ->
  (PdgTypes.Node.t * PdgTypes.NodeSet.t) list
