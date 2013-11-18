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
open Cil_datatype

(** Internal state of the Value Analysis during analysis. *)

(** State on one statement *)
type record

(** State for an entier function *)
type t = record Cil_datatype.Stmt.Hashtbl.t

val create : unit -> t
val clear : t -> unit  (* Not clear this is useful, as the table is garbage-collected *)

(** Extraction *)
val find_widening_info : t -> stmt -> int * Cvalue.Model.t
val find_superposition : t -> stmt -> State_set.t

(** Updating *)
val update_current : t -> stmt -> State_set.t -> unit
val update_and_tell_if_changed : t -> stmt -> State_set.t -> State_set.t
val update_widening_info : t -> stmt -> int -> Cvalue.Model.t -> unit

(** Export *)
val superpositions : t -> Cvalue.Model.t list Stmt.Hashtbl.t
val states : t -> Cvalue.Model.t Stmt.Hashtbl.t

(** Merge the results of the current analysis with the global results.
    Honor [-no-results*] options *)
val merge_db_table : 
  Db.Value.state Stmt.Hashtbl.t Lazy.t -> Db.Value.callstack -> unit
