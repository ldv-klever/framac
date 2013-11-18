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

include Plugin.S

module Pragma: Plugin.String_set
  (** Use pragmas of given function. *)

module Print: Plugin.Bool
  (** Print the impacted stmt on stdout. *)

module Reason: Plugin.Bool
  (** Build the graphs that explains why a node is impacted. *)

module Slicing: Plugin.Bool
  (** Slicing from the impacted stmt. *)

module Skip: Plugin.String_set
  (** Consider that the variables in the string are not impacted *)

module Upward: Plugin.Bool
  (** Also compute impact within callers *)

val is_on: unit -> bool

(*
Local Variables:
compile-command: "make -C ../.."
End:
*)
