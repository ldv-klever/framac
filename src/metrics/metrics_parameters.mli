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

module Metrics: Plugin.S

module Enabled: Plugin.WithOutput
(** Activate metrics *)

module ByFunction: Plugin.Bool
(** Activate metrics by function *)

module ValueCoverage: Plugin.WithOutput
(** Give an estimation about value analysis code penetration.
    Only works on CIL AST. *)

module AstType: Plugin.String
(** Set the ASTs on which the metrics should be computetd *)

module OutputFile: Plugin.String
(** Pretty print metrics to the given file.
    The output format will be recognized through the extension.
    Supported extensions are:
    "html" or "htm" for HTML
    "txt" or "text" for text
*)

module SyntacticallyReachable: Plugin.String_set
(** List of functions for which we compute the functions they may call *)

(*
Local Variables:
compile-command: "make -C ../.."
End:
*)
