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

module Enabled: Plugin.Bool

module DoAll: Plugin.Bool
module DoDivMod : Plugin.Bool
module DoFloatToInt : Plugin.Bool
module DoMemAccess : Plugin.Bool
module DoCalledPrecond : Plugin.Bool

module Trivial : Plugin.Bool
module Warn : Plugin.Bool
module FunctionSelection : Plugin.String_set

val warn: ?source:Lexing.position -> ('a, Format.formatter, unit) format -> 'a

(*
Local Variables:
compile-command: "make -C ../.."
End:
*)
