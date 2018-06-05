(**************************************************************************)
(*                                                                        *)
(*  This file is part of Frama-C.                                         *)
(*                                                                        *)
(*  Copyright (C) 2007-2018                                               *)
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

open Cil_types

(** Compute a sound over-approximation of what left-values must be tracked by
    the memory model library *)

val reset: unit -> unit
(** Must be called to redo the analysis *)

val use_model: unit -> bool
(** Is one variable monitored (at least)? *)

val must_model_vi: ?bhv:Cil.visitor_behavior -> ?kf:kernel_function
  -> ?stmt:stmt -> varinfo -> bool
(** [must_model_vi ?kf ?stmt vi] returns [true] if the varinfo [vi] at the given
    [stmt] in the given function [kf] must be tracked by the memory model
    library. If behavior [bhv] is specified then assume that [vi] is part
    of the new project generated by the given copy behavior [bhv] *)

val must_model_lval: ?bhv:Cil.visitor_behavior -> ?kf:kernel_function
  -> ?stmt:stmt -> lval -> bool
(** Same as {!must_model_vi}, for left-values *)

val must_model_exp: ?bhv:Cil.visitor_behavior -> ?kf:kernel_function
  -> ?stmt:stmt -> exp -> bool
(** Same as {!must_model_vi}, for expressions *)

(*
  Local Variables:
  compile-command: "make"
  End:
 *)