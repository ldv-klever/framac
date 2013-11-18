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

(** A call_stack is a list, telling which function was called at which
    site. The head of the list tells about the latest call. *)
type call_site = (kernel_function * kinstr)
type callstack = call_site list

(** Functions dealing with call stacks. *)
val clear_call_stack : unit -> unit
val pop_call_stack : unit -> unit
val push_call_stack : kernel_function -> kinstr -> unit

(** The current function is the one on top of the call stack. *)
val current_kf : unit -> kernel_function
val call_stack : unit -> callstack

(** Print a call stack. The first one does not display the call sites. *)
val pretty_call_stack_short : Format.formatter -> callstack -> unit
val pretty_call_stack : Format.formatter -> callstack -> unit

(** Prints the current callstack. *)
val pp_callstack : Format.formatter -> unit

(* TODO: Document the rest of this file. *)
val get_rounding_mode : unit -> Ival.Float_abstract.rounding_mode
val do_degenerate : lval option -> unit
val stop_if_stop_at_first_alarm_mode : unit -> unit
val emitter : Emitter.t
val warn_all_mode : CilE.warn_mode
val with_alarm_stop_at_first : CilE.warn_mode
val with_alarms_raise_exn : exn -> CilE.warn_mode
val warn_all_quiet_mode : unit -> CilE.warn_mode
val get_slevel : Kernel_function.t -> Value_parameters.SlevelFunction.value
val set_loc : kinstr -> unit
module Got_Imprecise_Value : State_builder.Ref with type data = Datatype.Bool.t
val pretty_actuals : Format.formatter -> ('a * Cvalue.V.t * 'b) list -> unit
val pretty_current_cfunction_name : Format.formatter -> unit
val warning_once_current : ('a, Format.formatter, unit) format -> 'a
module StmtCanReachCache : State_builder.Hashtbl 
  with type key = Kernel_function.t
  and type data = stmt -> stmt -> Datatype.Bool.t
val stmt_can_reach : StmtCanReachCache.key -> StmtCanReachCache.data
val debug_result :
  Kernel_function.t ->
  Cvalue.V_Offsetmap.t option * 'a * Base.SetLattice.t -> unit
val map_outputs :
  (Cvalue.Model.t -> 'a) ->
  (Cvalue.V_Offsetmap.t option * Cvalue.Model.t) list ->
  (Cvalue.V_Offsetmap.t option * 'a) list
val remove_formals_from_state :
  varinfo list -> Cvalue.Model.t -> Cvalue.Model.t

(*
Local Variables:
compile-command: "make -C ../.."
End:
*)
