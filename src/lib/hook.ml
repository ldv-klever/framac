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

module type S = sig
  type param
  type result
  val extend: (param -> result) -> unit
  val extend_once: (param -> result) -> unit
  val apply: param -> result
  val is_empty: unit -> bool
  val clear: unit -> unit
  val length: unit -> int
end

module type Iter_hook = S with type result = unit

let add_once v queue =
  let already = Queue.fold (fun b v' -> b || v' == v) false queue in
  if not already then Queue.add v queue

module Build(P:sig type t end) = struct
  type param = P.t
  type result = unit
  let hooks = Queue.create ()
  let extend f = Queue.add f hooks
  let extend_once f = add_once f hooks

  let apply arg = Queue.iter (fun f -> f arg) hooks
    (* [JS 06 October 2008] the following code iter in reverse order without
       changing the order of the queue itself.

       let list = ref [] in
       Queue.iter (fun f -> list := f :: !list) hooks;
       List.iter (fun f -> f arg) !list *)

  let is_empty () = Queue.is_empty hooks
  let clear () = Queue.clear hooks
  let length () = Queue.length hooks
end

module Fold(P:sig type t end) = struct
  type param = P.t
  type result = P.t
  let hooks = Queue.create ()
  let extend f = Queue.add f hooks
  let extend_once f = add_once f hooks
  let apply arg = Queue.fold (fun arg f -> f arg) arg hooks
  let is_empty () = Queue.is_empty hooks
  let clear () = Queue.clear hooks
  let length () = Queue.length hooks
end

module Make(X:sig end) = Build(struct type t = unit end)

(*
Local Variables:
compile-command: "make -C ../.."
End:
*)
