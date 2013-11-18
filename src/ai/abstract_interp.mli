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

(** Signatures for generic lattices, with functors providing generic
    implementations. *)

exception Not_less_than
(** Raised by {!Lattice.cardinal_less_than}. *)

exception Is_not_included

(** Generic lattice.
    @plugin development guide *)
module type Lattice = sig

  exception Error_Top
  exception Error_Bottom

  include Datatype.S (** datatype of element of the lattice *)
  type widen_hint (** hints for the widening *)

  val join: t -> t -> t (** over-approximation of union *)
  val link: t -> t -> t (** under-approximation of union *)
  val meet: t -> t -> t (** under-approximation of intersection *)
  val narrow: t -> t -> t (** over-approximation of intersection *)
  val bottom: t (** the smallest *)
  val top: t  (** the largest *)

  val is_included: t -> t -> bool
  val is_included_exn: t -> t -> unit
  val intersects: t -> t -> bool

  val widen: widen_hint -> t -> t -> t
    (** [widen h t1 t2] is an over-approximation of [join t1 t2].
        Assumes [is_included t1 t2] *)

  val cardinal_zero_or_one: t -> bool

  val cardinal_less_than: t -> int -> int
(** @raise Not_less_than whenever the cardinal of the given lattice is higher
    than the given integer. *)

end

module type Lattice_With_Diff = sig

  include Lattice

  val diff : t -> t -> t
    (** [diff t1 t2] is an over-approximation of [t1-t2]. *)

  val diff_if_one : t -> t -> t
    (** [diff t1 t2] is an over-approximation of [t1-t2].
        @return t1 if [t2] is not a singleton. *)

  val fold_enum :
    split_non_enumerable:int -> (t -> 'a -> 'a) -> t -> 'a -> 'a
  val splitting_cardinal_less_than:
    split_non_enumerable:int -> t -> int -> int

  val pretty_debug : Format.formatter -> t -> unit

end

module type Lattice_Product = sig
  type t1
  type t2
  type tt = private Product of t1*t2 | Bottom
  include Lattice with type t = tt
  val inject : t1 -> t2 -> t
  val fst : t -> t1
  val snd : t -> t2
end

module type Lattice_Sum = sig
  type t1
  type t2
  type sum = private Top | Bottom | T1 of t1 | T2 of t2
  include Lattice with type t = sum
  val inject_t1 : t1 -> t
  val inject_t2 : t2 -> t
end

module type Lattice_Base = sig
  type l
  type tt = private Top | Bottom | Value of l
  include Lattice with type t = tt
  val project : t -> l
  val inject: l -> t
  val transform: (l -> l -> l) -> tt -> tt -> tt
end

module type Lattice_Set = sig
  module O: Datatype.Set
  type tt = private Set of O.t | Top
  include Lattice with type t = tt and type widen_hint = O.t
  val inject_singleton: O.elt -> t
  val inject: O.t -> t
  val empty: t
  val apply2: (O.elt -> O.elt -> O.elt) -> (t -> t -> t)
  val apply1: (O.elt -> O.elt) -> (t -> t)
  val fold: ( O.elt -> 'a -> 'a) -> t -> 'a -> 'a
  val iter: ( O.elt -> unit) -> t -> unit
  val exists: (O.elt -> bool) -> t -> bool
  val for_all: (O.elt -> bool) -> t -> bool
  val project : t -> O.t
  val mem : O.elt -> t -> bool
end

module type LatValue = Datatype.S_with_collections

module Int : sig
  include module type of Integer with type t = Integer.t
  include LatValue with type t := Integer.t
  val pretty : Format.formatter -> t -> unit
  val fold : (t -> 'a -> 'a) -> inf:t -> sup:t -> step:t -> 'a -> 'a

end

(** "Relative" integers. They are subtraction between two absolute integers *)
module Rel : sig
  type t

  val pretty: t Pretty_utils.formatter

  val equal: t -> t -> bool
  val compare: t -> t -> int
  val hash: t -> int

  val zero: t
  val is_zero: t -> bool

  val sub : t -> t -> t
  val add_abs : Int.t -> t -> Int.t 
  val sub_abs : Int.t -> Int.t -> t
  val pos_rem: t -> Int.t -> t

  val check: rem:t -> modu:Int.t -> bool
end

module Make_Lattice_Base (V : LatValue) : Lattice_Base with type l = V.t
module Make_Lattice_Set (V : LatValue) : Lattice_Set with type O.elt=V.t

module Make_Hashconsed_Lattice_Set
  (V : Hptset.Id_Datatype)
  (O: Hptset.S with type elt = V.t)
  : Lattice_Set with module O = O
(** See e.g. base.ml and locations.ml to see how this functor should be
    applied. The [O] module passed as argument is the same as [O] in the
    result. It is passed here to avoid having multiple modules calling
    [Hptset.Make] on the same argument (which is not forbidden by the datatype
    library *)

module type Collapse = sig val collapse : bool end

(** If [C.collapse] then [L1.bottom,_] = [_,L2.bottom] = [bottom] *)
(* Untested *)
module Make_Lattice_Product (L1:Lattice) (L2:Lattice) (C:Collapse):
  Lattice_Product with type t1 = L1.t and type t2 = L2.t


(* Untested *)
module Make_Lattice_Sum (L1:Lattice) (L2:Lattice):
  (Lattice_Sum with type t1 = L1.t and type t2 = L2.t)


(*
Local Variables:
compile-command: "make -C ../.."
End:
*)
