(** {b Qed Public API} *)
module Hcons : sig
(**************************************************************************)
(*                                                                        *)
(*  This file is part of WP plug-in of Frama-C.                           *)
(*                                                                        *)
(*  Copyright (C) 2007-2018                                               *)
(*    CEA (Commissariat a l'energie atomique et aux energies              *)
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

(* -------------------------------------------------------------------------- *)
(**    Hash-Consing Utilities                                                 *)
(* -------------------------------------------------------------------------- *)

val primes : int array
val hash_int : int -> int
val hash_tag : 'a -> int
val hash_pair : int -> int -> int
val hash_triple : int -> int -> int -> int
val hash_list : ('a -> int) -> int -> 'a list -> int
val hash_array : ('a -> int) -> int -> 'a array -> int
val hash_opt : ('a -> int) -> int -> 'a option -> int

val eq_list : 'a list -> 'a list -> bool (** Uses [==]. *)
val eq_array : 'a array -> 'a array -> bool (** Uses [==]. *)
val equal_list : ('a -> 'a -> bool) -> 'a list -> 'a list -> bool
val equal_array : ('a -> 'a -> bool) -> 'a array -> 'a array -> bool
val compare_list : ('a -> 'a -> int) -> 'a list -> 'a list -> int

val exists_array : ('a -> bool) -> 'a array -> bool
val forall_array : ('a -> bool) -> 'a array -> bool

val fold_list : ('a -> 'a -> 'a) -> ('b -> 'a) -> 'a -> 'b list -> 'a
val fold_array : ('a -> 'a -> 'a) -> ('b -> 'a) -> 'a -> 'b array -> 'a
end
module Listset : sig
(**************************************************************************)
(*                                                                        *)
(*  This file is part of WP plug-in of Frama-C.                           *)
(*                                                                        *)
(*  Copyright (C) 2007-2018                                               *)
(*    CEA (Commissariat a l'energie atomique et aux energies              *)
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

(* -------------------------------------------------------------------------- *)
(** Merging Set Functor *)
(* -------------------------------------------------------------------------- *)

module type Elt =
sig
  type t
  val equal : t -> t -> bool
  val compare : t -> t -> int
end

module Make(E : Elt) :
sig

  type elt = E.t

  type t = elt list
  val equal : t -> t -> bool
  val compare : t -> t -> int

  val empty : t

  (* good sharing *)
  val add : elt -> t -> t

  (* good sharing *)
  val remove : elt -> t -> t
  val mem : elt -> t -> bool
  val iter : (elt -> unit) -> t -> unit
  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a

  (* good sharing *)
  val filter : (elt -> bool) -> t -> t
  val partition : (elt -> bool) -> t -> t * t

  (* good sharing *)
  val union : t -> t -> t

  (* good sharing *)
  val inter : t -> t -> t

  (* good sharing *)
  val diff : t -> t -> t

  val subset : t -> t -> bool
  val intersect : t -> t -> bool
  val factorize : t -> t -> t * t * t
  (** Returns (left,common,right) *)

  val big_union : t list -> t
  val big_inter : t list -> t

end
end
module Listmap : sig
(**************************************************************************)
(*                                                                        *)
(*  This file is part of WP plug-in of Frama-C.                           *)
(*                                                                        *)
(*  Copyright (C) 2007-2018                                               *)
(*    CEA (Commissariat a l'energie atomique et aux energies              *)
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

(* -------------------------------------------------------------------------- *)
(** Merging List-Association Functor *)
(* -------------------------------------------------------------------------- *)

module type Key =
sig
  type t
  val equal : t -> t -> bool
  val compare : t -> t -> int
end

module Make(K : Key) :
sig

  type key = K.t

  type 'a t = (key * 'a) list

  val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
  
  val empty : 'a t
  val add : key -> 'a -> 'a t -> 'a t
  val mem : key -> 'a t -> bool
  val find : key -> 'a t -> 'a
  val findk : key -> 'a t -> key * 'a
  val remove : key -> 'a t -> 'a t

  (** [insert (fun key v old -> ...) key v map] *)
  val insert : (key -> 'a -> 'a -> 'a) -> key -> 'a -> 'a t -> 'a t

  val change : (key -> 'b -> 'a option -> 'a option) -> key -> 'b -> 'a t -> 'a t

  val filter : (key -> 'a -> bool) -> 'a t -> 'a t
  val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t

  val map : ('a -> 'b) -> 'a t -> 'b t
  val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
  val mapf : (key -> 'a -> 'b option) -> 'a t -> 'b t
  val mapq : (key -> 'a -> 'a option) -> 'a t -> 'a t
  val iter : (key -> 'a -> unit) -> 'a t -> unit
  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b

  val union : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t
  val inter : (key -> 'a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t
  val interf : (key -> 'a -> 'b -> 'c option) -> 'a t -> 'b t -> 'c t
  val interq : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t
  val diffq : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t
  val subset : (key -> 'a -> 'b -> bool) -> 'a t -> 'b t -> bool

  val iterk : (key -> 'a -> 'b -> unit) -> 'a t -> 'b t -> unit
  val iter2 : (key -> 'a option -> 'b option -> unit) -> 'a t -> 'b t -> unit
  val merge : (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t

end
end
module Intset : sig
(**************************************************************************)
(*                                                                        *)
(*  This file is part of WP plug-in of Frama-C.                           *)
(*                                                                        *)
(*  Copyright (C) 2007-2018                                               *)
(*    CEA (Commissariat a l'energie atomique et aux energies              *)
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

(** Set of integers using Patricia Trees.

    From the paper of Chris Okasaki and Andrew Gill:
    'Fast Mergeable Integer Maps'.
*)

type t

val compare : t -> t -> int
val equal : t -> t -> bool

val empty : t
val singleton : int -> t

val is_empty : t -> bool
val cardinal : t -> int
val elements : t -> int list

val mem : int -> t -> bool
val add : int -> t -> t
val remove :int -> t -> t
val union : t -> t -> t
val inter : t -> t -> t
val diff : t -> t -> t
val subset : t -> t -> bool

val iter : (int -> unit) -> t -> unit
val fold : (int -> 'a -> 'a) -> t -> 'a -> 'a

val for_all : (int -> bool) -> t -> bool
val exists : (int -> bool) -> t -> bool
val filter : (int -> bool) -> t -> t
val partition : (int -> bool) -> t -> t * t

val intersect : t -> t -> bool
end
module Intmap : sig
(**************************************************************************)
(*                                                                        *)
(*  This file is part of WP plug-in of Frama-C.                           *)
(*                                                                        *)
(*  Copyright (C) 2007-2018                                               *)
(*    CEA (Commissariat a l'energie atomique et aux energies              *)
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

(** Maps with integers keys using Patricia Trees.

    From the paper of Chris Okasaki and Andrew Gill:
    'Fast Mergeable Integer Maps'.
*)

type 'a t

val empty : 'a t
val singleton : int -> 'a -> 'a t

val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool

val is_empty : 'a t -> bool
val size : 'a t -> int
val mem : int -> 'a t -> bool
val find : int -> 'a t -> 'a (** or raise Not_found *)

val add : int -> 'a -> 'a t -> 'a t
val remove : int -> 'a t -> 'a t

(** [insert (fun key v old -> ...) key v map] *)
val insert : (int -> 'a -> 'a -> 'a) -> int -> 'a -> 'a t -> 'a t

val change : (int -> 'b -> 'a option -> 'a option) -> int -> 'b -> 'a t -> 'a t

val iter : ('a -> unit) -> 'a t -> unit
val iteri : (int -> 'a -> unit) -> 'a t -> unit

val fold : ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b
val foldi : (int -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b

val mapl : (int -> 'a -> 'b) -> 'a t -> 'b list

val map : ('a -> 'b) -> 'a t -> 'b t
val mapi : (int -> 'a -> 'b) -> 'a t -> 'b t
val mapf : (int -> 'a -> 'b option) -> 'a t -> 'b t
val mapq : (int -> 'a -> 'a option) -> 'a t -> 'a t
val filter : (int -> 'a -> bool) -> 'a t -> 'a t
val partition : (int -> 'a -> bool) -> 'a t -> 'a t * 'a t
val partition_split : (int -> 'a -> 'a option * 'a option) -> 'a t -> 'a t * 'a t

val for_all: (int -> 'a -> bool) -> 'a t -> bool
val exists: (int -> 'a -> bool) -> 'a t -> bool

val union : (int -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t
val inter : (int -> 'a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t
val interf : (int -> 'a -> 'b -> 'c option) -> 'a t -> 'b t -> 'c t
val interq : (int -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t
val diffq :  (int -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t
val subsetk : 'a t -> 'b t -> bool
val subset : (int -> 'a -> 'b -> bool) -> 'a t -> 'b t -> bool
val intersect : 'a t -> 'b t -> bool
val intersectf : (int -> 'a -> 'b -> bool) -> 'a t -> 'b t -> bool


val merge : (int -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t
val iter2 : (int -> 'a option -> 'b option -> unit) -> 'a t -> 'b t -> unit
val iterk : (int -> 'a -> 'b -> unit) -> 'a t -> 'b t -> unit

val pp_bits : Format.formatter -> int -> unit
val pp_tree : string -> Format.formatter -> 'a t -> unit
end
module Idxset : sig
(**************************************************************************)
(*                                                                        *)
(*  This file is part of WP plug-in of Frama-C.                           *)
(*                                                                        *)
(*  Copyright (C) 2007-2018                                               *)
(*    CEA (Commissariat a l'energie atomique et aux energies              *)
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

(** Set of indexed elements implemented as Patricia sets. *)

module type S =
sig
  type elt
  type t
  val empty : t
  val is_empty : t -> bool
  val mem : elt -> t -> bool
  val find : elt -> t -> elt
  val add : elt -> t -> t
  val singleton : elt -> t
  val remove : elt -> t -> t
  val union : t -> t -> t
  val inter : t -> t -> t
  val diff : t -> t -> t
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val subset : t -> t -> bool
  val iter : (elt -> unit) -> t -> unit
  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
  val for_all : (elt -> bool) -> t -> bool
  val exists : (elt -> bool) -> t -> bool
  val filter : (elt -> bool) -> t -> t
  val partition : (elt -> bool) -> t -> t * t
  val cardinal : t -> int
  val elements : t -> elt list
  val map : (elt -> elt) -> t -> t
  val mapf : (elt -> elt option) -> t -> t
  val intersect : t -> t -> bool
end

module type IndexedElements =
sig
  type t
  val id : t -> int (** unique per t *)
end

module Make( E : IndexedElements ) : S with type elt = E.t
end
module Idxmap : sig
(**************************************************************************)
(*                                                                        *)
(*  This file is part of WP plug-in of Frama-C.                           *)
(*                                                                        *)
(*  Copyright (C) 2007-2018                                               *)
(*    CEA (Commissariat a l'energie atomique et aux energies              *)
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

(** Map with indexed keys *)

module type S =
sig
  type key
  type 'a t
  val is_empty : 'a t -> bool
  val empty : 'a t
  val add : key -> 'a -> 'a t -> 'a t
  val mem : key -> 'a t -> bool
  val find : key -> 'a t -> 'a
  val remove : key -> 'a t -> 'a t
  val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
  val iter : (key -> 'a -> unit) -> 'a t -> unit
  val map : (key -> 'a -> 'b) -> 'a t -> 'b t
  val mapf : (key -> 'a -> 'b option) -> 'a t -> 'b t
  val mapq : (key -> 'a -> 'a option) -> 'a t -> 'a t
  val filter : (key -> 'a -> bool) -> 'a t -> 'a t
  val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t
  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val union : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t
  val inter : (key -> 'a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t
  val interf : (key -> 'a -> 'b -> 'c option) -> 'a t -> 'b t -> 'c t
  val interq : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t
  val diffq : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t
  val merge : (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t
  val iter2 : (key -> 'a option -> 'b option -> unit) -> 'a t -> 'b t -> unit
  val subset : (key -> 'a -> 'b -> bool) -> 'a t -> 'b t -> bool

  (** [insert (fun key v old -> ...) key v map] *)
  val insert : (key -> 'a -> 'a -> 'a) -> key -> 'a -> 'a t -> 'a t

  val change : (key -> 'b -> 'a option -> 'a option) -> key -> 'b -> 'a t -> 'a t

end

module type IndexedKey =
sig
  type t
  val id : t -> int (** unique per t *)
end

module Make( K : IndexedKey ) : S with type key = K.t
end
module Mergemap : sig
(**************************************************************************)
(*                                                                        *)
(*  This file is part of WP plug-in of Frama-C.                           *)
(*                                                                        *)
(*  Copyright (C) 2007-2018                                               *)
(*    CEA (Commissariat a l'energie atomique et aux energies              *)
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

(* -------------------------------------------------------------------------- *)
(** Merging Map Functor *)
(* -------------------------------------------------------------------------- *)

module type Key =
sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
end

module Make(K : Key) :
sig

  type key = K.t

  type 'a t = (key * 'a) list Intmap.t

  val is_empty : 'a t -> bool

  val empty : 'a t
  val add : key -> 'a -> 'a t -> 'a t
  val mem : key -> 'a t -> bool
  val find : key -> 'a t -> 'a
  val findk : key -> 'a t -> key * 'a
  val remove : key -> 'a t -> 'a t
  val size : 'a t -> int

  (** [insert (fun key v old -> ...) key v map] *)
  val insert : (key -> 'a -> 'a -> 'a) -> key -> 'a -> 'a t -> 'a t

  val change : (key -> 'b -> 'a option -> 'a option) -> key -> 'b -> 'a t -> 'a t

  val filter : (key -> 'a -> bool) -> 'a t -> 'a t
  val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t

  val map : ('a -> 'b) -> 'a t -> 'b t
  val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
  val mapf : (key -> 'a -> 'b option) -> 'a t -> 'b t
  val mapq : (key -> 'a -> 'a option) -> 'a t -> 'a t

  val iter : (key -> 'a -> unit) -> 'a t -> unit
  val iter_sorted : (key -> 'a -> unit) -> 'a t -> unit
  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val fold_sorted: (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val union : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t
  val inter : (key -> 'a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t
  val interf : (key -> 'a -> 'b -> 'c option) -> 'a t -> 'b t -> 'c t
  val interq : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t
  val diffq : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t
  val subset : (key -> 'a -> 'b -> bool) -> 'a t -> 'b t -> bool
  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool

  val iterk : (key -> 'a -> 'b -> unit) -> 'a t -> 'b t -> unit
  val iter2 : (key -> 'a option -> 'b option -> unit) -> 'a t -> 'b t -> unit
  val merge : (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t

end
end
module Mergeset : sig
(**************************************************************************)
(*                                                                        *)
(*  This file is part of WP plug-in of Frama-C.                           *)
(*                                                                        *)
(*  Copyright (C) 2007-2018                                               *)
(*    CEA (Commissariat a l'energie atomique et aux energies              *)
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

(* -------------------------------------------------------------------------- *)
(** Merging Set Functor *)
(* -------------------------------------------------------------------------- *)

module type Elt =
sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
end

module Make(E : Elt) :
sig

  type elt = E.t

  type t = elt list Intmap.t

  val equal : t -> t -> bool
  val compare : t -> t -> int
  
  val is_empty : t -> bool
  val empty : t

  (* good sharing *)
  val add : elt -> t -> t
  val singleton : elt -> t
  val elements : t -> elt list

  (* good sharing *)
  val remove : elt -> t -> t

  val mem : elt -> t -> bool
  val iter : (elt -> unit) -> t -> unit
  val iter_sorted : (elt -> unit) -> t -> unit
  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
  val fold_sorted: (elt -> 'a -> 'a) -> t -> 'a -> 'a

  val filter : (elt -> bool) -> t -> t
  val partition : (elt -> bool) -> t -> t * t
  val for_all : (elt -> bool) -> t -> bool
  val exists : (elt -> bool) -> t -> bool

  val union : t -> t -> t
  val inter : t -> t -> t
  val diff  : t -> t -> t
  val subset : t -> t -> bool
  val intersect : t -> t -> bool

  val of_list : elt list -> t
end
end
module Collection : sig
(**************************************************************************)
(*                                                                        *)
(*  This file is part of WP plug-in of Frama-C.                           *)
(*                                                                        *)
(*  Copyright (C) 2007-2018                                               *)
(*    CEA (Commissariat a l'energie atomique et aux energies              *)
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

(* -------------------------------------------------------------------------- *)
(** Merging Maps and Sets *)
(* -------------------------------------------------------------------------- *)

module type T =
sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
end

module type Map =
sig

  type key

  type 'a t

  val empty : 'a t
  val add : key -> 'a -> 'a t -> 'a t
  val mem : key -> 'a t -> bool
  val find : key -> 'a t -> 'a
  val findk : key -> 'a t -> key * 'a
  val size : 'a t -> int
  val is_empty : 'a t -> bool

  (** [insert (fun key v old -> ...) key v map] *)
  val insert : (key -> 'a -> 'a -> 'a) -> key -> 'a -> 'a t -> 'a t

  val change : (key -> 'b -> 'a option -> 'a option) -> key -> 'b -> 'a t -> 'a t

  val map  : ('a -> 'b) -> 'a t -> 'b t
  val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
  val mapf : (key -> 'a -> 'b option) -> 'a t -> 'b t
  val mapq : (key -> 'a -> 'a option) -> 'a t -> 'a t
  val filter : (key -> 'a -> bool) -> 'a t -> 'a t
  val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t
  val iter : (key -> 'a -> unit) -> 'a t -> unit
  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b

  val iter_sorted : (key -> 'a -> unit) -> 'a t -> unit
  val fold_sorted : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b

  val union : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t
  val inter : (key -> 'a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t
  val interf : (key -> 'a -> 'b -> 'c option) -> 'a t -> 'b t -> 'c t
  val interq : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t
  val diffq : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t
  val subset : (key -> 'a -> 'b -> bool) -> 'a t -> 'b t -> bool
  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool

  val iterk : (key -> 'a -> 'b -> unit) -> 'a t -> 'b t -> unit
  val iter2 : (key -> 'a option -> 'b option -> unit) -> 'a t -> 'b t -> unit
  val merge : (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t

  type domain
  val domain : 'a t -> domain

end

module type Set =
sig

  type elt

  type t

  val empty : t
  val add : elt -> t -> t
  val singleton : elt -> t
  val elements : t -> elt list
  val is_empty : t -> bool

  val mem : elt -> t -> bool
  val iter : (elt -> unit) -> t -> unit
  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a

  val filter : (elt -> bool) -> t -> t
  val partition : (elt -> bool) -> t -> t * t
  val for_all : (elt -> bool) -> t -> bool
  val exists : (elt -> bool) -> t -> bool

  val iter_sorted : (elt -> unit) -> t -> unit
  val fold_sorted : (elt -> 'a -> 'a) -> t -> 'a -> 'a

  val union : t -> t -> t
  val inter : t -> t -> t
  val diff : t -> t -> t

  val subset : t -> t -> bool
  val intersect : t -> t -> bool

  val of_list : elt list -> t

  type 'a mapping
  val mapping : (elt -> 'a) -> t -> 'a mapping

end

module type S =
sig

  type t
  type set
  type 'a map

  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int

  module Map : Map
    with type 'a t = 'a map
     and type key = t
     and type domain = set
  module Set : Set
    with type t = set
     and type elt = t
     and type 'a mapping = 'a map

end

module Make(A : T) : S with type t = A.t
end
module Partition : sig
(**************************************************************************)
(*                                                                        *)
(*  This file is part of WP plug-in of Frama-C.                           *)
(*                                                                        *)
(*  Copyright (C) 2007-2018                                               *)
(*    CEA (Commissariat a l'energie atomique et aux energies              *)
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

(** Union-find based partitions *)

module type Elt =
sig
  type t
  val equal : t -> t -> bool
  val compare : t -> t -> int
end

module type Set =
sig
  type t
  type elt
  val singleton : elt -> t
  val iter : (elt -> unit) -> t -> unit
  val union : t -> t -> t
  val inter : t -> t -> t
end

module type Map =
sig
  type 'a t
  type key
  val empty : 'a t
  val is_empty : 'a t -> bool
  val find : key -> 'a t -> 'a
  val add : key -> 'a -> 'a t -> 'a t
  val remove : key -> 'a t -> 'a t
  val iter : (key -> 'a -> unit) -> 'a t -> unit
end


module Make(E : Elt)
    (S : Set with type elt = E.t)
    (M : Map with type key = E.t) :
sig
  type t
  type elt = E.t
  type set = S.t

  val empty : t
  val equal : t -> elt -> elt -> bool
  val merge : t -> elt -> elt -> t
  val merge_list : t -> elt list -> t
  val merge_set : t -> set -> t
  val lookup : t -> elt -> elt
  val members : t -> elt -> set
  val iter : (elt -> set -> unit) -> t -> unit
  val unstable_iter : (elt -> elt -> unit) -> t -> unit
  val map : (elt -> elt) -> t -> t
  val union : t -> t -> t
  val inter : t -> t -> t
  val is_empty : t -> bool
end
end
module Cache : sig
(**************************************************************************)
(*                                                                        *)
(*  This file is part of WP plug-in of Frama-C.                           *)
(*                                                                        *)
(*  Copyright (C) 2007-2018                                               *)
(*    CEA (Commissariat a l'energie atomique et aux energies              *)
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

(* -------------------------------------------------------------------------- *)
(* --- Simple Caches                                                      --- *)
(* -------------------------------------------------------------------------- *)

module type S =
sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
end

module type Cache =
sig
  type 'a value
  type 'a cache
  val create : size:int -> 'a cache
  val clear : 'a cache -> unit
  val compute : 'a cache -> 'a value -> 'a value
end

module Unary(A : S) : Cache with type 'a value = A.t -> 'a
module Binary(A : S) : Cache with type 'a value = A.t -> A.t -> 'a

end
module Bvars : sig
(**************************************************************************)
(*                                                                        *)
(*  This file is part of WP plug-in of Frama-C.                           *)
(*                                                                        *)
(*  Copyright (C) 2007-2018                                               *)
(*    CEA (Commissariat a l'energie atomique et aux energies              *)
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

(* -------------------------------------------------------------------------- *)
(** Bound Variables Footprints.

    All provided operation are constant-time bitwise and integer operations.
*)
(* -------------------------------------------------------------------------- *)

type t (** An over-approximation of set of integers *)

val empty : t
val singleton : int -> t

val order : t -> int (** Max stack of binders *)
val bind : t -> t (** Decrease all elements in [s] after removing [0] *)

val union : t -> t -> t

val closed : t -> bool (** All variables are bound *)
val closed_at : int -> t -> bool
(** [closed_at n a] Does not contains variables [k<n] *)

val is_empty : t -> bool
(** No bound variables *)

val contains : int -> t -> bool
(** if [contains k s] returns [false] then [k] does not belong to [s] *)

val overlap : int -> int -> t -> bool
(** if [may_overlap k n s] returns [false] then no variable [i] with
    [k<=i<k+n] occurs in [s]. *)

val pretty : Format.formatter -> t -> unit
end
module Logic : sig
(**************************************************************************)
(*                                                                        *)
(*  This file is part of WP plug-in of Frama-C.                           *)
(*                                                                        *)
(*  Copyright (C) 2007-2018                                               *)
(*    CEA (Commissariat a l'energie atomique et aux energies              *)
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

(* -------------------------------------------------------------------------- *)
(** {1 First Order Logic Definition}                                          *)
(* -------------------------------------------------------------------------- *)

type 'a element =
  | E_none
  | E_true
  | E_false
  | E_int of int
  | E_fun of 'a * 'a element list

(** Algebraic properties for user operators. *)
type 'a operator = {
  invertible : bool ; (* x+y = x+z <-> y=z (on both side) *)
  associative : bool ; (* x+(y+z)=(x+y)+z *)
  commutative : bool ; (* x+y=y+x *)
  idempotent : bool ; (* x+x = x *)
  neutral : 'a element ;
  absorbant : 'a element ;
}

(** Algebraic properties for functions. *)
type 'a category =
  | Function      (** logic function *)
  | Constructor   (** [f xs = g ys] iff [f=g && xi=yi] *)
  | Injection     (** [f xs = f ys] iff [xi=yi] *)
  | Operator of 'a operator

(** Quantifiers and Binders *)
type binder =
  | Forall
  | Exists
  | Lambda

type ('f,'a) datatype =
  | Prop
  | Bool
  | Int
  | Real
  | Tvar of int (** ranges over [1..arity] *)
  | Array of ('f,'a) datatype * ('f,'a) datatype
  | Record of ('f *  ('f,'a) datatype) list
  | Data of 'a * ('f,'a) datatype list

type sort =
  | Sprop
  | Sbool
  | Sint
  | Sreal
  | Sdata
  | Sarray of sort

type maybe = Yes | No | Maybe

(** Ordered, hash-able and pretty-printable symbols *)
module type Symbol =
sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val pretty : Format.formatter -> t -> unit
  val debug : t -> string (** for printing during debug *)
end

(** {2 Abstract Data Types} *)
module type Data =
sig
  include Symbol
  val basename : t -> string (** hint for generating fresh names *)
end

(** {2 Field for Record Types} *)
module type Field =
sig
  include Symbol
  val sort : t -> sort (** of field *)
end

(** {2 User Defined Functions} *)
module type Function =
sig
  include Symbol
  val category : t -> t category
  val params : t -> sort list (** params ; exceeding params use Sdata *)
  val sort : t -> sort (** result *)
end

(** {2 Bound Variables} *)
module type Variable =
sig
  include Symbol
  val sort : t -> sort
  val basename : t -> string
  val dummy : t
end

(** {2 Representation of Patterns, Functions and Terms} *)

type ('f,'a) funtype = {
  result : ('f,'a) datatype ; (** Type of returned value *)
  params : ('f,'a) datatype list ; (** Type of parameters *)
}

(** representation of terms. type arguments are the following:
    - 'z: representation of integral constants
    - 'f: representation of fields
    - 'a: representation of abstract data types
    - 'd: representation of functions
    - 'x: representation of free variables
    - 'b: representation of bound term (phantom type equal to 'e)
    - 'e: sub-expression
*)
type ('f,'a,'d,'x,'b,'e) term_repr =
  | True
  | False
  | Kint  of Z.t
  | Kreal of Q.t
  | Times of Z.t * 'e      (** mult: k1 * e2 *)
  | Add   of 'e list      (** add:  e11 + ... + e1n *)
  | Mul   of 'e list      (** mult: e11 * ... * e1n *)
  | Div   of 'e * 'e
  | Mod   of 'e * 'e
  | Eq    of 'e * 'e
  | Neq   of 'e * 'e
  | Leq   of 'e * 'e
  | Lt    of 'e * 'e
  | Aget  of 'e * 'e      (** access: array1[idx2] *)
  | Aset  of 'e * 'e * 'e (** update: array1[idx2 -> elem3] *)
  | Acst  of ('f,'a) datatype * 'e (** constant array [ type -> value ] *)
  | Rget  of 'e * 'f
  | Rdef  of ('f * 'e) list
  | And   of 'e list      (** and: e11 && ... && e1n *)
  | Or    of 'e list      (** or:  e11 || ... || e1n *)
  | Not   of 'e
  | Imply of 'e list * 'e (** imply: (e11 && ... && e1n) ==> e2 *)
  | If    of 'e * 'e * 'e (** ite: if c1 then e2 else e3 *)
  | Fun   of 'd * 'e list (** Complete call (no partial app.) *)
  | Fvar  of 'x
  | Bvar  of int * ('f,'a) datatype
  | Apply of 'e * 'e list (** High-Order application (Cf. binder) *)
  | Bind  of binder * ('f,'a) datatype * 'b

type 'a affine = { constant : Z.t ; factors : (Z.t * 'a) list }

(** {2 Formulae} *)
module type Term =
sig

  module ADT : Data
  module Field : Field
  module Fun : Function
  module Var : Variable

  type term
  type bind


  module Term : Symbol with type t = term

  (** Non-structural, machine dependent, 
      but fast comparison and efficient merges *)
  module Tset : Idxset.S with type elt = term

  (** Non-structural, machine dependent, 
      but fast comparison and efficient merges *)
  module Tmap : Idxmap.S with type key = term

  (** Structuraly ordered, but less efficient access and non-linear merges *)
  module STset : Set.S with type elt = term

  (** Structuraly ordered, but less efficient access and non-linear merges *)
  module STmap : Map.S with type key = term
  
  (** {3 Variables} *)

  type var = Var.t
  type tau = (Field.t,ADT.t) datatype

  module Tau : Data with type t = tau
  module Vars : Idxset.S with type elt = var
  module Vmap : Idxmap.S with type key = var

  type pool
  val pool : ?copy:pool -> unit -> pool

  val add_var : pool -> var -> unit
  val add_vars : pool -> Vars.t -> unit
  val add_term : pool -> term -> unit

  val fresh : pool -> ?basename:string -> tau -> var
  val alpha : pool -> var -> var

  val tau_of_var : var -> tau
  val sort_of_var : var -> sort
  val base_of_var : var -> string

  (** {3 Terms} *)

  type 'a expression = (Field.t,ADT.t,Fun.t,var,bind,'a) term_repr

  type repr = term expression
  type path = int list (** position of a subterm in a term. *)
  type record = (Field.t * term) list

  val decide   : term -> bool (** Return [true] if and only the term is [e_true]. Constant time. *)
  val is_true  : term -> maybe (** Constant time. *)
  val is_false : term -> maybe (** Constant time. *)
  val is_prop  : term -> bool (** Boolean or Property *)
  val is_int   : term -> bool (** Integer sort *)
  val is_real  : term -> bool (** Real sort *)
  val is_arith : term -> bool (** Integer or Real sort *)

  val are_equal : term -> term -> maybe (** Computes equality *)
  val eval_eq   : term -> term -> bool  (** Same as [are_equal] is [Yes] *)
  val eval_neq  : term -> term -> bool  (** Same as [are_equal] is [No]  *)
  val eval_lt   : term -> term -> bool  (** Same as [e_lt] is [e_true] *)
  val eval_leq  : term -> term -> bool  (** Same as [e_leq] is [e_true]  *)

  val repr : term -> repr  (** Constant time *)
  val sort : term -> sort   (** Constant time *)
  val vars : term -> Vars.t (** Constant time *)

  val subterm: term -> path -> term
  val change_subterm: term -> path -> term -> term

  (** {3 Basic constructors} *)

  val e_true : term
  val e_false : term
  val e_bool : bool -> term
  val e_literal : bool -> term -> term
  val e_int : int -> term
  val e_float : float -> term
  val e_zint : Z.t -> term
  val e_real : Q.t -> term
  val e_var : var -> term
  val e_opp : term -> term
  val e_times : Z.t -> term -> term
  val e_sum : term list -> term
  val e_prod : term list -> term
  val e_add : term -> term -> term
  val e_sub : term -> term -> term
  val e_mul : term -> term -> term
  val e_div : term -> term -> term
  val e_mod : term -> term -> term
  val e_eq  : term -> term -> term
  val e_neq : term -> term -> term
  val e_leq : term -> term -> term
  val e_lt  : term -> term -> term
  val e_imply : term list -> term -> term
  val e_equiv : term -> term -> term
  val e_and   : term list -> term
  val e_or    : term list -> term
  val e_not   : term -> term
  val e_if    : term -> term -> term -> term
  val e_const : tau -> term -> term
  val e_get   : term -> term -> term
  val e_set   : term -> term -> term -> term
  val e_getfield : term -> Field.t -> term
  val e_record : record -> term
  val e_fun : Fun.t -> term list -> term

  val e_repr : repr -> term

  (** {3 Quantification and Binding} *)

  val e_forall : var list -> term -> term
  val e_exists : var list -> term -> term
  val e_lambda : var list -> term -> term
  val e_bind : binder -> var -> term -> term
  val e_apply : term -> term list -> term

  (** {3 Generalized Substitutions} *)

  type sigma
  val sigma : unit -> sigma
  val sigma_add : sigma -> term Tmap.t -> unit

  val e_subst : ?sigma:sigma -> (term -> term) -> term -> term
  val e_subst_var : var -> term -> term -> term

  (** {3 Locally Nameless Representation} *)

  val lc_bind : var -> term -> bind (** Close [x] as a new bound variable *)
  val lc_open : var -> bind -> term (** Instantiate top bound variable *)
  val lc_open_term : term -> bind -> term
  (** Instantiate top bound variable with the given term *)
  val lc_closed : term -> bool
  val lc_closed_at : int -> term -> bool
  val lc_vars : term -> Bvars.t
  val lc_repr : bind -> term

  val binders : term -> binder list
  (** Returns the list of head binders *)

  (** {3 Recursion Scheme} *)

  val e_map  : pool -> (term -> term) -> term -> term
  val e_iter : pool -> (term -> unit) -> term -> unit

  val f_map  : (int -> term -> term) -> int -> term -> term
  val f_iter : (int -> term -> unit) -> int -> term -> unit

  val lc_map : (term -> term) -> term -> term
  val lc_iter : (term -> unit) -> term -> unit

  (** {3 Partial Typing} *)

  (** Try to extract a type of term.
      Parameterized by optional extractors for field and functions.
      Extractors may raise [Not_found] ; however, they are only used when
      the provided kinds for fields and functions are not precise enough.
      @param field type of a field value
      @param record type of the record containing a field
      @param call type of the values returned by the function
      @raise Not_found if no type is found. *)
  val typeof :
    ?field:(Field.t -> tau) ->
    ?record:(Field.t -> tau) ->
    ?call:(Fun.t -> tau option list -> tau) -> term -> tau

  (** {3 Support for Builtins} *)

  val set_builtin : Fun.t -> (term list -> term) -> unit
  (** Register a simplifier for function [f]. The computation code
      	may raise [Not_found], in which case the symbol is not interpreted.

      	If [f] is an operator with algebraic rules (see type
      	[operator]), the children are normalized {i before} builtin
      	call.

      	Highest priority is [0].
      	Recursive calls must be performed on strictly smaller terms.
  *)

  val set_builtin_map : Fun.t -> (term list -> term list) -> unit
  (** Register a builtin for rewriting [f a1..an] into [f b1..bm].

      This is short cut for [set_builtin], where the head application of [f] avoids
      to run into an infinite loop.
  *)

  val set_builtin_eq : Fun.t -> (term -> term -> term) -> unit
  (** Register a builtin equality for comparing any term with head-symbol.
      	{b Must} only use recursive comparison for strictly smaller terms.
      	The recognized term with head function symbol is passed first.

      	Highest priority is [0].
      	Recursive calls must be performed on strictly smaller terms.
  *)

  val set_builtin_leq : Fun.t -> (term -> term -> term) -> unit
  (** Register a builtin for comparing any term with head-symbol.
      	{b Must} only use recursive comparison for strictly smaller terms.
      	The recognized term with head function symbol can be on both sides.
      	Strict comparison is automatically derived from the non-strict one.

      	Highest priority is [0].
      	Recursive calls must be performed on strictly smaller terms.
  *)

  (** {3 Specific Patterns} *)

  val consequence : term -> term -> term
  (** Knowing [h], [consequence h a] returns [b] such that [h -> (a<->b)] *)
  val literal : term -> bool * term

  val affine : term -> term affine
  val record_with : record -> (term * record) option

  (** {3 Symbol} *)

  type t = term
  val id : t -> int (** unique identifier (stored in t) *)
  val hash : t -> int (** constant access (stored in t) *)
  val equal : t -> t -> bool (** physical equality *)
  val compare : t -> t -> int (** atoms are lower than complex terms ; otherwise, sorted by id. *)
  val pretty : Format.formatter -> t -> unit
  val weigth : t -> int (** Informal size *)

  (** {3 Utilities} *)

  val is_closed : t -> bool (** No bound variables *)
  val is_simple : t -> bool (** Constants, variables, functions of arity 0 *)
  val is_atomic : t -> bool (** Constants and variables *)
  val is_primitive : t -> bool (** Constants only *)
  val is_neutral : Fun.t -> t -> bool
  val is_absorbant : Fun.t -> t -> bool

  val size : t -> int
  val basename : t -> string

  val debug : Format.formatter -> t -> unit
  val pp_id : Format.formatter -> t -> unit (** internal id *)
  val pp_rid : Format.formatter -> t -> unit (** head symbol with children id's *)
  val pp_repr : Format.formatter -> repr -> unit (** head symbol with children id's *)

  (** {2 Shared sub-terms} *)

  val is_subterm : term -> term -> bool
  (** Occurrence check. [is_subterm a b] returns [true] iff [a] is a subterm
      of [b]. Optimized {i wrt} shared subterms, term size, and term
      variables. *)

  val shared :
    ?shared:(term -> bool) ->
    ?shareable:(term -> bool) ->
    ?subterms:((term -> unit) -> term -> unit) ->
    term list -> term list
  (** Computes the sub-terms that appear several times.
      	[shared marked linked e] returns the shared subterms of [e].

      	The list of shared subterms is consistent with
      	order of definition: each trailing terms only depend on heading ones.

      	The traversal is controlled by two optional arguments:
      	- [shared] those terms are not traversed (considered as atomic, default to none)
      	- [shareable] those terms ([is_simple] excepted) that can be shared (default to all)
      	- [subterms] those sub-terms a term to be considered during
          traversal ([lc_iter] by default)
  *)

  (** Low-level shared primitives: [shared] is actually a combination of
      building marks, marking terms, and extracting definitions:

      {[ let share ?... e =
           let m = marks ?... () in
           List.iter (mark m) es ;
           defs m ]} *)

  type marks

  (** Create a marking accumulator.
      Same defaults than [shared]. *)

  val marks :
    ?shared:(term -> bool) ->
    ?shareable:(term -> bool) ->
    ?subterms:((term -> unit) -> term -> unit) ->
    unit -> marks

  (** Mark a term to be printed *)
  val mark : marks -> term -> unit

  (** Mark a term to be explicitly shared *)
  val share : marks -> term -> unit

  (** Returns a list of terms to be shared among all {i shared} or {i
      marked} subterms.  The order of terms is consistent with
      definition order: head terms might be used in tail ones. *)
  val defs : marks -> term list

end
end
module Pool : sig
(**************************************************************************)
(*                                                                        *)
(*  This file is part of WP plug-in of Frama-C.                           *)
(*                                                                        *)
(*  Copyright (C) 2007-2018                                               *)
(*    CEA (Commissariat a l'energie atomique et aux energies              *)
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

(* -------------------------------------------------------------------------- *)
(* ---     Variable Management                                            --- *)
(* -------------------------------------------------------------------------- *)

module type Type =
sig
  type t
  val dummy : t
  val equal : t -> t -> bool
end

module Make(T : Type) :
sig

  type var = (** Hashconsed *)
    private {
    vid : int ;
    vbase : string ;
    vrank : int ;
    vtau : T.t ;
  }

  val dummy : var (** null vid *)

  val hash : var -> int (** [vid] *)
  val equal : var -> var -> bool (** [==] *)
  val compare : var -> var -> int
  val pretty : Format.formatter -> var -> unit

  type pool
  val create : ?copy:pool -> unit -> pool
  val add : pool -> var -> unit
  val fresh : pool -> string -> T.t -> var
  val alpha : pool -> var -> var

end
end
module Kind : sig
(**************************************************************************)
(*                                                                        *)
(*  This file is part of WP plug-in of Frama-C.                           *)
(*                                                                        *)
(*  Copyright (C) 2007-2018                                               *)
(*    CEA (Commissariat a l'energie atomique et aux energies              *)
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

(* -------------------------------------------------------------------------- *)
(* --- Sort and Types Tools                                               --- *)
(* -------------------------------------------------------------------------- *)

(** Logic Types Utilities *)

open Logic

val of_tau : ('f,'a) datatype -> sort
val of_poly : (int -> sort) -> ('f,'a) datatype -> sort
val image : sort -> sort

val degree_of_tau  : ('f,'a) datatype -> int
val degree_of_list : ('f,'a) datatype list -> int
val degree_of_sig  : ('f,'a) funtype -> int

val type_params : int -> ('f,'a) datatype list

val merge : sort -> sort -> sort
val merge_list : ('a -> sort) -> sort -> 'a list -> sort

val tmap : ('a,'f) datatype array -> ('a,'f) datatype -> ('a,'f) datatype

val basename : sort -> string
val pretty : Format.formatter -> sort -> unit

val pp_tau :
  (Format.formatter -> int -> unit) ->
  (Format.formatter -> 'f -> unit) ->
  (Format.formatter -> 'a -> unit) ->
  Format.formatter -> ('f,'a) datatype -> unit

val pp_data :
  (Format.formatter -> 'a -> unit) ->
  (Format.formatter -> 'b -> unit) ->
  Format.formatter -> 'a -> 'b list -> unit

val pp_record:
  (Format.formatter -> 'f -> unit) ->
  (Format.formatter -> 'b -> unit) ->
  Format.formatter -> ?opened:bool -> ('f * 'b) list -> unit

val eq_tau :
  ('f -> 'f -> bool) ->
  ('a -> 'a -> bool) ->
  ('f,'a) datatype -> ('f,'a) datatype -> bool

val compare_tau:
  ('f -> 'f -> int) ->
  ('a -> 'a -> int) ->
  ('f,'a) datatype -> ('f,'a) datatype -> int

module MakeTau(F : Field)(A : Data) :
  Data with type t = (F.t,A.t) datatype

end
module Term : sig
(**************************************************************************)
(*                                                                        *)
(*  This file is part of WP plug-in of Frama-C.                           *)
(*                                                                        *)
(*  Copyright (C) 2007-2018                                               *)
(*    CEA (Commissariat a l'energie atomique et aux energies              *)
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

(** Logic expressions *)

module Make
    ( ADT : Logic.Data )
    ( Field : Logic.Field )
    ( Fun : Logic.Function )
  :
  sig
    (** Logic API *)
    include Logic.Term with module ADT = ADT
                        and module Field = Field
                        and module Fun = Fun

    (** Prints term in debug mode. *)
    val debug : Format.formatter -> term -> unit

    (** {2 Global State}
        One given [term] has valid meaning only for one particular state. *)

    type state (** Hash-consing, cache, rewriting rules, etc. *)
    val create : unit -> state
    (** Create a new fresh state. Local state is not modified. *)

    val get_state : unit -> state (** Return local state. *)
    val set_state : state -> unit (** Update local state. *)
    val clr_state : state -> unit (** Clear local state. *)

    (** Register a constant in the global state. *)
    val constant : term -> term

    (** {2 Registered Checks} *)

    val check : repr -> term -> term
    val check_unit : qed:term -> raw:term -> term
    val iter_checks : (qed:term -> raw:term -> unit) -> unit

    (** {2 Context Release} *)

    val release : unit -> unit
    (** Clear caches and checks. Global builtins are kept. *)

  end
end
module Plib : sig
(**************************************************************************)
(*                                                                        *)
(*  This file is part of WP plug-in of Frama-C.                           *)
(*                                                                        *)
(*  Copyright (C) 2007-2018                                               *)
(*    CEA (Commissariat a l'energie atomique et aux energies              *)
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

(* -------------------------------------------------------------------------- *)
(**    Pretty Printing Utilities.                                             *)
(* -------------------------------------------------------------------------- *)

(** Message Formatters *)

val kprintf : (string -> 'b) -> ('a,Format.formatter,unit,'b) format4 -> 'a
val sprintf : ('a,Format.formatter,unit,string) format4 -> 'a
val failure : ('a,Format.formatter,unit,'b) format4 -> 'a
val to_string : (Format.formatter -> 'a -> unit) -> 'a -> string

(** Pretty printers *)

type 'a printer = Format.formatter -> 'a -> unit
type 'a printer2 = Format.formatter -> 'a -> 'a -> unit

(** Function calls *)

val pp_call_var   : f:string -> 'a printer -> 'a list printer
val pp_call_void  : f:string -> 'a printer -> 'a list printer
val pp_call_apply : f:string -> 'a printer -> 'a list printer

(** Operators *)

val pp_assoc : ?e:string -> op:string -> 'a printer -> 'a list printer
val pp_binop : op:string -> 'a printer -> 'a printer2
val pp_fold_binop : ?e:string -> op:string -> 'a printer -> 'a list printer
val pp_fold_call  : ?e:string -> f:string -> 'a printer -> 'a list printer
val pp_fold_apply : ?e:string -> f:string -> 'a printer -> 'a list printer
val pp_fold_call_rev  : ?e:string -> f:string -> 'a printer -> 'a list printer
val pp_fold_apply_rev : ?e:string -> f:string -> 'a printer -> 'a list printer

(** Iterations *)

type index = Isingle | Ifirst | Ilast | Imiddle
val iteri : (index -> 'a -> unit) -> 'a list -> unit
val iterk : (int -> 'a -> unit) -> 'a list -> unit
val mapk : (int -> 'a -> 'b) -> 'a list -> 'b list

val pp_listcompact : sep:string -> 'a printer -> 'a list printer
val pp_listsep : sep:string -> 'a printer -> 'a list printer

(** string substitution *)
val global_substitute_fmt :
  Str.regexp -> string printer -> Format.formatter -> string -> unit
(** substitute the result of the given printer for each non-overlapping part
    of the given string that match the regexp *)

val iter_group : Str.regexp -> (string -> unit) -> string -> unit
(** call the given function for each non-overlapping part of the given string
    that match the regexp *)

val substitute_list  : 'a printer -> string -> 'a list printer
(** [substitute_list templ print_arg fmt l] prints in the formatter [fmt]
     the list [l] using the template [templ] and the printer [print_arg].
    The template use [%[0-9]+] hole.
*)

val is_template : string -> bool
(** Check whether the string contains [%[0-9]+] holes to be used
    with [substitute_list]. *)
end
module Pretty : sig
(**************************************************************************)
(*                                                                        *)
(*  This file is part of WP plug-in of Frama-C.                           *)
(*                                                                        *)
(*  Copyright (C) 2007-2018                                               *)
(*    CEA (Commissariat a l'energie atomique et aux energies              *)
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

(* -------------------------------------------------------------------------- *)
(**    Pretty Printer for Qed Output.                                         *)
(* -------------------------------------------------------------------------- *)

open Logic
open Format

module Make(T : Term) :
sig
  open T

  type env (** environment for pretty printing *)

  val empty : env
  val marks : env -> marks
  val known : env -> Vars.t -> env
  val fresh : env -> term -> string * env
  val bind : string -> term -> env -> env

  val pp_tau : formatter -> tau -> unit

  (** print with the given environment without modifying it *)
  val pp_term : env -> formatter -> term -> unit
  val pp_def : env -> formatter -> term -> unit

  (** print with the given environment and update it *)
  val pp_term_env : env -> formatter -> term -> unit
  val pp_def_env : env -> formatter -> term -> unit

end
end
module Engine : sig
(**************************************************************************)
(*                                                                        *)
(*  This file is part of WP plug-in of Frama-C.                           *)
(*                                                                        *)
(*  Copyright (C) 2007-2018                                               *)
(*    CEA (Commissariat a l'energie atomique et aux energies              *)
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

(* -------------------------------------------------------------------------- *)
(* --- Engine Signature                                                   --- *)
(* -------------------------------------------------------------------------- *)

(** Generic Engine Signature *)

open Format
open Plib

type op =
  | Op of string (** Infix or prefix operator *)
  | Assoc of string (** Left-associative binary operator (like + and -) *)
  | Call of string (** Logic function or predicate *)

type link =
  | F_call  of string (** n-ary function *)
  | F_subst of string (** n-ary function with substitution "foo(%1,%2)" *)
  | F_left  of string (** 2-ary function left-to-right + *)
  | F_right of string (** 2-ary function right-to-left + *)
  | F_list of string * string (** n-ary function with (cons,nil) constructors *)
  | F_assoc of string (** associative infix operator *)
  | F_bool_prop of string * string (** Has a bool and prop version *)

type callstyle =
  | CallVar  (** Call is [f(x,...)] ; [f()] can be written [f] *)
  | CallVoid (** Call is [f(x,...)] ; in [f()], [()] is mandatory *)
  | CallApply (** Call is [f x ...] *)

type mode =
  | Mpositive  (** Current scope is [Prop] in positive position. *)
  | Mnegative  (** Current scope is [Prop] in negative position. *)
  | Mterm      (** Current scope is [Term]. *)
  | Mterm_int  (** [Int]  is required but actual scope is [Term]. *)
  | Mterm_real (** [Real] is required but actual scope is [Term]. *)
  | Mint       (** Current scope is [Int]. *)
  | Mreal      (** Current scope is [Real]. *)

type flow = Flow | Atom

type cmode = Cprop | Cterm
type amode = Aint | Areal
type pmode = Positive | Negative | Boolean

type ('x,'f) ftrigger =
  | TgAny
  | TgVar  of 'x
  | TgGet  of ('x,'f) ftrigger * ('x,'f) ftrigger
  | TgSet  of ('x,'f) ftrigger * ('x,'f) ftrigger * ('x,'f) ftrigger
  | TgFun  of 'f * ('x,'f) ftrigger list
  | TgProp of 'f * ('x,'f) ftrigger list

type ('t,'f,'c) ftypedef =
  | Tabs
  | Tdef of 't
  | Trec of ('f * 't) list
  | Tsum of ('c * 't list) list

type scope = [ `Auto | `Unfolded | `Defined of string ]

module type Env =
sig
  type t
  type term
  val create : unit -> t
  val copy : t -> t
  val clear : t -> unit
  val used : t -> string -> bool
  val fresh : t -> sanitizer:('a -> string) -> ?suggest:bool -> 'a -> string
  val define : t -> string -> term -> unit
  val unfold : t -> term -> unit
  val shared : t -> term -> bool
  val shareable : t -> term -> bool
  val set_indexed_vars : t -> unit
  val iter : (string -> term -> unit) -> t -> unit
end

(** Generic Engine Signature *)

class type virtual ['z,'adt,'field,'logic,'tau,'var,'term,'env] engine =
  object

    (** {3 Linking} *)

    method sanitize : string -> string
    method virtual datatype : 'adt -> string
    method virtual field : 'field -> string
    method virtual link : 'logic -> link

    (** {3 Global and Local Environment} *)

    method env : 'env (** Returns a fresh copy of the current environment. *)
    method set_env : 'env -> unit (** Set environment. *)
    method lookup : 'term -> scope (** Term scope in the current environment. *)
    method scope : 'env -> (unit -> unit) -> unit
    (** Calls the continuation in the provided environment. 
        Previous environment is restored after return. *)

    method local : (unit -> unit) -> unit
    (** Calls the continuation in a local copy of the environment.
        Previous environment is restored after return, but allocators
        are left unchanged to enforce on-the-fly alpha-conversion. *)

    method global : (unit -> unit) -> unit
    (** Calls the continuation in a fresh local environment.
        Previous environment is restored after return. *)

    method bind : 'var -> string
    method find : 'var -> string

    (** {3 Types} *)

    method t_int  : string
    method t_real : string
    method t_bool : string
    method t_prop : string
    method t_atomic : 'tau -> bool

    method pp_array : 'tau printer (** For [Z->a] arrays *)
    method pp_farray : 'tau printer2 (** For [k->a] arrays *)

    method pp_tvar : int printer (** Type variables. *)
    method pp_datatype : 'adt -> 'tau list printer

    method pp_tau : 'tau printer (** Without parentheses. *)
    method pp_subtau : 'tau printer (** With parentheses if non-atomic. *)

    (** {3 Current Mode}

        The mode represents the expected type for a
        term to printed.  A requirement for all term printers in the
        engine is that current mode must be correctly set before call.
        Each term printer is then responsible for setting appropriate
        modes for its sub-terms.
    *)

    method mode : mode
    method with_mode : mode -> (mode -> unit) -> unit
    (** Calls the continuation with given mode for sub-terms.
        	The englobing mode is passed to continuation and then restored. *)

    method op_scope : amode -> string option
    (** Optional scoping post-fix operator when entering arithmetic mode. *)

    (** {3 Primitives} *)

    method e_true : cmode -> string (** ["true"] *)
    method e_false : cmode -> string (** ["false"] *)

    method pp_int : amode -> 'z printer
    method pp_real : Q.t printer

    (** {3 Variables} *)

    method pp_var : string printer

    (** {3 Calls}

        These printers only applies to connective, operators and
        functions that are morphisms {i w.r.t} current mode.
    *)

    method callstyle : callstyle
    method pp_fun : cmode -> 'logic -> 'term list printer
    method pp_apply : cmode -> 'term -> 'term list printer

    (** {3 Arithmetics Operators} *)

    method op_real_of_int : op
    method op_add : amode -> op
    method op_sub : amode -> op
    method op_mul : amode -> op
    method op_div : amode -> op
    method op_mod : amode -> op
    method op_minus : amode -> op

    method pp_times : formatter -> 'z -> 'term -> unit
    (** Defaults to [self#op_minus] or [self#op_mul] *)

    (** {3 Comparison Operators} *)

    method op_equal : cmode -> op
    method op_noteq : cmode -> op
    method op_eq  : cmode -> amode -> op
    method op_neq : cmode -> amode -> op
    method op_lt  : cmode -> amode -> op
    method op_leq : cmode -> amode -> op

    method pp_equal : 'term printer2
    method pp_noteq : 'term printer2

    (** {3 Arrays} *)

    method pp_array_cst : formatter -> 'tau -> 'term -> unit
    (** Constant array ["[v...]"]. *)

    method pp_array_get : formatter -> 'term -> 'term -> unit
    (** Access ["a[k]"]. *)

    method pp_array_set : formatter -> 'term -> 'term -> 'term -> unit
    (** Update ["a[k <- v]"]. *)

    (** {3 Records} *)

    method pp_get_field : formatter -> 'term -> 'field -> unit
    (** Field access. *)

    method pp_def_fields : ('field * 'term) list printer
    (** Record construction. *)

    (** {3 Logical Connectives} *)

    method op_not   : cmode -> op
    method op_and   : cmode -> op
    method op_or    : cmode -> op
    method op_imply : cmode -> op
    method op_equiv : cmode -> op

    (** {3 Conditionals} *)

    method pp_not : 'term printer
    method pp_imply : formatter -> 'term list -> 'term -> unit

    method pp_conditional : formatter -> 'term -> 'term -> 'term -> unit

    (** {3 Binders} *)

    method pp_forall : 'tau -> string list printer
    method pp_exists : 'tau -> string list printer
    method pp_lambda : (string * 'tau) list printer

    (** {3 Bindings} *)

    method shared : 'term -> bool
    method shareable : 'term -> bool
    method subterms : ('term -> unit) -> 'term -> unit
    method pp_let : formatter -> pmode -> string -> 'term -> unit

    (** {3 Terms} *)

    method is_atomic : 'term -> bool
    (** Sub-terms that require parentheses.
        	Shared sub-terms are detected on behalf of this method. *)

    method pp_flow : 'term printer
    (** Printer with shared sub-terms printed with their name and 
        without parentheses. *)

    method pp_atom : 'term printer
    (** Printer with shared sub-terms printed with their name and 
        within parentheses for non-atomic expressions. Additional
        scope terminates the expression when required (typically 
        for Coq). *)

    method pp_repr : 'term printer
    (** Raw representation of a term, as it is. This is where you should hook
        a printer to keep sharing, parentheses, and such. *)

    (** {3 Top Level} *)

    method pp_term : 'term printer
    (** Prints in {i term} mode.
        Default uses [self#pp_shared] with mode [Mterm] inside an [<hov>] box. *)

    method pp_prop : 'term printer
    (** Prints in {i prop} mode.
        Default uses [self#pp_shared] with mode [Mprop] inside an [<hv>] box. *)

    method pp_expr : 'tau -> 'term printer
    (** Prints in {i term}, {i arithmetic} or {i prop} mode with
        respect to provided type. *)

    method pp_sort : 'term printer
    (** Prints in {i term}, {i arithmetic} or {i prop} mode with
        respect to the sort of term. Boolean expression that also have a 
        property form are printed in [Mprop] mode. *)

  end
end
module Export : sig
(**************************************************************************)
(*                                                                        *)
(*  This file is part of WP plug-in of Frama-C.                           *)
(*                                                                        *)
(*  Copyright (C) 2007-2018                                               *)
(*    CEA (Commissariat a l'energie atomique et aux energies              *)
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

(* -------------------------------------------------------------------------- *)
(* --- Exportation to Foreign Languages                                   --- *)
(* -------------------------------------------------------------------------- *)

(** Export Engine Factory *)

open Format
open Logic
open Plib
open Engine

val cmode : mode -> cmode
val amode : mode -> amode
val pmode : mode -> pmode
val tmode : ('a,'f) Logic.datatype -> mode
val ctau  : ('a,'f) Logic.datatype -> cmode

val is_identifier : string -> bool
val sanitize : to_lowercase:bool -> string -> string

val debug : link -> string
val link_name : link -> string

module Make(T : Term) :
sig

  open T
  module TauMap : Map.S with type key = tau
  module Env : Env with type term := term

  type trigger = (var,Fun.t) ftrigger
  type typedef = (tau,Field.t,Fun.t) ftypedef

  class virtual engine :
    object

      method sanitize : string -> string
      method virtual datatype : ADT.t -> string
      method virtual field : Field.t -> string
      method virtual link : Fun.t -> link

      method env : Env.t (** A safe copy of the environment *)
      method set_env : Env.t -> unit (** Set the environment *)
      method marks : Env.t * T.marks (** The current environment with empty marks *)
      method lookup : term -> scope
      method set_env : Env.t -> unit
      method scope : Env.t -> (unit -> unit) -> unit
      method local : (unit -> unit) -> unit
      method global : (unit -> unit) -> unit
      method bind : var -> string
      method find : var -> string

      method virtual t_int  : string
      method virtual t_real : string
      method virtual t_bool : string
      method virtual t_prop : string
      method virtual t_atomic : tau -> bool
      method virtual pp_tvar : int printer
      method virtual pp_array : tau printer
      method virtual pp_farray : tau printer2
      method virtual pp_datatype : ADT.t -> tau list printer
      method pp_subtau : tau printer

      method mode : mode
      method with_mode : mode -> (mode -> unit) -> unit

      method virtual e_true : cmode -> string
      method virtual e_false : cmode -> string
      method virtual pp_int : amode -> Z.t printer
      method virtual pp_real : Q.t printer

      method virtual is_atomic : term -> bool
      method virtual op_spaced : string -> bool
      method virtual callstyle : callstyle
      method virtual pp_apply : cmode -> term -> term list printer
      method pp_fun : cmode -> Fun.t -> term list printer

      method virtual op_scope : amode -> string option
      method virtual op_real_of_int : op
      method virtual op_add : amode -> op
      method virtual op_sub : amode -> op
      method virtual op_mul : amode -> op
      method virtual op_div : amode -> op
      method virtual op_mod : amode -> op
      method virtual op_minus : amode -> op
      method pp_times : formatter -> Z.t -> term -> unit

      method virtual op_equal : cmode -> op
      method virtual op_noteq : cmode -> op
      method virtual op_eq  : cmode -> amode -> op
      method virtual op_neq : cmode -> amode -> op
      method virtual op_lt  : cmode -> amode -> op
      method virtual op_leq : cmode -> amode -> op

      method virtual pp_array_cst : formatter -> tau -> term -> unit
      method virtual pp_array_get : formatter -> term -> term -> unit
      method virtual pp_array_set : formatter -> term -> term -> term -> unit

      method virtual pp_get_field : formatter -> term -> Field.t -> unit
      method virtual pp_def_fields : record printer

      method virtual op_not   : cmode -> op
      method virtual op_and   : cmode -> op
      method virtual op_or    : cmode -> op
      method virtual op_imply : cmode -> op
      method virtual op_equiv : cmode -> op

      method pp_not : term printer
      method pp_imply : formatter -> term list -> term -> unit
      method pp_equal : term printer2
      method pp_noteq : term printer2

      method virtual pp_conditional : formatter -> term -> term -> term -> unit

      method virtual pp_forall : tau -> string list printer
      method virtual pp_exists : tau -> string list printer
      method virtual pp_lambda : (string * tau) list printer

      method shared : term -> bool
      method shareable : term -> bool
      method subterms : (term -> unit) -> term -> unit
      method virtual pp_let : formatter -> pmode -> string -> term -> unit
      method pp_atom : term printer
      method pp_flow : term printer
      method pp_repr : term printer

      method pp_tau : tau printer
      method pp_var : string printer
      method pp_term : term printer
      method pp_prop : term printer
      method pp_sort : term printer
      method pp_expr : tau -> term printer

    end

end
end
module Export_whycore : sig
(**************************************************************************)
(*                                                                        *)
(*  This file is part of WP plug-in of Frama-C.                           *)
(*                                                                        *)
(*  Copyright (C) 2007-2018                                               *)
(*    CEA (Commissariat a l'energie atomique et aux energies              *)
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

(* -------------------------------------------------------------------------- *)
(* --- Common Exportation Engine for Alt-Ergo and Why3                    --- *)
(* -------------------------------------------------------------------------- *)

open Logic
open Format
open Plib
open Engine

(** Common Exportation Engine for Why-3 and Alt-Ergo *)

module Make(T : Term) :
sig

  open T
  module Env : Engine.Env with type term := term
  type trigger = (T.var,Fun.t) ftrigger
  type typedef = (tau,Field.t,Fun.t) ftypedef

  class virtual engine :
    object

      method sanitize : string -> string
      method virtual datatype : ADT.t -> string
      method virtual field : Field.t -> string
      method virtual link : Fun.t -> link

      method env : Env.t
      method set_env : Env.t -> unit
      method marks : Env.t * T.marks
      method lookup : t -> scope
      method scope : Env.t -> (unit -> unit) -> unit
      method local : (unit -> unit) -> unit
      method global : (unit -> unit) -> unit

      method t_int  : string
      method t_real : string
      method t_bool : string
      method t_prop : string
      method virtual t_atomic : tau -> bool
      method pp_tvar : int printer

      method virtual pp_array : tau printer
      method virtual pp_farray : tau printer2
      method virtual pp_datatype : ADT.t -> tau list printer
      method pp_subtau : tau printer

      method mode : mode
      method with_mode : mode -> (mode -> unit) -> unit

      method virtual e_true : cmode -> string
      method virtual e_false : cmode -> string
      method virtual pp_int : amode -> Z.t printer
      method virtual pp_real : Q.t printer

      method virtual is_atomic : term -> bool
      method virtual op_spaced : string -> bool

      method virtual callstyle : callstyle
      method pp_apply : cmode -> term -> term list printer
      method pp_fun : cmode -> Fun.t -> term list printer

      method op_scope : amode -> string option
      method virtual op_real_of_int : op
      method virtual op_add : amode -> op
      method virtual op_sub : amode -> op
      method virtual op_mul : amode -> op
      method virtual op_div : amode -> op
      method virtual op_mod : amode -> op
      method virtual op_minus : amode -> op
      method pp_times : formatter -> Z.t -> term -> unit

      method virtual op_equal : cmode -> op
      method virtual op_noteq : cmode -> op
      method virtual op_eq  : cmode -> amode -> op
      method virtual op_neq : cmode -> amode -> op
      method virtual op_lt  : cmode -> amode -> op
      method virtual op_leq : cmode -> amode -> op

      method virtual pp_array_cst : formatter -> tau -> term -> unit
      method pp_array_get : formatter -> term -> term -> unit
      method pp_array_set : formatter -> term -> term -> term -> unit

      method virtual op_record : string * string
      method pp_get_field : formatter -> term -> Field.t -> unit
      method pp_def_fields : record printer

      method virtual op_not   : cmode -> op
      method virtual op_and   : cmode -> op
      method virtual op_or    : cmode -> op
      method virtual op_imply : cmode -> op
      method virtual op_equiv : cmode -> op

      method pp_not : term printer
      method pp_imply : formatter -> term list -> term -> unit
      method pp_equal : term printer2
      method pp_noteq : term printer2

      method virtual pp_conditional : formatter -> term -> term -> term -> unit

      method virtual pp_forall : tau -> string list printer
      method virtual pp_intros : tau -> string list printer
      method virtual pp_exists : tau -> string list printer
      method pp_lambda : (string * tau) list printer

      method bind : var -> string
      method find : var -> string
      method virtual pp_let : formatter -> pmode -> string -> term -> unit

      method shared : term -> bool
      method shareable : term -> bool
      method subterms : (term -> unit) -> term -> unit

      method pp_atom : term printer
      method pp_flow : term printer
      method pp_repr : term printer

      method pp_tau : tau printer
      method pp_var : string printer
      method pp_term : term printer
      method pp_prop : term printer
      method pp_sort : term printer
      method pp_expr : tau -> term printer

      method pp_param : (string * tau) printer
      method virtual pp_trigger : trigger printer
      method virtual pp_declare_adt : formatter -> ADT.t -> int -> unit
      method virtual pp_declare_def : formatter -> ADT.t -> int -> tau -> unit
      method virtual pp_declare_sum : formatter -> ADT.t -> int -> (Fun.t * tau list) list -> unit

      method pp_declare_symbol : cmode -> formatter -> Fun.t -> unit
      method declare_type : formatter -> ADT.t -> int -> typedef -> unit
      method declare_axiom : formatter -> string -> T.var list -> trigger list list -> term -> unit
      method declare_prop : kind:string -> formatter -> string -> T.var list -> trigger list list -> term -> unit

    end

end
end
module Export_altergo : sig
(**************************************************************************)
(*                                                                        *)
(*  This file is part of WP plug-in of Frama-C.                           *)
(*                                                                        *)
(*  Copyright (C) 2007-2018                                               *)
(*    CEA (Commissariat a l'energie atomique et aux energies              *)
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

open Logic
open Format
open Plib
open Engine

(** Exportation Engine for Alt-Ergo.

    Provides a full {{:Export.S.engine-c.html}engine}
    from a {{:Export.S.linker-c.html}linker}. *)

module Make(T : Term) :
sig

  open T
  module Env : Engine.Env with type term := term

  type trigger = (T.var,Fun.t) Engine.ftrigger
  type typedef = (tau,Field.t,Fun.t) Engine.ftypedef

  class virtual engine :
    object
      method set_quantify_let : bool -> unit

      method virtual get_typedef : ADT.t -> tau option
      method virtual set_typedef : ADT.t -> tau -> unit

      method typeof : term -> tau (** Defaults to T.typeof *)

      inherit [Z.t,ADT.t,Field.t,Fun.t,tau,var,term,Env.t] Engine.engine
      method marks : Env.t * T.marks
      method op_spaced : string -> bool
      method op_record : string * string
      method pp_forall : tau -> string list printer
      method pp_intros : tau -> string list printer
      method pp_exists : tau -> string list printer
      method pp_param : (string * tau) printer
      method pp_trigger : (var,Fun.t) ftrigger printer
      method pp_declare_symbol : cmode -> Fun.t printer
      method pp_declare_adt : formatter -> ADT.t -> int -> unit
      method pp_declare_def : formatter -> ADT.t -> int -> tau -> unit
      method pp_declare_sum : formatter -> ADT.t -> int -> (Fun.t * tau list) list -> unit
      method pp_goal : formatter -> term -> unit

      method declare_type : formatter -> ADT.t -> int -> typedef -> unit
      method declare_prop : kind:string -> formatter -> string -> T.var list -> trigger list list -> term -> unit
      method declare_axiom : formatter -> string -> var list -> trigger list list -> term -> unit
      method declare_signature : formatter -> Fun.t -> tau list -> tau -> unit
      method declare_definition : formatter -> Fun.t -> var list -> tau -> term -> unit

    end

end
end
module Export_why3 : sig
(**************************************************************************)
(*                                                                        *)
(*  This file is part of WP plug-in of Frama-C.                           *)
(*                                                                        *)
(*  Copyright (C) 2007-2018                                               *)
(*    CEA (Commissariat a l'energie atomique et aux energies              *)
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

open Logic
open Format
open Plib
open Engine

(** Exportation Engine for Why-3.

    Provides a full {{:Export.S.engine-c.html}engine}
    from a {{:Export.S.linker-c.html}linker}. *)

module Make(T : Term) :
sig

  open T

  module Env : Engine.Env with type term := term
  type trigger = (var,Fun.t) Engine.ftrigger
  type typedef = (tau,Field.t,Fun.t) Engine.ftypedef

  class virtual engine :
    object
      inherit [Z.t,ADT.t,Field.t,Fun.t,tau,var,term,Env.t] Engine.engine
      method marks : Env.t * T.marks
      method op_spaced : string -> bool
      method op_record : string * string
      method pp_forall : tau -> string list printer
      method pp_intros : tau -> string list printer
      method pp_exists : tau -> string list printer
      method pp_param : (string * tau) printer
      method pp_trigger : (var,Fun.t) ftrigger printer
      method pp_declare_symbol : cmode -> Fun.t printer
      method pp_declare_adt : formatter -> ADT.t -> int -> unit
      method pp_declare_def : formatter -> ADT.t -> int -> tau -> unit
      method pp_declare_sum : formatter -> ADT.t -> int -> (Fun.t * tau list) list -> unit
      method declare_type : formatter -> ADT.t -> int -> typedef -> unit
      method declare_prop : kind:string -> formatter -> string -> T.var list -> trigger list list -> term -> unit
      method declare_axiom : formatter -> string -> var list -> trigger list list -> term -> unit
      method declare_fixpoint : prefix:string -> formatter -> Fun.t -> var list -> tau -> term -> unit
      method declare_signature : formatter -> Fun.t -> tau list -> tau -> unit
      method declare_definition : formatter -> Fun.t -> var list -> tau -> term -> unit
    end

end
end
module Export_coq : sig
(**************************************************************************)
(*                                                                        *)
(*  This file is part of WP plug-in of Frama-C.                           *)
(*                                                                        *)
(*  Copyright (C) 2007-2018                                               *)
(*    CEA (Commissariat a l'energie atomique et aux energies              *)
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

open Logic
open Format

(** Exportation Engine for Coq.

    Provides a full {{:Export.S.engine-c.html}engine}
    from a {{:Export.S.linker-c.html}linker}. *)

module Make(T : Term) :
sig

  open T
  module Env : Engine.Env with type term := term
  type trigger = (var,Fun.t) Engine.ftrigger
  type typedef = (tau,Field.t,Fun.t) Engine.ftypedef

  class virtual engine :
    object
      inherit [Z.t,ADT.t,Field.t,Fun.t,tau,var,term,Env.t] Engine.engine
      method marks : Env.t * T.marks
      method op_spaced : string -> bool
      method declare_type : formatter -> ADT.t -> int -> typedef -> unit
      method declare_axiom : formatter -> string -> var list -> trigger list list -> term -> unit
      method declare_fixpoint : prefix:string -> formatter -> Fun.t -> var list -> tau -> term -> unit
      method declare_signature : formatter -> Fun.t -> tau list -> tau -> unit
      method declare_inductive : formatter -> Fun.t -> tau list -> tau -> (string * var list * trigger list list * term) list -> unit
      method declare_definition : formatter -> Fun.t -> var list -> tau -> term -> unit
    end

end
end
