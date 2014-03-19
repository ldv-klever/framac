(**************************************************************************)
(*                                                                        *)
(*  This file is part of WP plug-in of Frama-C.                           *)
(*                                                                        *)
(*  Copyright (C) 2007-2014                                               *)
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

(* This file is generated by Why3's Coq-realize driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require Import Rbasic_fun.
Require Import R_sqrt.
Require BuiltIn.
Require real.Real.
Require real.RealInfix.
Require real.Abs.
Require real.Square.

(* Why3 goal *)
Definition to_float32: R -> R.
Admitted.

(* Why3 goal *)
Definition to_float64: R -> R.
Admitted.

(* Why3 assumption *)
Definition is_float32 (x:R): Prop := ((to_float32 x) = x).

(* Why3 assumption *)
Definition is_float64 (x:R): Prop := ((to_float64 x) = x).

(* Why3 assumption *)
Inductive rounding_mode :=
  | Up : rounding_mode
  | Down : rounding_mode
  | ToZero : rounding_mode
  | NearestTiesToAway : rounding_mode
  | NearestTiesToEven : rounding_mode.
Axiom rounding_mode_WhyType : WhyType rounding_mode.
Existing Instance rounding_mode_WhyType.

(* Why3 goal *)
Definition round_double: rounding_mode -> R -> R.
Admitted.

(* Why3 goal *)
Definition round_float: rounding_mode -> R -> R.
Admitted.

(* Why3 goal *)
Variable is_finite32: R -> Prop.

(* Why3 goal *)
Variable is_finite64: R -> Prop.

(* Why3 goal *)
Lemma float_32 : forall (x:R),
  ((to_float32 x) = (round_float NearestTiesToEven x)).
Admitted.

(* Why3 goal *)
Lemma float_64 : forall (x:R),
  ((to_float64 x) = (round_double NearestTiesToEven x)).
Admitted.

(* Why3 goal *)
Lemma is_finite_to_float_32 : forall (x:R), (is_finite32 (to_float32 x)).
Admitted.

(* Why3 goal *)
Lemma is_finite_to_float_64 : forall (x:R), (is_finite64 (to_float64 x)).
Admitted.

(* Why3 assumption *)
Definition add_float32 (x:R) (y:R): R := (to_float32 (x + y)%R).

(* Why3 assumption *)
Definition add_float64 (x:R) (y:R): R := (to_float64 (x + y)%R).

(* Why3 assumption *)
Definition mul_float32 (x:R) (y:R): R := (to_float32 (x * y)%R).

(* Why3 assumption *)
Definition mul_float64 (x:R) (y:R): R := (to_float64 (x * y)%R).

(* Why3 assumption *)
Definition div_float32 (x:R) (y:R): R := (to_float32 (Rdiv x y)%R).

(* Why3 assumption *)
Definition div_float64 (x:R) (y:R): R := (to_float64 (Rdiv x y)%R).

(* Why3 assumption *)
Definition sqrt_float32 (x:R): R := (to_float32 (sqrt x)).

(* Why3 assumption *)
Definition sqrt_float64 (x:R): R := (to_float64 (sqrt x)).

(* Why3 goal *)
Definition model: R -> R.
Admitted.

(* Why3 assumption *)
Definition delta (x:R): R := (Rabs (x - (model x))%R).

(* Why3 assumption *)
Definition error (x:R): R := (Rdiv (delta x) (Rabs (model x)))%R.

(* Why3 goal *)
Lemma model_float_32 : forall (x:R), ((model (to_float32 x)) = (model x)).
Admitted.

(* Why3 goal *)
Lemma model_float_64 : forall (x:R), ((model (to_float64 x)) = (model x)).
Admitted.

(* Why3 goal *)
Lemma model_add : forall (x:R) (y:R),
  ((model (x + y)%R) = ((model x) + (model y))%R).
Admitted.

(* Why3 goal *)
Lemma model_mul : forall (x:R) (y:R),
  ((model (x * y)%R) = ((model x) * (model y))%R).
Admitted.

(* Why3 goal *)
Lemma model_div : forall (x:R) (y:R),
  ((model (Rdiv x y)%R) = (Rdiv (model x) (model y))%R).
Admitted.

(* Why3 goal *)
Lemma model_sqrt : forall (x:R), ((model (sqrt x)) = (sqrt (model x))).
Admitted.

