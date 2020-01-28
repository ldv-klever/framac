(**************************************************************************)
(*                                                                        *)
(*  This file is part of WP plug-in of Frama-C.                           *)
(*                                                                        *)
(*  Copyright (C) 2007-2019                                               *)
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
Require Reals.Rbasic_fun.
Require Reals.R_sqrt.
Require BuiltIn.
Require bool.Bool.
Require int.Int.
Require real.Real.
Require real.RealInfix.
Require real.Abs.
Require real.FromInt.
Require real.Square.

(* Why3 goal *)
Definition f32 : Type.
Admitted.

(* Why3 goal *)
Definition f64 : Type.
Admitted.

(* Why3 goal *)
Definition to_f32: R -> f32.
Admitted.

(* Why3 goal *)
Definition of_f32: f32 -> R.
Admitted.

(* Why3 goal *)
Definition to_f64: R -> f64.
Admitted.

(* Why3 goal *)
Definition of_f64: f64 -> R.
Admitted.

(* Why3 goal *)
Lemma to_f32_zero : ((of_f32 (to_f32 0%R)) = 0%R).
Admitted.

(* Why3 goal *)
Lemma to_f32_one : ((of_f32 (to_f32 1%R)) = 1%R).
Admitted.

(* Why3 goal *)
Lemma to_f64_zero : ((of_f64 (to_f64 0%R)) = 0%R).
Admitted.

(* Why3 goal *)
Lemma to_f64_one : ((of_f64 (to_f64 1%R)) = 1%R).
Admitted.

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
Definition round_float: rounding_mode -> R -> f32.
Admitted.

(* Why3 goal *)
Definition round_double: rounding_mode -> R -> f64.
Admitted.

(* Why3 goal *)
Lemma float_32 : forall (x:R), ((to_f32 x) = (round_float NearestTiesToEven
  x)).
Admitted.

(* Why3 goal *)
Lemma float_64 : forall (x:R), ((to_f64 x) = (round_double NearestTiesToEven
  x)).
Admitted.

(* Why3 assumption *)
Inductive float_kind :=
  | Finite : float_kind
  | NaN : float_kind
  | Inf_pos : float_kind
  | Inf_neg : float_kind.
Axiom float_kind_WhyType : WhyType float_kind.
Existing Instance float_kind_WhyType.

(* Why3 goal *)
Definition classify_f32: f32 -> float_kind.
Admitted.

(* Why3 goal *)
Definition classify_f64: f64 -> float_kind.
Admitted.

(* Why3 assumption *)
Definition is_finite_f32 (f:f32): Prop := ((classify_f32 f) = Finite).

(* Why3 assumption *)
Definition is_finite_f64 (d:f64): Prop := ((classify_f64 d) = Finite).

(* Why3 assumption *)
Definition is_NaN_f32 (f:f32): Prop := ((classify_f32 f) = NaN).

(* Why3 assumption *)
Definition is_NaN_f64 (d:f64): Prop := ((classify_f64 d) = NaN).

(* Why3 assumption *)
Definition is_infinite_f32 (f:f32): Prop := ((classify_f32 f) = Inf_pos) \/
  ((classify_f32 f) = Inf_neg).

(* Why3 assumption *)
Definition is_infinite_f64 (d:f64): Prop := ((classify_f64 d) = Inf_pos) \/
  ((classify_f64 d) = Inf_neg).

(* Why3 assumption *)
Definition is_positive_infinite_f32 (f:f32): Prop :=
  ((classify_f32 f) = Inf_pos).

(* Why3 assumption *)
Definition is_positive_infinite_f64 (d:f64): Prop :=
  ((classify_f64 d) = Inf_pos).

(* Why3 assumption *)
Definition is_negative_infinite_f32 (f:f32): Prop :=
  ((classify_f32 f) = Inf_neg).

(* Why3 assumption *)
Definition is_negative_infinite_f64 (d:f64): Prop :=
  ((classify_f64 d) = Inf_neg).

(* Why3 goal *)
Lemma is_finite_to_float_32 : forall (x:R), (is_finite_f32 (to_f32 x)).
Admitted.

(* Why3 goal *)
Lemma is_finite_to_float_64 : forall (x:R), (is_finite_f64 (to_f64 x)).
Admitted.

(* Why3 goal *)
Lemma to_float_is_finite_32 : forall (f:f32), (is_finite_f32 f) ->
  ((to_f32 (of_f32 f)) = f).
Admitted.

(* Why3 goal *)
Lemma to_float_is_finite_64 : forall (d:f64), (is_finite_f64 d) ->
  ((to_f64 (of_f64 d)) = d).
Admitted.

(* Why3 assumption *)
Definition finite (x:R): Prop := (is_finite_f32 (to_f32 x)) /\ (is_finite_f64
  (to_f64 x)).

(* Why3 goal *)
Lemma finite_small_f32 : forall (x:R),
  (((-179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368%R)%R <= x)%R /\
  (x <= 340282346600000016151267322115014000640%R)%R) -> (is_finite_f32
  (to_f32 x)).
Admitted.

(* Why3 goal *)
Lemma finite_small_f64 : forall (x:R),
  (((-179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368%R)%R <= x)%R /\
  (x <= 179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368%R)%R) ->
  (is_finite_f64 (to_f64 x)).
Admitted.

(* Why3 goal *)
Lemma finite_range_f32 : forall (f:f32), (is_finite_f32 f) <->
  (((-340282346600000016151267322115014000640%R)%R <= (of_f32 f))%R /\
  ((of_f32 f) <= 340282346600000016151267322115014000640%R)%R).
Admitted.

(* Why3 goal *)
Lemma finite_range_f64 : forall (d:f64), (is_finite_f64 d) <->
  (((-179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368%R)%R <= (of_f64 d))%R /\
  ((of_f64 d) <= 179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368%R)%R).
Admitted.

(* Why3 goal *)
Definition eq_f32b: f32 -> f32 -> bool.
Admitted.

(* Why3 goal *)
Definition eq_f64b: f64 -> f64 -> bool.
Admitted.

(* Why3 assumption *)
Definition eq_f32 (x:f32) (y:f32): Prop := ((eq_f32b x y) = true).

(* Why3 assumption *)
Definition eq_f64 (x:f64) (y:f64): Prop := ((eq_f64b x y) = true).

(* Why3 goal *)
Lemma eq_finite_f32 : forall (x:f32) (y:f32), (is_finite_f32 x) ->
  ((is_finite_f32 y) -> ((eq_f32 x y) <-> ((of_f32 x) = (of_f32 y)))).
Admitted.

(* Why3 goal *)
Lemma eq_finite_f64 : forall (x:f64) (y:f64), (is_finite_f64 x) ->
  ((is_finite_f64 y) -> ((eq_f64 x y) <-> ((of_f64 x) = (of_f64 y)))).
Admitted.

(* Why3 goal *)
Definition ne_f32b: f32 -> f32 -> bool.
Admitted.

(* Why3 goal *)
Definition ne_f64b: f64 -> f64 -> bool.
Admitted.

(* Why3 assumption *)
Definition ne_f32 (x:f32) (y:f32): Prop := ((ne_f32b x y) = true).

(* Why3 assumption *)
Definition ne_f64 (x:f64) (y:f64): Prop := ((ne_f64b x y) = true).

(* Why3 goal *)
Lemma ne_finite_f32 : forall (x:f32) (y:f32), (is_finite_f32 x) ->
  ((is_finite_f32 y) -> ((ne_f32 x y) <-> ~ ((of_f32 x) = (of_f32 y)))).
Admitted.

(* Why3 goal *)
Lemma ne_finite_f64 : forall (x:f64) (y:f64), (is_finite_f64 x) ->
  ((is_finite_f64 y) -> ((ne_f64 x y) <-> ~ ((of_f64 x) = (of_f64 y)))).
Admitted.

(* Why3 goal *)
Definition le_f32b: f32 -> f32 -> bool.
Admitted.

(* Why3 goal *)
Definition le_f64b: f64 -> f64 -> bool.
Admitted.

(* Why3 assumption *)
Definition le_f32 (x:f32) (y:f32): Prop := ((le_f32b x y) = true).

(* Why3 assumption *)
Definition le_f64 (x:f64) (y:f64): Prop := ((le_f64b x y) = true).

(* Why3 goal *)
Lemma le_finite_f32 : forall (x:f32) (y:f32), (is_finite_f32 x) ->
  ((is_finite_f32 y) -> ((le_f32 x y) <-> ((of_f32 x) <= (of_f32 y))%R)).
Admitted.

(* Why3 goal *)
Lemma le_finite_f64 : forall (x:f64) (y:f64), (is_finite_f64 x) ->
  ((is_finite_f64 y) -> ((le_f64 x y) <-> ((of_f64 x) <= (of_f64 y))%R)).
Admitted.

(* Why3 goal *)
Definition lt_f32b: f32 -> f32 -> bool.
Admitted.

(* Why3 goal *)
Definition lt_f64b: f64 -> f64 -> bool.
Admitted.

(* Why3 assumption *)
Definition lt_f32 (x:f32) (y:f32): Prop := ((lt_f32b x y) = true).

(* Why3 assumption *)
Definition lt_f64 (x:f64) (y:f64): Prop := ((lt_f64b x y) = true).

(* Why3 goal *)
Lemma lt_finite_f32 : forall (x:f32) (y:f32), (is_finite_f32 x) ->
  ((is_finite_f32 y) -> ((lt_f32 x y) <-> ((of_f32 x) < (of_f32 y))%R)).
Admitted.

(* Why3 goal *)
Lemma lt_finite_f64 : forall (x:f64) (y:f64), (is_finite_f64 x) ->
  ((is_finite_f64 y) -> ((lt_f64 x y) <-> ((of_f64 x) < (of_f64 y))%R)).
Admitted.

(* Why3 goal *)
Definition neg_f32: f32 -> f32.
Admitted.

(* Why3 goal *)
Definition neg_f64: f64 -> f64.
Admitted.

(* Why3 goal *)
Lemma neg_finite_f32 : forall (x:f32), (is_finite_f32 x) ->
  ((of_f32 (neg_f32 x)) = (-(of_f32 x))%R).
Admitted.

(* Why3 goal *)
Lemma neg_finite_f64 : forall (x:f64), (is_finite_f64 x) ->
  ((of_f64 (neg_f64 x)) = (-(of_f64 x))%R).
Admitted.

(* Why3 goal *)
Definition add_f32: f32 -> f32 -> f32.
Admitted.

(* Why3 goal *)
Definition add_f64: f64 -> f64 -> f64.
Admitted.

(* Why3 goal *)
Lemma add_finite_f32 : forall (x:f32) (y:f32), (is_finite_f32 x) ->
  ((is_finite_f32 y) -> ((add_f32 x
  y) = (to_f32 ((of_f32 x) + (of_f32 y))%R))).
Admitted.

(* Why3 goal *)
Lemma add_finite_f64 : forall (x:f64) (y:f64), (is_finite_f64 x) ->
  ((is_finite_f64 y) -> ((add_f64 x
  y) = (to_f64 ((of_f64 x) + (of_f64 y))%R))).
Admitted.

(* Why3 goal *)
Definition mul_f32: f32 -> f32 -> f32.
Admitted.

(* Why3 goal *)
Definition mul_f64: f64 -> f64 -> f64.
Admitted.

(* Why3 goal *)
Lemma mul_finite_f32 : forall (x:f32) (y:f32), (is_finite_f32 x) ->
  ((is_finite_f32 y) -> ((mul_f32 x
  y) = (to_f32 ((of_f32 x) * (of_f32 y))%R))).
Admitted.

(* Why3 goal *)
Lemma mul_finite_f64 : forall (x:f64) (y:f64), (is_finite_f64 x) ->
  ((is_finite_f64 y) -> ((mul_f64 x
  y) = (to_f64 ((of_f64 x) * (of_f64 y))%R))).
Admitted.

(* Why3 goal *)
Definition div_f32: f32 -> f32 -> f32.
Admitted.

(* Why3 goal *)
Definition div_f64: f64 -> f64 -> f64.
Admitted.

(* Why3 goal *)
Lemma div_finite_f32 : forall (x:f32) (y:f32), (is_finite_f32 x) ->
  ((is_finite_f32 y) -> ((div_f32 x
  y) = (to_f32 ((of_f32 x) / (of_f32 y))%R))).
Admitted.

(* Why3 goal *)
Lemma div_finite_f64 : forall (x:f64) (y:f64), (is_finite_f64 x) ->
  ((is_finite_f64 y) -> ((div_f64 x
  y) = (to_f64 ((of_f64 x) / (of_f64 y))%R))).
Admitted.

(* Why3 goal *)
Definition sqrt_f32: f32 -> f32.
Admitted.

(* Why3 goal *)
Definition sqrt_f64: f64 -> f64.
Admitted.

(* Why3 goal *)
Lemma sqrt_finite_f32 : forall (x:f32), (is_finite_f32 x) ->
  ((sqrt_f32 x) = (to_f32 (Reals.R_sqrt.sqrt (of_f32 x)))).
Admitted.

(* Why3 goal *)
Lemma sqrt_finite_f64 : forall (x:f64), (is_finite_f64 x) ->
  ((sqrt_f64 x) = (to_f64 (Reals.R_sqrt.sqrt (of_f64 x)))).
Admitted.

(* Why3 goal *)
Definition model_f32: f32 -> R.
Admitted.

(* Why3 assumption *)
Definition delta_f32 (f:f32): R :=
  (Reals.Rbasic_fun.Rabs ((of_f32 f) - (model_f32 f))%R).

(* Why3 assumption *)
Definition error_f32 (f:f32): R :=
  ((delta_f32 f) / (Reals.Rbasic_fun.Rabs (model_f32 f)))%R.

(* Why3 goal *)
Definition model_f64: f64 -> R.
Admitted.

(* Why3 assumption *)
Definition delta_f64 (f:f64): R :=
  (Reals.Rbasic_fun.Rabs ((of_f64 f) - (model_f64 f))%R).

(* Why3 assumption *)
Definition error_f64 (f:f64): R :=
  ((delta_f64 f) / (Reals.Rbasic_fun.Rabs (model_f64 f)))%R.

