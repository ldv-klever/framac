(**************************************************************************)
(*                                                                        *)
(*  This file is part of Frama-C.                                         *)
(*                                                                        *)
(*  Copyright (C) 2007-2017                                               *)
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

open Eval

let key = Structure.Key_Domain.create_key "cvalue_domain"

let extract get = match get key with
  | None -> fun _ -> Cvalue.Model.top
  | Some get -> function
    | `Bottom -> Cvalue.Model.bottom
    | `Value state -> get state

module Model = struct

  include Cvalue.Model
  type value = Main_values.CVal.t
  type location = Main_locations.PLoc.location

  (* The origin denotes whether the attached value has been reduced by
     its reinterpretation. *)
  type origin = bool

  let extract_expr _ _ _ = `Value (Cvalue.V.top, false), Alarmset.all

  let indeterminate_alarms lval = let open Cvalue.V_Or_Uninitialized in function
      | C_uninit_esc _   -> Alarmset.add (Alarms.Dangling lval)
                              (Alarmset.singleton (Alarms.Uninitialized lval))
      | C_uninit_noesc _ -> Alarmset.singleton (Alarms.Uninitialized lval)
      | C_init_esc _     -> Alarmset.singleton (Alarms.Dangling lval)
      | C_init_noesc _   -> Alarmset.none


  let eval_one_loc state lval typ =
    let eval_one_loc single_loc =
      (* ignore alarm, which will be emitted by warn_reduce_by_accessed_loc *)
      let v = Cvalue.Model.find_indeterminate state single_loc in
      Cvalue.V_Or_Uninitialized.get_v v, indeterminate_alarms lval v
    in
    fun loc (acc_result, acc_alarms) ->
      let result, alarms = eval_one_loc loc in
      let result = Cvalue_forward.make_volatile ~typ:typ result in
      Cvalue.V.join result acc_result, Alarmset.union alarms acc_alarms

  let extract_lval _oracle state lval typ loc =
    let process_one_loc = eval_one_loc state lval typ in
    let acc = Cvalue.V.bottom, Alarmset.none in
    let value1, alarms1 = Precise_locs.fold process_one_loc loc acc in
    let expr = Cil.dummy_exp (Cil_types.Lval lval) in
    let value2, alarms2 = Cvalue_forward.reinterpret expr typ value1 in
    let alarms = Alarmset.union alarms1 alarms2 in
    (* The origin denotes whether the conversion has really improved the result.
       In particular float that are top_int are reduced there. On the other hand,
       we do not want to take into account conversions unsigned -> signed, etc. *)
    let origin = Cvalue.V.(equal value1 top_int) && Cil.isFloatingType typ in
    if Cvalue.V.is_bottom value2
    then `Bottom, alarms
    else `Value (value2, origin), alarms


  let backward_location state _lval typ precise_loc value =
    let size = Precise_locs.loc_size precise_loc in
    let upto = succ (Ival.get_small_cardinal()) in
    let loc = Precise_locs.imprecise_location precise_loc in
    let eval_one_loc single_loc =
      let v = Cvalue.Model.find state single_loc in
      let v = Cvalue_forward.make_volatile ~typ v in
      Cvalue_forward.unsafe_reinterpret typ v
    in
    let process_ival base ival (acc_loc, acc_val as acc) =
      let loc_bits = Locations.Location_Bits.inject base ival in
      let single_loc = Locations.make_loc loc_bits size in
      let v = eval_one_loc single_loc in
      if Cvalue.V.intersects v value
      then Locations.Location_Bits.join loc_bits acc_loc, Cvalue.V.join v acc_val
      else acc
    in
    let fold_ival base ival acc =
      if Ival.cardinal_is_less_than ival upto
      then Ival.fold_enum (process_ival base) ival acc
      else process_ival base ival acc
    in
    let fold_location loc acc =
      try
        let loc = loc.Locations.loc in
        Locations.Location_Bits.fold_i fold_ival loc acc
      with
        Locations.Location_Bits.Error_Top -> loc.Locations.loc, value
    in
    let acc = Locations.Location_Bits.bottom, Cvalue.V.bottom in
    let loc_bits, value = fold_location loc acc in
    if Locations.Location_Bits.is_bottom loc_bits
    then `Bottom
    else
      let loc = Precise_locs.inject_location_bits loc_bits in
      `Value (Precise_locs.make_precise_loc loc ~size, value)

end


module State = struct

  type state = Model.t * Locals_scoping.clobbered_set

  let structure =
    Abstract_domain.Node (Abstract_domain.Leaf key, Abstract_domain.Void)

  include Datatype.Make_with_collections (
    struct
      include Datatype.Serializable_undefined
      type t = state
      let name = Model.name ^ "+clobbered_set"
      let reprs = List.map (fun s -> s, Locals_scoping.bottom ()) Model.reprs
      let structural_descr =
        Structural_descr.(
          t_tuple [| Model.packed_descr; pack Locals_scoping.structural_descr |])
      let pretty fmt (s, _) = Model.pretty fmt s
      let equal (a, _) (b, _) = Model.equal a b
      let compare (a, _) (b, _) = Model.compare a b
      let hash (s, _) = Model.hash s
      let rehash = Datatype.identity
      let copy = Datatype.undefined
      let mem_project = Datatype.never_any_project
    end )

  type value = Model.value
  type location = Model.location

  let top = Model.top, Locals_scoping.bottom ()
  let is_included (a, _) (b, _) = Model.is_included a b
  let join (a, clob) (b, _) = Model.join a b, clob
  let join_and_is_included a b = let r = join a b in r, equal r b

  let widen kf stmt (a, clob) (b, _) =
    let hint = Widen.getWidenHints kf stmt in
    Model.widen hint a b, clob

  type origin = Model.origin

  let extract_expr evaluate (s, _) expr = Model.extract_expr evaluate s expr
  let extract_lval oracle (s, _) lval typ loc =
    Model.extract_lval oracle s lval typ loc
  let backward_location (state, _) lval typ precise_loc value =
    Model.backward_location state lval typ precise_loc value
  let reduce_further _ _ _ = []


  module Transfer
      (Valuation: Abstract_domain.Valuation with type value = value
                                             and type origin = origin
                                             and type loc = location)
  = struct

    module T = Cvalue_transfer.Transfer (Valuation)
    type value = Valuation.value
    type location = Valuation.loc
    type state = t
    type valuation = Valuation.t

    let update valuation (s, clob) = T.update valuation s, clob

    let assign stmt lv expr assigned valuation (s, clob) =
      T.assign stmt lv expr assigned valuation s >>-: fun s ->
      (* TODO: use the value in assignment *)
      let _ =
        Eval.value_assigned assigned >>-: fun value ->
        let location = Precise_locs.imprecise_location lv.lloc in
        Locals_scoping.remember_if_locals_in_value clob location value
      in
      s, clob

    let assume stmt expr positive valuation (s, clob) =
      T.assume stmt expr positive valuation s >>-: fun s ->
      s, clob

    let init_with_clob clob = function
      | Default     -> Default
      | Continue s  -> Continue (s, clob)
      | Custom list ->
        Custom (List.map (fun (stmt, s) -> (stmt, (s, clob))) list)

    let result_with_clob bases result =
      let clob = Locals_scoping.bottom () in
      Locals_scoping.remember_bases_with_locals clob bases;
      List.map (fun post_state -> post_state, clob) result

    let start_call stmt call valuation (s, _clob) =
      match T.start_call stmt call valuation s with
      | Compute (init, b), _ ->
        Compute (init_with_clob (Locals_scoping.bottom ()) init, b)
      | Result (list, c), post_clob ->
        Result ((list >>-: fun l -> result_with_clob post_clob l), c)

    let finalize_call stmt call ~pre ~post =
      let (post_state, post_clob) = post
      and pre_state, clob = pre in
      Locals_scoping.(remember_bases_with_locals clob post_clob.clob);
      T.finalize_call stmt call ~pre:pre_state ~post:post_state
      >>-: fun state ->
      state, clob

    (* TODO *)
    let approximate_call _stmt _call (_state, _clob) = assert false

  end

  (* ------------------------------------------------------------------------ *)
  (*                                 Mem Exec                                 *)
  (* ------------------------------------------------------------------------ *)

  (* Auxiliary function that keeps only some bases inside a memory state *)
  let filter_by_bases bases (state, clob) =
    Cvalue.Model.filter_by_shape (Base.Hptset.shape bases) state, clob

  let reuse ~current_input:(state, _) ~previous_output:(output, clob) =
    let state =
      match output with
      | Cvalue.Model.Bottom | Cvalue.Model.Top as state -> state
      | Cvalue.Model.Map outputs ->
        Cvalue.Model.fold Cvalue.Model.add_base outputs state
    in
    state, clob

  (* ------------------------------------------------------------------------ *)
  (*                                  Logic                                   *)
  (* ------------------------------------------------------------------------ *)

  (* Evaluation environment. *)
  type eval_env = Eval_terms.eval_env * Locals_scoping.clobbered_set
  let env_current_state (env, clob) =
    let t = Eval_terms.env_current_state env in
    if Model.is_reachable t then `Value (t, clob) else `Bottom
  let env_annot ~pre:(pre, _) ~here:(here, clob) () =
    Eval_terms.env_annot ~pre ~here (), clob
  let env_pre_f ~pre:(pre, clob) () =
    Eval_terms.env_pre_f ~pre (), clob
  let env_post_f ~pre:(pre, _) ~post:(post, clob) ~result () =
    Eval_terms.env_post_f ~pre ~post ~result (), clob
  let eval_predicate (env, _) pred =
    match Eval_terms.eval_predicate env pred with
    | Eval_terms.True -> Alarmset.True
    | Eval_terms.False -> Alarmset.False
    | Eval_terms.Unknown -> Alarmset.Unknown
  let reduce_by_predicate (env, clob) b pred =
    Eval_terms.reduce_by_predicate env b pred, clob


  (* ---------------------------------------------------------------------- *)
  (*                             Specifications                             *)
  (* ---------------------------------------------------------------------- *)

  (* Evaluate [kf] in state [with_formals], first by reducing by the
     preconditions, then by evaluating the assigns, then by reducing
     by the post-conditions. *)
  let compute_using_specification call_kinstr call spec state =
    if Value_parameters.InterpreterMode.get ()
    then begin
      Value_util.warning_once_current "Library function call. Stopping.";
      exit 0
    end;
    Value_parameters.feedback ~once:true "@[using specification for function %a@]"
      Kernel_function.pretty call.kf;
    Cvalue_specification.compute_using_specification
      call spec ~call_kinstr ~with_formals:state
    >>-: fun result ->
    let aux (offsm, post_state) =
      match offsm with
      | None -> post_state
      | Some offsm ->
        let vi = Extlib.the call.return in
        let b = Base.of_varinfo vi in
        Cvalue.Model.add_base b offsm post_state
    in
    List.map aux result.Value_types.c_values, result.Value_types.c_clobbered

  let compute_using_specification call_kinstr call fundec (state, clob) =
    compute_using_specification call_kinstr call fundec state
    >>- fun (res, sclob) ->
    Locals_scoping.(remember_bases_with_locals clob sclob);
    let list = List.map (fun return -> return, clob) res in
    Bottom.bot_of_list list


  (* ------------------------------------------------------------------------ *)
  (*                             Initialization                               *)
  (* ------------------------------------------------------------------------ *)

  let initialize_var (state, clob) _lval loc value =
    let value = match value with
      | `Bottom           -> Cvalue.V_Or_Uninitialized.uninitialized
      | `Value (v, true)  -> Cvalue.V_Or_Uninitialized.C_init_noesc v
      | `Value (v, false) -> Cvalue.V_Or_Uninitialized.C_uninit_noesc v
    in
    let loc = Precise_locs.imprecise_location loc in
    Model.add_indeterminate_binding ~exact:true state loc value, clob

  let empty () =
    let open Cvalue in
    let state = Model.empty_map in
    let min_valid = Base.min_valid_absolute_address () in
    let max_valid = Base.max_valid_absolute_address () in
    if Integer.le min_valid max_valid
    then begin
      (* Bind everything between [0..max] to bottom. Offsetmaps cannot
         contain holes, which can happen when min > 0 holds. *)
      let bot =
        V_Offsetmap.create_isotropic
          ~size:max_valid (V_Or_Uninitialized.initialized V.bottom)
      in
      let v = if true (* TODO: command line option *)
        then V_Or_Uninitialized.initialized V.top_int
        else V_Or_Uninitialized.uninitialized
      in
      let offsm =
        V_Offsetmap.add
          (min_valid, max_valid) (v, Integer.one, Abstract_interp.Rel.zero) bot
      in
      Cvalue.Model.add_base Base.null offsm state, Locals_scoping.bottom ()
    end
    else state, Locals_scoping.bottom ()

  let initialize_var_using_type (state, clob) varinfo =
    Cvalue_init.initialize_var_using_type varinfo state, clob

  let global_state () =
    if Db.Value.globals_use_supplied_state ()
    then
      let state = Db.Value.globals_state () in
      let state =
        if Model.is_reachable state
        then `Value (state,  Locals_scoping.bottom ())
        else `Bottom
      in
      Some state
    else None


  (* ------------------------------------------------------------------------ *)
  (*                                  Misc                                    *)
  (* ------------------------------------------------------------------------ *)

  let enter_scope _kf vars (state, clob) =
    let bind_local state vi =
      let b = Base.of_varinfo vi in
      let offsm =
        Bottom.non_bottom (Cvalue.Default_offsetmap.default_offsetmap b)
      in
      Model.add_base b offsm state
    in
    List.fold_left bind_local state vars, clob

  let leave_scope kf vars (state, clob) =
    let state = Model.remove_variables vars state in
    try
      let fdec = Kernel_function.get_definition kf in
      Locals_scoping.make_escaping_fundec fdec clob vars state, clob
    with Kernel_function.No_Definition -> state, clob

  let enter_loop _stmt (s, clob) = s, clob

  let leave_loop _stmt (s, clob) = s, clob

  let incr_loop_counter _stmt (s, clob) = s, clob


  (* ------------------------------------------------------------------------ *)
  (*                                Storage                                   *)
  (* ------------------------------------------------------------------------ *)

  module Store = struct
    let register_initial_state callstack (state, _clob) =
      Db.Value.merge_initial_state callstack state
    let register_state_before_stmt callstack stmt (state, _clob) =
      Db.Value.update_callstack_table ~after:false stmt callstack state
    let register_state_after_stmt callstack stmt (state, _clob) =
      Db.Value.update_callstack_table ~after:true stmt callstack state

    let return state =
      if Cvalue.Model.(equal state bottom)
      then `Bottom
      else `Value (state, Locals_scoping.top ())

    let lift_tbl tbl =
      let open Value_types in
      let h = Callstack.Hashtbl.create 7 in
      let process callstack state =
        Callstack.Hashtbl.replace h callstack (state, Locals_scoping.top ())
      in
      Callstack.Hashtbl.iter process tbl;
      h

    let get_initial_state kf = return (Db.Value.get_initial_state kf)
    let get_initial_state_by_callstack kf =
      Extlib.opt_map lift_tbl (Db.Value.get_initial_state_callstack kf)

    let get_stmt_state stmt = return (Db.Value.get_stmt_state stmt)
    let get_stmt_state_by_callstack ~after stmt =
      Extlib.opt_map lift_tbl (Db.Value.get_stmt_state_callstack ~after stmt)

  end
end


let inject cvalue_model = cvalue_model, Locals_scoping.bottom ()
let project (state, _) = state


type prefix = Hptmap.prefix
module Subpart = struct
  type t = Model.subtree
  let hash = Model.hash_subtree
  let equal = Model.equal_subtree
end
let distinct_subpart a b =
  if Model.equal a b then None
  else
    try Model.comp_prefixes a b; None
    with Model.Found_prefix (p, s1, s2) -> Some (p, s1, s2)
let find_subpart s prefix = Model.find_prefix s prefix

(*
Local Variables:
compile-command: "make -C ../../../../.."
End:
*)
