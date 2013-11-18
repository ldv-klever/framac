(**************************************************************************)
(*                                                                        *)
(*  This file is part of Frama-C.                                         *)
(*                                                                        *)
(*  Copyright (C) 2007-2013                                               *)
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

open Cvalue
open Abstract_interp
open Cil
open Locations
open Value_util
open Cil_types
open Cil_datatype

exception Invalid_CEA_alloc

let make_size size =
  let size=try
	     let size = Cvalue.V.project_ival size in
	     Ival.project_int size
    with Ival.Not_Singleton_Int | V.Not_based_on_null ->
      raise Invalid_CEA_alloc
  in
  if Int.le size Int.zero then raise Invalid_CEA_alloc;
  size

(* Variables malloced by calls to [Frama_C_alloc_infinite_*] *)
module Dynamic_Alloc_Infinite_Table =
  State_builder.Hashtbl
    (Datatype.String.Hashtbl)
    (Locations.Location_Bytes)
    (struct
       let dependencies = [Db.Value.self]
       let size = 79
       let name = "Dynamic_Alloc_Infinite_Table"
     end)

(* All bases resulting from a call to malloc. Used to model 'free' correctly *)
module Dynamic_Alloc_Bases =
  State_builder.Ref
    (Base.Hptset)
    (struct
       let dependencies = [Ast.self]
       let name = "Dynamic_Alloc_Bases"
       let default () = Base.Hptset.empty
     end)
let () = Ast.add_monotonic_state Dynamic_Alloc_Bases.self

let register_malloced_base b =
  Dynamic_Alloc_Bases.set (Base.Hptset.add b (Dynamic_Alloc_Bases.get ()))

let frama_c_alloc_infinite initial_content state actuals =
  try
    let file,size = match actuals with
      | [_,file,_] -> file, Bit_utils.max_bit_size ()
      | [_,file,_;_,size,_] -> 
	file,Int.mul (Bit_utils.sizeofchar ()) (make_size size)
      | _ -> raise Invalid_CEA_alloc
    in
    let loc = Cvalue.V.fold_bases     
      (fun file_base acc -> 
	let file = match file_base with
	  | Base.String (_,e) -> 
	    ( match Base.get_string e with
		Base.CSString s -> s
	      | Base.CSWstring _s -> assert false)
	  | Base.Var (s,_) | Base.Initialized_Var (s,_) -> s.Cil_types.vname
	  | Base.Null -> "__fc_NULL"
	in
	let loc =
	  Dynamic_Alloc_Infinite_Table.memo
            (fun file ->
              let new_name =
		if Extlib.string_prefix ~strict:true "__malloc_" file
		then file
		else Format.sprintf "__malloc_%s" file
              in
              let new_name = Cabs2cil.fresh_global new_name in
              let unbounded_type =
		Cil_types.TArray
		  (charType,
		   Some (new_exp ~loc:Location.unknown
			   (Cil_types.Const (Cil_types.CStr "NOSIZE"))),
		   empty_size_cache (),[])
              in
              let new_varinfo =
		makeGlobalVar ~logic:true new_name unbounded_type
              in
              let new_offsetmap =
		Cvalue.V_Offsetmap.create_isotropic ~size initial_content
              in
              let new_base =
		Cvalue.Default_offsetmap.create_initialized_var
		  new_varinfo
		  (Base.Known (Int.zero, Int.pred size))
		  new_offsetmap
              in
              register_malloced_base new_base;
              Location_Bytes.inject new_base Ival.zero)
            file
	in
	Cvalue.V.join loc acc)
      file
      Cvalue.V.bottom
    in 
    { Value_types.c_values =  [Eval_op.wrap_ptr loc,state];
      c_clobbered = Base.SetLattice.bottom;
      c_cacheable = Value_types.Cacheable;
    }
  with
    | Ival.Error_Top | Invalid_CEA_alloc
      -> Value_parameters.error
      "Invalid argument for Frama_C_alloc_infinite function: %a"
      pretty_actuals actuals;
	do_degenerate None;
	raise Db.Value.Aborted
    | Not_found -> assert false

let () =
  Builtins.register_builtin "Frama_C_alloc_infinite_zero" 
    (frama_c_alloc_infinite Cvalue.V_Or_Uninitialized.singleton_zero) 
let () =
  Builtins.register_builtin "Frama_C_alloc_infinite" 
    (frama_c_alloc_infinite Cvalue.V_Or_Uninitialized.uninitialized) 


(* Retun an offsetmap containing <uninitialized> on its entire validity. Used
   to fill the memory returned by malloc, or to destroy it after a free *)
let unallocated_offsetmap b =
  let size = match Base.validity b with
    | Base.Known (_, m)
    | Base.Unknown (_, _, m) -> Int.succ m
    | Base.Periodic (_, _, p) -> p
    | Base.Invalid -> assert false
  in
  V_Offsetmap.create_isotropic V_Or_Uninitialized.uninitialized ~size


let malloc_var ~loc name typ (elem_sure_valid, elem_max_valid) state =
  let type_base =
    if Int.equal Int.one elem_max_valid
    then typ
    else 
      let esize_arr = Cil.kinteger64 ~loc IInt elem_max_valid in
      TArray (typ, Some esize_arr, empty_size_cache (), [])
  in
  let var = makeGlobalVar ~logic:true name type_base in
  Library_functions.register_new_var var type_base;
  (* Sizes are in bits *)
  let size_typ = Int.of_int (bitsSizeOf typ) in
  let size = Integer.mul elem_max_valid size_typ in
  let bot = V_Or_Uninitialized.initialized V.bottom in
  let offsm_default = V_Offsetmap.create_isotropic bot ~size in
  let last_bit = Integer.pred size in
  let validity = 
    if Int.equal elem_sure_valid elem_max_valid
    then
      Base.Known (Int.zero, last_bit)
    else
      let valid_size = Integer.mul elem_sure_valid size_typ in
      Base.Unknown (Int.zero, Some (Int.pred valid_size), Int.pred size)
  in
(*  Format.printf "validity: %a@." Base.pretty_validity validity; *)
  let new_base =
    Default_offsetmap.create_initialized_var var validity offsm_default
  in
  let offsm_uninitialized = unallocated_offsetmap new_base in
  let state = Model.add_base new_base offsm_uninitialized state in
  register_malloced_base new_base;
  let locv = Location_Bytes.inject new_base Ival.zero in
  { Value_types.c_values = [Eval_op.wrap_ptr locv, state] ;
    c_clobbered = Base.SetLattice.bottom;
    c_cacheable = Value_types.NoCacheCallers;
  },
  var
    
let alloc_with_validity initial_state actuals =
  try
    let esize, size = match actuals with
      | [esize,size,_] -> esize, size
      | _ -> raise Invalid_CEA_alloc
    in
    let loc = esize.eloc in
    let size = Cvalue.V.project_ival size in
    ( match Ival.min_and_max size with
      Some size_valid_arr, Some size_arr when Int.ge size_valid_arr Int.zero ->
	let name = Cabs2cil.fresh_global "Frama_C_alloc" in
        let res, _ =
          malloc_var loc name charType (size_valid_arr, size_arr) initial_state
        in
        res
    | _ -> raise Invalid_CEA_alloc )
  with Ival.Error_Top | Invalid_CEA_alloc | V.Not_based_on_null ->
    Value_parameters.error
      "Invalid argument for Frama_C_alloc_size function";
    do_degenerate None;
    raise Db.Value.Aborted

let () = Builtins.register_builtin "Frama_C_alloc_size" alloc_with_validity


(* Variable that has been returned by a call to malloc at this callstack *)
module MallocedByStack =
  State_builder.Hashtbl(Value_types.Callstack.Hashtbl)(Varinfo)
    (struct
       let name = "Value.Builtins_malloc.MallocedByStack"
       let size = 17
       let dependencies = [Ast.self]
     end)
let () = Ast.add_monotonic_state MallocedByStack.self

let regexp_alloc = Str.regexp_string "alloc"

let alloc_once_by_stack : Db.Value.builtin_sig = fun state actuals->
  let stack = call_stack () in
  try
    let exp, size_v = match actuals with
      | [exp,size,_] -> exp, size
      | _ -> Value_parameters.abort "Invalid argument(s) for stack malloc"
    in
    let cst = Cil.isIntegerConstant exp in
    try
      let v = MallocedByStack.find stack in
      let base = Base.find v in
      let offsm_uninit = unallocated_offsetmap base in
      let already_present, new_offsm =
        try
          let cur = Model.find_base base state in
          true, V_Offsetmap.join offsm_uninit cur
        with Not_found -> false, offsm_uninit
      in
      if already_present then
        if cst then
          Value_parameters.result ~current:true ~once:true
            "@[Re-allocating@ variable@ %a@]" Printer.pp_varinfo v
        else
          Value_parameters.result ~current:true ~once:true
            "@[Re-allocating@ variable@ %a@ of size %d@ (requested: %a)@]"
            Printer.pp_varinfo v (sizeOf_int v.vtype) V.pretty size_v;

      let state = Model.add_base base new_offsm state in
      let locv = Location_Bytes.inject (Base.find v) Ival.zero in
      { Value_types.c_values = [Eval_op.wrap_ptr locv, state] ;
        c_clobbered = Base.SetLattice.bottom;
        (* This function returns always the same base in the same context,
           but the context uses the callstack: its results cannot be cached
           by memexec *)
        c_cacheable = Value_types.NoCacheCallers;
      }

    with Not_found -> (* Variable has not yet been allocated *)
      let size =
        if not cst then Int.of_int 100000
        else Ival.project_int (Cvalue.V.project_ival size_v)
      in
      let kf_caller,line = match stack with 
	| [] -> assert false
	| top :: [] -> top (* Impossible unless the builtin is main *)
	| top0 :: top1 :: [] -> fst top1, snd top0
	| top0 :: top1 :: top2 :: _ ->
          (* Skip caller of malloc to name the variable if the function looks
             like a generic wrapper to malloc *)
          let name = Kernel_function.get_name (fst top1) in
          try
            ignore (Str.search_forward regexp_alloc name 0);
            fst top2, snd top1
          with Not_found -> fst top1, snd top0
      in
      let line = match line with
        | Kglobal -> 0
        | Kstmt s -> (fst (Stmt.loc s)).Lexing.pos_lnum
      in
      let new_name = Pretty_utils.sfprintf
        "__%s%a_l%d" 
	(if Kernel_function.get_name kf_caller="malloc" then "" 
	 else "malloc_")
	Kernel_function.pretty kf_caller line
      in
      let new_name = Cabs2cil.fresh_global new_name in
      let typ, size_arr = match snd (List.hd (call_stack ())) with
        | Kstmt {skind = Instr (Call (Some lv, _, _, _))} ->
            (match Cil.unrollType (typeOfLval lv) with
               | TPtr (t, _) when not (Cil.isVoidType t) ->
                   (try
                      let s = Int.of_int (sizeOf_int t) in
                      if Int.equal (Int.rem size s) Int.zero
                      then t, Int.div size s
                      else charType, size
                    with Cil.SizeOfError _ -> charType, size)
               | _ -> charType, size
            )
        | _ -> charType, size
      in
      let res, v = 
	malloc_var ~loc:exp.eloc new_name typ (size_arr, size_arr) state
      in
      if cst then
        Value_parameters.result ~current:true ~once:true
          "Allocating variable %a%t" Printer.pp_varinfo v pp_callstack
      else
        Value_parameters.result ~current:true ~once:true
          "@[Allocating@ variable@ %a@ of size %a@ instead of@ requested %a@]%t"
          Printer.pp_varinfo v Int.pretty size V.pretty size_v pp_callstack;
      MallocedByStack.add stack v;
      res
  with Ival.Error_Top | Invalid_CEA_alloc ->
    Value_parameters.error
      "Invalid argument for Frama_C_alloc_stack function";
    do_degenerate None;
    raise Db.Value.Aborted

let () = Builtins.register_builtin "Frama_C_alloc_by_stack" alloc_once_by_stack

(* Change all references to bases into ESCAPINGADDR into the given state,
   and remove thoses bases from the state entirely *)
let free ~exact bases state =
  let state_removed = 
    Base.Hptset.fold
      (fun b state -> Cvalue.Model.add_base b (unallocated_offsetmap b) state)
      bases state
  in
  let state = if exact then state_removed else Model.join state state_removed in
  let is_the_base_to_free x = Base.Hptset.mem x bases in
  let offsetmap_top_addresses_of_locals =
    Locals_scoping.offsetmap_top_addresses_of_locals is_the_base_to_free
  in
  Locals_scoping.state_top_addresses_of_locals 
    (fun _ _ -> ()) (* no informative message *)
    offsetmap_top_addresses_of_locals ~exact (Locals_scoping.top ())
    state

(** Builtin for [free] function *)
let frama_c_free state actuals =
  try begin match actuals with
    | [ _, arg, _ ] ->
        (* Categorizes the bases in arg *)
        let f base offset (acc, card) =
	  let allocated_base =
            Base.Hptset.mem base (Dynamic_Alloc_Bases.get())
	  in
          (* Does arg contain at least one invalid value? *)
	  if (not allocated_base && not (Base.is_null base))
            || Ival.contains_non_zero offset
	  then Value_util.warning_once_current
	    "Wrong free: assert(pass a freeable address)";
          (* Collect the bases to remove from the memory state.
             Also count the number of freeable bases (including NULL). *)
	  if Ival.contains_zero offset
	  then begin
	      if allocated_base 
	      then Base.Hptset.add base acc, card + 1
	      else if Base.is_null base
	      then acc, card + 1
	      else acc, card
	    end
	  else acc, card
	in
	let bases_to_remove, card =
          Cvalue.V.fold_i f arg (Base.Hptset.empty, 0)
        in
        let state =
	  match card with
            0 -> Model.bottom
          | 1 -> free ~exact:true bases_to_remove state
          | _ -> free ~exact:false bases_to_remove state
        in
        (* TODO: reduce on arg if it is an lval *)
	{ Value_types.c_values = [None, state];
	  c_clobbered = Base.SetLattice.bottom;
          c_cacheable = Value_types.Cacheable;
        }

    | _ ->
        Value_parameters.error
	  "Invalid argument for Frama_C_free function";
        do_degenerate None;
        raise Db.Value.Aborted
    end
  with
  | Db.Value.Outside_builtin_possibilities ->
      Value_parameters.error
	"Outside possibilities for Frama_C_free function";
      do_degenerate None;
      raise Db.Value.Aborted

let () = Builtins.register_builtin "Frama_C_free" frama_c_free


(*
Local Variables:
compile-command: "make -C ../.."
End:
*)
