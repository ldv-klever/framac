(**************************************************************************)
(*                                                                        *)
(*  This file is part of Frama-C.                                         *)
(*                                                                        *)
(*  Copyright (C) 2007-2015                                               *)
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
open CilE

type syntactic_context =
  | SyNone
  | SyCallResult
  | SyBinOp of Cil_types.exp * Cil_types.binop * Cil_types.exp * Cil_types.exp
  | SyUnOp of  Cil_types.exp
  | SyMem of  Cil_types.lval
  | SyMemLogic of Cil_types.term
  | SySep of Cil_types.lval * Cil_types.lval

(* Printer that shows additional information about temporaries *)
let local_printer: Printer.extensible_printer = object (self)
  inherit Printer.extensible_printer () as super

  (* Temporary variables for which we want to print more information *)
  val mutable temporaries = Cil_datatype.Varinfo.Set.empty

  method! code_annotation fmt ca =
    temporaries <- Cil_datatype.Varinfo.Set.empty;
    match ca.annot_content with
    | AAssert(_, p) ->  
      (* ignore the ACSL name *) 
      Format.fprintf fmt "@[<v>@[assert@ %a;@]" self#predicate p.content;
      (* print temporary variables information *)
      if not (Cil_datatype.Varinfo.Set.is_empty temporaries) then begin
        Format.fprintf fmt "@ @[(%t)@]" self#pp_temporaries
      end;
      Format.fprintf fmt "@]";
  | _ -> assert false

  method private pp_temporaries fmt =
    let pp_var fmt vi =
      Format.fprintf fmt "%s from@ @[%s@]" vi.vname (Extlib.the vi.vdescr)
    in
    Pretty_utils.pp_iter Cil_datatype.Varinfo.Set.iter
      ~pre:"" ~suf:"" ~sep:",@ " pp_var fmt temporaries

  method! logic_var fmt lvi =
    (match lvi.lv_origin with
    | None | Some { vdescr = None }-> ()
    | Some ({ vdescr = Some _ } as vi) ->
      temporaries <- Cil_datatype.Varinfo.Set.add vi temporaries
    );
    super#logic_var fmt lvi
end 

let current_stmt_tbl =
  let s = Stack.create () in
  Stack.push Kglobal s;
  s

let start_stmt ki = Stack.push ki current_stmt_tbl

let end_stmt () =
  try ignore (Stack.pop current_stmt_tbl)
  with Stack.Empty -> assert false

let current_stmt () =
  try Stack.top current_stmt_tbl
  with Stack.Empty -> assert false

let syntactic_context = ref SyNone
let set_syntactic_context e =
  syntactic_context := e

let get_syntactic_context () = current_stmt (),!syntactic_context

let sc_kinstr_loc ki =
  match ki with
    | Kglobal -> (* can occur in case of obscure bugs (already happended)
                    with wacky initializers. Module Initial_state of
                    value analysis correctly positions the loc *)
        assert (Cil_datatype.Kinstr.equal Kglobal
                  (fst (get_syntactic_context ())));
        Cil.CurrentLoc.get ()
    | Kstmt s -> Cil_datatype.Stmt.loc s

let do_warn {a_log=log;a_call=call} f =
  Extlib.may f log;
  call ()

let register_alarm ?kf ?(status=Property_status.Dont_know) e ki a =
  Value_messages.new_alarm ki a status;
  Alarms.register ~loc:(sc_kinstr_loc ki) ?kf ~status e ki a

let warn_pointer_comparison warn_mode =
  do_warn warn_mode.defined_logic
    (fun (emitter, suffix) ->
      let aux ki e1 e2 =
	let annot, is_new =
	  register_alarm emitter ki (Alarms.Pointer_comparison (e1, e2))
	in
	if is_new then
          Kernel.warning ~current:true
            "@[pointer comparison:@ %a@]%t"
            local_printer#code_annotation annot suffix;
      in
      match get_syntactic_context () with
	| _,SyNone -> ()
	| _,(SyMem _ | SyMemLogic _ | SySep _ | SyCallResult) ->
	  assert false
	| ki, SyUnOp e -> aux ki None e
	| ki, SyBinOp (_, (Eq|Ne|Ge|Le|Gt|Lt), e1, e2) -> aux ki (Some e1) e2
	| _, SyBinOp _ ->
	  assert false)

(* warn for division by 0. If [addresses] holds, also emit an alarm about the
   denominator not being comparable to \null. This is somewhat a hack, made
   mandatory because in the logic we are able to prove [&x + 2 != 0], with [x]
   having a non-array type. If we give a True status to such an assertion,
   no alarm remains for e.g. [1/((int)(&x +2))] .) *)
let warn_div warn_mode ~addresses =
  if addresses then begin
    (* Warn for the denominator not being comparable to Null *)
    do_warn warn_mode.defined_logic
      (fun _ ->
        match get_syntactic_context () with
	| _,SyNone -> ()
	| _,(SyUnOp _ | SyMem _ | SyMemLogic _ | SySep _ | SyCallResult) ->
	  assert false
	| _, (SyBinOp (_, (Div _|Mod), _, e) as old_sc) ->
          (* Extract the relevant part of the syntactic context *)
          set_syntactic_context (SyUnOp e);
          warn_pointer_comparison warn_mode;
          (* Restore it for the 'denominator-non-null' alarm below. *)
          set_syntactic_context old_sc
	|_, SyBinOp _ -> assert false
      )
  end;
  (* Warn for a null denominator *)
  do_warn warn_mode.others
    (fun (emitter, suffix) ->
      match get_syntactic_context () with
	| _,SyNone -> ()
	| _,(SyUnOp _ | SyMem _ | SyMemLogic _ | SySep _ | SyCallResult) ->
	  assert false
	| ki, (SyBinOp (_, (Div _|Mod), _, e)) ->
	  let annot, is_new = 
	    register_alarm emitter ki (Alarms.Division_by_zero e) 
	  in
	  if is_new then
            Kernel.warning ~current:true
              "@[division by zero:@ %a@]%t"
              local_printer#code_annotation annot suffix;
	|_, SyBinOp _ -> assert false) 

(** Auxiliary function that displays two simultaneous alarms as a conjunction *)
let warn_conjuctive_annots warn annot1 annot2 =
  match annot1, annot2 with
    | Some annot, None | None, Some annot -> warn annot
    | Some { annot_content = AAssert(_, pmn) },
        Some { annot_content = AAssert(_, pmx) }
        -> 
        let p = Logic_const.pand (pmn, pmx) in
	let annot = Logic_const.new_code_annotation (AAssert([], p)) in
        warn annot
    | _, _ -> ()

let warn_integer_overflow warn_mode ~signed ~min:mn ~max:mx =
  do_warn warn_mode.others
    (fun (emitter, suffix) ->
      match get_syntactic_context () with
	| ki, (SyUnOp e | SyBinOp(e, _, _, _)) ->
          let warn annot =
	    Kernel.warning ~current:true
	      "@[%s overflow.@ %a@]%t"
              (if signed then "signed" else "unsigned")
	      local_printer#code_annotation annot suffix
          in
	  let signed lower bound =
	    Extlib.may_map ~dft:None
	      (fun n ->
                let kind = if signed then Alarms.Signed else Alarms.Unsigned in
		let annot, is_new =
		  register_alarm emitter ki
		    (Alarms.Overflow(kind, e, n, lower)) 
		in 
		if is_new then Some annot else None)
              bound
	  in
          warn_conjuctive_annots 
	    warn
	    (signed Alarms.Lower_bound mn) 
	    (signed Alarms.Upper_bound mx)
	| _ -> assert false)

let warn_float_to_int_overflow warn_mode mn mx msg =
  do_warn warn_mode.others
    (fun (emitter, suffix) ->
      match get_syntactic_context () with
	| ki, SyUnOp e ->
          let warn annot =
            Kernel.warning ~current:true
	      "@[overflow@ in conversion@ of %t@ from@ floating-point@ \
               to integer.@ %a@]%t" msg
	      local_printer#code_annotation annot suffix
          in
	  let aux lower bound =
	    Extlib.may_map ~dft:None
	      (fun n ->
		let annot, is_new =
		  register_alarm emitter ki (Alarms.Float_to_int(e, n, lower)) 
		in 
		if is_new then Some annot else None
              )
	      bound
	  in
          warn_conjuctive_annots
	    warn
	    (aux Alarms.Lower_bound mn)
	    (aux Alarms.Upper_bound mx)
	| _ -> assert false)

let warn_shift warn_mode size =
  do_warn warn_mode.others
    (fun (emitter, suffix) ->
      match get_syntactic_context () with
	| _,SyNone -> ()
	| _,(SyUnOp _ | SyMem _ | SyMemLogic _ | SySep _ | SyCallResult) ->
	  assert false
	| ki,SyBinOp (_, (Shiftrt | Shiftlt _),_,exp_d) ->
	  let annot, is_new =
	    register_alarm emitter ki (Alarms.Invalid_shift(exp_d, Some size))
	  in
	  if is_new then
            Kernel.warning ~current:true
              "@[invalid RHS operand for shift.@ %a@]%t"
              local_printer#code_annotation annot suffix;
	| _, SyBinOp _ ->
	  assert false)

let warn_shift_left_positive warn_mode =
  do_warn warn_mode.others
    (fun (emitter, suffix) ->
      match get_syntactic_context () with
	| _,SyNone -> ()
	| _, (SyUnOp _ | SyMem _ | SyMemLogic _ | SySep _ | SyCallResult) ->
	  assert false
	| ki, SyBinOp (_, (Shiftrt | Shiftlt _),exp_l,_) ->
	  let annot, is_new =
	    register_alarm emitter ki (Alarms.Invalid_shift(exp_l, None))
	  in
	  if is_new then
            Kernel.warning ~current:true
              "@[invalid LHS operand for left shift.@ %a@]%t"
              local_printer#code_annotation annot suffix
	| _, SyBinOp _ ->
	  assert false)

let pretty_warn_mem_mode fmt m =
  Format.pp_print_string fmt
    (match m with Alarms.For_reading -> "read" | Alarms.For_writing -> "write")

let warn_mem warn_mode wmm =
  do_warn warn_mode.others
    (fun (emitter, suffix) ->
      let warn_term ki mk_alarm =
	let valid = wmm in
	let annot, is_new = register_alarm emitter ki (mk_alarm valid) in
	if is_new then
          Kernel.warning ~current:true "@[out of bounds %a.@ %a@]%t"
            pretty_warn_mem_mode wmm
            local_printer#code_annotation annot suffix;
      in
      match get_syntactic_context () with
	| _,SyNone -> ()
	| _,(SyBinOp _ | SyUnOp _ | SySep _ | SyCallResult) -> assert false
	| ki,SyMem lv_d -> 
	  warn_term ki (fun v -> Alarms.Memory_access(lv_d, v));
	| ki,SyMemLogic term -> 
	  warn_term ki (fun v -> Alarms.Logic_memory_access(term, v)))

let warn_mem_read warn_mode = warn_mem warn_mode Alarms.For_reading 
let warn_mem_write warn_mode = warn_mem warn_mode Alarms.For_writing

let warn_index warn_mode ~positive ~range =
  do_warn warn_mode.others
    (fun (emitter, suffix) ->
      match get_syntactic_context () with
	| _,SyNone -> ()
	| _,(SyMem _ | SyMemLogic _ | SyUnOp _ | SySep _ | SyCallResult) ->
	  assert false
	| ki ,SyBinOp (_, IndexPI, e1, e2) ->
	  let left =
	    if not positive then
	      Some
		(register_alarm 
		   emitter ki (Alarms.Index_out_of_bound(e1, None)))
	    else None
	  in
	  let annot, is_new =
	    register_alarm emitter ki (Alarms.Index_out_of_bound(e1, Some e2))
	  in
	  let warn a =
            Kernel.warning ~current:true
              "@[accessing out of bounds index %s.@ @[%a@]@]%t" 
	      range
	      local_printer#code_annotation a
	      suffix
	  in
	  if is_new then
	    let a = match left, annot with
	      | None, _ | Some(_, false), _ -> annot
	      | Some({ annot_content = AAssert(_, l) }, true),
		{ annot_content = AAssert(_, r) } -> 
		let p = Logic_const.pand (l, r) in
		Logic_const.new_code_annotation (AAssert([], p))
	      | Some _, _ -> assert false
	    in
	    warn a
	  else
	    Extlib.may (fun (a, b) -> if b then warn a) left
	| _, SyBinOp _ ->
	  assert false)

let warn_valid_string warn_mode =
  do_warn warn_mode.defined_logic
    (fun (emitter, suffix) ->
      let aux ki e =
	let annot, is_new =
	  register_alarm emitter ki (Alarms.Valid_string e)
	in
	if is_new then
          Kernel.warning ~current:true
            "@[may not point to a valid string:@ %a@]%t"
            local_printer#code_annotation annot suffix;
      in
      match get_syntactic_context () with
	| _,SyNone -> ()
	| _,(SyMemLogic _ | SySep _ | SyCallResult | SyMem _ | SyBinOp _) ->
	  assert false
        | ki, SyUnOp e ->
          aux ki e)

let warn_pointer_subtraction warn_mode =
  do_warn warn_mode.defined_logic
    (fun (emitter, suffix) ->
      match get_syntactic_context () with
	| _,SyNone -> ()
	| _,(SyMem _ | SyMemLogic _ | SySep _ | SyCallResult | SyUnOp _) ->
	  assert false
	| ki, SyBinOp (_, _, e1, e2) ->
	  let annot, is_new =
	    register_alarm emitter ki (Alarms.Differing_blocks (e1, e2))
	  in
	  if is_new then
            Kernel.warning ~current:true
              "@[pointer subtraction:@ %a@]%t"
              local_printer#code_annotation annot suffix)

let warn_nan_infinite warn_mode fkind pp =
  let sfkind = match fkind with
    | None -> "real"
    | Some FFloat -> "float"
    | Some FDouble -> "double"
    | Some FLongDouble -> "long double"
  in
  do_warn warn_mode.others
    (fun (emitter, suffix) ->
      match get_syntactic_context () with
	| _,SyNone -> ()
	| _,(SyBinOp _ | SyMem _ | SyMemLogic _ | SySep _) -> assert false
	| _, SyCallResult -> (* cf. bug 997 *)
	  Kernel.warning ~current:true ~once:true
            "@[non-finite@ %s@ value being@ returned:@ \
              assert(\\is_finite(\\returned_value))@]%t" sfkind suffix;
	| ki,SyUnOp (exp_r) ->
          (* Should always be called with a non-none fkind, except in logic
             mode (in which case this code is not executed *)
          let fkind = Extlib.the fkind in
	  let annot, is_new =
	    register_alarm emitter ki (Alarms.Is_nan_or_infinite (exp_r, fkind))
	  in
	  if is_new then
            Kernel.warning ~current:true ~once:true
              "@[non-finite@ %s@ value@ (%t):@ %a@]%t"
              sfkind pp local_printer#code_annotation annot suffix)

let warn_uninitialized warn_mode = 
  do_warn warn_mode.unspecified
    (fun (emitter, suffix) ->
      match get_syntactic_context () with
	| _, SyNone
	| _, (SyBinOp _ | SyUnOp _ | SySep _ | SyMemLogic _) -> assert false
	| _, SyCallResult ->
	  Kernel.warning ~once:true ~current:true
            "@[returned value may be uninitialized:@ \
              assert \\initialized(\\returned_value)@]%t" suffix;
	| ki, SyMem lv_d ->
	  let annot, is_new =
	    register_alarm emitter ki (Alarms.Uninitialized lv_d)
	  in
	  if is_new then
            Kernel.warning ~current:true
              "@[accessing uninitialized left-value:@ %a@]%t"
              local_printer#code_annotation annot suffix)

let warn_escapingaddr warn_mode =
  do_warn warn_mode.unspecified
    (fun (emitter, suffix) ->
      match get_syntactic_context () with
	| _,SyNone -> ()
	| _,(SyBinOp _ | SyUnOp _ | SySep _ | SyMemLogic _) -> assert false
	| _, SyCallResult ->
	  Kernel.warning ~once:true ~current:true
            "@[returned value may be contain escaping addresses:@ \
              assert \\dangling(\\returned_value)@]%t" suffix;
	| ki,SyMem lv_d ->
	  let annot, is_new =
	    register_alarm emitter ki (Alarms.Dangling lv_d)
	  in
	  if is_new then
            Kernel.warning ~current:true
              "@[accessing left-value@ that contains@ escaping@ addresses:\
                 @ %a@]%t" local_printer#code_annotation annot suffix)
    
let warn_separated warn_mode =
  do_warn warn_mode.others
    (fun (emitter, suffix) ->
      match get_syntactic_context () with
      | _,SyNone -> ()
      | _,(SyBinOp _ | SyUnOp _ | SyMem _ | SyMemLogic _| SyCallResult) ->
	assert false
      | ki,SySep(lv1,lv2) ->
	let annot, is_new =
	  register_alarm emitter ki (Alarms.Not_separated(lv1, lv2))
	in
	if is_new then
          Kernel.warning ~current:true
            "@[undefined multiple accesses in expression.@ %a@]%t"
            local_printer#code_annotation annot suffix)

let warn_overlap msg warn_mode =
  do_warn warn_mode.others
    (fun (emitter, suffix) ->
      match get_syntactic_context () with
	| _,SyNone -> ()
	| _,(SyBinOp _ | SyUnOp _ | SyMem _ | SyMemLogic _| SyCallResult) ->
	  assert false
	| ki,SySep(lv1,lv2) ->
	  let annot, is_new =
	    register_alarm emitter ki (Alarms.Overlap(lv1, lv2))
	  in
	  if is_new then
            Kernel.warning ~current:true
              "@[partially overlapping@ lvalue assignment%t.@ %a@]%t"
              msg local_printer#code_annotation annot suffix)
