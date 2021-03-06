(**************************************************************************)
(*                                                                        *)
(*  This file is part of the Frama-C's E-ACSL plug-in.                    *)
(*                                                                        *)
(*  Copyright (C) 2012-2019                                               *)
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

module E_acsl_label = Label
open Cil_types
open Cil_datatype

let dkey = Options.dkey_translation

let not_yet env s =
  Env.Context.save env;
  Error.not_yet s

let handle_error f env =
  let env = Error.handle f env in
  Env.Context.restore env

(* internal to [named_predicate_to_exp] but put it outside in order to not add
   extra tedious parameter.
   It is [true] iff we are currently visiting \valid. *)
let is_visiting_valid = ref false

(* ************************************************************************** *)
(* Transforming terms and predicates into C expressions (if any) *)
(* ************************************************************************** *)

let relation_to_binop = function
  | Rlt -> Lt
  | Rgt -> Gt
  | Rle -> Le
  | Rge -> Ge
  | Req -> Eq
  | Rneq -> Ne

let name_of_mpz_arith_bop = function
  | PlusA _ -> "__gmpz_add"
  | MinusA _ -> "__gmpz_sub"
  | Mult _ -> "__gmpz_mul"
  | Div _ -> "__gmpz_tdiv_q"
  | Mod _ -> "__gmpz_tdiv_r"
  | Lt | Gt | Le | Ge | Eq | Ne | BAnd | BXor | BOr | LAnd | LOr
  | Shiftlt _ | Shiftrt | PlusPI | IndexPI | MinusPI | MinusPP -> assert false

(* Type of a string that represents a number.
   Used when a string is required to encode a constant number because it is not
   representable in any C type  *)
type strnum =
  | Str_Z         (* integers *)
  | Str_R         (* reals *)
  | C_number      (* integers and floats included *)

(* convert [e] in a way that it is compatible with the given typing context. *)
let add_cast ~loc ?name env ctx strnum t_opt e =
  let mk_mpz e =
    let _, e, env =
      Env.new_var
        ~loc
        ?name
        env
        t_opt
        (Gmp_types.Z.t ())
        (fun lv v -> [ Gmp.init_set ~loc (Cil.var lv) v e ])
    in
    e, env
  in
  let e, env = match strnum with
    | Str_Z -> mk_mpz e
    | Str_R -> Rational.create ~loc ?name e env t_opt
    | C_number -> e, env
  in
  match ctx with
  | None ->
    e, env
  | Some ctx ->
    let ty = Cil.typeOf e in
    match Gmp_types.Z.is_t ty, Gmp_types.Z.is_t ctx with
    | true, true ->
      (* Z --> Z *)
        e, env
    | false, true ->
      if Gmp_types.Q.is_t ty then
        (* R --> Z *)
        Rational.cast_to_z ~loc ?name e env
      else
        (* C integer --> Z *)
        let e =
          if not (Cil.isIntegralType ty) && strnum = C_number then
            (* special case for \null that must be casted to long: it is the
               only non integral value that can be seen as an integer, while the
               type system infers that it is C-representable (see
               tests/runtime/null.i) *)
            Cil.mkCast e Cil.longType (* \null *)
          else
            e
        in
        mk_mpz e
    | _, false ->
      if Gmp_types.Q.is_t ctx then
        if Gmp_types.Q.is_t (Cil.typeOf e) then (* R --> R *) e, env
        else (* C integer or Z --> R *) Rational.create ~loc ?name e env t_opt
      else if Gmp_types.Z.is_t ty || strnum = Str_Z then
        (* Z --> C type or the integer is represented by a string:
           anyway, it fits into a C integer: convert it *)
        let fname, new_ty =
          if Cil.isSignedInteger ctx then "__gmpz_get_si", Cil.longType
          else "__gmpz_get_ui", Cil.ulongType
        in
        let _, e, env =
          Env.new_var
            ~loc
            ?name
            env
            None
            new_ty
            (fun v _ -> [ Misc.mk_call ~loc ~result:(Cil.var v) fname [ e ] ])
        in
        e, env
      else if Gmp_types.Q.is_t ty || strnum = Str_R then
        (* R --> C type or the real is represented by a string *)
        Rational.add_cast ~loc ?name e env ctx
      else
        Cil.mkCastT ~force:false ~overflow:Check ~e ~oldt:ty ~newt:ctx, env

let constant_to_exp ~loc t c =
  let mk_real s =
    let s = Rational.normalize_str s in
    Cil.mkString ~loc s, Str_R
  in
  match c with
  | Integer(n, _repr) ->
    let ity = Typing.get_number_ty t in
    (match ity with
     | Typing.Nan -> assert false
     | Typing.Real -> Error.not_yet "real number constant"
     | Typing.Rational -> mk_real (Integer.to_string n)
     | Typing.Gmpz ->
       (* too large integer *)
       Cil.mkString ~loc (Integer.to_string n), Str_Z
     | Typing.C_float fkind ->
       Cil.kfloat ~loc fkind (Int64.to_float (Integer.to_int64 n)), C_number
     | Typing.C_integer kind ->
         let cast = Typing.get_cast t in
         match cast, kind with
       | Some ty, (ILongLong | IULongLong) when Gmp_types.Z.is_t ty ->
         (* too large integer *)
         Cil.mkString ~loc (Integer.to_string n), Str_Z
       | Some ty, _ when Gmp_types.Q.is_t ty ->
         mk_real (Integer.to_string n)
         | (None | Some _), _ ->
         (* do not keep the initial string representation because the generated
            constant must reflect its type computed by the type system. For
            instance, when translating [INT_MAX+1], we must generate a [long
            long] addition and so [1LL]. If we keep the initial string
            representation, the kind would be ignored in the generated code and
            so [1] would be generated. *)
         Cil.kinteger64 ~loc ~kind n, C_number)
  | LStr s -> Cil.new_exp ~loc (Const (CStr s)), C_number
  | LWStr s -> Cil.new_exp ~loc (Const (CWStr s)), C_number
  | LChr c -> Cil.new_exp ~loc (Const (CChr c)), C_number
  | LReal lr ->
    if lr.r_lower = lr.r_upper
    then Cil.kfloat ~loc FDouble lr.r_nearest, C_number
    else mk_real lr.r_literal
  | LEnum e -> Cil.new_exp ~loc (Const (CEnum e)), C_number

let conditional_to_exp ?(name="if") loc t_opt e1 (e2, env2) (e3, env3) =
  let env = Env.pop (Env.pop env3) in
  match e1.enode with
  | Const(CInt64(n, _, _)) when Integer.is_zero n ->
    e3, Env.transfer ~from:env3 env
  | Const(CInt64(n, _, _)) when Integer.is_one n ->
    e2, Env.transfer ~from:env2 env
  | _ ->
    let ty = match t_opt with
      | None (* predicate *) -> Cil.intType
      | Some t -> Typing.get_typ t
    in
    let _, e, env =
      Env.new_var
        ~loc
        ~name
        env
        t_opt
        ty
        (fun v ev ->
          let lv = Cil.var v in
          let ty = Cil.typeOf ev in
          let init_set =
            assert (not (Gmp_types.Q.is_t ty));
            Gmp.init_set
          in
          let affect e = init_set ~loc lv ev e in
          let then_block, _ =
            let s = affect e2 in
            Env.pop_and_get env2 s ~global_clear:false Env.Middle
          in
          let else_block, _ =
            let s = affect e3 in
            Env.pop_and_get env3 s ~global_clear:false Env.Middle
          in
          [ Cil.mkStmt ~valid_sid:true (If(e1, then_block, else_block, loc)) ])
    in
    e, env

let rec thost_to_host kf env th = match th with
  | TVar { lv_origin = Some v } ->
    let v' = Visitor_behavior.Get.varinfo (Env.get_behavior env) v in
    Var v', env, v.vname
  | TVar ({ lv_origin = None } as logic_v) ->
    let v' = Env.Logic_binding.get env logic_v in
    Var v', env, logic_v.lv_name
  | TResult _typ ->
    let vis = Env.get_visitor env in
    let kf = Extlib.the vis#current_kf in
    let lhost = Misc.result_lhost kf in
    (match lhost with
     | Var v ->
       let v' = Visitor_behavior.Get.varinfo (Env.get_behavior env) v in
       Var v', env, "result"
    | _ -> assert false)
  | TMem t ->
    let e, env = term_to_exp kf env t in
    Mem e, env, ""

and toffset_to_offset ?loc kf env = function
  | TNoOffset -> NoOffset, env
  | TField(f, offset) ->
    let offset, env = toffset_to_offset ?loc kf env offset in
    Field(f, offset), env
  | TIndex(t, offset) ->
    let e, env = term_to_exp kf env t in
    let offset, env = toffset_to_offset kf env offset in
    Index(e, offset), env
  | TModel _ -> not_yet env "model"

and tlval_to_lval kf env (host, offset) =
  let host, env, name = thost_to_host kf env host in
  let offset, env = toffset_to_offset kf env offset in
  let name = match offset with NoOffset -> name | Field _ | Index _ -> "" in
  (host, offset), env, name

(* the returned boolean says that the expression is an mpz_string;
   the returned string is the name of the generated variable corresponding to
   the term. *)
and context_insensitive_term_to_exp kf env t =
  let loc = t.term_loc in
  match t.term_node with
  | TConst c ->
    let c, strnum = constant_to_exp ~loc t c in
    c, env, strnum, ""
  | TLval lv ->
    let lv, env, name = tlval_to_lval kf env lv in
    Cil.new_exp ~loc (Lval lv), env, C_number, name
  | TSizeOf ty -> Cil.sizeOf ~loc ty, env, C_number, "sizeof"
  | TSizeOfE t ->
    let e, env = term_to_exp kf env t in
    Cil.sizeOf ~loc (Cil.typeOf e), env, C_number, "sizeof"
  | TSizeOfStr s ->
    Cil.new_exp ~loc (SizeOfStr s), env, C_number, "sizeofstr"
  | TAlignOf ty -> Cil.new_exp ~loc (AlignOf ty), env, C_number, "alignof"
  | TAlignOfE t ->
    let e, env = term_to_exp kf env t in
    Cil.new_exp ~loc (AlignOfE e), env, C_number, "alignof"
  | TUnOp(Neg _ | BNot as op, t') ->
    let ty = Typing.get_typ t in
    let e, env = term_to_exp kf env t' in
    if Gmp_types.Z.is_t ty then
      let name, vname = match op with
	| Neg _ -> "__gmpz_neg", "neg"
	| BNot -> "__gmpz_com", "bnot"
	| LNot -> assert false
      in
      let _, e, env =
	Env.new_var_and_mpz_init
	  ~loc
	  env
	  ~name:vname
	  (Some t)
	  (fun _ ev -> [ Misc.mk_call ~loc name [ ev; e ] ])
      in
      e, env, C_number, ""
    else if Gmp_types.Q.is_t ty then
      not_yet env "reals: Neg | BNot"
    else
      Cil.new_exp ~loc (UnOp(op, e, ty)), env, C_number, ""
  | TUnOp(LNot, t) ->
    let ty = Typing.get_op t in
    if Gmp_types.Z.is_t ty then
      (* [!t] is converted into [t == 0] *)
      let zero = Logic_const.tinteger 0 in
      let ctx = Typing.get_number_ty t in
      Typing.type_term ~use_gmp_opt:true ~ctx zero;
      let e, env =
        comparison_to_exp kf ~loc ~name:"not" env Typing.gmpz Eq t zero (Some t)
      in
      e, env, C_number, ""
    else begin
      assert (Cil.isIntegralType ty);
      let e, env = term_to_exp kf env t in
      Cil.new_exp ~loc (UnOp(LNot, e, Cil.intType)), env, C_number, ""
    end
  | TBinOp(PlusA _ | MinusA _ | Mult _ as bop, t1, t2) ->
    let ty = Typing.get_typ t in
    let e1, env = term_to_exp kf env t1 in
    let e2, env = term_to_exp kf env t2 in
    if Gmp_types.Z.is_t ty then
      let name = name_of_mpz_arith_bop bop in
      let mk_stmts _ e = [ Misc.mk_call ~loc name [ e; e1; e2 ] ] in
      let name = Misc.name_of_binop bop in
      let _, e, env =
	Env.new_var_and_mpz_init ~loc ~name env (Some t) mk_stmts
      in
      e, env, C_number, ""
    else if Gmp_types.Q.is_t ty then
      let e, env = Rational.binop ~loc bop e1 e2 env (Some t) in
      e, env, C_number, ""
    else begin
      assert (Logic_typing.is_integral_type t.term_type);
      Cil.new_exp ~loc (BinOp(bop, e1, e2, ty)), env, C_number, ""
    end
  | TBinOp(Div _ | Mod _ as bop, t1, t2) ->
    let ty = Typing.get_typ t in
    let e1, env = term_to_exp kf env t1 in
    let e2, env = term_to_exp kf env t2 in
    if Gmp_types.Z.is_t ty then
      (* TODO: preventing division by zero should not be required anymore.
         RTE should do this automatically. *)
      let ctx = Typing.get_number_ty t in
      let t = Some t in
      let name = name_of_mpz_arith_bop bop in
      (* [TODO] can now do better since the type system got some info about
         possible values of [t2] *)
      (* guarding divisions and modulos *)
      let zero = Logic_const.tinteger 0 in
      Typing.type_term ~use_gmp_opt:true ~ctx zero;
      (* do not generate [e2] from [t2] twice *)
      let guard, env =
        let name = Misc.name_of_binop bop ^ "_guard" in
        comparison_to_exp
          ~loc kf env Typing.gmpz ~e1:e2 ~name Eq t2 zero t
      in
      let mk_stmts _v e =
        assert (Gmp_types.Z.is_t ty);
	let vis = Env.get_visitor env in
	let kf = Extlib.the vis#current_kf in
	let cond =
	  Misc.mk_e_acsl_guard
	    (Env.annotation_kind env)
	    kf
	    guard
	    (Logic_const.prel ~loc (Req, t2, zero))
	in
	Env.add_assert env cond (Logic_const.prel (Rneq, t2, zero));
	let instr = Misc.mk_call ~loc name [ e; e1; e2 ] in
	[ cond; instr ]
      in
      let name = Misc.name_of_binop bop in
      let _, e, env = Env.new_var_and_mpz_init ~loc ~name env t mk_stmts in
      e, env, C_number, ""
    else if Gmp_types.Q.is_t ty then
      let e, env = Rational.binop ~loc bop e1 e2 env (Some t) in
      e, env, C_number, ""
    else begin
      assert (Logic_typing.is_integral_type t.term_type);
      (* no guard required since RTEs are generated separately *)
      Cil.new_exp ~loc (BinOp(bop, e1, e2, ty)), env, C_number, ""
    end
  | TBinOp(Lt | Gt | Le | Ge | Eq | Ne as bop, t1, t2) ->
    (* comparison operators *)
    let ity = Typing.get_integer_op t in
    let e, env = comparison_to_exp ~loc kf env ity bop t1 t2 (Some t) in
    e, env, C_number, ""
  | TBinOp((Shiftlt _ | Shiftrt), _, _) ->
    (* left/right shift *)
    not_yet env "left/right shift"
  | TBinOp(LOr, t1, t2) ->
    (* t1 || t2 <==> if t1 then true else t2 *)
    let e1, env1 = term_to_exp kf (Env.rte env true) t1 in
    let env' = Env.push env1 in
    let res2 = term_to_exp kf (Env.push env') t2 in
    let e, env =
      conditional_to_exp ~name:"or" loc (Some t) e1 (Cil.one loc, env') res2
    in
    e, env, C_number, ""
  | TBinOp(LAnd, t1, t2) ->
    (* t1 && t2 <==> if t1 then t2 else false *)
    let e1, env1 = term_to_exp kf (Env.rte env true) t1 in
    let _, env2 as res2 = term_to_exp kf (Env.push env1) t2 in
    let env3 = Env.push env2 in
    let e, env =
      conditional_to_exp ~name:"and" loc (Some t) e1 res2 (Cil.zero loc, env3)
    in
    e, env, C_number, ""
  | TBinOp((BOr | BXor | BAnd), _, _) ->
    (* other logic/arith operators  *)
    not_yet env "missing binary bitwise operator"
  | TBinOp(PlusPI | IndexPI | MinusPI as bop, t1, t2) ->
    if Misc.is_set_of_ptr_or_array t1.term_type ||
      Misc.is_set_of_ptr_or_array t2.term_type then
        (* case of arithmetic over set of pointers (due to use of ranges)
          should have already been handled in [mmodel_call_with_ranges] *)
        assert false;
    (* binary operation over pointers *)
    let ty = match t1.term_type with
      | Ctype ty -> ty
      | _ -> assert false
    in
    let e1, env = term_to_exp kf env t1 in
    let e2, env = term_to_exp kf env t2 in
    Cil.new_exp ~loc (BinOp(bop, e1, e2, ty)), env, C_number, ""
  | TBinOp(MinusPP, t1, t2) ->
    begin match Typing.get_number_ty t with
      | Typing.C_integer _ ->
        let e1, env = term_to_exp kf env t1 in
        let e2, env = term_to_exp kf env t2 in
        let ty = Typing.get_typ t in
        Cil.new_exp ~loc (BinOp(MinusPP, e1, e2, ty)), env, C_number, ""
      | Typing.Gmpz ->
        not_yet env "pointer subtraction resulting in gmp"
      | Typing.(C_float _ | Rational | Real | Nan) ->
        assert false
    end
  | TCastE(ty, _, t') ->
    let e, env = term_to_exp kf env t' in
    let e, env =
      add_cast ~loc ~name:"cast" env (Some ty) C_number (Some t) e
    in
    e, env, C_number, ""
  | TLogic_coerce _ -> assert false (* handle in [term_to_exp] *)
  | TAddrOf lv ->
    let lv, env, _ = tlval_to_lval kf env lv in
    Cil.mkAddrOf ~loc lv, env, C_number, "addrof"
  | TStartOf lv ->
    let lv, env, _ = tlval_to_lval kf env lv in
    Cil.mkAddrOrStartOf ~loc lv, env, C_number, "startof"
  | Tapp(li, [], targs) ->
    let fname = li.l_var_info.lv_name in
    (* build the varinfo (as an expression) which stores the result of the
       function call. *)
    let _, e, env =
      if Builtins.mem li.l_var_info.lv_name then
        (* E-ACSL built-in function call *)
        let args, env =
      try
            List.fold_right
              (fun targ (l, env) ->
                 let e, env = term_to_exp kf env targ in
            e :: l, env)
              targs
          ([], env)
      with Invalid_argument _ ->
            Options.fatal
              "[Tapp] unexpected number of arguments when calling %s"
          fname
    in
      Env.new_var
        ~loc
        ~name:(fname ^ "_app")
        env
        (Some t)
        (Misc.cty (Extlib.the li.l_type))
        (fun vi _ ->
             [ Misc.mk_call ~loc ~result:(Cil.var vi) fname args ])
      else
        (* build the arguments and compute the integer_ty of the parameters *)
        let params_ty, args, env =
          List.fold_right
            (fun targ (params_ty, args, env) ->
               let e, env = term_to_exp kf env targ in
               let param_ty = Typing.get_number_ty targ in
               let e, env =
                 try
                   let ty = Typing.typ_of_number_ty param_ty in
                   add_cast loc env (Some ty) C_number (Some targ) e
                 with Typing.Not_a_number ->
                   e, env
               in
               param_ty :: params_ty, e :: args, env)
            targs
            ([], [], env)
        in
        let gen_fname =
          Varname.get ~scope:Varname.Global (Functions.RTL.mk_gen_name fname)
    in
        Logic_functions.tapp_to_exp ~loc gen_fname env t li params_ty args
    in
    e, env, C_number, "app"
  | Tapp(_, _ :: _, _) ->
    not_yet env "logic functions with labels"
  | Tlambda _ -> not_yet env "functional"
  | TDataCons _ -> not_yet env "constructor"
  | Tif(t1, t2, t3) ->
    let e1, env1 = term_to_exp kf (Env.rte env true) t1 in
    let (_, env2 as res2) = term_to_exp kf (Env.push env1) t2 in
    let res3 = term_to_exp kf (Env.push env2) t3 in
    let e, env = conditional_to_exp loc (Some t) e1 res2 res3 in
    e, env, C_number, ""
  | Tat(t, BuiltinLabel Here) ->
    let e, env = term_to_exp kf env t in
    e, env, C_number, ""
  | Tat(t', label) ->
    let lscope = Env.Logic_scope.get env in
    let pot = Misc.PoT_term t' in
    if Lscope.is_used lscope pot then
      let e, env = At_with_lscope.to_exp ~loc kf env pot label in
      e, env, C_number, ""
    else
      let e, env = term_to_exp kf (Env.push env) t' in
      let e, env, sty = at_to_exp_no_lscope env (Some t) label e in
      e, env, sty, ""
  | Tbase_addr(BuiltinLabel Here, t) ->
    let name = "base_addr" in
    let e, env = Mmodel_translate.call ~loc kf name Cil.voidPtrType env t in
    e, env, C_number, name
  | Tbase_addr _ -> not_yet env "labeled \\base_addr"
  | Toffset(BuiltinLabel Here, t) ->
    let size_t = Cil.theMachine.Cil.typeOfSizeOf in
    let name = "offset" in
    let e, env = Mmodel_translate.call ~loc kf name size_t env t in
    e, env, C_number, name
  | Toffset _ -> not_yet env "labeled \\offset"
  | Tblock_length(BuiltinLabel Here, t) ->
    let size_t = Cil.theMachine.Cil.typeOfSizeOf in
    let name = "block_length" in
    let e, env = Mmodel_translate.call ~loc kf name size_t env t in
    e, env, C_number, name
  | Tblock_length _ -> not_yet env "labeled \\block_length"
  | Tnull ->
    Cil.mkCast (Cil.zero ~loc) (TPtr(TVoid [], [])), env, C_number, "null"
  | TUpdate _ -> not_yet env "functional update"
  | Ttypeof _ -> not_yet env "typeof"
  | Ttype _ -> not_yet env "C type"
  | Tempty_set -> not_yet env "empty tset"
  | Tunion _ -> not_yet env "union of tsets"
  | Tinter _ -> not_yet env "intersection of tsets"
  | Tcomprehension _ -> not_yet env "tset comprehension"
  | Trange _ -> not_yet env "range"
  | Toffset_max _ | Toffset_min _ -> Error.not_yet "AstraVer offset"
  | TOffsetOf _ -> Error.not_yet "offsetof macro"
  | Tpif _ -> Error.not_yet "predicate if-then-else"
  | TCoerce _ | TCoerceE _ -> Error.not_yet "AstraVer coercion"
  | Tlet(li, t) ->
    let lvs = Lscope.Lvs_let(li.l_var_info, Misc.term_of_li li) in
    let env = Env.Logic_scope.extend env lvs in
    let env = env_of_li li kf env loc in
    let e, env = term_to_exp kf env t in
    Interval.Env.remove li.l_var_info;
    e, env, C_number, ""

(* Convert an ACSL term into a corresponding C expression (if any) in the given
   environment. Also extend this environment in order to include the generating
   constructs. *)
and term_to_exp kf env t =
  let generate_rte = Env.generate_rte env in
  Options.feedback ~dkey ~level:4 "translating term %a (rte? %b)"
    Printer.pp_term t generate_rte;
  let env = Env.rte env false in
  let t = match t.term_node with TLogic_coerce(_, t) -> t | _ -> t in
  let e, env, sty, name = context_insensitive_term_to_exp kf env t in
  let env = if generate_rte then translate_rte kf env e else env in
  let cast = Typing.get_cast t in
  let name = if name = "" then None else Some name in
  add_cast
    ~loc:t.term_loc
    ?name
    env
    cast
    sty
    (Some t)
    e

(* generate the C code equivalent to [t1 bop t2]. *)
and comparison_to_exp
    ~loc ?e1 kf env ity bop ?(name = Misc.name_of_binop bop) t1 t2 t_opt =
  let e1, env = match e1 with
    | None ->
      let e1, env = term_to_exp kf env t1 in
      e1, env
    | Some e1 ->
      e1, env
  in
  let e2, env = term_to_exp kf env t2 in
  match ity with
  | Typing.C_integer _ | Typing.C_float _ | Typing.Nan ->
    Cil.mkBinOp ~loc bop e1 e2, env
  | Typing.Gmpz ->
    let _, e, env = Env.new_var
        ~loc
        env
        t_opt
        ~name
        Cil.intType
        (fun v _ ->
          [ Misc.mk_call ~loc ~result:(Cil.var v) "__gmpz_cmp" [ e1; e2 ] ])
    in
    Cil.new_exp ~loc (BinOp(bop, e, Cil.zero ~loc, Cil.intType)), env
  | Typing.Rational ->
    Rational.cmp ~loc bop e1 e2 env t_opt
  | Typing.Real ->
    Error.not_yet "comparison involving real numbers"

and at_to_exp_no_lscope env t_opt label e =
  let stmt = E_acsl_label.get_stmt (Env.get_visitor env) label in
  (* generate a new variable denoting [\at(t',label)].
     That is this variable which is the resulting expression.
     ACSL typing rule ensures that the type of this variable is the same as
     the one of [e]. *)
  let loc = Stmt.loc stmt in
  let res_v, res, new_env =
    Env.new_var
      ~loc
      ~name:"at"
      ~scope:Varname.Function
      env
      t_opt
      (Cil.typeOf e)
      (fun _ _ -> [])
  in
  let env_ref = ref new_env in
  (* visitor modifying in place the labeled statement in order to store [e]
     in the resulting variable at this location (which is the only correct
     one). *)
  let o = object
    inherit Visitor.frama_c_inplace
    method !vstmt_aux stmt =
      (* either a standard C affectation or a call to an initializer according
         to the type of [e] *)
      let ty = Cil.typeOf e in
      let init_set =
        if Gmp_types.Q.is_t ty then Rational.init_set else Gmp.init_set
      in
      let new_stmt = init_set ~loc (Cil.var res_v) res e in
      assert (!env_ref == new_env);
      (* generate the new block of code for the labeled statement and the
        corresponding environment *)
      let block, new_env =
       Env.pop_and_get new_env new_stmt ~global_clear:false Env.Middle
      in
      env_ref := Env.extend_stmt_in_place new_env stmt ~label block;
      Cil.ChangeTo stmt
  end
  in
  let bhv = Env.get_behavior new_env in
  let new_stmt =
    Visitor.visitFramacStmt o (Visitor_behavior.Get.stmt bhv stmt)
  in
  Visitor_behavior.Set.stmt bhv stmt new_stmt;
  res, !env_ref, C_number

and env_of_li li kf env loc =
  let t = Misc.term_of_li li in
  let ty = Typing.get_typ t in
  let vi, vi_e, env = Env.Logic_binding.add ~ty env li.l_var_info in
  let e, env = term_to_exp kf env t in
  let stmt = match Typing.get_number_ty t with
    | Typing.(C_integer _ | C_float _ | Nan) ->
      Cil.mkStmtOneInstr (Set (Cil.var vi, e, loc))
    | Typing.Gmpz ->
      Gmp.init_set ~loc (Cil.var vi) vi_e e
    | Typing.Rational ->
      Rational.init_set ~loc (Cil.var vi) vi_e e
    | Typing.Real ->
      Error.not_yet "real number"
  in
  Env.add_stmt env stmt

(* Convert an ACSL named predicate into a corresponding C expression (if
   any) in the given environment. Also extend this environment which includes
   the generating constructs. *)
and named_predicate_content_to_exp ?name kf env p =
  let loc = p.pred_loc in
  match p.pred_content with
  | Pfalse -> Cil.zero ~loc, env
  | Ptrue -> Cil.one ~loc, env
  | Papp(li, labels, args) ->
    (* Simply use the implementation of Tapp(li, labels, args).
       To achieve this, we create a clone of [li] for which the type is
       transformed from [None] (type of predicates) to
       [Some int] (type as a term). *)
    let prj = Project.current () in
    let o = object inherit Visitor.frama_c_copy prj end in
    let li = Visitor.visitFramacLogicInfo o li in
    let lty = Ctype Cil.intType in
    li.l_type <- Some lty;
    let tapp = Logic_const.term ~loc (Tapp(li, labels, args)) lty in
    Typing.type_term ~use_gmp_opt:false ~ctx:Typing.c_int tapp;
    let e, env = term_to_exp kf env tapp in
    e, env
  | Pseparated _ -> not_yet env "\\separated"
  | Pdangling _ -> not_yet env "\\dangling"
  | Pvalid_function _ -> not_yet env "\\valid_function"
  | Prel(rel, t1, t2) ->
    let ity = Typing.get_integer_op_of_predicate p in
    comparison_to_exp ~loc kf env ity (relation_to_binop rel) t1 t2 None
  | Pand(p1, p2) ->
    (* p1 && p2 <==> if p1 then p2 else false *)
    let e1, env1 = named_predicate_to_exp kf (Env.rte env true) p1 in
    let _, env2 as res2 =
      named_predicate_to_exp kf (Env.push env1) p2 in
    let env3 = Env.push env2 in
    let name = match name with None -> "and" | Some n -> n in
    conditional_to_exp ~name loc None e1 res2 (Cil.zero loc, env3)
  | Por(p1, p2) ->
    (* p1 || p2 <==> if p1 then true else p2 *)
    let e1, env1 = named_predicate_to_exp kf (Env.rte env true) p1 in
    let env' = Env.push env1 in
    let res2 = named_predicate_to_exp kf (Env.push env') p2 in
    let name = match name with None -> "or" | Some n -> n in
    conditional_to_exp ~name loc None e1 (Cil.one loc, env') res2
  | Pxor _ -> not_yet env "xor"
  | Pimplies(p1, p2) ->
    (* (p1 ==> p2) <==> !p1 || p2 *)
    named_predicate_to_exp
      ~name:"implies"
      kf
      env
      (Logic_const.por ~loc ((Logic_const.pnot ~loc p1), p2))
  | Piff(p1, p2) ->
    (* (p1 <==> p2) <==> (p1 ==> p2 && p2 ==> p1) *)
    named_predicate_to_exp
      ~name:"equiv"
      kf
      env
      (Logic_const.pand ~loc
	 (Logic_const.pimplies ~loc (p1, p2),
	  Logic_const.pimplies ~loc (p2, p1)))
  | Pnot p ->
    let e, env = named_predicate_to_exp kf env p in
    Cil.new_exp ~loc (UnOp(LNot, e, Cil.intType)), env
  | Pif(t, p2, p3) ->
    let e1, env1 = term_to_exp kf (Env.rte env true) t in
    let (_, env2 as res2) =
      named_predicate_to_exp kf (Env.push env1) p2 in
    let res3 = named_predicate_to_exp kf (Env.push env2) p3 in
    conditional_to_exp loc None e1 res2 res3
  | Plet(li, p) ->
    let lvs = Lscope.Lvs_let(li.l_var_info, Misc.term_of_li li) in
    let env = Env.Logic_scope.extend env lvs in
    let env = env_of_li li kf env loc in
    let e, env = named_predicate_to_exp kf env p in
    Interval.Env.remove li.l_var_info;
    e, env
  | Pforall _ | Pexists _ -> Quantif.quantif_to_exp kf env p
  | Pat(p, BuiltinLabel Here) ->
    named_predicate_to_exp kf env p
  | Pat(p', label) ->
    let lscope = Env.Logic_scope.get env in
    let pot = Misc.PoT_pred p' in
    if Lscope.is_used lscope pot then
      At_with_lscope.to_exp ~loc kf env pot label
    else begin
      (* convert [t'] to [e] in a separated local env *)
      let e, env = named_predicate_to_exp kf (Env.push env) p' in
      let e, env, sty = at_to_exp_no_lscope env None label e in
      assert (sty = C_number);
      e, env
    end
  | Pvalid_read(BuiltinLabel Here as llabel, t) as pc
  | (Pvalid(BuiltinLabel Here as llabel, t) as pc) ->
    let call_valid t =
      let name = match pc with
        | Pvalid _ -> "valid"
        | Pvalid_read _ -> "valid_read"
        | _ -> assert false
      in
      Mmodel_translate.call_valid ~loc kf name Cil.intType env t
    in
    if !is_visiting_valid then begin
      (* we already transformed \valid(t) into \initialized(&t) && \valid(t):
         now convert this right-most valid. *)
      is_visiting_valid := false;
      call_valid t p
    end else begin
      match t.term_node, t.term_type with
      | TLval tlv, Ctype ty ->
        let init =
          Logic_const.pinitialized ~loc (llabel, Misc.term_addr_of ~loc tlv ty)
        in
        Typing.type_named_predicate ~must_clear:false init;
        let p = Logic_const.pand ~loc (init, p) in
        is_visiting_valid := true;
        named_predicate_to_exp kf env p
      | _ ->
        call_valid t p
    end
  | Pvalid _ -> not_yet env "labeled \\valid"
  | Pvalid_read _ -> not_yet env "labeled \\valid_read"
  | Pinitialized(BuiltinLabel Here, t) ->
    (match t.term_node with
    (* optimisation when we know that the initialisation is ok *)
    | TAddrOf (TResult _, TNoOffset) -> Cil.one ~loc, env
    | TAddrOf (TVar { lv_origin = Some vi }, TNoOffset)
      when
        vi.vformal || vi.vglob || Functions.RTL.is_generated_name vi.vname ->
      Cil.one ~loc, env
    | _ ->
      Mmodel_translate.call_with_size
        ~loc
        kf
        "initialized"
        Cil.intType
        env
        t
        p)
  | Pinitialized _ -> not_yet env "labeled \\initialized"
  | Pallocable _ -> not_yet env "\\allocate"
  | Pfreeable(BuiltinLabel Here, t) ->
    Mmodel_translate.call ~loc kf "freeable" Cil.intType env t
  | Pfreeable _ -> not_yet env "labeled \\freeable"
  | Pfresh _ -> not_yet env "\\fresh"
  | Psubtype _ -> not_yet env "AstraVer subtype"

and named_predicate_to_exp ?name kf ?rte env p =
  let rte = match rte with None -> Env.generate_rte env | Some b -> b in
  let env = Env.rte env false in
  let e, env = named_predicate_content_to_exp ?name kf env p in
  let env = if rte then translate_rte kf env e else env in
  let cast = Typing.get_cast_of_predicate p in
  add_cast
    ~loc:p.pred_loc
    ?name
    env
    cast
    C_number
    None
    e

and translate_rte_annots:
    'a. (Format.formatter -> 'a -> unit) -> 'a ->
  kernel_function -> Env.t -> code_annotation list -> Env.t =
  fun pp elt kf env l ->
    let old_valid = !is_visiting_valid in
    let old_kind = Env.annotation_kind env in
    let env = Env.set_annotation_kind env Misc.RTE in
    let env =
      List.fold_left
        (fun env a -> match a.annot_content with
         | AAssert(_, _, p) ->
	  handle_error
	    (fun env ->
	      Options.feedback ~dkey ~level:4 "prevent RTE from %a" pp elt;
                (* The logic scope MUST NOT be reset here since we still might
                   be in the middle of the translation of the original
                   predicate. *)
        let lscope_reset_old = Env.Logic_scope.get_reset env in
        let env = Env.Logic_scope.set_reset env false in
        let env = translate_named_predicate kf (Env.rte env false) p in
        let env = Env.Logic_scope.set_reset env lscope_reset_old in
        env)
	    env
        | _ -> assert false)
        env
        l
    in
    is_visiting_valid := old_valid;
    Env.set_annotation_kind env old_kind

and translate_rte kf env e =
  let stmt = Cil.mkStmtOneInstr ~valid_sid:true (Skip e.eloc) in
  let l = Rte.exp kf stmt e in
  translate_rte_annots Printer.pp_exp e kf env l

and translate_named_predicate kf env p =
  Options.feedback ~dkey ~level:3 "translating predicate %a"
    Printer.pp_predicate p;
  let rte = Env.generate_rte env in
  Typing.type_named_predicate ~must_clear:rte p;
  let e, env = named_predicate_to_exp kf ~rte env p in
  assert (Typ.equal (Cil.typeOf e) Cil.intType);
  let env = Env.Logic_scope.reset env in
  Env.add_stmt
    env
    (Misc.mk_e_acsl_guard ~reverse:true (Env.annotation_kind env) kf e p)

let named_predicate_to_exp ?name kf env p =
  named_predicate_to_exp ?name kf env p (* forget optional argument ?rte *)

let () =
  Loops.term_to_exp_ref := term_to_exp;
  Loops.translate_named_predicate_ref := translate_named_predicate;
  Loops.named_predicate_ref := named_predicate_to_exp;
  Quantif.predicate_to_exp_ref := named_predicate_to_exp;
  At_with_lscope.term_to_exp_ref := term_to_exp;
  At_with_lscope.predicate_to_exp_ref := named_predicate_to_exp;
  Mmodel_translate.term_to_exp_ref := term_to_exp;
  Mmodel_translate.predicate_to_exp_ref := named_predicate_to_exp;
  Logic_functions.term_to_exp_ref := term_to_exp;
  Logic_functions.named_predicate_to_exp_ref := named_predicate_to_exp

(* This function is used by Guillaume.
   However, it is correct to use it only in specific contexts. *)
let predicate_to_exp kf p =
  Typing.type_named_predicate ~must_clear:true p;
  let empty_env = Env.empty (new Visitor.frama_c_copy Project_skeleton.dummy) in
  let e, _ = named_predicate_to_exp kf empty_env p in
  assert (Typ.equal (Cil.typeOf e) Cil.intType);
  e

exception No_simple_translation of term

(* This function is used by plug-in [Cfp]. *)
let term_to_exp typ t =
  (* infer a context from the given [typ] whenever possible *)
  let ctx_of_typ ty =
    if Gmp_types.Z.is_t ty then Typing.gmpz
    else if Gmp_types.Q.is_t ty then Typing.rational
    else
      match ty with
      | TInt(ik, _) -> Typing.ikind ik
      | TFloat(fk, _) -> Typing.fkind fk
      | _ -> Typing.nan
  in
  let ctx = Extlib.opt_map ctx_of_typ typ in
  Typing.type_term ~use_gmp_opt:true ?ctx t;
  let env = Env.empty (new Visitor.frama_c_copy Project_skeleton.dummy) in
  let env = Env.push env in
  let env = Env.rte env false in
  let e, env =
    try term_to_exp (Kernel_function.dummy ()) env t
    with Misc.Unregistered_library_function _ -> raise (No_simple_translation t)
  in
  if not (Env.has_no_new_stmt env) then raise (No_simple_translation t);
  e

(* ************************************************************************** *)
(* [translate_*] translates a given ACSL annotation into the corresponding C
   statement (if any) for runtime assertion checking.

   IMPORTANT: the order of translation of pre-/post-spec must be consistent with
   the pushes done in [Keep_status] *)
(* ************************************************************************** *)

let assumes_predicate bhv =
  List.fold_left
    (fun acc p ->
      let loc = p.ip_content.pred_loc in
      Logic_const.pand ~loc (acc,
                             Logic_const.unamed ~loc p.ip_content.pred_content))
    Logic_const.ptrue
    bhv.b_assumes

let translate_preconditions kf env behaviors =
  let env = Env.set_annotation_kind env Misc.Precondition in
  let do_behavior env b =
    let assumes_pred = assumes_predicate b in
    List.fold_left
      (fun env p ->
         let do_it env =
           if Keep_status.must_translate kf Keep_status.K_Requires then
             let loc = p.ip_content.pred_loc in
             let p =
               Logic_const.pimplies
                 ~loc
                 (assumes_pred,
                  Logic_const.unamed ~loc p.ip_content.pred_content)
	    in
	    translate_named_predicate kf env p
	  else
	    env
	in
	handle_error do_it env)
      env
      b.b_requires
  in
  List.fold_left do_behavior env behaviors

let translate_postconditions kf env behaviors =
  let env = Env.set_annotation_kind env Misc.Postcondition in
  (* generate one guard by postcondition of each behavior *)
  let do_behavior env b =
    let env =
      handle_error
        (fun env ->
          (* test ordering does matter for keeping statuses consistent *)
          if b.b_assigns <> WritesAny
            && Keep_status.must_translate kf Keep_status.K_Assigns
          then not_yet env "assigns clause in behavior";
          (* ignore b.b_extended since we never translate them *)
          env)
        env
    in
    let assumes_pred = assumes_predicate b in
    List.fold_left
      (fun env (t, p) ->
        if Keep_status.must_translate kf Keep_status.K_Ensures then
	  let do_it env =
	    match t with
	    | Normal ->
	      let loc = p.ip_content.pred_loc in
	      let p = p.ip_content in
	      let p =
		Logic_const.pimplies
		  ~loc
		  (Logic_const.pold ~loc assumes_pred,
		   Logic_const.unamed ~loc p.pred_content)
	      in
	      translate_named_predicate kf env p
	    | Exits | Breaks | Continues | Returns ->
	      not_yet env "abnormal termination case in behavior"
	  in
	  handle_error do_it env
	else env)
      env
      b.b_post_cond
  in
  (* fix ordering of behaviors' iterations *)
  let bhvs =
    List.sort (fun b1 b2 -> String.compare b1.b_name b2.b_name) behaviors
  in
  List.fold_left do_behavior env bhvs

let translate_pre_spec kf env spec =
  let unsupported f x = ignore (handle_error (fun env -> f x; env) env) in
  let convert_unsupported_clauses env =
    unsupported
      (Extlib.may
         (fun _ ->
           if Keep_status.must_translate kf Keep_status.K_Decreases then
             not_yet env "variant clause"))
      spec.spec_variant;
    (* TODO: spec.spec_terminates is not part of the E-ACSL subset *)
    unsupported
      (Extlib.may
         (fun _ ->
           if Keep_status.must_translate kf Keep_status.K_Terminates then
             not_yet env "terminates clause"))
      spec.spec_terminates;
    (match spec.spec_complete_behaviors with
    | [] -> ()
    | l ->
      unsupported
        (List.iter
           (fun _ ->
             if Keep_status.must_translate kf Keep_status.K_Complete then
               not_yet env "complete behaviors"))
        l);
    (match spec.spec_disjoint_behaviors with
    | [] -> ()
    | l ->
      unsupported
        (List.iter
           (fun _ ->
             if Keep_status.must_translate kf Keep_status.K_Disjoint then
               not_yet env "disjoint behaviors"))
        l);
    env
  in
  let env = convert_unsupported_clauses env in
  handle_error
    (fun env -> translate_preconditions kf env spec.spec_behavior)
    env

let translate_post_spec kf env spec =
  handle_error
    (fun env -> translate_postconditions kf env spec.spec_behavior)
    env

let translate_pre_code_annotation kf env annot =
  let convert env = match annot.annot_content with
    | AAssert(l, _, p) ->
      if Keep_status.must_translate kf Keep_status.K_Assert then
	let env = Env.set_annotation_kind env Misc.Assertion in
	if l <> [] then
	  not_yet env "@[assertion applied only on some behaviors@]";
	translate_named_predicate kf env p
      else
	env
    | AStmtSpec(l, spec) ->
      if l <> [] then
        not_yet env "@[statement contract applied only on some behaviors@]";
      translate_pre_spec kf env spec ;
    | AInvariant(l, loop_invariant, p) ->
      if Keep_status.must_translate kf Keep_status.K_Invariant then
	let env = Env.set_annotation_kind env Misc.Invariant in
	if l <> [] then
	  not_yet env "@[invariant applied only on some behaviors@]";
	let env = translate_named_predicate kf env p in
	if loop_invariant then Env.add_loop_invariant env p else env
      else
	env
    | AVariant _ ->
      if Keep_status.must_translate kf Keep_status.K_Variant
      then not_yet env "variant"
      else env
    | AAssigns _ ->
      (* TODO: it is not a precondition *)
      if Keep_status.must_translate kf Keep_status.K_Assigns
      then not_yet env "assigns"
      else env
    | AAllocation _ ->
      if Keep_status.must_translate kf Keep_status.K_Allocation
      then not_yet env "allocation"
      else env
    | APragma _ -> not_yet env "pragma"
    | AExtended _ -> env (* never translate extensions. *)
  in
  handle_error convert env

let translate_post_code_annotation kf env annot =
  let convert env = match annot.annot_content with
    | AStmtSpec(_, spec) -> translate_post_spec kf env spec
    | AAssert _
    | AInvariant _
    | AVariant _
    | AAssigns _
    | AAllocation _
    | APragma _
    | AExtended _ -> env
  in
  handle_error convert env

(*
Local Variables:
compile-command: "make -C ../.."
End:
*)
