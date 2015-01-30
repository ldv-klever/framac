(**************************************************************************)
(*                                                                        *)
(*  This file is part of Frama-C.                                         *)
(*                                                                        *)
(*  Copyright (C) 2007-2014                                               *)
(*    CEA   (Commissariat à l'énergie atomique et aux énergies            *)
(*           alternatives)                                                *)
(*    INRIA (Institut National de Recherche en Informatique et en         *)
(*           Automatique)                                                 *)
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

module CurrentLoc = Cil_const.CurrentLoc

let error (b,_e) fstring =
  Kernel.abort
    ~source:b
    ("In annotation: " ^^ fstring)

module Logic_builtin =
  State_builder.Hashtbl
    (Datatype.String.Hashtbl)
    (Cil_datatype.Builtin_logic_info)
    (struct
       let name = "built-in logic functions table"
       let dependencies = []
       let size = 17
     end)

module Logic_info =
  State_builder.Hashtbl
    (Datatype.String.Hashtbl)
    (Cil_datatype.Logic_info)
    (struct
       let name = "logic functions table"
       let dependencies = [ Logic_builtin.self ]
       let size = 17
     end)

module Logic_builtin_used = struct
  include State_builder.Ref
    (Cil_datatype.Logic_info.Set)
    (struct
      let name = "used built-in logic functions"
      let dependencies = [ Logic_builtin.self; Logic_info.self ]
      let default () = Cil_datatype.Logic_info.Set.empty
     end)
  let add li = set (Cil_datatype.Logic_info.Set.add li (get()))
  let mem li = Cil_datatype.Logic_info.Set.mem li (get())
  let iter f = Cil_datatype.Logic_info.Set.iter f (get())
end

module Logic_type_builtin =
  State_builder.Hashtbl
    (Datatype.String.Hashtbl)
    (Cil_datatype.Logic_type_info)
    (struct
       let name = "built-in logic types table"
       let dependencies = []
       let size = 17
     end)


let is_builtin_logic_type = Logic_type_builtin.mem

module Logic_type_info =
  State_builder.Hashtbl
    (Datatype.String.Hashtbl)
    (Cil_datatype.Logic_type_info)
    (struct
       let name = "logic types table"
       let dependencies = [ Logic_type_builtin.self ]
       let size = 17
     end)

module Logic_ctor_builtin =
  State_builder.Hashtbl
    (Datatype.String.Hashtbl)
    (Cil_datatype.Logic_ctor_info)
    (struct
       let name = "built-in logic contructors table"
       let dependencies = []
       let size = 17
     end)

module Logic_ctor_info =
  State_builder.Hashtbl
    (Datatype.String.Hashtbl)
    (Cil_datatype.Logic_ctor_info)
    (struct
       let name = "logic contructors table"
       let dependencies = [ Logic_ctor_builtin.self ]
       let size = 17
     end)

module Lemmas =
  State_builder.Hashtbl
    (Datatype.String.Hashtbl)
    (Cil_datatype.Global_annotation)
    (struct
        let name = "lemmas"
        let dependencies = []
        let size = 17
     end)

module Model_info =
  State_builder.Hashtbl
    (Datatype.String.Hashtbl)
    (Cil_datatype.Model_info)
    (struct
      let name = "model fields table"
      let dependencies = []
      let size = 17
     end)

module Forward_decls =
  State_builder.Hashtbl
    (Datatype.String.Hashtbl)
    (Datatype.Quadruple
       (Logic_ctor_info.Datatype) (Logic_type_info.Datatype) (Logic_info.Datatype) (Model_info.Datatype))
    (struct
      let name = "forward logic declarations table"
      let dependencies = []
      let size = 2
    end)

let check_and_pass_forward_logic_ctor,
    check_and_pass_forward_logic_type,
    check_and_pass_forward_logic_info,
    check_and_pass_forward_model_info =
  let mk ~type_name ~entity_name get name oldinfo =
    let module H = Datatype.String.Hashtbl in
    let tbls = Forward_decls.find "" in
    if oldinfo != H.find (get tbls) name then
      Kernel.fatal
        ~current:true
        "An attempt to add a new %s for the existing %s `%s' \
         instead of updating the existing one"
        type_name entity_name name;
    H.remove (get tbls) name
  in
  mk ~type_name:"logic_ctor_info" ~entity_name:"logic type constructor"   (fun (ctors, _, _, _) -> ctors),
  mk ~type_name:"logic_type_info" ~entity_name:"logic type"               (fun (_, types, _, _) -> types),
  mk ~type_name:"logic_info"      ~entity_name:"logic function/predicate" (fun (_, _, infos, _) -> infos),
  mk ~type_name:"model_info"      ~entity_name:"model variable/field"     (fun (_, _, _, models) -> models)

let check_forward_declarations () =
  let ctors, types, infos, models = Forward_decls.find "" in
  let error kind name _ = Kernel.fatal ~current:true "Unresolved forwardly declared %s `%s'" kind name in
  let module H = Datatype.String.Hashtbl in
  H.iter (error "logic type constructor") ctors;
  H.iter (error "logic type") types;
  H.iter (error "logic function or predicate") infos;
  H.iter (error "model variable or field") models

(* We depend from ast, but it is initialized after Logic_typing... *)
let init_dependencies from =
  State_dependency_graph.add_dependencies
    ~from
    [ Logic_info.self;
      Logic_type_info.self;
      Logic_ctor_info.self;
      Lemmas.self;
      Model_info.self;
      Forward_decls.self
    ]

let builtin_to_logic b =
  let params =
    List.map (fun (x, t) -> Cil_const.make_logic_var_formal x t) b.bl_profile
  in
  let li = Cil_const.make_logic_info b.bl_name in
  li.l_type <- b.bl_type;
  li.l_tparams <- b.bl_params;
  li.l_profile <- params;
  li.l_labels <- b.bl_labels;
  Logic_builtin_used.add li;
  Logic_info.add b.bl_name li;
  li

let is_builtin_logic_function = Logic_builtin.mem

let is_logic_function s = is_builtin_logic_function s || Logic_info.mem s

let find_all_logic_functions s =
  match Logic_info.find_all s with
  | [] ->
    let builtins = Logic_builtin.find_all s in
    let res = List.map builtin_to_logic builtins in
	(*        Format.printf "builtin func:@.";
		  List.iter (fun x -> Format.printf "%s#%d@." x.l_var_info.lv_name x.l_var_info.lv_id) res;
	 *)
    res
  | l ->
	(*        Format.printf "func in env:@.";
		  List.iter (fun x -> Format.printf "%s#%d@." x.l_var_info.lv_name x.l_var_info.lv_id) l; *)
    l

let find_first_logic_function s =
    try
      let li =
        let _, _, infos, _ = Forward_decls.find "" in
        Datatype.String.Hashtbl.find infos s
      in
      List.find ((==) li) (find_all_logic_functions s)
    with
    | Not_found ->
      Kernel.fatal "Logic functions/predicates table consistency violation: `%s' is not found" s

let find_logic_cons vi =
  List.find
    (fun x -> Cil_datatype.Logic_var.equal x.l_var_info vi)
    (Logic_info.find_all vi.lv_name)

(* add_logic_function takes as argument a function eq_logic_info which
   decides whether two logic_info are identical. It is intended to be
   Logic_utils.is_same_logic_profile, but this one can not be called
   from here since it will cause a circular dependency Logic_env <-
   Logic_utils <- Cil <- Logic_env
*)

let add_logic_function_gen is_same_profile l =
  if is_builtin_logic_function l.l_var_info.lv_name then
    error (CurrentLoc.get())
      "logic function or predicate %s is built-in. You can not redefine it"
      l.l_var_info.lv_name;
  try
    check_and_pass_forward_logic_info l.l_var_info.lv_name l
  with
  | Not_found ->
    List.iter
      (fun li ->
         if is_same_profile li l && Forward_decls.mem "" then (* Don't report error on the first pass *)
	   error (CurrentLoc.get ())
             "already declared logic function or predicate %s with same profile"
             l.l_var_info.lv_name)
      (Logic_info.find_all l.l_var_info.lv_name);
    Logic_info.add l.l_var_info.lv_name l

let remove_logic_function = Logic_info.remove

let is_logic_type = Logic_type_info.mem
let find_logic_type = Logic_type_info.find
let add_logic_type t infos =
  try
    check_and_pass_forward_logic_type t infos
  with
  | Not_found ->
    if is_logic_type t
    (* type variables hide type definitions on their scope *)
    then error (CurrentLoc.get ()) "logic type %s already declared" t
    else Logic_type_info.add t infos
let remove_logic_type = Logic_type_info.remove

let is_logic_ctor = Logic_ctor_info.mem
let find_logic_ctor = Logic_ctor_info.find
let add_logic_ctor c infos =
  try
    check_and_pass_forward_logic_ctor infos.ctor_name infos
  with
  | Not_found ->
    if is_logic_ctor c
    then error (CurrentLoc.get ()) "logic constructor %s already declared" c
    else Logic_ctor_info.add c infos
let remove_logic_ctor = Logic_ctor_info.remove

let is_model_field = Model_info.mem

let find_all_model_fields s = Model_info.find_all s

let find_model_field s typ =
  let l = Model_info.find_all s in
  let rec find_cons typ =
    try
      List.find (fun x -> Cil_datatype.Typ.equal x.mi_base_type typ) l
    with Not_found as e ->
      (* Don't use Cil.unrollType here:
         unrollType will unroll until it finds something other
         than TNamed. We want to go step by step.
      *)
      (match typ with
        | TNamed(ti,_) -> find_cons ti.ttype
        | _ -> raise e)
  in find_cons typ

let add_model_field m =
  try
    check_and_pass_forward_model_info m.mi_name m
  with Not_found ->
    try
      ignore (find_model_field m.mi_name m.mi_base_type);
      error (CurrentLoc.get())
        "Cannot add model field %s to type %a: it already exists."
        m.mi_name Cil_datatype.Typ.pretty m.mi_base_type
    with Not_found -> Model_info.add m.mi_name m

let remove_model_field = Model_info.remove

let is_builtin_logic_ctor = Logic_ctor_builtin.mem

let builtin_states =
  [ Logic_builtin.self; Logic_type_builtin.self; Logic_ctor_builtin.self ]

module Builtins= struct
  include Hook.Make(struct end)
    (* ensures we do not apply the hooks twice *)
  module Applied =
    State_builder.False_ref
      (struct
        let name = "Application of logic built-ins hook"
        let dependencies = builtin_states
         (* if the built-in states are not kept, hooks must be replayed. *)
       end)

  let apply () =
    Kernel.feedback ~level:5 "Applying logic built-ins hooks for project %s"
      (Project.get_name (Project.current()));
    if Applied.get () then Kernel.feedback ~level:5 "Already applied"
    else begin Applied.set true; apply () end
end

let save_tables filename =
  if not (Forward_decls.mem filename) then
    let module H = Datatype.String.Hashtbl in
    let (ctors, types, infos, models) as tbls =
      H.create (Logic_ctor_info.length ()),
      H.create (Logic_type_info.length ()),
      H.create (Logic_info.length ()),
      H.create (Model_info.length ())
    in
    Logic_ctor_info.iter (fun k v -> if not (Logic_ctor_builtin.mem k) then H.add ctors k v);
    Logic_type_info.iter (fun k v -> if not (Logic_type_builtin.mem k) then H.add types k v);
    Logic_info.iter (fun k v -> if not (Logic_builtin_used.mem v) then H.add infos k v);
    Model_info.iter (H.add models);
    Forward_decls.add filename tbls
  else
    Kernel.fatal ~current:true
      "The forward declarations from file `%s' have already been saved" filename

let prepare_tables ?(stage=`Names) () =
  Logic_ctor_info.clear ();
  Logic_type_info.clear ();
  Logic_info.clear ();
  Lemmas.clear ();
  Model_info.clear ();
  Logic_type_builtin.iter Logic_type_info.add;
  Logic_ctor_builtin.iter Logic_ctor_info.add;
  Logic_builtin_used.iter (fun x -> Logic_info.add x.l_var_info.lv_name x);
  match stage with
  | `Names -> ()
  | `Types (filename, imports) | `Bodies (filename, imports) ->
    let module H = Datatype.String.Hashtbl in
    begin try
      let ctors, types, infos, models = Forward_decls.find filename in
      let ctors, types, infos, models = H.copy ctors, H.copy types, H.copy infos, H.copy models in
      Forward_decls.replace "" (ctors, types, infos, models)
    with
    | Not_found -> Kernel.fatal ~current:true "The file `%s' has not been pre-parsed for imports" filename
    end;
    ListLabels.iter
      ((filename, []) :: imports)
      ~f:(fun (filename', names) ->
          try
            let ctors, types, infos, models = Forward_decls.find filename' in
            let to_import = H.create (List.length names) in
            List.iter (fun name -> H.add to_import name None) names;
            let check () =
              H.iter
                (fun name source_file ->
                   if source_file = None then
                     error (CurrentLoc.get ())
                       "The name `%s' requested for import from file `%s' \
                        was not found"
                       name filename')
                to_import
            in
            let add (type data) (module T : State_builder.Hashtbl with type key = string and type data = data) k v =
              let listed, imported = names = [] || H.mem to_import k, T.mem k in
              (* Re-importing is only allowed either from the file itself of from the same file
                 (for overloaded names) *)
              if listed && (not imported || H.find to_import k = Some filename') then begin
                T.add k v;
                H.replace to_import k (Some filename')
              end else if listed then
                let error fmt =
                  let b, e = Cil_datatype.Location.unknown in
                  let b = { b with Lexing.pos_fname = filename } in
                  error (b, e) fmt
                in
                try
                  match H.find to_import k with
                  | Some filename'' when filename' <> filename && filename'' <> filename ->
                    error
                      "The name `%s' requested for import from file `%s' \
                       has already been imported from another file `%s'. \
                       Cross-file overloading is not supported"
                      k filename' filename''
                  | Some _ | None -> raise Not_found
                with
                | Not_found ->
                  error
                    "The name `%s' requested for import from file `%s' \
                     has already been declared in the importing file. \
                     Imported names overloading is not supported"
                     k filename'
            in
            H.iter (add (module Logic_ctor_info)) ctors;
            H.iter (add (module Logic_type_info)) types;
            H.iter (add (module Logic_info)) infos;
            H.iter (add (module Model_info)) models;
            check ()
          with
          | Not_found ->
            error (CurrentLoc.get ())
              "The file `%s' specified in import declaration of file `%s' was not provided \
               to the Frama-C front-end"
              filename' filename)

(** C typedefs *)
(**
  -  true => identifier is a type name
  -  false => identifier is a plain identifier
*)
let typenames: (string, bool) Hashtbl.t = Hashtbl.create 13

let add_typename t = Hashtbl.add typenames t true
let hide_typename t = Hashtbl.add typenames t false
let remove_typename t = Hashtbl.remove typenames t
let reset_typenames () = Hashtbl.clear typenames

let typename_status t =
  try Hashtbl.find typenames t with Not_found -> false

let builtin_types_as_typenames () =
  Logic_type_builtin.iter (fun x _ -> add_typename x)

let add_builtin_logic_function_gen is_same_profile l =
  List.iter
    (fun li ->
       if is_same_profile li l then
	 error (CurrentLoc.get ())
	   "already declared builtin logic function or predicate \
            %s with same profile"
	   l.bl_name)
    (Logic_builtin.find_all l.bl_name);
  Logic_builtin.add l.bl_name l

let add_builtin_logic_type name infos =
  if not (Logic_type_builtin.mem name) then begin
    Logic_type_builtin.add name infos;
    add_typename name;
    add_logic_type name infos
  end

let add_builtin_logic_ctor name infos =
  if not (Logic_ctor_builtin.mem name) then begin
    Logic_ctor_builtin.add name infos;
    add_logic_ctor name infos
  end

let iter_builtin_logic_function f = Logic_builtin.iter (fun _ info -> f info)
let iter_builtin_logic_type f = Logic_type_builtin.iter (fun _ info -> f info)
let iter_builtin_logic_ctor f = Logic_ctor_builtin.iter (fun _ info -> f info)

(*
  Local Variables:
  compile-command: "make -C ../../.."
  End:
*)
