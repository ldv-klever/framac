(**************************************************************************)
(*                                                                        *)
(*  This file is part of Frama-C.                                         *)
(*                                                                        *)
(*  Copyright (C) 2007-2018                                               *)
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
open Cil
open Visitor
open Cil_datatype

type cpp_opt_kind = Gnu | Not_gnu | Unknown

let pretty_cpp_opt_kind fmt =
  function
  | Gnu -> Format.pp_print_string fmt "Gnu"
  | Not_gnu -> Format.pp_print_string fmt "Not_gnu"
  | Unknown -> Format.pp_print_string fmt "Unknown"

type file =
  | NeedCPP of
      string (* filename of the [.c] to preprocess *)
      * string (* Preprocessor command.
                  [filename.c -o tempfilname.i] will be appended at the
                    end.*)
      * cpp_opt_kind
  | NoCPP of string (** filename of a preprocessed [.c] *)
  | External of string * string (* file * name of plug-in that handles it *)

module D =
  Datatype.Make
    (struct
      include Datatype.Serializable_undefined
      type t = file
      let name = "File"
      let reprs =
        [ NeedCPP("", "", Unknown); NoCPP ""; External("", "") ]
      let structural_descr = Structural_descr.t_abstract
      let mem_project = Datatype.never_any_project
      let copy = Datatype.identity (* immutable strings *)
      let internal_pretty_code p_caller fmt t =
        let pp fmt = match t with
          | NoCPP s -> Format.fprintf fmt "@[File.NoCPP %S@]" (s :> string)
          | External (f,p) ->
            Format.fprintf fmt "@[File.External (%S,%S)@]" (f :> string) p
          | NeedCPP (a,b,c) ->
              Format.fprintf
                fmt "@[File.NeedCPP (%S,%S,%a)@]" (a :> string) b pretty_cpp_opt_kind c
        in
        Type.par p_caller Type.Call fmt pp
     end)
include D

let check_suffixes = Hashtbl.create 17
let new_file_type = Hashtbl.add check_suffixes
let get_suffixes () =
  Hashtbl.fold
    (fun s _ acc -> s :: acc)
    check_suffixes
    [ ".c"; ".i"; ".h" ]

let get_name = function NeedCPP (s,_,_) | NoCPP s | External (s,_) -> s

(* ************************************************************************* *)
(** {2 Preprocessor command} *)
(* ************************************************************************* *)

(* Do not trust custom command-line to be gnu like by default, but give
   them a chance, with a warning indicating that things may go wrong. *)
let cpp_opt_kind () =
  if Kernel.CppGnuLike.is_set () then
    if Kernel.CppGnuLike.get () then Gnu else Not_gnu
  else Unknown

(* the preprocessor command is:
   If the program has an explicit argument -cpp-command "XX -Y"
   (quotes are required by the shell)
   then XX -Y
   else use the command in [Config.preprocessor].*)
let get_preprocessor_command () =
  let cmdline = Kernel.CppCommand.get() in
  if cmdline <> "" then begin
     (cmdline, cpp_opt_kind ())
  end else begin
    let gnu =
      if Config.using_default_cpp then
        if Config.preprocessor_is_gnu_like then Gnu else Not_gnu
      else cpp_opt_kind ()
    in
    Config.preprocessor, gnu
  end

let from_filename ?cpp f =
  let path = Datatype.Filepath.of_string f in
  let cpp, is_gnu_like =
    let cmdline = Kernel.CppCommand.get() in
    if cmdline <> "" then
      cmdline, cpp_opt_kind ()
    else
      let flags = Json_compilation_database.get_flags path in
      let cpp, gnu =
    match cpp with
      | None -> get_preprocessor_command ()
        | Some cpp -> cpp, cpp_opt_kind ()
      in
      (if flags = "" then cpp else cpp ^ " " ^ flags), gnu
  in
  if Filename.check_suffix f ".i" then begin
    NoCPP f
  end else
    let suf =
      try
        let suf_idx = String.rindex f '.' in
        String.sub f suf_idx (String.length f - suf_idx)
      with Not_found -> (* raised by String.rindex if '.' \notin f *)
        ""
    in
    if Hashtbl.mem check_suffixes suf then
      External (f, suf)
    else if cpp <> "" then begin
      if not Config.preprocessor_keep_comments then
        Kernel.warning ~once:true
          "Default pre-processor does not keep comments. Any ACSL annotation \
           on non-pre-processed file will be discarded.";
      NeedCPP (f, cpp, is_gnu_like)
    end else
      Kernel.abort "No working pre-processor found. You can only analyze \
                    pre-processed .i files."

(* ************************************************************************* *)
(** {2 Internal states} *)
(* ************************************************************************* *)

module Files : sig
  val get: unit -> t list
  val register: t list -> unit
  val pre_register: t -> unit
  val is_computed: unit -> bool
  val reset: unit -> unit
  val pre_register_state: State.t
end = struct

  module S =
    State_builder.List_ref
      (D)
      (struct
         let dependencies =
           [ Kernel.CppCommand.self;
             Kernel.CppExtraArgs.self;
             Kernel.JsonCompilationDatabase.self;
             Kernel.Files.self ]
         let name = "Files for preprocessing"
       end)

  module Pre_files =
    State_builder.List_ref
      (D)
      (struct
        let dependencies = []
        let name = "Built-ins headers and source"
       end)

  let () =
    State_dependency_graph.add_dependencies
      ~from:S.self
      [ Ast.self; Ast.UntypedFiles.self; Cabshelper.Comments.self ]

  let () =
    State_dependency_graph.add_dependencies
      ~from:Pre_files.self
      [ Ast.self;
	Ast.UntypedFiles.self;
	Cabshelper.Comments.self;
        Cil.Frama_c_builtins.self ]

  let () =
    Ast.add_linked_state Cabshelper.Comments.self

  let pre_register_state = Pre_files.self

  (* Allow to register files in advance, e.g. prolog files for plugins *)
  let pre_register file =
    let prev_files = Pre_files.get () in Pre_files.set (prev_files @ [file])

  let register files =
    if S.is_computed () then
      raise (Ast.Bad_Initialization "[File.register] Too many initializations");
    let prev_files = S.get () in
    S.set (prev_files @ files);
    S.mark_as_computed ()

  let get () = Pre_files.get () @ S.get ()
  let is_computed () = S.is_computed ()

  let reset () =
    let selection = State_selection.with_dependencies S.self in
    (* Keep built-in files set *)
    Project.clear ~selection ()
end

let get_all = Files.get
let pre_register = Files.pre_register


(* ************************************************************************* *)
(** {2 Machdep} *)
(* ************************************************************************* *)

(* not exported, see [pretty_machdep] below. *)
let print_machdep fmt (m : Cil_types.mach) =
  begin
    let open Cil_types in
    Format.fprintf fmt "Machine: %s@\n" m.version ;
    let pp_size_error fmt v =
      if v < 0
      then Format.pp_print_string fmt "error"
      else Format.fprintf fmt "%2d" v
    in
    let pp_size_bits fmt v =
      if v >= 0 then Format.fprintf fmt "%d bits, " (v*8)
    in
    let pp_align_error fmt v =
      if v < 0
      then Format.pp_print_string fmt "alignof error"
      else Format.fprintf fmt "aligned on %d bits" (v*8)
    in
    List.iter
      (fun (name,size,align) ->
         Format.fprintf fmt
           "   sizeof %11s = %a (%a%a)@\n"
           name pp_size_error size pp_size_bits size pp_align_error align)
      [
        "short",  m.sizeof_short, m.alignof_short ;
        "int",    m.sizeof_int,   m.alignof_int ;
        "long",   m.sizeof_long,  m.alignof_long ;
        "long long", m.sizeof_longlong,  m.alignof_longlong ;
        "float",  m.sizeof_float,  m.alignof_float ;
        "double", m.sizeof_double, m.alignof_double ;
        "long double", m.sizeof_longdouble, m.alignof_longdouble ;
        "pointer", m.sizeof_ptr, m.alignof_ptr ;
        "void", m.sizeof_void, 1 ;
        "function", m.sizeof_fun, m.alignof_fun ;
      ] ;
    List.iter
      (fun (name,typeof) ->
         Format.fprintf fmt "   typeof %11s = %s@\n" name typeof)
      [
        "sizeof(T)", m.size_t ;
        "wchar_t", m.wchar_t ;
        "ptrdiff_t", m.ptrdiff_t ;
      ] ;
    Format.fprintf fmt "   char is %s@\n"
      (if m.char_is_unsigned then "unsigned" else "signed");
    Format.fprintf fmt "   machine is %s endian@\n"
      (if m.little_endian then "little" else "big") ;
    Format.fprintf fmt "   strings are %s chars@\n"
      (if m.const_string_literals then "const" else "writable") ;
    Format.fprintf fmt "   assembly names %s leading '_'@\n"
      (if m.underscore_name then "have" else "have no") ;
    Format.fprintf fmt "   compiler %s builtin __va_list@\n"
      (if m.has__builtin_va_list then "has" else "has not") ;
    Format.fprintf fmt "   compiler %s __head as a keyword@\n"
      (if m.__thread_is_keyword then "uses" else "does not use") ;
  end

module DatatypeMachdep = Datatype.Make_with_collections(struct
  include Datatype.Serializable_undefined
  let reprs = [Machdeps.x86_32]
  let name = "File.Machdep"
  type t = Cil_types.mach
  let compare : t -> t -> int = Pervasives.compare
  let equal : t -> t -> bool = (=)
  let hash : t -> int = Hashtbl.hash
  let copy = Datatype.identity
end)

let default_machdeps =
  [ "x86_16", Machdeps.x86_16;
    "x86_32", Machdeps.x86_32;
    "x86_64", Machdeps.x86_64;
    "gcc_x86_16", Machdeps.x86_16;
    "gcc_x86_32", Machdeps.gcc_x86_32;
    "gcc_x86_64", Machdeps.gcc_x86_64;
    "ppc_32", Machdeps.ppc_32;
    "msvc_x86_64", Machdeps.msvc_x86_64;
  ]

let regexp_existing_machdep_macro = Str.regexp "-D[ ]*__FC_MACHDEP_"

let existing_machdep_macro () =
  let extra = String.concat " " (Kernel.CppExtraArgs.get ()) in
  try
    ignore (Str.search_forward regexp_existing_machdep_macro extra 0);
    true
  with Not_found -> false

let machdep_macro = function
  | "x86_16" | "gcc_x86_16" -> "__FC_MACHDEP_X86_16"
  | "x86_32" | "gcc_x86_32" -> "__FC_MACHDEP_X86_32"
  | "x86_64" | "gcc_x86_64" -> "__FC_MACHDEP_X86_64"
  | "ppc_32"                -> "__FC_MACHDEP_PPC_32"
  | "msvc_x86_64"           -> "__FC_MACHDEP_MSVC_X86_64"
  | s ->
      let res = "__FC_MACHDEP_" ^ (Transitioning.String.uppercase_ascii s) in
      Kernel.warning ~once:true
        "machdep %s has no registered macro. Using %s for pre-processing" s res;
      res

module Machdeps =
  State_builder.Hashtbl(Datatype.String.Hashtbl)(DatatypeMachdep)
    (struct
      let name = " File.Machdeps"
      let size = 5
      let dependencies = []
     end)

let mem_machdep s = Machdeps.mem s || List.mem_assoc s default_machdeps

let new_machdep s m =
  try
    let cm = Machdeps.find s in
    if not (cm = m) then
      Kernel.abort "trying to register incompatible machdeps under name `%s'" s
  with Not_found ->
    Machdeps.add s m

let pretty_machdeps fmt =
  Machdeps.iter (fun x _ -> Format.fprintf fmt "@ %s" x);
  List.iter (fun (x, _) -> Format.fprintf fmt "@ %s" x) default_machdeps

let machdep_help () =
  let m = Kernel.Machdep.get () in
  if m = "help" then begin
    Kernel.feedback
      "@[supported machines are%t@ (default is x86_32).@]"
      pretty_machdeps;
    raise Cmdline.Exit
  end else
    Cmdline.nop

let () = Cmdline.run_after_exiting_stage machdep_help

let set_machdep () =
  let m = Kernel.Machdep.get () in
  if not (mem_machdep m) then
    Kernel.abort "@[unsupported machine %s.@ Try one of%t.@]" m pretty_machdeps

let () = Cmdline.run_after_configuring_stage set_machdep

(* Local to this module. Use Cil.theMachine.theMachine outside *)
let get_machdep () =
  let m = Kernel.Machdep.get () in
  try
    Machdeps.find m
  with Not_found ->
    try
      List.assoc m default_machdeps
    with Not_found -> (* Should not happen given the checks above *)
      Kernel.fatal "Machdep %s not registered" m

let pretty_machdep ?fmt ?machdep () =
  let machine = match machdep with None -> get_machdep () | Some m -> m in
  match fmt with
  | None -> Log.print_on_output (fun fmt -> print_machdep fmt machine)
  | Some fmt -> print_machdep fmt machine

(* ************************************************************************* *)
(** {2 Initializations} *)
(* ************************************************************************* *)

let generate_pp_file =
  let newline = Str.regexp "^" in
  let linedir = Str.regexp "#[ ]*\\(line\\)? \\([0-9]+\\)[ ]*\\(\"\\([^\"]+\\)\"\\)?" in
  let warn_preprocessor_output =
    let module H = Datatype.String.Hashtbl in
    let h = H.create 2 in
    fun s file line ->
      let key = s ^ " " ^ file in
      if not (H.mem h key) then begin
        Kernel.warning
          "@[Frama-C@ detected@ suspicious@ preprocessor@ output@ %s (%s, line %d).@ \
           This@ is@ likely@ to@ be@ due@ to@ GCC@ bug 23779@ related@ to@ \
           incorrect@ handling@ of@ CR+LF@ newlines@ in@ comments. Consider@ using@ UNIX-style@ line@ ends@ or@ \
           another@ preprocessor@ e.g.@ clang@ (see@ also@ option -cpp-command).@]"
          s file line;
        H.replace h key ()
      end
  in
  fun pp_in_file pp_out_file ->
  let pp_input =
    let ic = open_in pp_in_file in
    let n = in_channel_length ic in
    let s = Bytes.create n in
    really_input ic s 0 n;
    close_in ic;
    (* Dirty HARDLY AVOIDABLE HACK!!! Workaround for OLD GCC BUG #23779 about incorrect processing of
       \r in comments (they are replaced with \n(!!!)).
       In this case we get wrong preprocessor output, but at least we don't fail
       and are able to warn the user about the issue. *)
    Array.(concat @@
           let lines = of_list @@ Str.split newline (Bytes.unsafe_to_string s) in
           [lines; make (length lines) ""])
  in
  let pp_line_present = Array.make (Array.length pp_input) false in
  let newline_length = String.length "\n" in
  let oc = open_out Filename.(remove_extension pp_in_file ^ ".pp" ^ extension pp_in_file) in
  let file = ref pp_in_file and line = ref 1 in
  let ic = open_in pp_out_file in
  begin try while true do
    let s = input_line ic ^ "\n" in
    if Str.string_match linedir s 0 then begin
      line := int_of_string (Str.matched_group 2 s);
      try file := Str.matched_group 4 s with Not_found -> ();
    end else if String.equal !file pp_in_file then begin
      let s =
        let first_nonspace s =
          let fnsp = ref 0 in
          while !fnsp < String.length s && (s.[!fnsp] = ' ' || s.[!fnsp] = '\t') do incr fnsp; done;
          !fnsp
        in
        let olds = pp_input.(!line - 1) in
        let olds = if String.length olds >= 2 && olds.[0] = '/' && olds.[1] = '/' then "" else olds in
        let fs = first_nonspace s and oldfs = first_nonspace olds in
        if pp_line_present.(!line - 1) then begin
          (* Handle multiline output *)
          if fs <= oldfs && olds <> "" then
            warn_preprocessor_output "overwriting the same input file location twice" pp_in_file !line;
          String.((if olds = "" then "" else sub olds 0 (length olds - 1)) ^ sub s fs @@ length s - fs)
        end else if fs > 0 && oldfs > 0 && not String.(equal (sub olds 0 oldfs) @@ sub s 0 fs) then
          (* Handle messed indentation *)
          String.(sub olds 0 oldfs ^ sub s fs @@ length s - fs)
        else
          s
      in
      if String.(length s > newline_length || length pp_input.(!line - 1) = newline_length) then
        pp_input.(!line - 1) <- s
      else
        pp_input.(!line - 1) <- "// " ^ pp_input.(!line - 1);
      pp_line_present.(!line - 1) <- true;
      incr line
    end
  done with
  | End_of_file ->
    close_in ic
  end;
  (* DIRTY HACK CONT'D *)
  let pp_input, pp_line_present =
    let exception Exceed of int in
    try
      let n = Array.length pp_input in
      for i = n / 2 to n - 1 do
        if pp_line_present.(i) then raise (Exceed i)
      done;
      Array.(sub pp_input 0 (n / 2), sub pp_line_present 0 (n / 2))
    with
    | Exceed line ->
      warn_preprocessor_output "exceeding beyond the end location of the input file" pp_in_file line;
      pp_input, pp_line_present
  in
  Array.iter2
    Printf.(fun present -> if present then fprintf oc "%s" else fprintf oc "// %s")
    pp_line_present pp_input;
  close_out oc

let safe_remove_file (f : Datatype.Filepath.t) =
  if not (Kernel.is_debug_key_enabled Kernel.dkey_parser) then
    Extlib.safe_remove (f :> string)

let build_cpp_cmd cmdl supp_args in_file out_file =
  try
          (* Format.eprintf "-cpp-command=|%s|@\n" cmdl; *)
          (* look at the command line to find two "%s" or one "%1" and a "%2"
          *)
    let percent1 = String.index cmdl '%' in
          (* Format.eprintf "-cpp-command percent1=%d@\n" percent1;
             Format.eprintf "-cpp-command %%%c@\n" (String.get cmdl
             (percent1+1)); *)
    let percent2 = String.index_from cmdl (percent1+1) '%' in
          (* Format.eprintf "-cpp-command percent2=%d@\n" percent2;
             Format.eprintf "-cpp-command %%%c@\n" (String.get cmdl
             (percent2+1)); *)
    let file1, file2 =
      match String.get cmdl (percent1+1), String.get cmdl (percent2+1)
      with
      | '1', '2' ->
        in_file, out_file
            (* "%1" followed by "%2" is used to printf 'ppf' after 'f' *)
      | '2', '1' ->
        out_file, in_file
      | _, _ -> raise (Invalid_argument "maybe a bad cpp command")
    in
    let cmd1 = String.sub cmdl 0 percent1 in
          (* Format.eprintf "-cpp-command cmd1=|%s|@\n" cmd1; *)
    let cmd2 =
      String.sub cmdl (percent1 + 2) (percent2 - (percent1 + 2))
    in
          (* Format.eprintf "-cpp-command cmd2=|%s|@\n" cmd2; *)
    let cmd3 =
      String.sub cmdl (percent2 + 2) (String.length cmdl - (percent2 + 2))
    in
          (* Format.eprintf "-cpp-command cmd3=|%s|@\n" cmd3; *)
    Format.sprintf "%s%s %s %s%s%s" cmd1
            (* using Filename.quote for filenames which contain space or
               shell metacharacters *)
      (Filename.quote file1)
      supp_args
      cmd2 (Filename.quote file2) cmd3
  with
  | Invalid_argument _
  | Not_found ->
    Format.sprintf "%s %s -o %s %s" cmdl
      supp_args
              (* using Filename.quote for filenames which contain space or
                 shell metacharacters *)
      (Filename.quote out_file) (Filename.quote in_file)

let parse_cabs = function
  | NoCPP f ->
      if not (Sys.file_exists f) then
        Kernel.abort "preprocessed file %S does not exist" f;
      let path = Datatype.Filepath.of_string f in
      Kernel.feedback "Parsing %a (no preprocessing)"
        Datatype.Filepath.pretty path;
      Frontc.parse_to_cabs (Datatype.Filepath.of_string f)
  | NeedCPP (f, cmdl, is_gnu_like) ->
      if not (Sys.file_exists (f :> string)) then
        Kernel.abort "source file %S does not exist" (f :> string);
      let debug = Kernel.is_debug_key_enabled Kernel.dkey_parser in
      let add_if_gnu opt =
        match is_gnu_like with
          | Gnu -> [opt]
          | Not_gnu -> []
          | Unknown ->
              Kernel.warning
                ~once:true
                "your preprocessor is not known to handle option `%s'. \
                 If pre-processing fails because of it, please add \
                 -no-cpp-frama-c-compliant option to Frama-C's command-line. \
                 If you do not want to see this warning again, explicitly use \
                 option -cpp-frama-c-compliant."
                opt;
              [opt]
      in
      let ppf =
        try
          Datatype.Filepath.of_string
            (Extlib.temp_file_cleanup_at_exit ~debug
               (Filename.basename (f :> string)) ".i")
        with Extlib.Temp_file_error s ->
          Kernel.abort "cannot create temporary file: %s" s
      in
      (* Hypothesis: the preprocessor is POSIX compliant,
         hence understands -I and -D. *)
      let include_args =
        if Kernel.FramaCStdLib.get () then [Config.datadir ^ "/libc"]
        else []
      in
      let define_args =
        if Kernel.FramaCStdLib.get () && not (existing_machdep_macro ())
        then [machdep_macro (Kernel.Machdep.get ())]
        else []
      in
      let extra_args =
        if include_args = [] && define_args = [] then []
        else add_if_gnu "-nostdinc"
      in
      let define_args = "__FRAMAC__" :: define_args in
      (* Hypothesis: the preprocessor does support the arch-related
         options tested when 'configure' was run. *)
      let required_cpp_arch_args = (get_machdep ()).cpp_arch_flags in
      let supported_cpp_arch_args, unsupported_cpp_arch_args =
        List.partition (fun arg ->
            List.mem arg Config.preprocessor_supported_arch_options)
          required_cpp_arch_args
      in
      if is_gnu_like = Unknown && not (Kernel.CppCommand.is_set ())
         && unsupported_cpp_arch_args <> [] then
        Kernel.warning ~once:true
          "your preprocessor is not known to handle option(s) `%a', \
           considered necessary for machdep `%s'. To ensure compatibility \
           between your preprocessor and the machdep, consider using \
           -cpp-command with the appropriate flags. \
           Your preprocessor is known to support these flags: %a"
          (Pretty_utils.pp_list ~sep:" " Format.pp_print_string)
          unsupported_cpp_arch_args (Kernel.Machdep.get ())
          (Pretty_utils.pp_list ~sep:" " Format.pp_print_string)
          Config.preprocessor_supported_arch_options;
      let extra_args =
        if Kernel.ReadAnnot.get () then
          if Kernel.PreprocessAnnot.is_set () then
            if Kernel.PreprocessAnnot.get () then
              "-dD" :: extra_args
            else extra_args
          else
            let opt = add_if_gnu "-dD" in
            opt @ extra_args
        else extra_args
      in
      let pp_str = Format.pp_print_string in
      let string_of_supp_args extra includes defines =
        Format.asprintf "%a%a%a"
          (Pretty_utils.pp_list ~pre:" -I" ~sep:" -I" ~empty:"" pp_str) includes
          (Pretty_utils.pp_list ~pre:" -D" ~sep:" -D" ~empty:"" pp_str) defines
          (Pretty_utils.pp_list ~pre:" " ~sep:" " ~empty:"" pp_str) extra
      in
      let supp_args =
        string_of_supp_args
          (Kernel.CppExtraArgs.get () @ extra_args @ supported_cpp_arch_args)
          include_args define_args
      in
      Kernel.feedback ~dkey:Kernel.dkey_pp
        "@{<i>preprocessing@} with \"%s %s %s\"" cmdl supp_args f;
      let path = Datatype.Filepath.of_string f in
      Kernel.feedback "Parsing %a (with preprocessing)"
        Datatype.Filepath.pretty path;
      let cpp_command = build_cpp_cmd cmdl supp_args f (ppf :> string) in
      if Sys.command cpp_command <> 0 then begin
        safe_remove_file ppf;
        Kernel.abort "failed to run: %s@\n\
          you may set the CPP environment variable to select the proper \
          preprocessor command or use the option \"-cpp-command\"." cpp_command
      end;
      let ppf =
        if Kernel.ReadAnnot.get() &&
             ((Kernel.PreprocessAnnot.is_set () &&
                 Kernel.PreprocessAnnot.get())
              || (match is_gnu_like with
                    | Gnu -> true
                    | Not_gnu -> false
                    | Unknown ->
                        Kernel.warning
                          ~once:true
                          "trying to preprocess annotation with an unknown \
                           preprocessor."; true))
        then begin
          let pp_annot_supp_args =
            Format.asprintf "%s -nostdinc %a"
              (if Kernel.GeneratePPFile.get () then "-traditional-cpp" else "")
              (Pretty_utils.pp_list ~sep:" " Format.pp_print_string)
              supported_cpp_arch_args
          in
          let ppf' =
            try Logic_preprocess.file ".c"
                  (build_cpp_cmd cmdl pp_annot_supp_args)
                  (ppf : Filepath.Normalized.t :> string)
            with Sys_error _ as e ->
              safe_remove_file ppf;
              Kernel.abort "preprocessing of annotations failed (%s)"
                (Printexc.to_string e)
          in
          safe_remove_file ppf ;
          ppf'
        end else ppf
      in
      if Kernel.GeneratePPFile.get () then
        generate_pp_file f (ppf :> string);
      let _, decls = Frontc.parse_to_cabs ppf in
      safe_remove_file ppf;
      path, decls
  | External (f, suf) ->
      if not (Sys.file_exists f) then
        Kernel.abort "file %S does not exist." f;
      try
        let path = Datatype.Filepath.of_string f in
        Kernel.feedback "Parsing %a (external front-end)"
          Datatype.Filepath.pretty path;
        Hashtbl.find check_suffixes suf f
      with Not_found ->
        Kernel.abort "could not find a suitable plugin for parsing %S." f

(** Keep defined entry point even if not defined, and possibly the functions
    with only specifications (according to parameter
    keep_unused_specified_function). This function is meant to be passed to
    {!Rmtmps.removeUnusedTemps}. *)
let keep_entry_point ?(specs=Kernel.Keep_unused_specified_functions.get ()) g =
  Rmtmps.isDefaultRoot g ||
    match g with
    | GFun({svar = v; sspec = spec},_)
    | GFunDecl(spec,v,_) ->
      Kernel.MainFunction.get_plain_string () = v.vname
      (* Always keep the declaration of the entry point *)
      || (specs && not (is_empty_funspec spec))
      (* and the declarations carrying specifications according to the
         command line.*)
    | _ -> false

type 'a what =
  | Term_node : term_node what
  | Predicate : predicate_node what

let propagate_logic_info_default_labels =
  let module H = Logic_info.Hashtbl in
  let inplace_visit = inplace_visit () in
  let locations = H.create 200 in
  let glob_annot_visitor =
    object(self)
      inherit genericCilVisitor inplace_visit

      method! vfile _ =
        H.clear locations;
        DoChildren

      method! vannotation =
        function
        | Dfun_or_pred (li, loc)
        | Dinvariant (li, loc)
        | Dtype_annot (li, loc) ->
          H.add locations li loc;
          SkipChildren
        | Daxiomatic (_, annots, _, _) ->
          List.iter (fun annot -> ignore @@ self#vannotation annot) annots;
          SkipChildren
        | _ -> SkipChildren
    end
  in
  let sorted = ref [] in
  let logic_info_decl_visitor =
    let finished = H.create 200 in
    let rec logic_info_use_visitor path =
      object
        inherit genericCilVisitor inplace_visit

        method! vlogic_info_use li =
          if not List.(memq li (tl path)) && not (H.mem finished li) && li != List.hd path then
            logic_info_decl_handler path li
          else
            SkipChildren
      end
    and logic_info_decl_handler path li =
      ignore @@ visitCilLogicInfo (logic_info_use_visitor (li :: path)) li;
      sorted := li :: !sorted;
      H.add finished li ();
      SkipChildren
    in
    object
      inherit genericCilVisitor inplace_visit

      method! vfile _ =
        H.clear finished;
        sorted := [];
        DoChildren

      method! vlogic_info_decl = logic_info_decl_handler []
    end
  in
  let fixpoint_reached = ref false in
  let logic_info_use_visitor li =
    object
      inherit genericCilVisitor inplace_visit

      method! vlogic_info_use =
        function
        | { l_labels = [_] } ->
          li.l_labels <- [FormalLabel "L"];
          fixpoint_reached := false;
          SkipChildren
        | { l_labels = _ :: _; l_type; l_var_info } ->
          let pp_kind fmt ty =
            Format.fprintf fmt @@
              match ty with
              | Some _ -> "function"
              | None -> "predicate"
          in
          Kernel.abort
            ~current:true
            "Detected multi-label logic %a `%a' usage in an unlabeled logic %a `%a'"
            pp_kind l_type
            Printer.pp_logic_var l_var_info
            pp_kind li.l_type
            Printer.pp_logic_var li.l_var_info
        | _ -> SkipChildren
    end
  in
  let default_label_assoc_visitor =
    object(self)
      inherit genericCilVisitor inplace_visit

      val mutable labels = Stack.create ()

      initializer
        Stack.push (Some Logic_const.here_label) labels

      method private do_with_label_opt : 'a. logic_label option -> 'a visitAction =
        fun lab ->
        Stack.push lab labels;
        DoChildrenPost (fun x -> ignore @@ Stack.pop labels; x)

      method private do_with_label : 'a. logic_label -> 'a visitAction = fun lab -> self#do_with_label_opt (Some lab)
      method private do_without_label : 'a. 'a visitAction = self#do_with_label_opt None

      method private do_app : 'a. 'a what -> _ -> _ -> 'a visitAction =
        fun (type a) what li args ->
        try
          ChangeDoChildrenPost ((let labs = [Extlib.the (Stack.top labels)] in
                                 match (what : a what) with
                                 | Term_node -> (Tapp (li, labs, args) : a) | Predicate -> Papp (li, labs, args)),
                                Extlib.id)
        with
        | Stack.Empty
        | Invalid_argument _ ->
          Kernel.abort
            ~current:true
            "No default label in context of labeled logic %s application: %a"
            (match what with Term_node -> "function" | Predicate -> "function/predicate")
            Printer.pp_logic_var li.l_var_info

      method! vterm_node =
        function
        | Tapp ({ l_labels = [_] } as li, [], args) -> self#do_app Term_node li args
        | Tat (_, lab) -> self#do_with_label lab
        | _ -> DoChildren

      method! vpredicate_node =
        function
        | Papp ({ l_labels = [_] } as li, [], args) -> self#do_app Predicate li args
        | Pat (_, lab) -> self#do_with_label lab
        | _ -> DoChildren

      method! vassigns _ = self#do_with_label Logic_const.old_label

      method! vallocates _ = self#do_with_label Logic_const.old_label

      method! vlogic_info_decl =
        function
        | { l_labels = [lab] } -> self#do_with_label lab
        | _ -> self#do_without_label

      method! vannotation =
        function
        | Dlemma (_, _, [lab], _, _, _, _) -> self#do_with_label lab
        | _ -> self#do_without_label
    end
  in
  fun file ->
    visitCilFile glob_annot_visitor file;
    visitCilFile logic_info_decl_visitor file;
    while not !fixpoint_reached do
      fixpoint_reached := true;
      List.iter
        (fun li ->
           if li.l_labels = [] then
             ignore @@ visitCilLogicInfo (logic_info_use_visitor li) li)
        (List.rev !sorted)
    done;
    visitCilFile default_label_assoc_visitor file

type _ parsing_mode =
  | Topological : Cil_types.file parsing_mode
  | Recursive   : (Cil_types.file * Cabs.file list) parsing_mode

let files_to_cil (type k) : k parsing_mode -> file list -> k =
  let cabs f =
    let fname, decls =
      try
        parse_cabs f
      with exn when Errorloc.had_errors () ->
        if Kernel.Debug.get () >= 1 then raise exn
        else
          Kernel.abort "@[stopping on@ file %S@ that@ has@ errors.%t@]"
            (get_name f)
            (fun fmt ->
               if Filename.check_suffix (get_name f) ".c" &&
                  not (Kernel.is_debug_key_enabled Kernel.dkey_pp)
               then
                 Format.fprintf fmt "@ Add@ '-kernel-msg-key pp'@ \
                                     for preprocessing command.")
    in
    let decls, imports =
      List.fold_left
        (fun (decls, imports) ->
           function
           | b, Cabs.GLOBANNOT l ->
             let l, imports =
               List.fold_left
                 (fun (decls, imports) ->
                    function
                    | { Logic_ptree.decl_node = Logic_ptree.LDimport (fname, names) } ->
                      decls, (fname, names) :: imports
                    | decl -> decl :: decls, imports)
                 ([], imports)
                 l
             in
             begin match l with
               | [] -> decls, imports
               | _ :: _ -> (b, Cabs.GLOBANNOT (List.rev l)) :: decls, imports
             end
           | decl -> decl :: decls, imports)
        ([], [])
        decls
    in
    (fname, List.rev decls), imports
  in
  let parse ~stage cabs =
    try
      let file = Frontc.parse ~stage cabs in
      file.fileName <- fst cabs;
      Kernel.debug ~dkey:Kernel.dkey_file_print_one "result of parsing %a:@\n%a"
        Filepath.Normalized.pretty (fst cabs) Cil_printer.pp_file file;
      if Errorloc.had_errors () then raise Exit;
      file
    with exn when Errorloc.had_errors () ->
      if Kernel.Debug.get () >= 1 then raise exn
      else
        Kernel.abort "skipping file %a that has errors." Filepath.Normalized.pretty (fst cabs)
  in
  function
  | Recursive ->
    fun files ->
      (* Parsing and merging must occur in the very same order.
         Otherwise the order of files on the command line will not be consistently
         handled. *)
      Kernel.feedback ~level:2 "parsing";
      let cabs_imports = List.map cabs files in
      let cil_files =
        List.iter (fun (cabs, _) -> ignore @@ parse ~stage:`Names cabs) cabs_imports;
        List.iter
          (fun (cabs, imports) ->
             ignore @@ parse ~stage:(`Types ((fst cabs : Filepath.Normalized.t :> string), imports)) cabs)
          cabs_imports;
        List.map
          (fun  (cabs, imports) ->
             parse ~stage:(`Bodies ((fst cabs : Filepath.Normalized.t :> string), imports)) cabs)
          cabs_imports
      in
      let cabs_files = List.map fst cabs_imports in
      Ast.UntypedFiles.set cabs_files;
      (* Perform symbolic merge of all files *)
      Kernel.feedback ~level:2 "symbolic link";
      let merged_file = Mergecil.merge cil_files "whole_program" in
      Logic_utils.complete_types merged_file;
      if Kernel.UnspecifiedAccess.get () then
        Undefined_sequence.check_sequences merged_file;
      merged_file, cabs_files
  | Topological ->
    fun files ->
      (* Parsing and merging must occur in the very same order.
         Otherwise the order of files on the command line will not be consistently
         handled. *)
      Kernel.feedback ~level:2 "parsing";
      let cil_files =
        List.map
          (fun f ->
             let f = parse ~stage:`Once @@ fst @@ cabs f in
             Rmtmps.removeUnusedTemps f;
             f)
          files
      in
      (* Perform symbolic merge of all files *)
      Kernel.feedback ~level:2 "symbolic link";
      let merged_file = Mergecil.merge cil_files "whole_program" in
      Logic_utils.complete_types merged_file;
      if Kernel.UnspecifiedAccess.get () then
        Undefined_sequence.check_sequences merged_file;
      merged_file
(* "Implicit" annotations are those added by the kernel with ACSL name
   'Frama_C_implicit_init'. Currently, this concerns statements that are
   generated to initialize local variables. *)
module Implicit_annotations =
  State_builder.Hashtbl
    (Property.Hashtbl)(Datatype.List(Property))
    (struct
        let name = "File.Implicit_annotations"
        let dependencies = [Annotations.code_annot_state]
        let size = 32
     end)

let () = Ast.add_linked_state Implicit_annotations.self

let () =
  Property_status.register_property_remove_hook
    (fun p ->
       if Implicit_annotations.mem p then begin
         Kernel.debug ~dkey:Kernel.dkey_file_annot
           "Removing implicit property %a" Property.pretty p;
         Implicit_annotations.remove p
       end)

let emit_status p hyps =
  Kernel.debug ~dkey:Kernel.dkey_file_annot
    "Marking implicit property %a as true" Property.pretty p;
  Property_status.emit Emitter.kernel ~hyps p Property_status.True

let emit_all_statuses _ =
  Kernel.debug ~dkey:Kernel.dkey_file_annot "Marking properties";
  Implicit_annotations.iter emit_status

let () = Ast.apply_after_computed emit_all_statuses

let add_annotation kf st a =
  Annotations.add_code_annot Emitter.end_user ~kf st a;
  (* Now check if the annotation is valid by construction
     (provided normalization is correct). *)
  match a.annot_content with
  | AStmtSpec
      ([],
       ({ spec_behavior = [ { b_name = "Frama_C_implicit_init" } as bhv]})) ->
    let props = Property.ip_post_cond_of_behavior kf (Kstmt st) [] bhv in
    List.iter (fun p -> Implicit_annotations.add p []) props
  | _ -> ()

let synchronize_source_annot has_new_stmt kf =
  match kf.fundec with
  | Definition (fd,_) ->
    let (visitor:cilVisitor) = object
      inherit nopCilVisitor as super
      val block_with_user_annots = ref None
      val user_annots_for_next_stmt = ref []
      method! vstmt st =
        super#pop_stmt st;
        let father = super#current_stmt in
        super#push_stmt st;
        let is_in_same_block () = match !block_with_user_annots,father with
          | None, None -> true
          | Some block, Some stmt_father when block == stmt_father -> true
          | _, _ -> false
        in
        let is_annot_next annot =
          match annot.annot_content with
          | AStmtSpec _ | APragma (Slice_pragma SPstmt | Impact_pragma IPstmt)
            -> true
          | AExtended(_,is_loop,(_,name,_,_)) ->
            (match Logic_env.extension_category name with
             | Some (Ext_code_annot (Ext_here | Ext_next_loop)) -> false
             | Some (Ext_code_annot Ext_next_stmt) -> true
             | Some (Ext_code_annot Ext_next_both) -> not is_loop
             | Some (Ext_contract | Ext_global) | None ->
               Kernel.(
                 warning ~wkey:wkey_acsl_extension
                   "%s is not a code annotation extension" name);
               false)
          | AAssert _ | AInvariant _ | AVariant _
          | AAssigns _ | AAllocation _
          | APragma (Slice_pragma (SPctrl | SPexpr _))
          | APragma (Astraver_pragma _ | Assert_pragma _)
          | APragma (Impact_pragma (IPexpr _))
          | APragma (Loop_pragma _) -> false
        in
        let synchronize_user_annot a = add_annotation kf st a in
        let synchronize_previous_user_annots () =
          if !user_annots_for_next_stmt <> [] then begin
            if is_in_same_block () then begin
              let my_annots = !user_annots_for_next_stmt in
              let post_action st =
                let treat_annot (has_annot,st) (st_ann, annot) =
                  if is_annot_next annot then begin
                    if has_annot || st.labels <> [] || st_ann.labels <> []
                    then begin
                      st_ann.skind <- (Block (Cil.mkBlockNonScoping [st]));
                      has_new_stmt := true;
                      Annotations.add_code_annot
                        Emitter.end_user ~kf st_ann annot;
                      (true, st_ann)
                    end else begin
                      add_annotation kf st annot;
                      (true,st)
                    end
                  end else begin
                    add_annotation kf st annot;
                    (true, st)
                  end
                in
                let (_,st) =
                  List.fold_left treat_annot (false,st) my_annots
                in
                st
              in
              block_with_user_annots:=None;
              user_annots_for_next_stmt:=[];
              ChangeDoChildrenPost(st,post_action)
            end
            else begin
              Kernel.warning ~current:true ~once:true
                "Ignoring previous annotation relative \
                 to next statement effects" ;
              block_with_user_annots := None ;
              user_annots_for_next_stmt := [];
              DoChildren
            end
          end else begin
            block_with_user_annots := None ;
            user_annots_for_next_stmt := [];
            DoChildren;
          end
        in
        let add_user_annot_for_next_stmt st annot =
          if !user_annots_for_next_stmt = [] then begin
            block_with_user_annots := father;
            user_annots_for_next_stmt := [st,annot]
          end else if is_in_same_block () then
            user_annots_for_next_stmt :=
              (st, annot)::!user_annots_for_next_stmt
          else begin
            Kernel.warning ~current:true ~once:true
              "Ignoring previous annotation relative to next statement \
               effects";
            block_with_user_annots := father;
            user_annots_for_next_stmt := [st, annot] ;
          end;
          ChangeTo (Cil.mkStmtOneInstr (Skip Cil_datatype.Location.unknown))
        in
        assert (!block_with_user_annots = None
               || !user_annots_for_next_stmt <> []);
        match st.skind with
        | Instr (Code_annot (annot,_)) ->
          (* Code annotation isn't considered as a real stmt.
             So, previous annotations should be relative to the next stmt.
             Only this [annot] may be synchronised to that stmt *)
          if is_annot_next annot then
            (* Annotation relative to the effect of next statement *)
            add_user_annot_for_next_stmt st annot
          else
            (* Annotation relative to the current control point *)
            (match !user_annots_for_next_stmt with
             | [] -> synchronize_user_annot annot; DoChildren
             | _ ->
               (* we have an annotation relative to the next
                  real C statement somewhere above, and we have
                  not reached it yet. Just stack the current annotation.*)
               add_user_annot_for_next_stmt st annot)
        | Loop (annot, _, _, _, _) ->
          (* Synchronize previous annotations on that statement *)
          let res = synchronize_previous_user_annots () in
          (* Synchronize loop annotations on that statement *)
          List.iter synchronize_user_annot
            (List.sort (fun x y -> x.annot_id - y.annot_id) annot);
          res
        | _ ->
          (* Synchronize previous annotations on that statement *)
          synchronize_previous_user_annots () ;
    end
    in
    ignore (visitCilFunction visitor fd)
  | Declaration _ -> ()

let register_global = function
  | GFun (fundec, loc) ->
      let onerets = ref [] in
      if Kernel.Oneret.get () then begin
        let callback return goto = onerets := (return,goto) :: !onerets in
        (* ensure there is only one return *)
        Oneret.oneret ~callback fundec
      end;
      (* Build the Control Flow Graph for all
         functions *)
      if Kernel.SimplifyCfg.get () then begin
        Cfg.prepareCFG ~keepSwitch:(Kernel.KeepSwitch.get ()) fundec;
        Cfg.clearCFGinfo fundec;
        Cfg.cfgFun fundec;
        (* prepareCFG may add additional labels that are not used in the end. *)
        Rmtmps.remove_unused_labels fundec;
      end;
      Globals.Functions.add (Definition(fundec,loc));
      let kf = Globals.Functions.get fundec.svar in
      (* Finally set property-status on oneret clauses *)
      if Kernel.Oneret.get () then
        List.iter
          (fun ((sret,b,pret),gotos) ->
             let ipreturns =
               Property.ip_of_ensures kf (Kstmt sret) b (Returns,pret) in
             let ipgotos = List.map
                 (fun (sgot,agot) -> Property.ip_of_code_annot_single kf sgot agot)
                 gotos in
             Implicit_annotations.add ipreturns ipgotos
          ) !onerets
  | GFunDecl (spec, f,loc) ->
      (* global prototypes *)
      let args =
        try Some (Cil.getFormalsDecl f) with Not_found -> None
      in
      (* Use a copy of the spec, as the original one will be erased by
         AST cleanup. *)
      let spec = { spec with spec_variant = spec.spec_variant } in
      Globals.Functions.add (Declaration(spec,f,args,loc))
  | GVarDecl (vi,_) when not vi.vdefined ->
      (* global variables declaration with no definitions *)
      Globals.Vars.add_decl vi
  | GVar (varinfo,initinfo,_) ->
      (* global variables definitions *)
      Globals.Vars.add varinfo initinfo;
  | GAnnot (annot, _loc) ->
    Annotations.add_global Emitter.end_user annot
  | _ -> ()

let computeCFG ~clear_id file =
  Cfg.clearFileCFG ~clear_id file;
  Cfg.computeFileCFG file

(* Remove (inplace) annotations that are physically in the AST (and that have
   been moved inside kernel tables) by turning them into Skip, then
   remove empty statements and blocks. *)
let cleanup file =
  let visitor = object(self)
    inherit Visitor.frama_c_inplace

    val mutable keep_stmt = Stmt.Set.empty

    val mutable changed = false

    method private remove_lexical_annotations stmt =
      match stmt.skind with
        | Instr(Code_annot(_,loc)) ->
            stmt.skind <- Instr(Skip(loc))
        | Loop (_::_, b1,l1,s1,s2) ->
            stmt.skind <- Loop ([], b1, l1, s1, s2)
        | _ -> ()

    method! vstmt_aux st =
      self#remove_lexical_annotations st;
      let loc = Stmt.loc st in
      if Annotations.has_code_annot st || st.labels <> [] then
        keep_stmt <- Stmt.Set.add st keep_stmt;
      match st.skind with
      | Block b ->
            (* queue is flushed afterwards*)
            let b' = Cil.visitCilBlock (self:>cilVisitor) b in
        (match b'.bstmts, b'.blocals, b'.bstatics with
         | [], [], [] -> changed <- true; st.skind <- (Instr (Skip loc))
         | _ -> if b != b' then st.skind <- Block b');
                   SkipChildren
        | _ -> DoChildren

    method! vblock b =
      let optim b =
        b.bstmts <-
          List.filter
          (fun x ->
             not (Cil.is_skip x.skind) || Stmt.Set.mem x keep_stmt ||
               ( changed <- true; false) (* don't try this at home, kids...*)
          )
          b.bstmts;
        (* Now that annotations are in the table, we do not need to
           retain the block anymore.
         *)
        b.battrs <- List.filter
          (function
          | Attr(l,[]) when l = Cabs2cil.frama_c_keep_block -> false
          | _ -> true)
          b.battrs;
        b
      in
      (* uncomment if you don't want to consider scope of locals (see below) *)
      (* b.blocals <- [];*)
      ChangeDoChildrenPost(b,optim)

    method! vglob_aux = function
    | GFun (f,_) ->
      f.sspec <- Cil.empty_funspec ();
      (* uncomment if you dont want to treat scope of locals (see above)*)
      (* f.sbody.blocals <- f.slocals; *)
      DoChildren
    | GFunDecl(s,_,_) ->
      Logic_utils.clear_funspec s;
      DoChildren
    | GType _ | GCompTag _ | GCompTagDecl _ | GEnumTag _
    | GEnumTagDecl _ | GVar _ | GVarDecl _ | GAsm _ | GPragma _ | GText _
    | GAnnot _  ->
        SkipChildren

    method! vfile f =
      ChangeDoChildrenPost
        (f,fun f -> if changed then begin
           Cfg.clearFileCFG ~clear_id:false f;
           Cfg.computeFileCFG f; f end
         else f)
  end
  in visitFramacFileSameGlobals visitor file

let print_renaming: Cil.cilVisitor = object
  inherit Cil.nopCilVisitor
  method! vvdec v =
    if v.vname <> v.vorig_name then begin
      Kernel.result ~current:true
        "Variable %s has been renamed to %s" v.vorig_name v.vname
    end;
    DoChildren
end

module Transform_before_cleanup =
  Hook.Build_ordered
    (struct module Id = Datatype.String type t = Cil_types.file end)
module Transform_after_cleanup =
  Hook.Build_ordered
    (struct module Id = Datatype.String type t = Cil_types.file end)
module Transform_after_parameter_change =
  Hook.Build_ordered
    (struct module Id = Datatype.String type t = State.t end)
let transform_parameters = ref State.Set.empty

type code_transformation_category =
  { name: string;
    before_id: Transform_before_cleanup.id;
    after_id: Transform_after_cleanup.id;
    prm_id: Transform_after_parameter_change.id }

let register_code_transformation_category s =
  { name = s;
    before_id = Transform_before_cleanup.register_key s;
    after_id = Transform_after_cleanup.register_key s;
    prm_id = Transform_after_parameter_change.register_key s }

let add_transform_parameter
    ~before ~after name f (p:(module Parameter_sig.S)) =
  let module P = (val p: Parameter_sig.S) in
  let hook self =
    (* hook is launched if AST already exists and the apply was triggered by
       the corresponding option change *)
    if State.equal self P.self && Ast.is_computed () then begin
      Kernel.feedback ~dkey:Kernel.dkey_file_transform
        "applying %s to current AST, after option %s changed"
        name.name P.option_name;
      f (Ast.get());
      if Kernel.Check.get () then
        Filecheck.check_ast
          ("after code transformation: " ^ name.name ^
              " triggered by " ^ P.option_name)
    end
  in
  (* P.add_set_hook must be done only once. *)
  if not (State.Set.mem P.self !transform_parameters) then begin
    transform_parameters:=State.Set.add P.self !transform_parameters;
    P.add_set_hook (fun _ _ -> Transform_after_parameter_change.apply P.self)
  end;
  Transform_after_parameter_change.extend name.prm_id hook;
  List.iter
    (fun b ->
      Transform_after_parameter_change.add_dependency name.prm_id b.prm_id)
    before;
  List.iter
    (fun a ->
      Transform_after_parameter_change.add_dependency a.prm_id name.prm_id)
    after

module Cfg_recomputation_queue =
  State_builder.Set_ref(Cil_datatype.Fundec.Set)
    (struct
      let name = "File.Cfg_recomputation_queue"
      let dependencies = [Ast.self]
     end)

let () = Ast.add_linked_state Cfg_recomputation_queue.self

let must_recompute_cfg f = Cfg_recomputation_queue.add f

let recompute_cfg _ =
  (* just in case f happens to modify the CFG *)
  Cfg_recomputation_queue.iter
    (fun f -> Cfg.clearCFGinfo ~clear_id:false f; Cfg.cfgFun f);
  Cfg_recomputation_queue.clear ()

let transform_and_check name is_normalized f ast =
  let printer =
    if is_normalized then Printer.pp_file else Cil_printer.pp_file
  in
  Kernel.feedback
    ~dkey:Kernel.dkey_file_transform
    "applying %s to file:@\n%a" name printer ast;
  f ast;
  recompute_cfg ();
  if Kernel.Check.get () then begin
    Filecheck.check_ast
      ~is_normalized  ~ast ("after code transformation: " ^ name);
  end

let add_code_transformation_before_cleanup
    ?(deps:(module Parameter_sig.S) list = [])
    ?(before=[]) ?(after=[]) name f =
  Transform_before_cleanup.extend
    name.before_id (transform_and_check name.name false f);
  List.iter
    (fun b ->
      Transform_before_cleanup.add_dependency name.before_id b.before_id)
    before;
  List.iter
    (fun a ->
      Transform_before_cleanup.add_dependency a.before_id name.before_id)
    after;
  List.iter (add_transform_parameter ~before ~after name f) deps

let add_code_transformation_after_cleanup
    ?(deps:(module Parameter_sig.S) list = [])  ?(before=[]) ?(after=[])
    name f =
  Transform_after_cleanup.extend name.after_id
    (transform_and_check name.name true f);
  List.iter
    (fun b ->
      Transform_after_cleanup.add_dependency name.after_id b.after_id) before;
  List.iter
    (fun a ->
      Transform_after_cleanup.add_dependency a.after_id name.after_id) after;
  List.iter (add_transform_parameter ~before ~after name f) deps

let syntactic_constant_folding ast =
  if Kernel.Constfold.get () then
    Cil.visitCilFileSameGlobals (Cil.constFoldVisitor true) ast

let constfold = register_code_transformation_category "constfold"

let () =
  let deps = [ (module Kernel.Constfold: Parameter_sig.S) ] in
  add_code_transformation_after_cleanup
    ~deps constfold syntactic_constant_folding

let prepare_cil_file ast =
  Kernel.feedback ~level:2 "preparing the AST";
  computeCFG ~clear_id:true ast;
  if Kernel.Check.get () then begin
    Filecheck.check_ast ~is_normalized:false ~ast "initial AST"
  end;
  Kernel.feedback ~level:2 "First check done";
  if Kernel.Orig_name.get () then begin
    Cil.visitCilFileSameGlobals print_renaming ast
  end;
  Transform_before_cleanup.apply ast;
  (* Remove unused temp variables and globals. *)
  Kernel.feedback ~level:2 "cleaning unused parts";
  Rmtmps.removeUnusedTemps ~isRoot:keep_entry_point ast;
  if Kernel.Check.get () then begin
    Filecheck.check_ast ~is_normalized:false ~ast "Removed temp vars"
  end;
  (try
     List.iter register_global ast.globals
   with Globals.Vars.AlreadyExists(vi,_) ->
     Kernel.fatal
       "Trying to add the same varinfo twice: %a (vid:%d)"
       Printer.pp_varinfo vi vi.vid);
  Kernel.feedback ~level:2 "register globals done";
  (* Lemma functions *)
  Logic_lemma_functions.make_axioms_for_functions ast;
  (* NB: register_global also calls oneret, which might introduce new
     statements and new annotations tied to them. Since sid are set by cfg,
     we must compute it again before annotation synchronisation *)
  Cfg.clearFileCFG ~clear_id:false ast;
  Cfg.computeFileCFG ast;
  let recompute = ref false in
  Globals.Functions.iter (synchronize_source_annot recompute);
  Cil.visitCilFileSameGlobals
    (object(self)
      inherit Cil.nopCilVisitor
      method! vinst =
        function
        | Call (None, { enode = Lval (Var { vname = "__builtin_unreachable" }, NoOffset) }, [], loc) ->
          let annot = Logic_const.new_code_annotation (AAssert ([], Logic_const.unamed ~loc Pfalse)) in
          Annotations.add_code_annot
            Emitter.kernel
            ~kf:(Globals.Functions.get (Extlib.the self#current_func).svar)
            (Extlib.the self#current_stmt)
            annot;
          ChangeTo [Code_annot (annot, loc)]
        | Call (_, { enode = Lval (Var { vname = "__builtin_unreachable" }, _) }, _, _) ->
          Kernel.error "Wrong arguments to __builtin_unreachable";
          SkipChildren
        | _ -> SkipChildren
     end)
     ast;
  Kernel.feedback ~level:2 "replacing __builtin_unreachable with 'assert false' done";
  (* We might also introduce new blocks for synchronization. *)
  if !recompute then begin
    Cfg.clearFileCFG ~clear_id:false ast;
    Cfg.computeFileCFG ast;
  end;
  cleanup ast;
  Ast.set_file ast;
  (* Check that normalization is correct. *)
  if Kernel.Check.get() then begin
     Filecheck.check_ast ~ast "AST after normalization";
  end;
  Globals.Functions.iter Annotations.register_funspec;
  if Kernel.Check.get () then begin
    Filecheck.check_ast ~ast "AST after annotation registration"
  end;
  Transform_after_cleanup.apply ast;
  (* reset tables depending on AST in case they have been computed during
     the transformation. *)
  Ast.set_file ast

let fill_built_ins () =
  if Cil.selfMachine_is_computed () then begin
    Kernel.debug "Machine is computed, just fill the built-ins";
    Cil.init_builtins ();
  end else begin
    Kernel.debug "Machine is not computed, initialize everything";
    Cil.initCIL (Logic_builtin.init()) (get_machdep ());
  end;
  (* Fill logic tables with builtins *)
  Logic_env.Builtins.apply ();
  Logic_env.prepare_tables ()

let init_project_from_cil_file prj file =
  let selection =
    State_selection.diff
      State_selection.full
      (State_selection.list_union
         (List.map State_selection.with_dependencies
            [Cil.Builtin_functions.self;
             Ast.self;
             Files.pre_register_state]))
  in
  Project.copy ~selection prj;
  Project.on prj (fun file -> fill_built_ins (); prepare_cil_file file) file


module Global_annotation_graph = struct
  module Base =
    Graph.Imperative.Digraph.Concrete(Cil_datatype.Global)
  include Base
  include Graph.Traverse.Dfs(Base)
  include Graph.Topological.Make(Base)
end

let find_typeinfo ty =
  let module F = struct exception Found of global end in
  let globs = (Ast.get()).globals in
  try
    List.iter
      (fun g -> match g with
        | GType (ty',_) when ty == ty' -> raise (F.Found g)
        | GType (ty',_) when ty.tname = ty'.tname ->
            Kernel.fatal
              "Lost sharing between definition and declaration of type %s"
              ty.tname
        | _ -> ())
      globs;
    Kernel.fatal "Reordering AST: unknown typedef for %s"  ty.tname
  with F.Found g -> g

let extract_logic_infos g =
  let rec aux acc = function
  | Dfun_or_pred (li,_) | Dinvariant (li,_) | Dtype_annot (li,_) -> li :: acc
  | Dvolatile _ | Dtype _ | Dlemma _
  | Dmodel_annot _ | Dcustom_annot _ | Dextended _ -> acc
  | Daxiomatic(_,l,_,_) -> List.fold_left aux acc l
  in aux [] g

let find_logic_info_decl li =
  let module F = struct exception Found of global end in
  let globs = (Ast.get()).globals in
  try
    List.iter
      (fun g -> match g with
        | GAnnot (ga,_) ->
            if
              List.exists
                (fun li' -> Logic_info.equal li li')
                (extract_logic_infos ga)
            then raise (F.Found g)
        | _ -> ())
      globs;
    Kernel.fatal "Reordering AST: unknown declaration \
                  for logic function or predicate %s"
      li.l_var_info.lv_name
  with F.Found g -> g

class reorder_ast: Visitor.frama_c_visitor =
  let unique_name_recursive_axiomatic =
    let i = ref 0 in
    fun () ->
      if !i = 0 then begin incr i; "__FC_recursive_axiomatic" end
      else begin
        let res = "__FC_recursive_axiomatic_" ^ (string_of_int !i) in
        incr i; res
      end
  in
object(self)
  inherit Visitor.frama_c_inplace
  val mutable known_enuminfo = Enuminfo.Set.empty
  val mutable known_compinfo = Compinfo.Set.empty
  val mutable known_typeinfo = Typeinfo.Set.empty
  val mutable known_var = Varinfo.Set.empty
  val mutable known_logic_info = Logic_info.Set.empty
  val mutable local_logic_info = Logic_info.Set.empty

  (* globals that have to be declared before current declaration. *)
  val mutable needed_decls = []
  (* global annotations are treated separately, as they need special
     care when revisiting their content *)
  val mutable needed_annots = []

  val current_annot = Stack.create ()

  val subvisit = Stack.create ()

  val typedefs = Stack.create ()

  val logic_info_deps = Global_annotation_graph.create ()

  method private add_known_enuminfo ei =
    known_enuminfo <- Enuminfo.Set.add ei known_enuminfo

  method private add_known_compinfo ci =
    known_compinfo <- Compinfo.Set.add ci known_compinfo

  method private add_known_type ty =
    known_typeinfo <- Typeinfo.Set.add ty known_typeinfo

  method private add_known_var vi =
    known_var <- Varinfo.Set.add vi known_var

  method private add_known_logic_info li =
    known_logic_info <- Logic_info.Set.add li known_logic_info

  method private add_needed_decl g =
    needed_decls <- g :: needed_decls

  method private add_needed_annot g =
    needed_annots <- g :: needed_annots

  method private add_annot_depend g =
    try
      let g' = Stack.top current_annot in
      if g == g' then ()
      else
        Global_annotation_graph.add_edge
          logic_info_deps g g' (* g' depends upon g *)
    with Stack.Empty ->
      Global_annotation_graph.add_vertex logic_info_deps g
      (* Otherwise, if we only have one annotation to take care of,
         the graph will be empty... *)

  method private add_known_annots g =
    let lis = extract_logic_infos g in
    List.iter self#add_known_logic_info lis

  method private clear_deps () =
    needed_decls <- [];
    needed_annots <- [];
    Stack.clear current_annot;
    Stack.clear typedefs;
    Global_annotation_graph.clear logic_info_deps

  method private make_annots g =
    let g =
      match g with
        | [ g ] -> g
        | _ -> (* We'll eventually add some globals, but the value returned
                  by visitor itself is supposed to be a singleton. Everything
                  is done in post-action.
               *)
            Kernel.fatal "unexpected result of visiting global when reordering"
    in
    let deps =
      if Global_annotation_graph.nb_vertex logic_info_deps = 0 then []
      else if Global_annotation_graph.has_cycle logic_info_deps then begin
        (* Assumption: elements from the stdlib are not part of a cycle with
           others logic functions, i.e. the stdlib is well-formed.  *)
        let entries =
          Global_annotation_graph.fold
            (fun g acc ->
               let stdlib =
                 Cil.findAttribute "fc_stdlib" (Cil_datatype.Global.attr g)
        in
               let key =
                 match  stdlib with
                 | [ AStr s ] -> s
                 | _ -> ""
               in
               let elts =
                 try Datatype.String.Map.find key acc
                 with Not_found -> []
               in
               Datatype.String.Map.add key (g::elts) acc
            )
            logic_info_deps Datatype.String.Map.empty
        in
        Datatype.String.Map.fold
          (fun k l res ->
             let attr = if k = "" then [] else [ Attr("fc_stdlib", [AStr k])] in
             let entries =
               List.fold_left
                 (fun acc g ->
                    match g with GAnnot (g,_) -> g :: acc | _ -> acc)
                 [] l
             in
             (GAnnot
            (Daxiomatic
               (unique_name_recursive_axiomatic (),
                    entries, attr,
                Location.unknown),
                 Location.unknown))::res)
          entries []
      end else begin
        Global_annotation_graph.fold
          (fun ga acc -> ga :: acc) logic_info_deps []
      end
    in
    assert (List.length deps = List.length needed_annots);
    match g with
      | GAnnot _ -> List.rev deps
       (** g is already in the dependencies graph. *)
      | _ -> List.rev (g::deps)

  (* TODO: add methods for uses of undeclared identifiers.
     Use functions that maps an identifier to its decl.
     Don't forget to check for cycles for TNamed and logic_info.
  *)

  method! vtype ty =
    (match ty with
      | TVoid _ | TInt _ | TFloat _ | TPtr _
      | TFun _ | TBuiltin_va_list _ | TArray _ -> ()

      | TNamed (ty,_) ->
          let g = find_typeinfo ty in
          if not (Typeinfo.Set.mem ty known_typeinfo) then begin
            self#add_needed_decl g;
            Stack.push g typedefs;
            Stack.push true subvisit;
            ignore
              (Visitor.visitFramacGlobal (self:>Visitor.frama_c_visitor) g);
            ignore (Stack.pop typedefs);
            ignore (Stack.pop subvisit);
          end
          else
            Stack.iter
              (fun g' -> if g == g' then
                  Kernel.fatal
                    "Globals' reordering failed: \
                     recursive definition of type %s"
                    ty.tname)
              typedefs
      | TComp(ci,_,_) ->
          if not (Compinfo.Set.mem ci known_compinfo) then begin
            self#add_needed_decl (GCompTagDecl (ci,Location.unknown));
            self#add_known_compinfo ci
          end
      | TEnum(ei,_) ->
          if not (Enuminfo.Set.mem ei known_enuminfo) then begin
            self#add_needed_decl (GEnumTagDecl (ei, Location.unknown));
            self#add_known_enuminfo ei
          end);
    DoChildren

  method! vvrbl vi =
    if vi.vglob && not (Varinfo.Set.mem vi known_var) then begin
      if Cil.isFunctionType vi.vtype then
        self#add_needed_decl (GFunDecl (Cil.empty_funspec(),vi,vi.vdecl))
      else
        self#add_needed_decl (GVarDecl (vi,vi.vdecl));
      self#add_known_var vi;
    end;
    DoChildren

  method private logic_info_occurrence lv =
    if not (Logic_env.is_builtin_logic_function lv.l_var_info.lv_name) then
      begin
        let g = find_logic_info_decl lv in
        if not (Logic_info.Set.mem lv known_logic_info) then begin
          self#add_annot_depend g;
          Stack.push true subvisit;
          (* visit will also push g in needed_annot. *)
          ignore (Visitor.visitFramacGlobal (self:>Visitor.frama_c_visitor) g);
          ignore (Stack.pop subvisit)
        end else if List.memq g needed_annots then begin
          self#add_annot_depend g;
        end;
      end

  method private add_local_logic_info li =
    local_logic_info <- Logic_info.Set.add li local_logic_info

  method private remove_local_logic_info li =
    local_logic_info <- Logic_info.Set.remove li local_logic_info

  method private is_local_logic_info li =
    Logic_info.Set.mem li local_logic_info

  method! vlogic_var_use lv =
    let logic_infos = Annotations.logic_info_of_global lv.lv_name in
    (try
       self#logic_info_occurrence
         (List.find
            (fun x -> Cil_datatype.Logic_var.equal x.l_var_info lv)
            logic_infos)
     with Not_found -> ());
    DoChildren

  method! vterm t =
    match t.term_node with
      | Tlet(li,_) -> self#add_local_logic_info li;
          DoChildrenPost (fun t -> self#remove_local_logic_info li; t)
      | _ -> DoChildren

  method! vpredicate_node p =
    match p with
      | Plet(li,_) -> self#add_local_logic_info li;
          DoChildrenPost (fun t -> self#remove_local_logic_info li; t)
      | _ -> DoChildren

  method! vlogic_info_use lv =
    if not (self#is_local_logic_info lv) then self#logic_info_occurrence lv;
    DoChildren

  method! vglob_aux g =
    let is_subvisit = try Stack.top subvisit with Stack.Empty -> false in
    (match g with
      | GType (ty,_) -> self#add_known_type ty; self#add_needed_decl g
      | GCompTagDecl(ci,_) | GCompTag(ci,_) -> self#add_known_compinfo ci
      | GEnumTagDecl(ei,_) | GEnumTag(ei,_) -> self#add_known_enuminfo ei
      | GVarDecl(vi,_) | GVar (vi,_,_) | GFun({svar = vi},_) | GFunDecl (_,vi,_)
        -> self#add_known_var vi
      | GAsm _ | GPragma _ | GText _ -> ()
      | GAnnot (ga,_) ->
          Stack.push g current_annot;
          self#add_known_annots ga;
          Global_annotation_graph.add_vertex logic_info_deps g;
          self#add_needed_annot g);
    let post_action g =
      (match g with
        | [GAnnot _] -> ignore (Stack.pop current_annot)
        | _ -> ());
      if is_subvisit then g (* everything will be done at toplevel *)
      else begin
        let res = List.rev_append needed_decls (self#make_annots g) in
        self#clear_deps ();
        res
      end
    in
    DoChildrenPost post_action
end

module Remove_spurious = struct
  type env =
      { typeinfos: Typeinfo.Set.t;
        compinfos: Compinfo.Set.t;
        enuminfos: Enuminfo.Set.t;
        varinfos: Varinfo.Set.t;
        logic_infos: Logic_info.Set.t;
        kept: global list;
      }

let treat_one_global acc g =
  match g with
    | GType (ty,_) when Typeinfo.Set.mem ty acc.typeinfos -> acc
    | GType (ty,_) ->
        { acc with
          typeinfos = Typeinfo.Set.add ty acc.typeinfos;
          kept = g :: acc.kept }
    | GCompTag _ -> { acc with kept = g :: acc.kept }
    | GCompTagDecl(ci,_) when Compinfo.Set.mem ci acc.compinfos -> acc
    | GCompTagDecl(ci,_) ->
        { acc with
          compinfos = Compinfo.Set.add ci acc.compinfos;
          kept = g :: acc.kept }
    | GEnumTag _ -> { acc with kept = g :: acc.kept }
    | GEnumTagDecl(ei,_) when Enuminfo.Set.mem ei acc.enuminfos -> acc
    | GEnumTagDecl(ei,_) ->
        { acc with
          enuminfos = Enuminfo.Set.add ei acc.enuminfos;
          kept = g :: acc.kept }
    | GVarDecl(vi,_) | GFunDecl (_, vi, _)
        when Varinfo.Set.mem vi acc.varinfos -> acc
    | GVarDecl(vi,_) ->
        { acc with
          varinfos = Varinfo.Set.add vi acc.varinfos;
          kept = g :: acc.kept }
    | GVar _ | GFun _ | GFunDecl _ -> { acc with kept = g :: acc.kept }
    | GAsm _ | GPragma _ | GText _ -> { acc with kept = g :: acc.kept }
    | GAnnot (a,_) ->
        let lis = extract_logic_infos a in
        if List.exists (fun x -> Logic_info.Set.mem x acc.logic_infos) lis
        then acc
        else begin
          let known_li =
            List.fold_left (Extlib.swap Logic_info.Set.add) acc.logic_infos lis
          in
          { acc with
            kept = g::acc.kept;
            logic_infos = known_li;
          }
        end

let empty =
  { typeinfos = Typeinfo.Set.empty;
    compinfos = Compinfo.Set.empty;
    enuminfos = Enuminfo.Set.empty;
    varinfos = Varinfo.Set.empty;
    logic_infos = Logic_info.Set.empty;
    kept = [];
  }

let process file =
  let env = List.fold_left treat_one_global empty file.globals in
  file.globals <- List.rev env.kept

end

let reorder_custom_ast ast =
  Visitor.visitFramacFile (new reorder_ast) ast;
  Remove_spurious.process ast

let reorder_ast () = reorder_custom_ast (Ast.get())

(* Fill logic tables with builtins *)
let init_cil () =
  Cil.initCIL (Logic_builtin.init()) (get_machdep ());
  Logic_env.Builtins.apply ();
  Logic_env.prepare_tables ()

let prepare_from_c_files () =
  init_cil ();
  let files = Files.get () in (* Allow pre-registration of prolog files *)
  let cil =
    if Kernel.ReadAnnot.get () then
      fst @@ files_to_cil Recursive files
    else
      files_to_cil Topological files
  in
  prepare_cil_file cil

let init_project_from_visitor ?(reorder=false) prj
    (vis:Visitor.frama_c_visitor) =
  if not (Cil.is_copy_behavior vis#behavior)
    || not (Project.equal prj (Extlib.the vis#project))
  then
    Kernel.fatal
      "Visitor does not copy or does not operate on correct project.";
  Project.on prj (fun () -> Cil.initCIL (fun () -> ()) (get_machdep ())) ();
  let old_ast = Ast.get () in
  let ast = visitFramacFileCopy vis old_ast in
  let finalize ast =
    computeCFG ~clear_id:false ast;
    Ast.set_file ast
  in
  let selection = State_selection.with_dependencies Ast.self in
  Project.on ~selection prj finalize ast;
  (* reorder _before_ check. *)
  if reorder then Project.on prj reorder_ast ();
  if Kernel.Check.get() then begin
    let name = prj.Project.name in
    Project.on prj (Filecheck.check_ast ~ast) ("AST of " ^ name);
    assert
      (Kernel.verify (old_ast == Ast.get())
         "Creation of project %s modifies original project"  name);
    Filecheck.check_ast ("Original AST after creation of " ^ name)
  end

let prepare_from_visitor ?reorder prj visitor =
  let visitor = visitor prj in
  init_project_from_visitor ?reorder prj visitor

let create_project_from_visitor ?reorder ?(last=true) prj_name visitor =
  let selection =
    State_selection.list_union
      (List.map State_selection.with_dependencies
         [ Kernel.Files.self; Files.pre_register_state ])
  in
  let selection = State_selection.diff State_selection.full selection in
  let prj = Project.create_by_copy ~selection ~last prj_name in
  (* reset projectified parameters to their default values *)
  let temp = Project.create "File.temp" in
  Project.copy
    ~selection:(Parameter_state.get_reset_selection ()) ~src:temp prj;
  Project.remove ~project:temp ();
  Project.on prj init_cil ();
  prepare_from_visitor ?reorder prj visitor;
  prj

let init_from_c_files files =
  (match files with [] -> () | _ :: _ -> Files.register files);
  prepare_from_c_files ()

let init_from_cmdline () =
  let prj1 = Project.current () in
  if Kernel.Copy.get () then begin
    let selection =
      State_selection.list_union
        (List.map State_selection.with_dependencies
           [ Cil.Builtin_functions.self;
             Logic_env.Logic_info.self;
             Logic_env.Logic_type_info.self;
             Logic_env.Logic_ctor_info.self;
             Ast.self ])
    in
    Project.clear ~selection ();
    let prj2 = Project.create_by_copy ~last:false "debug_copy_prj" in
    Project.set_current prj2;
  end;
  let files = Kernel.Files.get () in
  if files = [] && not !Config.is_gui then Kernel.warning "no input file.";
  let files =
    List.map (fun s -> from_filename s) files
  in
  try
    init_from_c_files files;
    if Kernel.Check.get () then begin
      Filecheck.check_ast "Copy of original AST"
    end;
    if Kernel.Copy.get () then begin
      Project.on prj1 fill_built_ins ();
      prepare_from_visitor prj1 (fun prj -> new Visitor.frama_c_copy prj);
      Project.set_current prj1;
    end;
  with Ast.Bad_Initialization s ->
    Kernel.fatal "@[<v 0>Cannot initialize from C files@ \
                        Kernel raised Bad_Initialization %s@]" s

let init_from_cmdline =
  Journal.register
    "File.init_from_cmdline"
    (Datatype.func Datatype.unit Datatype.unit)
    init_from_cmdline

let init_from_c_files =
  Journal.register
    "File.init_from_c_files"
    (Datatype.func (Datatype.list ty) Datatype.unit)
    init_from_c_files

let prepare_from_c_files =
  Journal.register
    "File.prepare_from_c_files"
    (Datatype.func Datatype.unit Datatype.unit)
    prepare_from_c_files

let () = Ast.set_default_initialization
  (fun () ->
     if Files.is_computed () then prepare_from_c_files ()
     else init_from_cmdline ())

let pp_file_to fmt_opt =
  let pp_ast = (if not @@ Kernel.PrintAnnot.get () then Printer.without_annot else Extlib.id) Printer.pp_file in
  let ast = Ast.get () in
  (match fmt_opt with
    | None -> Kernel.CodeOutput.output (fun fmt -> pp_ast fmt ast)
    | Some fmt -> pp_ast fmt ast)

let unjournalized_pretty prj (fmt_opt:Format.formatter option) () =
  Project.on prj pp_file_to fmt_opt

let journalized_pretty_ast =
  Journal.register "File.pretty_ast"
    (Datatype.func3
       ~label1:("prj",Some Project.current) Project.ty
       ~label2:("fmt",Some (fun () -> None))
       (let module O = Datatype.Option(Datatype.Formatter) in
        O.ty)
       Datatype.unit Datatype.unit)
    unjournalized_pretty

let pretty_ast ?(prj=Project.current ()) ?fmt () =
  journalized_pretty_ast prj fmt ()

let create_rebuilt_project_from_visitor
    ?reorder ?last ?(preprocess=false) prj_name visitor =
  let prj = create_project_from_visitor ?reorder ?last prj_name visitor in
  try
    let f =
      let name = "frama_c_project_" ^ prj_name ^ "_" in
      let ext = if preprocess then ".c" else ".i" in
      let debug = Kernel.Debug.get () > 0 in
      let tmp_fname = Extlib.temp_file_cleanup_at_exit ~debug name ext in
      tmp_fname
    in
    let cout = open_out (f :> string) in
    let fmt = Format.formatter_of_out_channel cout in
    unjournalized_pretty prj (Some fmt) ();
    let redo () =
(*      Kernel.feedback "redoing initialization on file %s" f;*)
      Files.reset ();
      init_from_c_files [ if preprocess then from_filename f else NoCPP f ]
    in
    Project.on prj redo ();
    prj
  with Extlib.Temp_file_error s | Sys_error s ->
    Kernel.abort "cannot create temporary file: %s" s

(*
Local Variables:
compile-command: "make -C ../../.."
End:
*)
