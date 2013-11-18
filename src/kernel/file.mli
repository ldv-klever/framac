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

(** Frama-c preprocessing and Cil AST initialization.
    @plugin development guide *)

type file =
  | NeedCPP of string * string
      (** The first string is the filename of the [.c] to preprocess.
          The second one is the preprocessor command ([filename.c -o
          tempfilname.i] will be appended at the end).*)
  | NoCPP of string
      (** Already pre-processed file [.i] *)
  | External of string * string
      (** file that can be translated into a Cil AST through an external
          function, together with the recognized suffix. *)

include Datatype.S with type t = file

val new_file_type:
  string -> (string -> Cil_types.file * Cabs.file) -> unit
  (** [new_file_type suffix func funcname] registers a new type of files (with
      corresponding suffix) as recognized by Frama-C through [func]. *)

val new_machdep: string -> (module Cil.Machdeps) -> unit
(** [new_machdep name module] registers a new machdep name as recognized by
    Frama-C through The usual uses is
    [Cmdline.run_after_loading_stage
    (fun () -> File.new_machdep
    "my_machdep"
    (module My_machdep_implem: Cil.Machdeps))]
    @since Nitrogen-20111001
    @modify Fluorine-20130401 Receives the machdep (as a module) as argument
    @raise Invalid_argument if the given name already exists *)

val get_suffixes: unit -> string list
  (** @return the list of accepted suffixes of input source files
      @since Boron-20100401 *)

val get_name: t -> string
  (** File name. *)

val get_preprocessor_command: unit -> string
  (** Return the preprocessor command to use. *)

val pre_register: t -> unit
  (** Register some file as source file before command-line files *)

val get_all: unit -> t list
  (** Return the list of toplevel files. *)

val from_filename: ?cpp:string -> string -> t
  (** Build a file from its name. The optional argument is the preprocessor
      command. Default is [!get_preprocessor_command ()]. *)

(* ************************************************************************* *)
(** {2 Initializers} *)
(* ************************************************************************* *)

class check_file: string -> Visitor.frama_c_visitor
  (** visitor that performs various consistency checks over the AST.
      The string argument will be used in the error message in case of
      inconsistency, in order to trace the issue.
  *)

val prepare_from_c_files: unit -> unit
  (** Initialize the AST of the current project according to the current
      filename list.
      @raise File_types.Bad_Initialization if called more than once. *)

val init_from_c_files: t list -> unit
  (** Initialize the cil file representation of the current project.
      Should be called at most once per project.
      @raise File_types.Bad_Initialization if called more than once.
      @plugin development guide *)

val init_project_from_cil_file: Project.t -> Cil_types.file -> unit
  (** Initialize the cil file representation with the given file for the
      given project from the current one.
      Should be called at most once per project.
      @raise File_types.Bad_Initialization if called more than once.
      @plugin development guide *)

val init_project_from_visitor:
  ?reorder:bool -> Project.t -> Visitor.frama_c_visitor -> unit
  (** [init_project_from_visitor prj vis] initialize the cil file
      representation of [prj]. [prj] must be essentially empty: it can have
      some options set, but not an existing cil file; [proj] is filled using
      [vis], which must be a copy visitor that puts its results in [prj].
      if [reorder] is [true] (default is [false]) the new AST in [prj] 
      will be reordered.
      @since Oxygen-20120901
      @modify Fluorine-20130401 added reorder optional argument
      @plugin development guide
   *)

val create_project_from_visitor:
  ?reorder:bool -> string -> (Project.t -> Visitor.frama_c_visitor) -> Project.t
  (** Return a new project with a new cil file representation by visiting the
      file of the current project. If [reorder] is [true], the globals in the
      AST of the new project are reordered (default is [false]).
      The visitor is responsible to avoid sharing between old file and new
      file (i.e. it should use {!Cil.copy_visit} at some point).
      @raise File_types.Bad_Initialization if called more than once.
      @since Beryllium-20090601-beta1
      @modify Fluorine-20130401 added reorder optional argument
      @plugin development guide *)

val create_rebuilt_project_from_visitor:
  ?reorder:bool -> ?preprocess:bool -> 
  string -> (Project.t -> Visitor.frama_c_visitor) -> Project.t
(** Like {!create_project_from_visitor}, but the new generated cil file is
    generated into a temp .i or .c file according to [preprocess], then re-built
    by Frama-C in the returned project. For instance, use this function if the
    new cil file contains a constructor {!GText} as global.

    Not that the generation of a preprocessed C file may fail in some cases
    (e.g. if it includes headers already included). Thus the generated file is
    NOT preprocessed by default.

    @raise File_types.Bad_Initialization if called more than once.
    @since Nitrogen-20111001 
    @modify Fluorine-20130401 added reorder optional argument
*)

val init_from_cmdline: unit -> unit
(** Initialize the cil file representation with the file given on the
    command line.
    Should be called at most once per project.
    @raise File_types.Bad_Initialization if called more than once.
    @plugin development guide *)

val reorder_ast: unit -> unit
 (** reorder globals so that all uses of an identifier are preceded by its
     declaration. This may introduce new declarations in the AST.
     @since Oxygen-20120901
 *)

(* ************************************************************************* *)
(** {2 Pretty printing} *)
(* ************************************************************************* *)

val pretty_ast : ?prj:Project.t -> ?fmt:Format.formatter -> unit -> unit
  (** Print the project CIL file on the given Formatter.
      The default project is the current one.
      The default formatter is [Kernel.CodeOutput.get_fmt ()].
      @raise File_types.Bad_Initialization if the file is not initialized. *)

(*
Local Variables:
compile-command: "make -C ../.."
End:
*)
