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

(* Dependencies to kernel options *)
let kernel_parameters_correctness = [
  Kernel.MainFunction.parameter;
  Kernel.LibEntry.parameter;
  Kernel.AbsoluteValidRange.parameter;
  Kernel.SafeArrays.parameter;
  Kernel.UnspecifiedAccess.parameter;
]

let parameters_correctness = ref []
let parameters_tuning = ref []
let add_dep p =
  State_dependency_graph.add_codependencies
    ~onto:Db.Value.self 
    [State.get p.Parameter.name]
let add_correctness_dep p =
  add_dep p;
  parameters_correctness := p :: !parameters_correctness
let add_precision_dep p =
  add_dep p;
  parameters_tuning := p :: !parameters_tuning

let () = List.iter add_correctness_dep kernel_parameters_correctness

include Plugin.Register
    (struct
       let name = "value analysis"
       let shortname = "value"
       let help =
 "automatically computes variation domains for the variables of the program"
    end)

module ForceValues =
  WithOutput
    (struct
       let option_name = "-val"
       let help = "compute values"
       let output_by_default = true
     end)

let precision_tuning = add_group "Precision vs. time"
let initial_context = add_group "Initial Context"
let performance = add_group "Results memoization vs. time"
let interpreter = add_group "Deterministic programs"
let alarms = add_group "Propagation and alarms "

(* -------------------------------------------------------------------------- *)
(* --- Aux                                                                --- *)
(* -------------------------------------------------------------------------- *)

let check_c_function_exists ~f ~option ~arg =
  try ignore (Globals.Functions.find_by_name f)
  with Not_found ->
    warning "option '%s %s': function '%s' does not exist" option arg f

(* -------------------------------------------------------------------------- *)
(* --- Performance options                                                --- *)
(* -------------------------------------------------------------------------- *)

let () = Plugin.argument_is_function_name ()
let () = Plugin.set_group performance
module NoResultsFunctions =
  StringSet
    (struct
       let option_name = "-no-results-function"
       let arg_name = "f"
       let help = "do not record the values obtained for the statements of \
function f"
     end)
let () = add_dep NoResultsFunctions.parameter

let () = Plugin.set_group performance
let () = Plugin.set_negative_option_name "-val-store-results"
module NoResultsAll =
  False
    (struct
       let option_name = "-no-results"
       let help = "do not record values for any of the statements of the \
program"
     end)
let () = add_dep NoResultsAll.parameter

let () = Plugin.set_group performance
module ResultsAfter =
  Bool
    (struct
       let option_name = "-val-after-results"
       let help = "record precisely the values obtained after the evaluation of each statement"
       let default = !Config.is_gui 
     end)
let () = add_dep ResultsAfter.parameter

let () = Plugin.set_group performance
module ResultsCallstack =
  Bool
    (struct
       let option_name = "-val-callstack-results"
       let help = "record precisely the values obtained for each callstack leading to each statement"
       let default = false
     end)
let () = add_dep ResultsCallstack.parameter

let () = Plugin.set_group performance
module MemoryFootprint =
  Int
    (struct
       let option_name = "-memory-footprint"
       let default = 2
       let arg_name = ""
       let help = "tell the analyser to compromise towards speed or towards low memory use. 1 : small memory; 2 : medium (suitable for recent notebooks); 3 : big (suitable for workstations with 3Gb physical memory or more). Defaults to 2"
     end)
let () =
  MemoryFootprint.add_set_hook
    (fun _ x ->
       Binary_cache.MemoryFootprint.set x;
       Buckx.MemoryFootprint.set x);
  State_dependency_graph.add_dependencies
    ~from:MemoryFootprint.self
    [ Binary_cache.MemoryFootprint.self; Buckx.MemoryFootprint.self ]

(* ------------------------------------------------------------------------- *)
(* --- Non-standard alarms                                               --- *)
(* ------------------------------------------------------------------------- *)
    
let () = Plugin.set_group alarms
module AllRoundingModes =
  False
    (struct
       let option_name = "-all-rounding-modes"
       let help = "Take more target FPU and compiler behaviors into account"
     end)
let () = add_correctness_dep AllRoundingModes.parameter

let () = Plugin.set_group alarms
module UndefinedPointerComparisonPropagateAll =
  False
    (struct
       let option_name = "-undefined-pointer-comparison-propagate-all"
       let help = "if the target program appears to contain undefined pointer comparisons, propagate both outcomes {0; 1} in addition to the emission of an alarm"
     end)
let () = add_correctness_dep UndefinedPointerComparisonPropagateAll.parameter

let () = Plugin.set_group alarms
module LeftShiftNegative =
  True
    (struct
       let option_name = "-val-left-shift-negative-alarms"
       let help =
         "Emit alarms when left shifting negative integers"
     end)
let () = add_correctness_dep LeftShiftNegative.parameter

let () = Plugin.set_group alarms
module IgnoreRecursiveCalls =
  False
    (struct
       let option_name = "-val-ignore-recursive-calls"
       let help =
         "Pretend function calls that would be recursive do not happen. Causes unsoundness"
     end)
let () = add_correctness_dep IgnoreRecursiveCalls.parameter

(* ------------------------------------------------------------------------- *)
(* --- Initial context                                                   --- *)
(* ------------------------------------------------------------------------- *)

let () = Plugin.set_group initial_context
module AutomaticContextMaxDepth =
  Int
    (struct
       let option_name = "-context-depth"
       let default = 2
       let arg_name = "n"
       let help = "use <n> as the depth of the default context for value analysis. (defaults to 2)"
     end)
let () = add_correctness_dep AutomaticContextMaxDepth.parameter

let () = Plugin.set_group initial_context
module AutomaticContextMaxWidth =
  Int
    (struct
       let option_name = "-context-width"
       let default = 2
       let arg_name = "n"
       let help = "use <n> as the width of the default context for value analysis. (defaults to 2)"
     end)
let () = AutomaticContextMaxWidth.set_range ~min:1 ~max:max_int
let () = add_correctness_dep AutomaticContextMaxWidth.parameter

let () = Plugin.set_group initial_context
module AllocatedContextValid =
  False
    (struct
       let option_name = "-context-valid-pointers"
       let help = "only allocate valid pointers until context-depth, and then use NULL (defaults to false)"
     end)
let () = add_correctness_dep AllocatedContextValid.parameter

let () = Plugin.set_group initial_context
let () = Plugin.set_negative_option_name "-uninitialized-padding-globals"
module InitializedPaddingGlobals =
  True
    (struct
       let option_name = "-initialized-padding-globals"
       let help = "Padding in global variables is initialized to zero"
     end)
let () = add_correctness_dep InitializedPaddingGlobals.parameter

(* ------------------------------------------------------------------------- *)
(* --- Tuning                                                            --- *)
(* ------------------------------------------------------------------------- *)

let () = Plugin.set_group precision_tuning
module WideningLevel =
  Int
    (struct
       let default = 3
       let option_name = "-wlevel"
       let arg_name = "n"
       let help =
         "do <n> loop iterations before widening (defaults to 3)"
     end)
let () = add_precision_dep WideningLevel.parameter

let () = Plugin.set_group precision_tuning
module ILevel =
  Int
    (struct
       let option_name = "-val-ilevel"
       let default = 8
       let arg_name = "n"
       let help =
         "Sets of integers are represented as sets up to <n> elements. \
            Above, intervals with congruence information are used \
            (defaults to 8; experimental)"
     end)
let () = add_precision_dep ILevel.parameter
let () = ILevel.add_update_hook (fun _ i -> Ival.set_small_cardinal i)
let () = ILevel.set_range 4 64

let () = Plugin.set_group precision_tuning
module SemanticUnrollingLevel =
  Zero
    (struct
       let option_name = "-slevel"
       let arg_name = "n"
       let help =
         "superpose up to <n> states when unrolling control flow. The larger n, the more precise and expensive the analysis (defaults to 0)"
     end)
let () = add_precision_dep SemanticUnrollingLevel.parameter

let split_option =
  let rx = Str.regexp_string ":" in
  fun s ->
    try
      match Str.split rx s with
        | [ f ; n ] -> (f, n)
        | _ -> failwith ""
    with _ -> failwith "split_option"

let () = Plugin.set_group precision_tuning
module SlevelFunction =
  StringHashtbl
    (struct
       let option_name = "-slevel-function"
       let arg_name = "f:n"
       let help = "override slevel with <n> when analyzing <f>"
     end)
    (struct
      include Datatype.Int

      let parse s =
        try
          let f, n =  split_option s in
          check_c_function_exists ~f:f ~option:"-slevel-function" ~arg:s;
          let n = int_of_string n in
          f, n
        with
       | Failure _ -> abort "Could not parse option \"-slevel-function %s\"" s
      let redefine_binding _k ~old:_ new_v = new_v
      let no_binding _ = SemanticUnrollingLevel.get ()
    end)
let () = add_precision_dep SlevelFunction.parameter

let split_option_multiple =
  let rx = Str.regexp_string ":" in
  fun s ->
    try
      match Str.split rx s with
        | f :: q -> f, q
        | _ -> failwith ""
    with _ -> failwith "split_option"

let () = Plugin.set_group precision_tuning
module SplitReturnFunction =
  StringHashtbl
    (struct
       let option_name = "-val-split-return-function"
       let arg_name = "f:n"
       let help = "split return states of function <f> according to \
                     \\result == n and \\result != n"
     end)
    (struct
      include Datatype.List(Datatype.Int)
      let parse s =
        try
          let f, l =  split_option_multiple s in
          check_c_function_exists
            ~f:f ~option:"-val-split-return-function" ~arg:s;
          let l = List.map int_of_string l in
          f, l
        with Failure _ -> 
	  abort "Could not parse option \"-val-split-return %s\"" s
      let redefine_binding _k ~old:_ new_v = new_v
      let no_binding _ = raise Not_found
    end)
let () = add_precision_dep SplitReturnFunction.parameter

let () = Plugin.set_group precision_tuning
module SplitReturnAuto =
  False
    (struct
       let option_name = "-val-split-return-auto"
       let help = "Automatically split states at the end of functions, \
                    according to the function return code"
     end)
let () = add_precision_dep SplitReturnAuto.parameter

let () = Plugin.set_group precision_tuning
module BuiltinsOverrides =
  StringHashtbl
    (struct
       let option_name = "-val-builtin"
       let arg_name = "f:ffc"
       let help = "when analyzing function <f>, try to use Frama-C builtin <ffc> instead. Fall back to <f> if <ffc> cannot handle its arguments (experimental)."
     end)
    (struct
        include Datatype.String
        let parse s =
          try
            let (fc, focaml) as r = split_option s in
            if not (!Db.Value.mem_builtin focaml) then
              abort "option '-val-builtin %s': undeclared builtin '%s'"
                s focaml;
            check_c_function_exists ~f:fc ~option:"-val-builtin" ~arg:s;
            r
          with Failure _ -> abort "Could not parse option \"-val-builtin %s\"" s
        let redefine_binding _k ~old:_ new_v = new_v
        let no_binding _ = raise Not_found
     end)
let () = add_precision_dep BuiltinsOverrides.parameter

let () = Plugin.set_group precision_tuning
module Subdivide_float_in_expr =
  Zero
    (struct
      let option_name = "-subdivide-float-var"
      let arg_name = "n"
      let help =
        "use <n> as number of subdivisions allowed for float variables in expressions (experimental, defaults to 0)"
    end)
let () = add_precision_dep Subdivide_float_in_expr.parameter

let () = Plugin.argument_is_function_name ()
let () = Plugin.set_group precision_tuning
module UsePrototype =
  StringSet
    (struct
      let option_name = "-val-use-spec"
      let arg_name = "f1,..,fn"
      let help = "use the ACSL specification of the functions instead of their definitions"
    end)
let () = add_precision_dep UsePrototype.parameter

let () = Plugin.set_group precision_tuning
module RmAssert =
  False
    (struct
      let option_name = "-remove-redundant-alarms"
      let help = "after the analysis, try to remove redundant alarms, so that the user needs inspect fewer of them"
    end)
let () = add_precision_dep RmAssert.parameter

let () = Plugin.set_group precision_tuning
module MemExecAll =
  False
    (struct
      let option_name = "-memexec-all"
      let help = "(experimental) speed up analysis by not recomputing functions already analyzed in the same context. Incompatible with some plugins and callbacks"
    end)
let () =
  MemExecAll.add_set_hook
    (fun _bold bnew ->
      if bnew then
        try
          Dynamic.Parameter.Bool.set "-inout-callwise" true
        with Dynamic.Unbound_value _ | Dynamic.Incompatible_type _ ->
          abort "Cannot set option -memexec-all. Is plugin Inout registered?"
    )

let () = Plugin.set_group precision_tuning
module ArrayPrecisionLevel =
  Int
    (struct
       let default = 200
       let option_name = "-plevel"
       let arg_name = "n"
       let help = "use <n> as the precision level for arrays accesses. \
Array accesses are precise as long as the interval for the index contains \
less than n values. (defaults to 200)"
     end)
let () = add_precision_dep ArrayPrecisionLevel.parameter
let () = ArrayPrecisionLevel.add_update_hook
  (fun _ v -> Lattice_Interval_Set.plevel := v)

let () = Plugin.set_group precision_tuning
module SeparateStmtStart =
  StringSet
    (struct
       let option_name = "-separate-stmts"
       let arg_name = "n1,..,nk"
       let help = ""
     end)
let () = add_correctness_dep SeparateStmtStart.parameter

let () = Plugin.set_group precision_tuning
module SeparateStmtWord =
  Int
    (struct
       let option_name = "-separate-n"
       let default = 0
       let arg_name = "n"
       let help = ""
     end)
let () = SeparateStmtWord.set_range ~min:0 ~max:1073741823
let () = add_correctness_dep SeparateStmtWord.parameter

let () = Plugin.set_group precision_tuning
module SeparateStmtOf =
  Int
    (struct
       let option_name = "-separate-of"
       let default = 0
       let arg_name = "n"
       let help = ""
     end)
let () = SeparateStmtOf.set_range ~min:0 ~max:1073741823
let () = add_correctness_dep SeparateStmtOf.parameter

(* ------------------------------------------------------------------------- *)
(* --- Messages                                                          --- *)
(* ------------------------------------------------------------------------- *)

let () = Plugin.set_group messages
module ValShowProgress =
  True
    (struct
       let option_name = "-val-show-progress"
       let help = "Show progression messages during analysis"
     end)

let () = Plugin.set_group messages
module TimingStep =
  Int
    (struct
       let option_name = "-val-show-time"
       let default = 0
       let arg_name = "n"
       let help = "Prints the time spent analyzing function calls, when it exceeds <n> seconds"
     end)
module FloatTimingStep = 
  State_builder.Float_ref 
    (struct
       let default () = Pervasives.infinity
       let name = "Value_parameters.FloatTimingStep"
       let dependencies = [TimingStep.self]
     end)
let () = TimingStep.add_set_hook (fun _ x -> FloatTimingStep.set (float x))

let () = Plugin.set_group messages
module ShowSlevel =
  Int
    (struct
       let option_name = "-val-show-slevel"
       let default = 100
       let arg_name = "n"
       let help = "Period for showing consumption of the alloted slevel during analysis"
     end)

let () = Plugin.set_group messages
module PrintCallstacks =
  False
    (struct
       let option_name = "-val-print-callstacks"
       let help = "When printing a message, also show the current call stack"
     end)

(* ------------------------------------------------------------------------- *)
(* --- Interpreter mode                                                  --- *)
(* ------------------------------------------------------------------------- *)

let () = Plugin.set_group interpreter
module InterpreterMode =
  False
    (struct
       let option_name = "-val-interpreter-mode"
       let help = "Stop at first call to a library function, if main() has \
arguments, on undecided branches"
     end)

let () = Plugin.argument_is_function_name ()
let () = Plugin.set_group interpreter
module ObviouslyTerminatesFunctions =
  StringSet
    (struct
       let option_name = "-obviously-terminates-function"
       let arg_name = "f"
       let help = ""
     end)
let () = add_dep ObviouslyTerminatesFunctions.parameter

let () = Plugin.set_group interpreter
module ObviouslyTerminatesAll =
  False
    (struct
       let option_name = "-obviously-terminates"
       let help = "undocumented. Among effects of this options are the same \
effects as -no-results"
     end)
let () = add_dep ObviouslyTerminatesAll.parameter

let () = Plugin.set_group interpreter
module StopAtNthAlarm =
  Int(struct
         let option_name = "-val-stop-at-nth-alarm"
	 let default = max_int
	 let arg_name = "n"
         let help = ""
       end)

(* -------------------------------------------------------------------------- *)
(* --- Ugliness required for correctness                                  --- *)
(* -------------------------------------------------------------------------- *)

let () = Plugin.is_invisible ()
module InitialStateChanged =
  Int (struct
         let option_name = "-new-initial-state"
         let default = 0
         let arg_name = "n"
         let help = ""
       end)
(* Changing the user-supplied initial state (or the arguments of main) through
   the API of Db.Value does reset the state of Value, but *not* the property
   statuses that Value has positioned. Currently, statuses can only depend
   on a command-line parameter. We use the dummy one above to force a reset
   when needed. *)
let () =
  add_correctness_dep InitialStateChanged.parameter;
  Db.Value.initial_state_changed :=
    (fun () -> InitialStateChanged.set (InitialStateChanged.get () + 1))
  
let parameters_correctness = !parameters_correctness
let parameters_tuning = !parameters_tuning

(*
Local Variables:
compile-command: "make -C ../.."
End:
*)
