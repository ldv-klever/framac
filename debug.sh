#/bin/bash

DIR=$(dirname $(readlink -f $0))

WHERE=$(ocamlopt -where)

SCRIPT="
load_printer ${WHERE}/nums.cma
load_printer ${WHERE/ocaml/zarith}/zarith.cma
load_printer src/lib/integer.cmo
"
# load_printer cil/src/cil_datatype.cmo
# load_printer src/printer/printer.cmo
rlwrap -P "$SCRIPT" ocamldebug -I "$DIR/cil/src" -I "$DIR/cil/src/ext" -I "$DIR/cil/src/frontc" -I "$DIR/cil/src/logic" -I "$DIR/src/" -I "$DIR/src/logic" -I "$DIR/src/printer" -I "$DIR/src/lib" -I "$DIR/src/kernel" -I "$DIR/src/type" -I "$DIR/src/project" $@
