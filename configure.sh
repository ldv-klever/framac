#!/bin/bash
prefix=$(opam config var prefix)
lib=$(opam config var lib)

./configure --prefix $prefix --sbindir=$lib/frama-c/sbin --libexecdir=$lib/frama-c/libexec --sysconfdir=$lib/frama-c/etc --sharedstatedir=$ib/frama-c/com --localstatedir=$lib/frama-c/var --libdir=$lib/frama-c/lib --includedir=$lib/frama-c/include --datarootdir=$lib/frama-c/share

