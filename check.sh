#!/bin/sh
for f in $(find src/linear examples/iterators | grep .dfy$ | grep -v ElimDupMap | grep -v FibPrefix); do
    time dafny verify $f || exit 1
done
