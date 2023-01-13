#!/bin/sh
for f in $(find src/linear | grep .dfy$ | grep -v ElimDupMap | grep -v ElimDupMix | grep -v FibPrefix | grep -v CircularDoublyLinkedList); do
    time dafny verify $f || exit 1
done
