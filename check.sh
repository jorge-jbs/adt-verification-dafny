#!/bin/sh
for f in $(find src/linear examples/iterators | grep .dfy$ | grep -v DupElementsMap); do
    time dafny $f /compile:0 || exit 1
done
