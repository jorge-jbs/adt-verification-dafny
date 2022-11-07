#!/bin/sh
for f in $(find src/linear examples/iterators | grep .dfy$ | grep -v DupElementsMap | grep -v Merge); do
    time dafny $f /compile:0 || exit 1
done
