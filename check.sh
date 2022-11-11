#!/bin/sh
for f in $(find src/linear examples/iterators examples/*.dfy | grep .dfy$ | grep -v DupElementsMap | grep -v Merge | grep -v Quicksort | grep -v FilterEven); do
    time dafny $f /compile:0 || exit 1
done
