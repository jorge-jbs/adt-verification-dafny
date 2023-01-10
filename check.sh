#!/bin/sh
for f in $(find src/linear | grep .dfy$ | grep -v Merge | grep -v Quicksort | grep -v FilterEven | grep -v FibPrefix | grep -v DupElementsMap); do
    time dafny $f /compile:0 || exit 1
done
