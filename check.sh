#!/bin/sh
for f in $(find src/linear | grep .dfy$ | grep -v FibPrefix); do
    time dafny $f /compile:0 || exit 1
done
