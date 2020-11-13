#!/bin/sh
for f in $(find . | grep .dfy$); do
    time dafny $f /compile:0 || exit 1
done
