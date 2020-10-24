#!/bin/sh
for f in $(find . | grep .dfy$); do
    time dafny $f
done
