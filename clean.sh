#!/bin/sh
for f in $(find . -regex ".*\.\(dll\|exe\)\(\.mdb\)?$"); do
    rm $f
done
