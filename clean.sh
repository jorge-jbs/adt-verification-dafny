#!/bin/sh
for f in $(find . -regex ".*\.dll\(\.mdb\)?$"); do
    rm $f
done
