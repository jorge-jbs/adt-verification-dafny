#!/bin/sh

deps=$(awk -v ROOT=$(dirname $1) '/^include ".*"/ { gsub(/"/, "", $2); print ROOT "/" $2 }' $1)

if [ ! -z "$deps" ]; then
    echo $(dirname $1)/$(basename $1 ".dfy").dll: $(echo $deps | xargs -L 1 readlink -f | tr '\n' ' ')
else
    echo $(dirname $1)/$(basename $1 ".dfy").dll: 
fi
