#!/bin/sh

./dafnyDep.sh $1 > $1.d

PATH=$PATH:~/Descargas/dafny-4.10.0-x64-ubuntu-20.04/dafny/ time dafny verify $1 --allow-warnings --verification-time-limit 1000 && touch $(dirname $1)/$(basename $1 ".dfy").dll
