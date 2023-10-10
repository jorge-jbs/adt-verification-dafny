#!/bin/sh

./dafnyDep.sh $1 > $1.d

#PATH=$PATH:~/Descargas/dafny-3.13.1-x64-ubuntu-20.04/dafny/ time dafny build $1
#PATH=$PATH:~/Descargas/dafny-4.2.0-x64-ubuntu-20.04/dafny/ time dafny build $1
PATH=$PATH:~/Descargas/dafny-4.3.0-x64-ubuntu-20.04/dafny/ time dafny verify $1
touch $(dirname $1)/$(basename $1 ".dfy").dll
