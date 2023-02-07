#!/bin/sh

./dafnyDep.sh $1 > $1.d

PATH=$PATH:~/Descargas/dafny-3.10.0-x64-ubuntu-16.04/dafny/ dafny build $1
