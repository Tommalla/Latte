#!/bin/bash

PREF="doc/lattests/good"

cd ..

for i in $(seq -f "%03g" 1 22)
do
    echo "Test: $i";
    ./latc_x86 $PREF/core$i.lat
    $PREF/core$i  > tmp.output
    diff $PREF/core$i.output tmp.output
    if [ $? != 0 ] ; then
       break
    fi
done
