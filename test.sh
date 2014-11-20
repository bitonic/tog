#!/bin/bash
set -e

tc="./dist/build/tog/tog"

make $tc

for f in examples/working/*.agda; do
    echo $f
    /usr/bin/time -f "%U" $tc -q --fastGetAbsName $@ $f
done
