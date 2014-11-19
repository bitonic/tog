#!/bin/bash
set -e

tc="./dist/build/tog/tog"

make $tc

for f in examples/working/*.agda; do
    if [[ "$f" != "examples/working/Prelude.agda" ]]; then
        echo $f
        /usr/bin/time -f "%U" $tc -q --fastGetAbsName $@ $f
    fi
done
