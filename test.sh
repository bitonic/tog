#!/bin/bash
set -e

term_type="GR"
tc="./dist/build/tog/tog"

make $tc

for f in examples/working/*.agda; do
    if [[ "$f" != "examples/working/Prelude.agda" ]]; then
        echo $f
        $tc -q -t $term_type $f
    fi
done
