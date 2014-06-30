#!/bin/bash
set -e

cabal build

term_type="GR"
tc="./dist/build/tc/tc"

echo '# Checking that things that should succeed succeed'
for f in examples/*.agda; do
    echo $f
    $tc test succeed $term_type $f
done
for f in tests/succed/*.agda; do
    echo $f
    $ts test succeed $term_type $f
done

echo '# Checking that things that should fail fail'
for f in tests/fail/*.agda; do
    echo $f
    $ts test fail $term_type $f
done

# echo '# Testing consistency between implementations'
# for f in examples/*.agda; do
#     echo $f
#     $tc test $f
# done
# for f in tests/succed/*.agda; do
#     echo $f
#     $ts test $f
# done
