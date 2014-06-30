#!/bin/bash
set -e

cabal build

term_types="S GR"
tc="./dist/build/tc/tc"

echo '# Checking that things that should succeed succeed'
for tt in $term_types; do
    echo "## With term type $tt"
    for f in examples/*.agda; do
        echo $f
        $tc check -q $f
    done
    for f in tests/succed/*.agda; do
        echo $f
        $ts check -q $f
    done
done

echo '# Checking that things that should fail fail'
for tt in $term_types; do
    echo "## With term type $tt"
    for f in tests/fail/*.agda; do
        echo $f
        $ts check -q $f
    done
done

echo '# Testing consistency between implementations'
for f in examples/*.agda; do
    echo $f
    $tc test $f
done
for f in tests/succed/*.agda; do
    echo $f
    $ts test $f
done
