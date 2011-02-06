#!/bin/bash

#set -x

APP=../build/delaunay/release/delaunay
VERIFICATOR=../build/verificator/release/verificator
N=100
TEST_IN=lattice_test.in
TEST_OUT=lattice_test.out

i=1
while true; do
  echo $i
  let i=$i+1
  python lattice_uniform.py $N 0 30 0 5 > $TEST_IN;
  cat $TEST_IN | $APP > $TEST_OUT || exit 1

  $VERIFICATOR $TEST_IN $TEST_OUT || exit 1
done

# vim: set ts=2 sw=2 et:
