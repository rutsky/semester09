#!/bin/bash

#set -x

APP=../../build/delaunay/delaunay
VERIFICATOR=../../build/verificator/verificator
N=100
TEST_IN=test.in
TEST_OUT=test.out

i=1
while true; do
  echo $i
  let i=$i+1
  python uniform.py $N > $TEST_IN;
  cat $TEST_IN | $APP > $TEST_OUT || exit 1

  $VERIFICATOR $TEST_IN $TEST_OUT || exit 1
done
