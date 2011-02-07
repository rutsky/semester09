#!/bin/sh

for f in ../tests/*.out; do
  test=`echo $f | sed s/\.out$//`
  echo 'Processing' $test
  asy -f pdf -nointeractiveView -o `basename $test`.pdf -c \
    'from "triangulation.asy" access draw_triangulation;
     draw_triangulation("'$test.in'", "'$test.out'");'
done

# vim: set ts=2 sw=2 et:
