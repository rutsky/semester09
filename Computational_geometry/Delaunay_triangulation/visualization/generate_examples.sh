#!/bin/bash

#set -x

drawcmd=./draw.sh
examples=examples/
tests=../tests/t
big_tests=../tests/big

for big_test in big_uniform_001000 big_ellipse_001000 big_circle_001000 \
      big_parabola_001000 big_ellipse95_uniform5_001000; do
  $drawcmd $big_tests/$big_test.in $big_tests/$big_test.out false
  mv $big_test.in.pdf $examples
done

for test in circle_022 ellipse_020_1 circle_rbox_020_1.in \
      lattice_ellipse_and_uniform_00100_1 lattice_near_ellipse_020_1 \
      lattice_parabola_020_1 lattice_uniform_3x20_020_1 \
      lattice_uniform_8x8_020_1 parabola_020_1 uniform_00020_1; do
  $drawcmd $tests/$test.in $tests/$test.out
  mv $test.in.pdf $examples
done

# vim: et ts=2 sw=2:
