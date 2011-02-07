#!/bin/sh

TESTS_DIR=../tests

if false; then
  # Small uniform tests.
  for n in `seq 1 99`; do
    for i in `seq 1 3`; do
      python uniform.py $n > $TESTS_DIR/uniform_`printf '%05d' $n`_$i.in
    done
  done
fi

if false; then
  # Big uniform tests.
  for n in `seq 100 100 5000`; do
    for i in `seq 1 5`; do
      python uniform.py $n > $TESTS_DIR/uniform_`printf '%05d' $n`_$i.in
    done
  done
fi

if false; then
  # Circle tests.
  for n in `seq 4 11` `seq 12 2 22`; do
    python schinzel_circles.py $n > $TESTS_DIR/circle_`printf '%03d' $n`.in
  done
fi

if false; then
  # Lattice points on small grid tests.
  for n in `seq 3 99`; do
    for i in `seq 1 5`; do
      python lattice_uniform.py $n 0 7 0 7 > \
          $TESTS_DIR/lattice_uniform_8x8_`printf '%03d' $n`_$i.in
    done
  done
  for n in `seq 3 99`; do
    for i in `seq 1 5`; do
      python lattice_uniform.py $n 0 19 0 2 > \
          $TESTS_DIR/lattice_uniform_3x20_`printf '%03d' $n`_$i.in
    done
  done
fi

if true; then
  for n in `seq 5 5 100`; do
    for i in `seq 1 2`; do
      SUFFIX=`printf '%03d' $n`_$i.in

      # Points on circle with rbox.
      #rbox $n s D2 | tail --lines=+3 - > \
      #   $TESTS_DIR/circle_rbox_$SUFFIX

      # Points on ellipse.
      #python ellipse.py $n > $TESTS_DIR/ellipse_$SUFFIX

      # Lattice points close to ellipse.
      #python lattice_near_ellipse.py $n > \
      #    $TESTS_DIR/lattice_near_ellipse_$SUFFIX

      # Points on parabola.
      python parabola.py $n > \
          $TESTS_DIR/parabola_$SUFFIX

      # Lattice points on parabola.
      python lattice_parabola.py $n > \
          $TESTS_DIR/lattice_parabola_$SUFFIX
    done
  done
fi

# vim: set ts=2 sw=2 et:
