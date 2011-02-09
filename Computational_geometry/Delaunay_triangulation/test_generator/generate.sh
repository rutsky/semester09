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
  for n in `seq 100 100 5000`; do
    for i in `seq 1 5`; do
      SUFFIX=`printf '%05d' $n`_$i.in

      # Big uniform tests.
      #python uniform.py $n > $TESTS_DIR/uniform_$SUFFIX

      # 95% of points on ellipse 5% uniformly distributed.
      # TODO: use ellipse95_uniform5.sh
      v2=$((n / 20))
      v1=$((n - $v2))
      # TODO: Use TEMP=`mktemp`
      TEMP=.tmp
      python lattice_uniform.py $v2 -550 550 -250 250 > $TEMP
      python lattice_near_ellipse.py $v1 >> $TEMP

      shuf $TEMP > $TESTS_DIR/lattice_ellipse_and_uniform_$SUFFIX
      rm -rf $TEMP
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
      python lattice_uniform.py $n 0 19 0 2 > \
          $TESTS_DIR/lattice_uniform_3x20_`printf '%03d' $n`_$i.in
    done
  done
fi

if false; then
  for n in `seq 5 5 100`; do
    for i in `seq 1 2`; do
      SUFFIX=`printf '%03d' $n`_$i.in

      # Points on circle with rbox.
      rbox $n s D2 | tail --lines=+3 - > \
         $TESTS_DIR/circle_rbox_$SUFFIX

      # Points on ellipse.
      python ellipse.py $n > $TESTS_DIR/ellipse_$SUFFIX

      # Lattice points close to ellipse.
      python lattice_near_ellipse.py $n > \
          $TESTS_DIR/lattice_near_ellipse_$SUFFIX

      # Points on parabola.
      python parabola.py $n > \
          $TESTS_DIR/parabola_$SUFFIX

      # Lattice points on parabola.
      python lattice_parabola.py $n > \
          $TESTS_DIR/lattice_parabola_$SUFFIX
    done
  done
fi

if true; then
  for n in `seq 1000 1000 100000`; do
    SUFFIX=`printf '%06d' $n`.in

    # Uniform.
    # python lattice_uniform.py $n 0 20000 0 20000 > \
    #     $TESTS_DIR/big_uniform_$SUFFIX

    # Ellipse.
    # python lattice_near_ellipse.py $n > \
    #     $TESTS_DIR/big_ellipse_$SUFFIX

    # Circle.
    # python lattice_near_circle.py $n > \
    #     $TESTS_DIR/big_circle_$SUFFIX

    # Parabola.
    # python lattice_parabola.py $n > \
    #     $TESTS_DIR/big_parabola_$SUFFIX

    # 95% ellipse 5% uniform.
    ./ellipse95_uniform5.sh $n > \
        $TESTS_DIR/big_ellipse95_uniform5_$SUFFIX
  done
fi

# vim: set ts=2 sw=2 et:
