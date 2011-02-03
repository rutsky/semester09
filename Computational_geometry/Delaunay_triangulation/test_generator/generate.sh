#!/bin/sh

if false; then
  # Small uniform tests.
  for n in `seq 1 99`; do
    for i in `seq 1 3`; do
      python uniform.py $n > ../tests/uniform_`printf '%05d' $n`_$i.in
    done
  done
fi

if false; then
  # Big uniform tests.
  for n in `seq 100 100 5000`; do
    for i in `seq 1 5`; do
      python uniform.py $n > ../tests/uniform_`printf '%05d' $n`_$i.in
    done
  done
fi

if true; then
  # Circle tests.
  for n in `seq 4 11` `seq 12 2 22`; do
    python schinzel_circles.py $n > ../tests/circle_`printf '%03d' $n`.in
  done
fi

# vim: set ts=2 sw=2 et:
