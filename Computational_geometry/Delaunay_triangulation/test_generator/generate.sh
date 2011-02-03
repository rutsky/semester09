#!/bin/sh

for n in `seq 1 99`; do
  for i in `seq 1 3`; do
    python uniform.py $n > ../tests/uniform_`printf '%05d' $n`_$i.in
  done
done

for n in `seq 100 100 5000`; do
  for i in `seq 1 5`; do
    python uniform.py $n > ../tests/uniform_`printf '%05d' $n`_$i.in
  done
done
