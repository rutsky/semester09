#!/bin/sh

if [ "$#" -ne "1" ]; then
  echo "Usage:"
  echo "  "$0" number_of_points"
  exit 0
fi

n=$1

# 95% of points on ellipse 5% uniformly distributed.
v2=$((n / 20))
v1=$((n - $v2))
TEMP=`mktemp`
python lattice_uniform.py $v2 -550 550 -250 250 > $TEMP
python lattice_near_ellipse.py $v1 >> $TEMP

shuf $TEMP
rm -rf $TEMP

# vim: set ts=2 sw=2 et:
