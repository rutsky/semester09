#!/bin/bash

for f in *.dia; do
  diagram=`echo $f | sed 's/\.dia$//'`
  TEMP=`tempfile -s .eps`
  dia -e $TEMP $f
  epstool -i $TEMP $diagram.eps
  rm $TEMP
done

# vim: set ts=2 sw=2 et:
