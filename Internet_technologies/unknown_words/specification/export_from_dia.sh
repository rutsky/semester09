#!/bin/bash

for f in *.dia; do
  diagram=`echo $f | sed 's/\.dia$//'`
  dia -e $diagram.eps $f
done

# vim: set ts=2 sw=2 et:
