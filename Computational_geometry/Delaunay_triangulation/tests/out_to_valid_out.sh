#!/bin/sh

for f in *.out; do
  test=`echo "$f" | sed s/\.out$//`
  
  if [ -e "$test.err" ]; then
    # Error output exists.
    rm -f $test.in $test.out $test.err $test.ver_err $test.info $test.time
  else
    mv $test.out $test.valid_out
  fi
done

# vim: set ts=2 sw=2 et:
