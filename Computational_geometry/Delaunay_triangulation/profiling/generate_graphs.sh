#!/bin/bash

# TODO

for test in uniform ellipse circle parabola ellipse95_uniform5; do
  echo "Processing '"$test"'"

  time_data_file="data_"$test"_time.dat"

  > $time_data_file
  
  for n in `seq 1000 1000 100000`; do
    test_file_prefix=../tests/big_$test"_"`printf '%06d' $n`
    
    time_file=$test_file_prefix.time
    echo -n $n" " >> $time_data_file
    cat $time_file >> $time_data_file
  done

  result_time_file="result_"$test"_time".pdf
  title=`echo $test | sed s/\_/-/g`
  asy -f pdf -nointeractiveView -o $result_time_file -c \
    'from "draw_graph.asy" access draw_graph;
    draw_graph("'$time_data_file'", "Seconds", "'$title'");'
done

# vim: et ts=2 sw=2:
