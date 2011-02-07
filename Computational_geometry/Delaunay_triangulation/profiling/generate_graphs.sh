#!/bin/bash

for test in uniform ellipse circle parabola ellipse95_uniform5; do
  echo "Processing '"$test"'"

  time_data_file="data_"$test"_time.dat"
  flips_data_file="data_"$test"_flips.dat"

  > $time_data_file
  > $flips_data_file
  
  for n in `seq 1000 1000 100000`; do
    test_file_prefix=../tests/big_$test"_"`printf '%06d' $n`
    
    # Running time.
    time_file=$test_file_prefix".time"
    echo -n $n" " >> $time_data_file
    cat $time_file >> $time_data_file

    profiling_file=$test_file_prefix".info"

    declare -a info=( )
    while read line ; do
      info[${#info[@]}]=$line
    done < $profiling_file

    # Don't work:
    #info[0]='aa'
    #i=0
    #cat $profiling_file | while read line; do
    #  echo info[$i] = $line
    #  info[$i]=$line;
    #  echo = ${info[1]}
    #  echo = ${info[1]}
    #  ((i++))
    #done

    # Flips.
    echo -n $n" " >> $flips_data_file
    echo ${info[1]} >> $flips_data_file
  done

  title=`echo $test | sed s/\_/-/g`

  result_time_file="result_"$test"_time".pdf
  asy -f pdf -nointeractiveView -o $result_time_file -c \
    'from "draw_graph.asy" access draw_graph;
    draw_graph("'$time_data_file'", "Seconds", "'$title'");'

  result_flips_file="result_"$test"_flips".pdf
  asy -f pdf -nointeractiveView -o $result_flips_file -c \
    'from "draw_graph.asy" access draw_graph;
    draw_graph("'$flips_data_file'", "Flips", "'$title'");'
done

# vim: et ts=2 sw=2:
