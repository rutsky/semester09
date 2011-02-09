#!/bin/bash

#set -x

for test in uniform ellipse circle parabola ellipse95_uniform5; do
  echo "Processing '"$test"'"

  time_data_file="data_"$test"_time.dat"
  flips_data_file="data_"$test"_flips.dat"
  triangles_data_file="data_"$test"_triangles.dat"
  localization_triangles_data_file="data_"$test"_localization_triangles.dat"
  delaunay_tests_data_file="data_"$test"_delaunay_tests.dat"

  > $time_data_file
  > $flips_data_file
  > $triangles_data_file
  > $localization_triangles_data_file
  > $delaunay_tests_data_file
  
  for n in `seq 1000 1000 100000`; do
    test_file_prefix=../tests/big/big_$test"_"`printf '%06d' $n`
    
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
    echo -n $n" " >> $triangles_data_file
    echo ${info[0]} >> $triangles_data_file

    echo -n $n" " >> $flips_data_file
    echo ${info[1]} >> $flips_data_file

    echo -n $n" " >> $localization_triangles_data_file
    echo ${info[2]} >> $localization_triangles_data_file

    echo -n $n" " >> $delaunay_tests_data_file
    echo ${info[3]} >> $delaunay_tests_data_file
  done

  title=`echo $test | sed s/\_/-/g`

  result_time_file="result_"$test"_time".pdf
  asy -f pdf -nointeractiveView -o $result_time_file -c \
    'from "draw_graph.asy" access draw_graph;
    draw_graph("'$time_data_file'", "Seconds", "'$title'");'

  result_triangles_file="result_"$test"_triangles".pdf
  asy -f pdf -nointeractiveView -o $result_triangles_file -c \
    'from "draw_graph.asy" access draw_graph;
    draw_graph("'$triangles_data_file'", "Stored triangles", "'$title'");'

  result_flips_file="result_"$test"_flips".pdf
  asy -f pdf -nointeractiveView -o $result_flips_file -c \
    'from "draw_graph.asy" access draw_graph;
    draw_graph("'$flips_data_file'", "Flips", "'$title'");'

  result_localization_triangles_file="result_"$test"_localization_triangles".pdf
  asy -f pdf -nointeractiveView -o $result_localization_triangles_file -c \
    'from "draw_graph.asy" access draw_graph;
    draw_graph("'$localization_triangles_data_file'", "Total triangles passed during localization", "'$title'");'

  result_delaunay_tests_file="result_"$test"_delaunay_tests".pdf
  asy -f pdf -nointeractiveView -o $result_delaunay_tests_file -c \
    'from "draw_graph.asy" access draw_graph;
    draw_graph("'$delaunay_tests_data_file'", "Point-in-circle tests", "'$title'");'
done

# vim: et ts=2 sw=2:
