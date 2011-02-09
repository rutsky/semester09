#!/bin/bash

if [ "$#" -lt "2" ]; then
  echo "Usage:"
  echo "  "$0" points_file triangles_file [draw_points]"
  exit 0
fi

if [ -n "$3" ]; then
  draw_cmd='draw_triangulation("'$1'", "'$2'", '$3');'
else
  draw_cmd='draw_triangulation("'$1'", "'$2'");'
fi

cmd='from "triangulation.asy" access draw_triangulation; '$draw_cmd
asy -f pdf -nointeractiveView -o `basename $1`.pdf -c "$cmd"
  
# vim: et ts=2 sw=2:
