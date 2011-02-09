#!/bin/sh

if [ "$#" -ne "2" ]; then
  echo "Usage:"
  echo "  "$0" points_file triangles_file"
  exit 0
fi

asy -f pdf -nointeractiveView -o `basename $1`.pdf -c 'from "triangulation.asy" access draw_triangulation; draw_triangulation("'$1'", "'$2'");'

# vim: et ts=2 sw=2:
