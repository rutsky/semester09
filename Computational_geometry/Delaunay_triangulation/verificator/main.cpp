/*
 *  This file is part of Delaunay triangulation robust implementation.
 *
 *  Copyright (C) 2010, 2011  Vladimir Rutsky <altsysrq@gmail.com>
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#include <iostream>

#include <boost/tuple/tuple_io.hpp>
#include <boost/tuple/tuple_comparison.hpp>

#include "delaunay_triangulation.hpp"
#include "point.hpp"
#include "point_io.hpp"
#include "point_predicates.hpp"
#include "point_types.hpp"

int main( int argc, char *argv[] )
{
  if (argc < 3)
  {
    std::cout << "Missing arguments.\n" <<
      "Usage:\n"
      "  " << argv[0] << " points_file triangles_file\n";
    return 1;
  }

  
}

// vim: set expandtab tabstop=2 shiftwidth=2:
