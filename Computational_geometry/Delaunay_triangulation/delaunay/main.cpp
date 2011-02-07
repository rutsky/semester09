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
#include <fstream>

#include <boost/random/mersenne_twister.hpp>

#include "delaunay_triangulation.hpp"
#include "point.hpp"
#include "point_io.hpp"
#include "point_predicates.hpp"
#include "point_types.hpp"

int main( int argc, char *argv[] )
{
  boost::mt19937 randGen;

  typedef dt::delaunay_triangulation<cg::point_2> triangulation_t;
  // NOTE: Extra brackets around constructor arguments are required!
  // Otherwise this statement will be interpreted as function declaration
  // in MS VS 2008 Express Edition.
  // TODO: Check that this note is not obsolete after adding randGen argument.
  triangulation_t triangulation((std::istream_iterator<cg::point_2>(std::cin)),
                                (std::istream_iterator<cg::point_2>()),
                                randGen);

  typedef
    std::ostream_iterator<cg::triangle_vertices_indices_t>
    out_iterator_t;
  std::copy(triangulation.begin(), triangulation.end(),
    out_iterator_t(std::cout));

  if (argc == 2)
  {
    // Single argument - name of file in which debug information should be
    // placed.
    std::ofstream infoFile(argv[1]);
    if (!infoFile)
    {
      perror(argv[1]);
      return -1;
    }

    // Number of stored triangles in used structure.
    infoFile << triangulation.stored_triangles_num() << "\n";
    // Number of performed flips.
    infoFile << triangulation.flips_num() << "\n";
    // Number of traversed triangles during point location.
    infoFile << triangulation.viewed_triangles_in_localization_num() << "\n";
    // Number of point-in-circle tests.
    infoFile << triangulation.delaunay_tests_num() << "\n";
  }
}
