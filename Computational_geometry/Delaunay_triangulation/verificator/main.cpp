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

#include <boost/tuple/tuple_io.hpp>
#include <boost/tuple/tuple_comparison.hpp>

#include "delaunay_triangulation_verification.hpp"
#include "point_io.hpp"
#include "point_types.hpp"

using namespace cg::verification;

template< class CharT, class Traits >
inline
std::basic_istream<CharT, Traits> &
  operator >> ( std::basic_istream<CharT, Traits> &is, triangle_vertices_indices_t &p )
{
  size_t i1, i2, i3;
  is >> i1 >> i2 >> i3;
  p = triangle_vertices_indices_t(i1, i2, i3);
  
  return is;
}

int main( int argc, char *argv[] )
{
  if (argc < 3)
  {
    std::cout << "Missing arguments.\n" <<
      "Usage:\n"
      "  " << argv[0] << " points_file triangles_file\n";
    return 1;
  }

  std::ifstream pointsFile(argv[1]);
  if (!pointsFile)
  {
    perror(argv[1]);
    return -1;
  }
  
  std::ifstream trianglesFile(argv[2]);
  if (!pointsFile)
  {
    perror(argv[2]);
    return -2;
  }
  
  triangulation_verification_result const result =
      verify_triangulation(
          std::istream_iterator<cg::point_2>(pointsFile),
          std::istream_iterator<cg::point_2>(),
          std::istream_iterator<triangle_vertices_indices_t>(trianglesFile),
          std::istream_iterator<triangle_vertices_indices_t>(),
        std::cerr, true);
  return static_cast<int>(result);
}

// vim: set et ts=2 sw=2:
