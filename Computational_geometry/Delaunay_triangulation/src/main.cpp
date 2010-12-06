/*
 *  This file is part of Delaunay triangulation robust implementation.
 *
 *  Copyright (C) 2010  Vladimir Rutsky <altsysrq@gmail.com>
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

int main()
{
  typedef dt::delaunay_triangulation<cg::point_2> triangulation_t;

  triangulation_t triangulation(std::istream_iterator<cg::point_2>(std::cin),
                                std::istream_iterator<cg::point_2>());

  typedef std::vector<triangulation_t::triangle_vertices_indices_t> triangles_t;
  triangles_t triangles;
  
  std::copy(triangulation.triangles_begin(), triangulation.triangles_end(),
            std::back_inserter(triangles));

  // Sort output.
  // TODO: Needed only for debug.
  std::sort(triangles.begin(), triangles.end());

  std::copy(triangulation.triangles_begin(), triangulation.triangles_end(),
    std::ostream_iterator<triangulation_t::triangle_vertices_indices_t>(
      std::cout, "\n"));
}
