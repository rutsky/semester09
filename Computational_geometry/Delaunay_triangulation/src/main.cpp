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

#include "delaunay_triangulation.hpp"
#include "point.hpp"
#include "point_predicates.hpp"

int main( int argc, char const *argv[] )
{
  std::cout << "Hi!\n";

  std::vector<cg::point_2> points;

  typedef dt::delaunay_triangulation<cg::point_2> triangulation_t;
  triangulation_t triangulation(points.begin(), points.end());

  std::copy(triangulation.triangles_begin(), triangulation.triangles_end(),
    std::ostream_iterator<triangulation_t::triangle_vertices_indices_t>(
      std::cout, "\n"));

  points.push_back(cg::point_2(0, 0));

  triangulation_t triangulation1(points.begin(), points.end());

  std::copy(triangulation1.triangles_begin(), triangulation1.triangles_end(),
    std::ostream_iterator<triangulation_t::triangle_vertices_indices_t>(
      std::cout, "\n"));

  points.push_back(cg::point_2(1, 0));
  points.push_back(cg::point_2(0, 1));
  triangulation_t triangulation2(points.begin(), points.end());

  std::copy(triangulation2.triangles_begin(), triangulation2.triangles_end(),
    std::ostream_iterator<triangulation_t::triangle_vertices_indices_t>(
      std::cout, "\n"));

  // Orientation tests.
  BOOST_VERIFY(
    cg::exact_orientation(cg::point_2(0, 0),
                          cg::point_2(0, 0),
                          cg::point_2(0, 0)) == cg::COLLINEAR);
  BOOST_VERIFY(
    cg::exact_orientation(cg::point_2(0, 0),
                          cg::point_2(1, 0),
                          cg::point_2(0, 1)) == cg::CLOCKWISE);
  BOOST_VERIFY(
    cg::exact_orientation(cg::point_2(0, 0),
                          cg::point_2(0, 1),
                          cg::point_2(1, 0)) == cg::COUNTERCLOCKWISE);

  BOOST_VERIFY(
    exact_side_of_oriented_circle(
          cg::point_2(0, -1),
          cg::point_2(1, 0),
          cg::point_2(0, 1),
          cg::point_2(-1, 0)) == cg::ON_ORIENTED_BOUNDARY);
  BOOST_VERIFY(
    exact_side_of_oriented_circle(
          cg::point_2(0, -1),
          cg::point_2(1, 0),
          cg::point_2(0, 1),
          cg::point_2(1, 1)) == cg::ON_NEGATIVE_SIDE);
  BOOST_VERIFY(
    exact_side_of_oriented_circle(
          cg::point_2(0, -1),
          cg::point_2(1, 0),
          cg::point_2(0, 1),
          cg::point_2(0, 0)) == cg::ON_POSITIVE_SIDE);
}
