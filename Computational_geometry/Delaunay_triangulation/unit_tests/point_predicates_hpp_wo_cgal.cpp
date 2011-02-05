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

#define BOOST_TEST_DYN_LINK
#define BOOST_TEST_NO_MAIN

#include <boost/test/unit_test.hpp>

#undef HAVE_CGAL
#undef USE_CGAL_PREDICATES
#undef USE_CGAL_ON_INEXACT

#include "point_predicates.hpp"

#include "point_types.hpp"

using namespace cg;

BOOST_AUTO_TEST_SUITE(point_predicates_hpp_wo_cgal)

BOOST_AUTO_TEST_CASE(test_exact_orientation)
{
  point_2 const p0_0(0, 0), p2_0(2, 0), p0_2(0, 2), p2_2(2, 2),
    p1_0(1, 0), p0_1(0, 1), p1_1(1, 1);

  BOOST_CHECK_EQUAL(exact_orientation(p2_0, p0_0, p0_2), or_clockwise);
  BOOST_CHECK_EQUAL(exact_orientation(p0_0, p0_2, p2_0), or_clockwise);
  BOOST_CHECK_EQUAL(exact_orientation(p0_2, p2_0, p0_0), or_clockwise);
  
  BOOST_CHECK_EQUAL(exact_orientation(p0_0, p2_0, p0_2), or_counterclockwise);
  BOOST_CHECK_EQUAL(exact_orientation(p2_0, p0_2, p0_0), or_counterclockwise);
  BOOST_CHECK_EQUAL(exact_orientation(p0_2, p0_0, p2_0), or_counterclockwise);
  
  BOOST_CHECK_EQUAL(exact_orientation(p0_0, p1_0, p2_0), or_collinear);
  BOOST_CHECK_EQUAL(exact_orientation(p1_0, p2_0, p0_0), or_collinear);
  BOOST_CHECK_EQUAL(exact_orientation(p2_0, p0_0, p1_0), or_collinear);

  BOOST_CHECK_EQUAL(exact_orientation(p0_0, p0_1, p0_2), or_collinear);
  BOOST_CHECK_EQUAL(exact_orientation(p0_1, p0_2, p0_0), or_collinear);
  BOOST_CHECK_EQUAL(exact_orientation(p0_2, p0_0, p0_1), or_collinear);
      
  BOOST_CHECK_EQUAL(exact_orientation(p2_0, p0_2, p1_1), or_collinear);

  BOOST_CHECK_EQUAL(exact_orientation(p0_0, p1_1, p1_1), or_collinear);
  BOOST_CHECK_EQUAL(exact_orientation(p0_0, p0_0, p1_1), or_collinear);
  BOOST_CHECK_EQUAL(exact_orientation(p1_1, p0_0, p1_1), or_collinear);

  BOOST_CHECK_EQUAL(exact_orientation(p1_1, p1_1, p1_1), or_collinear);
  
  // TODO: Suspicious test.
  BOOST_CHECK_THROW(exact_orientation(
      point_2(-1e9, -1e9 + 1e-4), point_2(0, 0), point_2(1e9 + 1e-4, 1e9)), 
      inexact_computations_exception);
}

BOOST_AUTO_TEST_CASE(test_exact_side_of_oriented_triangle)
{
  point_2 p0_0(0, 0), p2_0(2, 0), p0_2(0, 2), p2_2(2, 2),
    p1_0(1, 0), p0_1(0, 1), p1_1(1, 1);
    
  BOOST_CHECK_EQUAL(exact_side_of_oriented_triangle(p0_0, p2_0, p0_2, p1_1), 
      or_on_boundary);
  BOOST_CHECK_EQUAL(exact_side_of_oriented_triangle(p0_0, p2_0, p0_2, p2_2), 
      or_on_negative_side);
  BOOST_CHECK_EQUAL(exact_side_of_oriented_triangle(p2_0, p0_0, p0_2, p2_2), 
      or_on_positive_side);
  
  BOOST_CHECK_EQUAL(exact_side_of_oriented_triangle(p0_0, p2_0, p0_2, p2_2), 
      or_on_negative_side);
  BOOST_CHECK_EQUAL(exact_side_of_oriented_triangle(p0_0, p0_2, p2_0, p2_2), 
      or_on_positive_side);
  
  BOOST_CHECK_EQUAL(exact_side_of_oriented_triangle(p0_0, p2_0, p0_2, p1_1), 
      or_on_boundary);

  // TODO:
  //BOOST_CHECK_THROW(exact_side_of_oriented_triangle(
  //    point_2(1e-16, 1e-16), point_2(1e10, 1e-10), point_2(1e-10, 1e10), 
  //    point_2(0.5e10, 1e-16)),
  //    inexact_computations_exception);

  BOOST_CHECK_THROW(exact_side_of_oriented_triangle(p0_0, p0_0, p0_2, p1_1),
      invalid_argument);
}

BOOST_AUTO_TEST_CASE(test_exact_side_of_oriented_circle)
{
  point_2 p0_0(0, 0), p2_0(2, 0), p0_2(0, 2), p2_2(2, 2),
    p1_0(1, 0), p0_1(0, 1), p1_1(1, 1), p3_3(3, 3);
    
  BOOST_CHECK_EQUAL(exact_side_of_oriented_circle(p0_0, p2_0, p0_2, p2_2), 
      or_on_boundary);
  BOOST_CHECK_EQUAL(exact_side_of_oriented_circle(p0_0, p0_2, p2_0, p2_2), 
      or_on_boundary);

  BOOST_CHECK_EQUAL(exact_side_of_oriented_circle(p0_0, p0_2, p2_0, p3_3), 
      or_on_positive_side);
  BOOST_CHECK_EQUAL(exact_side_of_oriented_circle(p0_2, p0_0, p2_0, p3_3), 
      or_on_negative_side);

  BOOST_CHECK_EQUAL(exact_side_of_oriented_circle(p0_0, p0_2, p2_0, p1_1), 
      or_on_negative_side);
  BOOST_CHECK_EQUAL(exact_side_of_oriented_circle(p0_0, p2_0, p0_2, p1_1), 
      or_on_positive_side);
      
  BOOST_CHECK_EQUAL(exact_side_of_oriented_circle(p0_0, p1_0, p0_1, 
      point_2(1, 1 - 1e-10)),
      or_on_positive_side);
}

BOOST_AUTO_TEST_CASE(test_exact_is_collinear_points_lie_along_line)
{
  point_2 p0_0(0, 0), p2_0(2, 0), p0_2(0, 2), p2_2(2, 2),
    p1_0(1, 0), p0_1(0, 1), p1_1(1, 1), p3_3(3, 3);
    
  BOOST_CHECK(exact_is_collinear_points_lie_along_line(p0_0, p1_0, p2_0));
  BOOST_CHECK(!exact_is_collinear_points_lie_along_line(p0_0, p2_0, p1_0));

  BOOST_CHECK(exact_is_collinear_points_lie_along_line(p0_0, p0_0, p1_0));
} 

BOOST_AUTO_TEST_SUITE_END()
