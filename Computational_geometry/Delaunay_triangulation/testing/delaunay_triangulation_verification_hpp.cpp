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

#include <boost/assign/list_of.hpp>

#include "point_types.hpp"
#include "delaunay_triangulation_verification.hpp"

using namespace boost::assign;

using namespace cg;
using namespace cg::verification;
typedef triangle_vertices_indices_t triangle_t;

BOOST_AUTO_TEST_SUITE(delaunay_triangulation_verification_hpp)

BOOST_AUTO_TEST_CASE(test_triangulation_verification)
{
  std::vector<point_2> p;
  std::vector<triangle_t> t;
  
  BOOST_CHECK_EQUAL(verify_triangulation(
      p.begin(), p.end(), 
      t.begin(), t.end(), std::cout), tvr_valid);
  
  p = list_of<point_2>(1, 1);
  BOOST_CHECK_EQUAL(verify_triangulation(
      p.begin(), p.end(), 
      t.begin(), t.end(), std::cout), tvr_valid);
  
  p = list_of<point_2>(0, 0)(1, 0);
  BOOST_CHECK_EQUAL(verify_triangulation(
      p.begin(), p.end(), 
      t.begin(), t.end(), std::cout), tvr_valid);

  p = list_of<point_2>(0, 0)(1, 0)(2, 0);
  BOOST_CHECK_EQUAL(verify_triangulation(
      p.begin(), p.end(), 
      t.begin(), t.end(), std::cout), tvr_valid);

  p = list_of<point_2>(0, 0)(1, 0)(2, 0)(3, 0)(-10, 0);
  BOOST_CHECK_EQUAL(verify_triangulation(
      p.begin(), p.end(), 
      t.begin(), t.end(), std::cout), tvr_valid);
      
  t = list_of<triangle_t>();
  
  p.clear();
  BOOST_CHECK_EQUAL(verify_triangulation(
      p.begin(), p.end(), 
      t.begin(), t.end(), std::cout), tvr_excess_triangles);
  
  p = list_of<point_2>(1, 1);
  BOOST_CHECK_EQUAL(verify_triangulation(
      p.begin(), p.end(), 
      t.begin(), t.end(), std::cout), tvr_excess_triangles);
  
  p = list_of<point_2>(0, 0)(1, 0);
  BOOST_CHECK_EQUAL(verify_triangulation(
      p.begin(), p.end(), 
      t.begin(), t.end(), std::cout), tvr_excess_triangles);

  p = list_of<point_2>(0, 0)(1, 0)(2, 0);
  BOOST_CHECK_EQUAL(verify_triangulation(
      p.begin(), p.end(), 
      t.begin(), t.end(), std::cout), tvr_excess_triangles);

  p = list_of<point_2>(0, 0)(1, 0)(2, 0)(3, 0)(-10, 0);
  BOOST_CHECK_EQUAL(verify_triangulation(
      p.begin(), p.end(), 
      t.begin(), t.end(), std::cout), tvr_excess_triangles);
  
  p = list_of<point_2>(0, 0)(1, 0)(0, 1);
  t.clear();
  BOOST_CHECK_EQUAL(verify_triangulation(
      p.begin(), p.end(), 
      t.begin(), t.end(), std::cout), tvr_empty_triangulation);

  p = list_of<point_2>(0, 0)(1, 0)(0, 1);
  t = list_of<triangle_t>(0, 1, 2);
  BOOST_CHECK_EQUAL(verify_triangulation(
      p.begin(), p.end(), 
      t.begin(), t.end(), std::cout), tvr_valid);

  p = list_of<point_2>(0, 0)(1, 0)(0, 1);
  t = list_of<triangle_t>(0, 10, 2);
  BOOST_CHECK_EQUAL(verify_triangulation(
      p.begin(), p.end(), 
      t.begin(), t.end(), std::cout), tvr_invalid_index);

  p = list_of<point_2>(0, 0)(1, 0)(0, 1)(1, 1);
  t = list_of<triangle_t>(0, 1, 2)(1, 2, 3);
  BOOST_CHECK_EQUAL(verify_triangulation(
      p.begin(), p.end(), 
      t.begin(), t.end(), std::cout), tvr_valid);

  p = list_of<point_2>(0, 0)(1, 0)(0, 1)(1, 1)(1, 0);
  t = list_of<triangle_t>(0, 1, 2)(4, 2, 3);
  BOOST_CHECK_EQUAL(verify_triangulation(
      p.begin(), p.end(), 
      t.begin(), t.end(), std::cout), tvr_duplicate_vertices_in_triangulation);

  p = list_of<point_2>(0, 0)(1, 0)(0, 1)(1, 1)(1, 0);
  t = list_of<triangle_t>(0, 1, 2);
  BOOST_CHECK_EQUAL(verify_triangulation(
      p.begin(), p.end(), 
      t.begin(), t.end(), std::cout), tvr_points_and_indices_not_correspond);

  p = list_of<point_2>(0, 0)(1, 0)(2, 0)(1, 1);
  t = list_of<triangle_t>(0, 1, 2)(0, 3, 1)(1, 3, 2);
  BOOST_CHECK_EQUAL(verify_triangulation(
      p.begin(), p.end(), 
      t.begin(), t.end(), std::cout), tvr_singular_triangle);

  p = list_of<point_2>(0, 0)(1, 0)(0, 1)(0.5, 0);
  t = list_of<triangle_t>(0, 1, 2)(2, 1, 3);
  BOOST_CHECK_EQUAL(verify_triangulation(
      p.begin(), p.end(), 
      t.begin(), t.end(), std::cout), tvr_point_in_triangle);

  p = list_of<point_2>(0, 0)(1, 0)(0, 1)(0.1, 0.1);
  t = list_of<triangle_t>(0, 1, 2)(2, 1, 3);
  BOOST_CHECK_EQUAL(verify_triangulation(
      p.begin(), p.end(), 
      t.begin(), t.end(), std::cout), tvr_point_in_triangle);

  p = list_of<point_2>(0, 0)(1, 0)(0, 1)(2, 0)(2, 1);
  t = list_of<triangle_t>(0, 1, 2)(1, 3, 4);
  BOOST_CHECK_EQUAL(verify_triangulation(
      p.begin(), p.end(), 
      t.begin(), t.end(), std::cout), tvr_duplicate_border_out_edge);

  p = list_of<point_2>(0, 0)(1, 0)(0, 1)(2, 0)(2, 1)(3, 0);
  t = list_of<triangle_t>(0, 1, 2)(3, 4, 5);
  BOOST_CHECK_EQUAL(verify_triangulation(
      p.begin(), p.end(), 
      t.begin(), t.end(), std::cout), tvr_more_than_one_border_chain);

  p = list_of<point_2>(0, 0)(1, 0)(0, 1)(1, 1);
  t = list_of<triangle_t>(0, 1, 2)(2, 1, 3);
  BOOST_CHECK_EQUAL(verify_triangulation(
      p.begin(), p.end(), 
      t.begin(), t.end(), std::cout), tvr_valid);

  p = list_of<point_2>(0, 0)(1, 0)(0.7, 0.2)(1, 1);
  t = list_of<triangle_t>(0, 1, 2)(2, 1, 3);
  BOOST_CHECK_EQUAL(verify_triangulation(
      p.begin(), p.end(), 
      t.begin(), t.end(), std::cout), tvr_border_chain_not_convex);
}

BOOST_AUTO_TEST_SUITE_END()

// vim: set expandtab tabstop=2 shiftwidth=2:

