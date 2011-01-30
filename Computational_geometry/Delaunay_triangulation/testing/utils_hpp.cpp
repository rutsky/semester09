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

using namespace boost::assign;

#include "utils.hpp"
#include "point_types.hpp"
#include "point_ops.hpp"
#include "point_io.hpp"

using namespace cg;

BOOST_AUTO_TEST_SUITE(utils_hpp)

BOOST_AUTO_TEST_CASE(main)
{
  std::vector<point_2> points;
  point_2 min, max;
  
  points = list_of<point_2>(0, 0)(-1, -1)(1, 1);
  boost::tie(min, max) = 
    axis_aligned_bounding_box(points.begin(), points.end());
  BOOST_CHECK_EQUAL(min, point_2(-1, -1));
  BOOST_CHECK_EQUAL(max, point_2(1, 1));
}

BOOST_AUTO_TEST_SUITE_END()
