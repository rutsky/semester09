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

#include "point_predicates.hpp"

#include "point_types.hpp"

using namespace cg;

BOOST_AUTO_TEST_SUITE(point_predicates_hpp)

BOOST_AUTO_TEST_CASE(test_turns)
{
  point_2 const p0_0(0, 0), p2_0(2, 0), p0_2(0, 2), p2_2(2, 2),
    p1_0(1, 0), p0_1(0, 1), p1_1(1, 1);
    
  BOOST_CHECK(exact_is_left_turn(p0_0, p0_2, p2_0));
  BOOST_CHECK(exact_is_right_turn(p0_0, p2_0, p0_2));
  BOOST_CHECK(exact_is_collinear(p0_0, p1_1, p2_2));
  
  // TODO: test is_collinear(sequence)
}

BOOST_AUTO_TEST_SUITE_END()
