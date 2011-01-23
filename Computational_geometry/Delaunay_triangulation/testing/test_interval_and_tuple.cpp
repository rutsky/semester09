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

#include <boost/numeric/interval.hpp>

#include "point_types.hpp"
#include "point_ops.hpp"

BOOST_AUTO_TEST_SUITE(test_interval_and_tuple)

BOOST_AUTO_TEST_CASE(test_tuple)
{
  typedef double scalar_t;
  typedef boost::numeric::interval<scalar_t> interval_t;
  
  interval_t x, y;
  cg::point_2 p(7, 8);
  
  boost::tie(x, y) = cg::tuple(p);
  BOOST_CHECK_EQUAL(x.lower(), p.x);
  BOOST_CHECK_EQUAL(y.lower(), p.y);
}

BOOST_AUTO_TEST_SUITE_END()
