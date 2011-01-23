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

#define BOOST_TEST_DYN_LINK
#define BOOST_TEST_NO_MAIN

#include <boost/test/unit_test.hpp>

#include <sstream>

#include "point_types.hpp"
#include "point_io.hpp"

BOOST_AUTO_TEST_SUITE(point_io_hpp)

BOOST_AUTO_TEST_CASE(test_point_out)
{
  cg::point_2 const p(1.0, 3.0);
  
  std::ostringstream ostr;
  
  ostr << p;

  BOOST_CHECK_EQUAL(ostr.str(), "(1,3)");
  BOOST_CHECK_EQUAL(p.y, 3.0);
}

BOOST_AUTO_TEST_CASE(test_point_in)
{
  std::istringstream istr("2.0 0.125");
  
  cg::point_2 p;
  istr >> p;

  BOOST_CHECK_EQUAL(p.x, 2.0);
  BOOST_CHECK_EQUAL(p.y, 0.125);
}

BOOST_AUTO_TEST_SUITE_END()
