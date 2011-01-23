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

#include "determinant.hpp"

BOOST_AUTO_TEST_SUITE(determinant_hpp)

BOOST_AUTO_TEST_CASE(main)
{
  // Determinant 1x1.
  BOOST_CHECK_EQUAL(cg::determinant(0), 0);
  BOOST_CHECK_EQUAL(cg::determinant(1.0), 1.0);
  BOOST_CHECK_EQUAL(cg::determinant(-5.0), -5.0);

  // Determinant 2x2.
  BOOST_CHECK_EQUAL(cg::determinant(1.0, 2.0,
                                    3.0, 4.0), -2.0);
  BOOST_CHECK_EQUAL(cg::determinant( 1, 4,
                                    -1, 9), 13);
  BOOST_CHECK_EQUAL(cg::determinant( 1,  4,
                                     1, -9), -13);
  BOOST_CHECK_EQUAL(cg::determinant( 0, 0,
                                    -1, 9), 0);
  BOOST_CHECK_EQUAL(cg::determinant( 1, 0,
                                    -1, 0), 0);
  BOOST_CHECK_EQUAL(cg::determinant( 7, 7,
                                    14, 14), 0);

  // Determinant 3x3.
  BOOST_CHECK_EQUAL(cg::determinant(3.0, 2.0, 3.0,
                                    4.0, 5.0, 6.0,
                                    7.0, 8.0, 9.0), -6.0);
  BOOST_CHECK_EQUAL(cg::determinant( 9,  0, -1,
                                     8, -1,  4,
                                     1,  4,  0), -177);
  BOOST_CHECK_EQUAL(cg::determinant( 9,  0, -1,
                                     8,  1,  4,
                                     1, -4,  0), 177);
  BOOST_CHECK_EQUAL(cg::determinant( 9,  0, -1,
                                     8, -1,  4,
                                     0,  0,  0), 0);
  BOOST_CHECK_EQUAL(cg::determinant( 9,  0,  0,
                                     8, -1,  0,
                                     1,  4,  0), 0);
  BOOST_CHECK_EQUAL(cg::determinant(-16,  2, -8,
                                      8, -1,  4,
                                      1,  4,  0), 0);

  // Determinant 4x4.
  BOOST_CHECK_EQUAL(cg::determinant( 1.0,  2.0,   3.0,  4.0,
                                     5.0,  6.0,   7.0,  8.0, 
                                     9.0,  0.0,  11.0, 12.0,
                                    13.0, 14.0, -15.0, 16.0), -3600);
  BOOST_CHECK_EQUAL(cg::determinant(  5,  8,  0,  2,
                                      7,  2,  2,  2,
                                      9,  1,  9,  7,
                                      3,  0,  2,  6), -1260);
  BOOST_CHECK_EQUAL(cg::determinant(  5,  8,  0,  2,
                                      7,  2,  2,  2,
                                     -9, -1, -9, -7,
                                      3,  0,  2,  6), 1260);
  BOOST_CHECK_EQUAL(cg::determinant(  5,  8,  0,  2,
                                      7,  2,  2,  2,
                                     -9, -1, -9, -7,
                                      0,  0,  0,  0), 0);
  BOOST_CHECK_EQUAL(cg::determinant(  5,  8,  0,  2,
                                      7,  2,  0,  2,
                                     -9, -1,  0, -7,
                                      3,  0,  0,  6), 0);
  BOOST_CHECK_EQUAL(cg::determinant(  5,  8,  0,  2,
                                      7,  2,  2,  2,
                                     -9, -1, -9, -7,
                                     14,  4,  4,  4), 0);
}

BOOST_AUTO_TEST_SUITE_END()
