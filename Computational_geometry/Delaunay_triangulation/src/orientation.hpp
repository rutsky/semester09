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

#ifndef ORIENTATION_HPP
#define ORIENTATION_HPP

#include <boost/static_assert.hpp>

#ifdef USING_CGAL
#include <CGAL/enum.h>
#endif // USING_CGAL

namespace cg
{
  // Compatible with CGAL::Sign.
  enum orientation_t
  {
    or_clockwise        = -1,
    or_collinear        =  0,
    or_counterclockwise = +1,

    or_on_negative_side = -1,
    or_on_boundary      =  0,
    or_on_positive_side = +1,
  };

#ifdef USING_CGAL
  BOOST_STATIC_ASSERT(or_clockwise        == CGAL::CLOCKWISE);
  BOOST_STATIC_ASSERT(or_collinear        == CGAL::COLLINEAR);
  BOOST_STATIC_ASSERT(or_counterclockwise == CGAL::COUNTERCLOCKWISE);

  BOOST_STATIC_ASSERT(or_on_negative_side == CGAL::ON_NEGATIVE_SIDE);
  BOOST_STATIC_ASSERT(or_on_boundary      == CGAL::ON_ORIENTED_BOUNDARY);
  BOOST_STATIC_ASSERT(or_on_positive_side == CGAL::ON_POSITIVE_SIDE);
#endif // USING_CGAL

#endif // ORIENTATION_HPP
