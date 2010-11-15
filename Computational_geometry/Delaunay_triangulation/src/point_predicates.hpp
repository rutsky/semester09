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

#ifndef POINT_PREDICATES_HPP
#define POINT_PREDICATES_HPP

#include <ostream>

#include <boost/assert.hpp>

#include <CGAL/Exact_predicates_inexact_constructions_kernel.h>
#include <CGAL/Filtered_predicate.h>

#include "point.hpp"

namespace cg
{
  enum orientation_t
  {
    CLOCKWISE = -1,
    COLLINEAR = 0,
    COUNTERCLOCKWISE = 1,
  };

  template< class CharT, class Traits >
  inline
  std::basic_ostream<CharT, Traits> &
    operator << ( std::basic_ostream<CharT, Traits> &os, orientation_t o )
  {
    switch (o)
    {
    case CLOCKWISE:
      os << "CW";
      break;
    case COLLINEAR:
      os << "COLLINEAR";
      break;
    case COUNTERCLOCKWISE:
      os << "CCW";
      break;
    default:
      BOOST_ASSERT(0);
    }
    return os;
  }

  /*
   * Returns orientation of (p0, p1, p2) triangle vertices as seen from (0, 0, 1)
   * in right-hand coordinate system.
   */
  template<class Scalar>
  inline
  orientation_t exact_orientation( point_t<Scalar, 2> const &p0,
                                   point_t<Scalar, 2> const &p1,
                                   point_t<Scalar, 2> const &p2 )
  {
    typedef CGAL::Exact_predicates_inexact_constructions_kernel kernel_t;

    CGAL::Orientation const result = CGAL::SF_Orientation_2<kernel_t>()(
        construct_2d_point<kernel_t::Point_2>(p1),
        construct_2d_point<kernel_t::Point_2>(p0),
        construct_2d_point<kernel_t::Point_2>(p2));
    
    if (result == CGAL::NEGATIVE)
      return CLOCKWISE;
    else if (result == CGAL::POSITIVE)
      return COUNTERCLOCKWISE;
    else
    {
      BOOST_ASSERT(result == CGAL::ZERO);
      return COLLINEAR;
    }
  }

  /*
   * Returns true if p2 lies on the left side of line (p0,p1).
   */
  template<class Scalar>
  inline
  bool exact_left_turn( point_t<Scalar, 2> const &p0,
                        point_t<Scalar, 2> const &p1,
                        point_t<Scalar, 2> const &p2 )
  {
    return exact_orientation(p0, p1, p2) == CLOCKWISE;
  }

  /*
   * Returns true if p2 lies on the right side of line (p0,p1).
   */
  template<class Scalar>
  inline
  bool exact_right_turn( point_t<Scalar, 2> const &p0,
                         point_t<Scalar, 2> const &p1,
                         point_t<Scalar, 2> const &p2 )
  {
    return exact_orientation(p0, p1, p2) == COUNTERCLOCKWISE;
  }

  /*
   * Returns true if p2 lies on the line (p0,p1).
   */
  template<class Scalar>
  inline
  bool exact_collinear( point_t<Scalar, 2> const &p0,
                        point_t<Scalar, 2> const &p1,
                        point_t<Scalar, 2> const &p2 )
  {
    return exact_orientation(p0, p1, p2) == COLLINEAR;
  }
}

#endif // POINT_PREDICATES_HPP
