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

#ifndef POINT_PREDICATES_HPP
#define POINT_PREDICATES_HPP

#include <sstream>

#include "inexact_computations_ex.hpp"
#include "point.hpp"
#include "orientation.hpp"
#include "exceptions.hpp"

// HAVE_CGAL - is program compiled with CGAL support.
// USE_CGAL_PREDICATES - use only CGAL predicates, otherwise interval-based
//     predicates will be used.
// USE_CGAL_ON_INEXACT - use CGAL when it is not possible to do exact
// computations in double precision arithmetics.

#ifndef HAVE_CGAL
  #ifdef USE_CGAL_PREDICATES
    #error __FILE__: Defined USE_CGAL_PREDICATES with undefined HAVE_CGAL.
  #endif
  #ifdef USE_CGAL_ON_INEXACT
    #error __FILE__: Defined USE_CGAL_ON_INEXACT with undefined HAVE_CGAL.
  #endif
#endif

#include "point_predicates_impl_cgal.hpp"
#include "point_predicates_impl_interval.hpp"

namespace cg
{
  /*
   * Returns orientation of (p0, p1, p2) triangle vertices as seen from
   * (0, 0, 1) in right-hand coordinate system.
   */
  template< class Scalar >
  inline
  orientation_t exact_orientation( point_t<Scalar, 2> const &p0,
                                   point_t<Scalar, 2> const &p1,
                                   point_t<Scalar, 2> const &p2 )
  {
#ifdef USE_CGAL_PREDICATES
    orientation_t const result =
      cgal_predicates::exact_orientation(p0, p1, p2);
#else
    orientation_t const result =
      interval_predicates::exact_orientation(p0, p1, p2);
#ifdef HAVE_CGAL
    BOOST_ASSERT(result == cgal_predicates::exact_orientation(p0, p1, p2));
#endif // HAVE_CGAL
#endif // USE_CGAL_PREDICATES
    return result;
  }

  /*
   * Input: points (p, q, r) must NOT lie on same line.
   * Returns:
   *   or_on_positive_side -
   *       s is on the positive side of oriented (p, q, r) triangle,
   *   or_on_boundary -
   *       s lies on (p, q, r) triangle,
   *   or_on_negative_side -
   *       s is on the negative of oriented (p, q, r) triangle.
   * If points p, q, r oriented counterclockwise when seen from (0, 0, 1)
   * in right-hand coordinate system, then "positive side" is interior of
   * triangle.
   */
  template< class Scalar >
  inline
  orientation_t exact_side_of_oriented_triangle(
      point_t<Scalar, 2> const &p,
      point_t<Scalar, 2> const &q,
      point_t<Scalar, 2> const &r,
      point_t<Scalar, 2> const &s )
  {
    if (cg::exact_orientation(p, q, r) == or_collinear)
    {
      std::ostringstream ostr;
      ostr << "exact_side_of_oriented_triangle(" <<
          p << "," << q << "," << r << "," << s << "): "
          "first three points are collinear";
      throw invalid_argument(ostr.str());
    }

#ifdef USE_CGAL_PREDICATES
    orientation_t const result =
      cgal_predicates::exact_side_of_oriented_triangle(p, q, r, s);
#else
    orientation_t const result =
      interval_predicates::exact_side_of_oriented_triangle(p, q, r, s);
#ifdef HAVE_CGAL
    BOOST_ASSERT(result ==
        cgal_predicates::exact_side_of_oriented_triangle(p, q, r, s));
#endif // HAVE_CGAL
#endif // USE_CGAL_PREDICATES
    return result;
  }

  /*
   * Returns:
   *   or_on_positive_side -
   *       s is on the left side of oriented (p, q, r) circle,
   *   or_on_boundary -
   *       s lies on (p, q, r) circle,
   *   or_on_negative_side -
   *       s is on the right side of oriented (p, q, r) circle.
   * If points p0, p1, p2 oriented counterclockwise when seen from (0, 0, 1)
   * in right-hand coordinate system, then "left side" is interior of circle.
   */
  template< class Scalar >
  inline
  orientation_t exact_side_of_oriented_circle(
      point_t<Scalar, 2> const &p,
      point_t<Scalar, 2> const &q,
      point_t<Scalar, 2> const &r,
      point_t<Scalar, 2> const &s )
  {
#ifdef USE_CGAL_PREDICATES
    orientation_t const result =
        cgal_predicates::exact_side_of_oriented_circle(p, q, r, s);
#else
    orientation_t const result =
        interval_predicates::exact_side_of_oriented_circle(p, q, r, s);
#ifdef HAVE_CGAL
    BOOST_ASSERT(result ==
        cgal_predicates::exact_side_of_oriented_circle(p, q, r, s));
#endif // HAVE_CGAL
#endif // USE_CGAL_PREDICATES
    return result;
  }

  //
  // Derivative functions.
  //
  
  /*
   * Returns true if p2 lies on the left side of line (p0,p1).
   */
  template< class Scalar >
  inline
  bool exact_is_left_turn( point_t<Scalar, 2> const &p0,
                           point_t<Scalar, 2> const &p1,
                           point_t<Scalar, 2> const &p2 )
  {
    return exact_orientation(p0, p1, p2) == or_clockwise;
  }

  /*
   * Returns true if p2 lies on the right side of line (p0,p1).
   */
  template< class Scalar >
  inline
  bool exact_is_right_turn( point_t<Scalar, 2> const &p0,
                            point_t<Scalar, 2> const &p1,
                            point_t<Scalar, 2> const &p2 )
  {
    return exact_orientation(p0, p1, p2) == or_counterclockwise;
  }

  /*
   * Returns true if p2 lies on the line (p0,p1).
   */
  template< class Scalar >
  inline
  bool exact_is_collinear( point_t<Scalar, 2> const &p0,
                           point_t<Scalar, 2> const &p1,
                           point_t<Scalar, 2> const &p2 )
  {
    return exact_orientation(p0, p1, p2) == or_collinear;
  }

  /*
   * Input: p0, p1, p2 lies on the same line.
   * Returns true if points p0, p1, p2 lies on line in order p0, p1, p2.
   * (Returns true if p1 lies on segment [p0, p2].)
   */
  template< class Scalar >
  inline
  bool exact_is_collinear_points_lie_along_line(
      point_t<Scalar, 2> const &p0,
      point_t<Scalar, 2> const &p1,
      point_t<Scalar, 2> const &p2 )
  {
    BOOST_ASSERT(exact_orientation(p0, p1, p2) == or_collinear);

    if (p0.x < p1.x)
    {
      //  *               *         - fixed
      // p0 ---          p1 ... p2  - true
      // p0 ---   p2 ... p1         - false
      return !(p1.x > p2.x);
    }
    else if (p0.x > p1.x)
    {
      //  *                      *  - fixed
      // p2 ... p1          --- p0  - true
      //        p1 ... p2   --- p0  - false
      return !(p1.x < p2.x);
    }
    else if (p0.y < p1.y)
    {
      return !(p1.y > p2.y);
    }
    else if (p0.y > p1.y)
    {
      return !(p1.y < p2.y);
    }

    BOOST_ASSERT(p0 == p1 && p1 == p2);
    return true;
  }
}

#endif // POINT_PREDICATES_HPP
