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

#include <boost/exception.hpp>

#include "point.hpp"
#include "orientation.hpp"

namespace cg
{
  struct inexact_computations_exception
    : virtual boost::exception
    , virtual std::exception
  {
  };

  /*
   * Returns orientation of (p0, p1, p2) triangle vertices as seen from
   * (0, 0, 1) in right-hand coordinate system.
   */
  template<class Scalar>
  inline
  orientation_t exact_orientation( point_t<Scalar, 2> const &p0,
                                   point_t<Scalar, 2> const &p1,
                                   point_t<Scalar, 2> const &p2 );

  /*
   * Returns:
   *   or_on_positive_side -
   *       q is on the left side of oriented (p0, p1, p2) triangle,
   *   or_on_boundary -
   *       q lies on (p0, p1, p2) triangle,
   *   or_on_negative_side -
   *       q is on the right side of oriented (p0, p1, p2) triangle.
   * If points p0, p1, p2 oriented counterclockwise when seen from (0, 0, 1)
   * in right-hand coordinate system, then "left side" is interior of triangle.
   */
  template<class Scalar>
  inline
  orientation_t exact_side_of_oriented_triangle(
      point_t<Scalar, 2> const &p0,
      point_t<Scalar, 2> const &p1,
      point_t<Scalar, 2> const &p2,
      point_t<Scalar, 2> const &q );

  /*
   * Returns:
   *   or_on_positive_side -
   *       q is on the left side of oriented (p0, p1, p2) circle,
   *   or_on_boundary -
   *       q lies on (p0, p1, p2) circle,
   *   or_on_negative_side -
   *       q is on the right side of oriented (p0, p1, p2) circle.
   * If points p0, p1, p2 oriented counterclockwise when seen from (0, 0, 1)
   * in right-hand coordinate system, then "left side" is interior of circle.
   */
  template<class Scalar>
  inline
  orientation_t exact_side_of_oriented_circle(
      point_t<Scalar, 2> const &p0,
      point_t<Scalar, 2> const &p1,
      point_t<Scalar, 2> const &p2,
      point_t<Scalar, 2> const &q );

  //
  // Derivative functions.
  //
  
  /*
   * Returns true if p2 lies on the left side of line (p0,p1).
   */
  template<class Scalar>
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
  template<class Scalar>
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
  template<class Scalar>
  inline
  bool exact_is_collinear( point_t<Scalar, 2> const &p0,
                           point_t<Scalar, 2> const &p1,
                           point_t<Scalar, 2> const &p2 )
  {
    return exact_orientation(p0, p1, p2) == or_collinear;
  }
}

#ifdef    USING_CGAL
#include "point_predicates_impl_cgal.hpp"
#else  // USING_CGAL
#include "point_predicates_impl_interval.hpp"
#endif // USING_CGAL

#endif // POINT_PREDICATES_HPP
