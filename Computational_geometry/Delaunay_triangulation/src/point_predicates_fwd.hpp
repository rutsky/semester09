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

#ifndef POINT_PREDICATES_FWD_HPP
#define POINT_PREDICATES_FWD_HPP

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
                                   point_t<Scalar, 2> const &p2 );

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
      point_t<Scalar, 2> const &p0,
      point_t<Scalar, 2> const &p1,
      point_t<Scalar, 2> const &p2,
      point_t<Scalar, 2> const &q );

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
      point_t<Scalar, 2> const &s );

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
                           point_t<Scalar, 2> const &p2 );

  /*
   * Returns true if p2 lies on the right side of line (p0,p1).
   */
  template< class Scalar >
  inline
  bool exact_is_right_turn( point_t<Scalar, 2> const &p0,
                            point_t<Scalar, 2> const &p1,
                            point_t<Scalar, 2> const &p2 );

  /*
   * Returns true if p2 lies on the line (p0,p1).
   */
  template< class Scalar >
  inline
  bool exact_is_collinear( point_t<Scalar, 2> const &p0,
                           point_t<Scalar, 2> const &p1,
                           point_t<Scalar, 2> const &p2 );

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
      point_t<Scalar, 2> const &p2 );
}

#endif // POINT_PREDICATES_FWD_HPP
