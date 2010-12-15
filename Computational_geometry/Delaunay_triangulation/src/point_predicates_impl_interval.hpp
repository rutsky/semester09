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

#ifndef POINT_PREDICATES_IMPL_INTERVAL_HPP
#define POINT_PREDICATES_IMPL_INTERVAL_HPP

#include <boost/assert.hpp>
#include <boost/numeric/interval.hpp>

#include "point.hpp"
#include "point_io.hpp"
#include "orientation.hpp"
#include "determinant.hpp"

namespace cg
{
  /*
   * Returns orientation of (p0, p1, p2) triangle vertices as seen from
   * (0, 0, 1) in right-hand coordinate system.
   */
  template<class Scalar>
  inline
  orientation_t exact_orientation( point_t<Scalar, 2> const &p0,
                                   point_t<Scalar, 2> const &p1,
                                   point_t<Scalar, 2> const &p2 )
  {
    typedef Scalar scalar_t;
    typedef boost::numeric::interval<scalar_t> interval_t;

    //                        v2
    //                      *
    //                     /
    //                    /
    //                   /
    // v0               /
    // *---------------*
    //                  v1

    interval_t v10x, v10y, v12x, v12y;
    v10x = p1.x;
    v10x -= p0.x;
    v10y = p1.y;
    v10y -= p0.y;
    v12x = p2.x;
    v12y -= p1.x;
    v12y = p2.y;
    v12y -= p1.y;

    // determinant =
    //     | v10.x v10.y |
    //     | v12.x v12.y |
    interval_t const det =
        cg::determinant(
             v10x, v10y,
             v12x, v12y);

    if (boost::numeric::zero_in(det))
    {
      // Determinant is close to zero, can't definitely say orientation while
      // computations are in current precision.

      //throw inexact_computations_exception();

      std::cout <<
          "Warning: "
          "exact_orientation(" << p0 << ", " << p1 << ", " << p2 << "): " <<
          "Can't definitely detect orientation, determinant lie in range " <<
          "(" << det.lower() << "," << det.upper() << ")\n";
      return or_collinear;
    }
    else if (det.lower() > 0)
    {
      return or_counterclockwise;
    }
    else
    {
      BOOST_ASSERT(det.upper() < 0);
      return or_clockwise;
    }
  }

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
      point_t<Scalar, 2> const &q )
  {
    // Based on exact_orientation() predicate.

    orientation_t const or2 = exact_orientation(p0, p1, q);
    orientation_t const or0 = exact_orientation(p1, p2, q);
    orientation_t const or1 = exact_orientation(p2, p0, q);

    if (or0 == or_collinear || or1 == or_collinear || or2 == or_collinear)
    {
      return or_on_boundary;
    }
    else if (or0 == or_clockwise && or1 == or_clockwise && or2 == or_clockwise)
    {
      return or_on_positive_side;
    }
    else
    {
      BOOST_ASSERT(or0 == or_counterclockwise &&
                   or1 == or_counterclockwise &&
                   or2 == or_counterclockwise);
      return or_on_negative_side;
    }
  }

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
      point_t<Scalar, 2> const &q )
  {
    typedef CGAL::Exact_predicates_inexact_constructions_kernel kernel_t;

    return CGAL::SF_Side_of_oriented_circle_2<kernel_t>()(
        construct_2d_point<kernel_t::Point_2>(p0),
        construct_2d_point<kernel_t::Point_2>(p1),
        construct_2d_point<kernel_t::Point_2>(p2),
        construct_2d_point<kernel_t::Point_2>(q));
  }
}

#endif // POINT_PREDICATES_IMPL_INTERVAL_HPP
