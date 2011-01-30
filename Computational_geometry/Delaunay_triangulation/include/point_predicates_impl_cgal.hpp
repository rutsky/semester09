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

#ifndef POINT_PREDICATES_IMPL_CGAL_HPP
#define POINT_PREDICATES_IMPL_CGAL_HPP

#ifdef HAVE_CGAL

#include <CGAL/Exact_predicates_inexact_constructions_kernel.h>
#include <CGAL/Filtered_predicate.h>

#include "point.hpp"
#include "orientation.hpp"
#include "point_utils.hpp"

// In orientation.hpp assumed, that orientation_t constant values equal
// to corresponded CGAL Sign enumeration constants.

namespace cg
{
  namespace cgal_predicates
  {
    /*
     * Returns orientation of (p0, p1, p2) triangle vertices as seen from
     * (0, 0, 1) in right-hand coordinate system.
     */
    template< class Scalar >
    inline
    orientation_t exact_orientation(
        point_t<Scalar, 2> const &p0,
        point_t<Scalar, 2> const &p1,
        point_t<Scalar, 2> const &p2 )
    {
      typedef CGAL::Exact_predicates_inexact_constructions_kernel kernel_t;

      return from_cgal(CGAL::SF_Orientation_2<kernel_t>()(
          construct_2d_point<kernel_t::Point_2>(p0),
          construct_2d_point<kernel_t::Point_2>(p1),
          construct_2d_point<kernel_t::Point_2>(p2)));
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
    template< class Scalar >
    inline
    orientation_t exact_side_of_oriented_triangle(
        point_t<Scalar, 2> const &p0,
        point_t<Scalar, 2> const &p1,
        point_t<Scalar, 2> const &p2,
        point_t<Scalar, 2> const &q )
    {
      typedef CGAL::Exact_predicates_inexact_constructions_kernel kernel_t;

      return from_cgal(CGAL::Triangle_2<kernel_t>(
          construct_2d_point<kernel_t::Point_2>(p0),
          construct_2d_point<kernel_t::Point_2>(p1),
          construct_2d_point<kernel_t::Point_2>(p2)).oriented_side(
              construct_2d_point<kernel_t::Point_2>(q)));
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

      return from_cgal(CGAL::SF_Side_of_oriented_circle_2<kernel_t>()(
          construct_2d_point<kernel_t::Point_2>(p0),
          construct_2d_point<kernel_t::Point_2>(p1),
          construct_2d_point<kernel_t::Point_2>(p2),
          construct_2d_point<kernel_t::Point_2>(q)));
    }
  }
}

#endif // HAVE_CGAL

#endif // POINT_PREDICATES_IMPL_CGAL_HPP
