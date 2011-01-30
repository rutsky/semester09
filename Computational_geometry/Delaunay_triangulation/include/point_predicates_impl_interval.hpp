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

#ifndef POINT_PREDICATES_IMPL_INTERVAL_HPP
#define POINT_PREDICATES_IMPL_INTERVAL_HPP

#include <iomanip>

#include <boost/assert.hpp>
#include <boost/numeric/interval.hpp>

#include "xmath.hpp"
#include "point.hpp"
#include "point_io.hpp"
#include "point_ops.hpp"
#include "orientation.hpp"
#include "determinant.hpp"
#include "inexact_computations_ex.hpp"
#include "point_predicates_fwd.hpp"

#ifdef USE_CGAL_ON_INEXACT
#include "point_predicates_impl_cgal.hpp"
#endif // USE_CGAL_ON_INEXACT

namespace cg
{
  namespace interval_predicates
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
      typedef Scalar scalar_t;
      typedef boost::numeric::interval<scalar_t> interval_t;

      //                    p2
      //                      *   ^
      //                     /   /
      //                    /   /
      //                   /  v12
      // p0               /   /
      // *---------------*   /
      //                  p1
      //  <-----v10------
      //

      interval_t v10x, v10y, v12x, v12y;
      boost::tie(v10x, v10y) = tuple(p0);
      boost::tie(v12x, v12y) = tuple(p2);
      v10x -= p1.x;
      v10y -= p1.y;
      v12x -= p1.x;
      v12y -= p1.y;

      // determinant =
      //     | v10.x v10.y |
      //     | v12.x v12.y |
      interval_t const det =
          determinant(
               v10x, v10y,
               v12x, v12y);

      // DEBUG
      /*
      std::cout <<
      std::setiosflags(std::ios_base::fixed) <<
      std::setprecision(16) <<
      "exact_orientation(" << p0 << "," << p1 << "," << p2 << "):\n" <<
      "  from:\n" <<
      "    |" << v10x.lower() << " " << v10y.lower() << "|\n" <<
      "    |" << v12x.lower() << " " << v12y.lower() << "|\n" <<
      "  to:\n" <<
      "    |" << v10x.upper() << " " << v10y.upper() << "|\n" <<
      "    |" << v12x.upper() << " " << v12y.upper() << "|\n" <<
      "  determinant in\n"
      "    ("<< det.lower() << "," << det.upper() << ")\n";
       */
      
      if (det.lower() == scalar_t(0) && det.upper() == scalar_t(0))
      {
        return or_collinear;
      }
      else if (boost::numeric::zero_in(det))
      {
        // Determinant is close to zero, can't definitely say orientation while
        // computations are in current precision.

        std::cerr << std::setiosflags(std::ios_base::fixed) <<
            std::setprecision(16) <<
            "Warning: "
            "exact_orientation(" << p0 << ", " << p1 << ", " << p2 << "): " <<
            "Can't definitely detect orientation, "
                "determinant lies in the range " <<
            "(" << det.lower() << "," << det.upper() << ")\n";
#ifdef USE_CGAL_ON_INEXACT
        std::cerr << "Executing CGAL version.\n";
        return cgal_predicates::exact_orientation(p0, p1, p2);
#else
        throw inexact_computations_exception();
#endif
      }
      else if (det.lower() > 0)
      {
        return or_clockwise;
      }
      else
      {
        BOOST_ASSERT(det.upper() < 0);
        return or_counterclockwise;
      }
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
      orientation_t const orTriangle = cg::exact_orientation(p, q, r);
      BOOST_ASSERT(orTriangle != or_collinear);

      orientation_t const or0 = cg::exact_orientation(p, q, s);
      orientation_t const or1 = cg::exact_orientation(q, r, s);
      orientation_t const or2 = cg::exact_orientation(r, p, s);

      if (or0 == orTriangle && or1 == orTriangle && or2 == orTriangle)
      {
        // Point inside triangle.
        return orTriangle;
      }
      else if (or0 == or_collinear && 
               exact_is_collinear_points_lie_along_line(p, s, q))
      {
        // s in [p, q].
        return or_on_boundary;
      }
      else if (or1 == or_collinear &&
               exact_is_collinear_points_lie_along_line(q, s, r))
      {
        // s in [q, r].
        return or_on_boundary;
      }
      else if (or2 == or_collinear &&
               exact_is_collinear_points_lie_along_line(r, s, p))
      {
        // s in [r, p].
        return or_on_boundary;
      }
      else
      {
        // s outside of (p, q, r) triangle.
        return opposite(orTriangle);
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
    template< class Scalar >
    inline
    orientation_t exact_side_of_oriented_circle(
        point_t<Scalar, 2> const &p,
        point_t<Scalar, 2> const &q,
        point_t<Scalar, 2> const &r,
        point_t<Scalar, 2> const &s )
    {
      typedef Scalar scalar_t;
      typedef boost::numeric::interval<scalar_t> interval_t;

      interval_t px, py, qx, qy, rx, ry, sx, sy;
      boost::tie(px, py) = tuple(p);
      boost::tie(qx, qy) = tuple(q);
      boost::tie(rx, ry) = tuple(r);
      boost::tie(sx, sy) = tuple(s);

      interval_t const det = determinant(
          px, py, sqr(px) + sqr(py), interval_t(1),
          qx, qy, sqr(qx) + sqr(qy), interval_t(1),
          rx, ry, sqr(rx) + sqr(ry), interval_t(1),
          sx, sy, sqr(sx) + sqr(sy), interval_t(1));

      if (det.lower() == scalar_t(0) && det.upper() == scalar_t(0))
      {
        return or_on_boundary;
      }
      else if (boost::numeric::zero_in(det))
      {
        // Determinant is close to zero, can't definitely say orientation while
        // computations are in current precision.

        std::cerr <<
            std::setiosflags(std::ios_base::fixed) <<
            std::setprecision(16) <<
            "Warning: "
            "exact_side_of_oriented_circle(" <<
            p << ", " << q << ", " << r << ", " << s << "): " <<
            "Can't definitely detect orientation, "
            "determinant lies in range " <<
            "(" << det.lower() << "," << det.upper() << ")\n";

#ifdef USE_CGAL_ON_INEXACT
        std::cerr << "Executing CGAL version.\n";
        return cgal_predicates::exact_side_of_oriented_circle(p, q, r, s);
#else
        throw inexact_computations_exception();
#endif
      }
      else if (det.lower() > 0)
      {
        return or_on_positive_side;
      }
      else
      {
        BOOST_ASSERT(det.upper() < 0);
        return or_on_negative_side;
      }
    }
  }
}

#endif // POINT_PREDICATES_IMPL_INTERVAL_HPP
