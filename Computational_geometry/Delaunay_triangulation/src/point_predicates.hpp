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

  /*
   * Returns orientation of PQR triangle vertices as seen from (0, 0, 1)
   * in right-hand coordinate system.
   */
  template<class Scalar>
  orientation_t exact_orientation( point_t<Scalar, 2> const &p,
                                   point_t<Scalar, 2> const &q,
                                   point_t<Scalar, 2> const &r )
  {
    typedef CGAL::Exact_predicates_inexact_constructions_kernel kernel_t;

    CGAL::Orientation const result = CGAL::SF_Orientation_2<kernel_t>()(
        construct_2d_point<kernel_t::Point_2>(p),
        construct_2d_point<kernel_t::Point_2>(q),
        construct_2d_point<kernel_t::Point_2>(r));
    
    if (result == CGAL::CLOCKWISE)
      return CLOCKWISE;
    else if (result == CGAL::COUNTERCLOCKWISE)
      return COUNTERCLOCKWISE;
    else
    {
      BOOST_ASSERT(result == CGAL::COLLINEAR);
      return COLLINEAR;
    }
  }
}

#endif // POINT_PREDICATES_HPP
