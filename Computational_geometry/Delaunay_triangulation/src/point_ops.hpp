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

#ifndef POINT_OPS_HPP
#define POINT_OPS_HPP

#include <boost/assert.hpp>
#include <boost/tuple/tuple.hpp>

#include "point.hpp"

namespace cg
{
  template< typename Scalar >
  inline
  boost::tuple<Scalar, Scalar> tuple( point_t<Scalar, 2> const &p )
  {
    return boost::tuple<Scalar, Scalar>(p.x, p.y);
  }

  template< typename Scalar, int Dim >
  inline
  bool operator == ( point_t<Scalar, Dim> const &p1,
                     point_t<Scalar, Dim> const &p2 )
  {
    for (size_t i = 0; i < Dim; ++i)
      if (p1[i] != p2[i])
        return false;

    return true;
  }

  template< typename Scalar, int Dim >
  inline
  point_t<Scalar, Dim>
      operator - ( point_t<Scalar, Dim> const &p1,
                   point_t<Scalar, Dim> const &p2 )
  {
    point_t<Scalar, Dim> result;

    for (size_t i = 0; i < Dim; ++i)
      result[i] = p1[i] - p2[i];

    return result;
  }

  template< typename Scalar, int Dim >
  inline
  point_t<Scalar, Dim>
      operator + ( point_t<Scalar, Dim> const &p1,
                   point_t<Scalar, Dim> const &p2 )
  {
    point_t<Scalar, Dim> result;

    for (size_t i = 0; i < Dim; ++i)
      result[i] = p1[i] + p2[i];

    return result;
  }

  template< typename Scalar, int Dim >
  inline
  point_t<Scalar, Dim>
      operator / ( point_t<Scalar, Dim> const &p,
                   Scalar v )
  {
    point_t<Scalar, Dim> result;

    for (size_t i = 0; i < Dim; ++i)
      result[i] = p[i] / v;

    return result;
  }
}

#endif // POINT_OPS_HPP
