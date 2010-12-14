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

namespace cg
{
  template< typename Scalar, int Dim >
  struct point_t
  {
  };

  template< typename Scalar >
  struct point_t<Scalar, 2>
  {
    typedef point_t<Scalar, 2> self_t;
    typedef Scalar scalar_t;

    static int const dim = 2;

    scalar_t x, y;

    point_t()
      : x()
      , y()
    {
    }

    point_t( scalar_t x, scalar_t y )
      : x(x)
      , y(y)
    {
    }

    scalar_t const & operator [] ( int i ) const
    {
      BOOST_ASSERT(i >= 0 && i < dim);
      // TODO: We hope that padding is zero.
      return reinterpret_cast<scalar_t const *>(this)[i];
    }

    scalar_t       & operator [] ( int i )
    {
      BOOST_ASSERT(i >= 0 && i < dim);
      // TODO: We hope that padding is zero.
      return reinterpret_cast<scalar_t *>(this)[i];
    }
  };
}

#endif // POINT_OPS_HPP
