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

#ifndef POINT_HPP
#define POINT_HPP

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

  template< typename Scalar, int Dim >
  point_t<Scalar, Dim> operator + ( point_t<Scalar, Dim> const &a, point_t<Scalar, Dim> const &b )
  {
    point_t<Scalar, Dim> result;
    for (size_t i = 0; i < Dim; ++i)
      result[i] = a[i] + b[i];
    return result;
  }

  template< typename Scalar, int Dim >
  point_t<Scalar, Dim> operator - ( point_t<Scalar, Dim> const &a, point_t<Scalar, Dim> const &b )
  {
    point_t<Scalar, Dim> result;
    for (size_t i = 0; i < Dim; ++i)
      result[i] = a[i] - b[i];
    return result;
  }

  template< typename Scalar, int Dim, typename OpScalar >
  point_t<Scalar, Dim> operator * ( point_t<Scalar, Dim> const &a, OpScalar const &c )
  {
    point_t<Scalar, Dim> result;
    for (size_t i = 0; i < Dim; ++i)
      result[i] = a[i] * c;
    return result;
  }

  template< typename Scalar, int Dim, typename OpScalar >
  point_t<Scalar, Dim> operator * ( OpScalar const &c, point_t<Scalar, Dim> const &a )
  {
    point_t<Scalar, Dim> result;
    for (size_t i = 0; i < Dim; ++i)
      result[i] = c * a[i];
    return result;
  }

  template< typename Scalar, int Dim, typename OpScalar >
  point_t<Scalar, Dim> operator / ( point_t<Scalar, Dim> const &a, OpScalar const &c )
  {
    point_t<Scalar, Dim> result;
    for (size_t i = 0; i < Dim; ++i)
      result[i] = a[i] / c;
    return result;
  }

  template< typename Scalar, int Dim >
  bool operator == ( point_t<Scalar, Dim> const &a, point_t<Scalar, Dim> const &b )
  {
    for (size_t i = 0; i < Dim; ++i)
      if (a[i] != b[i])
        return false;
    return true;
  }

  typedef point_t<double, 2> point_2;

  template< class DestPointType, class SrcPointType >
  DestPointType construct_2d_point( SrcPointType const &p )
  {
    return DestPointType(p.x, p.y);
  }
}

#endif // POINT_HPP
