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

#ifndef DETERMINANT_HPP
#define DETERMINANT_HPP

namespace cg
{
  template< class Scalar >
  inline
  Scalar determinant(
    Scalar const &a00 )
  {
    Scalar const result = a00;
    return result;
  }

  template< class Scalar >
  inline
  Scalar determinant(
    Scalar const &a00, Scalar const &a01,
    Scalar const &a10, Scalar const &a11 )
  {
    Scalar const result = a00 * a11 - a10 * a01;
    return result;
  }

  template< class Scalar >
  inline
  Scalar determinant(
    Scalar const &a00, Scalar const &a01, Scalar const &a02,
    Scalar const &a10, Scalar const &a11, Scalar const &a12,
    Scalar const &a20, Scalar const &a21, Scalar const &a22 )
  {
    // Minors 2x2.
    Scalar const m00 = determinant(a11, a12,
                                   a21, a22);
    Scalar const m10 = determinant(a01, a02,
                                   a21, a22);
    Scalar const m20 = determinant(a01, a02,
                                   a11, a12);
    
    // Alternating-sign sum of minors.
    Scalar const result = a00 * m00 - a10 * m10 + a20 * m20;
    return result;
  }

  template< class Scalar >
  inline
  Scalar determinant(
    Scalar const &a00, Scalar const &a01, Scalar const &a02, Scalar const &a03,
    Scalar const &a10, Scalar const &a11, Scalar const &a12, Scalar const &a13,
    Scalar const &a20, Scalar const &a21, Scalar const &a22, Scalar const &a23,
    Scalar const &a30, Scalar const &a31, Scalar const &a32, Scalar const &a33 )
  {
    // Minors 2x2.
    Scalar const m00 = determinant(a11, a12, a13,
                                   a21, a22, a23,
                                   a31, a32, a33);
    Scalar const m10 = determinant(a01, a02, a03,
                                   a21, a22, a23,
                                   a31, a32, a33);
    Scalar const m20 = determinant(a01, a02, a03,
                                   a11, a12, a13,
                                   a31, a32, a33);
    Scalar const m30 = determinant(a01, a02, a03,
                                   a11, a12, a13,
                                   a21, a22, a23);
    
    // Alternating-sign sum of minors.
    Scalar const result = a00 * m00 - a10 * m10 + a20 * m20 - a30 * m30;
    return result;
  }
}

#endif // DETERMINANT_HPP
