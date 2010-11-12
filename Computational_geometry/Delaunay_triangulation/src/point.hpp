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

template<typename Scalar, int Dim>
struct point_t
{
};

template<typename Scalar>
struct point_t<Scalar, 2>
{
  typedef point_t<Scalar, 2> self_t;
  typedef Scalar scalar_t;

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
};

typedef point_t<double, 2> point_2;

#endif // POINT_HPP
