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

#ifndef POINT_IO_HPP
#define POINT_IO_HPP

#include <iostream>

#include "point.hpp"

namespace cg
{
  template< class CharT, class Traits, typename Scalar, int Dim >
  inline
  std::basic_ostream<CharT, Traits> &
    operator << ( std::basic_ostream<CharT, Traits> &os, point_t<Scalar, Dim> const &p )
  {
    os << "(";
    for (int i = 0; i < Dim - 1; ++i)
      os << p[i] << ",";
    os << p[Dim - 1] << ")";

    return os;
  }
}

#endif // POINT_IO_HPP