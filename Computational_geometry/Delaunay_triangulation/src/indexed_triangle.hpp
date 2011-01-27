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

#ifndef INDEXED_TRIANGLE_HPP
#define INDEXED_TRIANGLE_HPP

#include <iostream>

#include <boost/tuple/tuple.hpp>

namespace cg
{
  struct triangle_vertices_indices_t
    : public boost::tuple<size_t, size_t, size_t>
  {
  private:
    typedef boost::tuple<size_t, size_t, size_t> base_t;

  public:
    triangle_vertices_indices_t()
      : base_t(static_cast<size_t>(-1),
               static_cast<size_t>(-1),
               static_cast<size_t>(-1))
    {
    }

    triangle_vertices_indices_t( size_t i0, size_t i1, size_t i2 )
      : base_t(i0, i1, i2)
    {
    }
  };

  // TODO: This is not proper place to put I/O.
  template< class CharT, class Traits >
  inline
  std::basic_ostream<CharT, Traits> &
    operator << ( std::basic_ostream<CharT, Traits> &os,
                  triangle_vertices_indices_t const &t )
  {
    os << t.get<0>() << " " << t.get<1>() << " " << t.get<2>() << "\n";

    return os;
  }

  template< class CharT, class Traits >
  inline
  std::basic_istream<CharT, Traits> &
    operator >> ( std::basic_istream<CharT, Traits> &is,
                  triangle_vertices_indices_t &t )
  {
    size_t i1, i2, i3;
    is >> i1 >> i2 >> i3;
    t = triangle_vertices_indices_t(i1, i2, i3);

    return is;
  }
}

#endif // INDEXED_TRIANGLE_HPP
