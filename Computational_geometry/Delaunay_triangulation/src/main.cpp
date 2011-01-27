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

#include <iostream>

#include <boost/tuple/tuple_io.hpp>
#include <boost/tuple/tuple_comparison.hpp>

#include "delaunay_triangulation.hpp"
#include "point.hpp"
#include "point_io.hpp"
#include "point_predicates.hpp"
#include "point_types.hpp"

typedef dt::delaunay_triangulation<cg::point_2> triangulation_t;

template< class CharT, class Traits >
inline
std::basic_ostream<CharT, Traits> &
  operator << ( std::basic_ostream<CharT, Traits> &os, 
                triangulation_t::triangle_vertices_indices_t const &t )
{
  os << t.get<0>() << t.get<1>() << t.get<2>();
  
  return os;
}

int main()
{
  // Reset random counter (for stable testing).
  // TODO: Not necessarilly defines determined shuffling of points.
  std::srand(0);

  triangulation_t triangulation(std::istream_iterator<cg::point_2>(std::cin),
                                std::istream_iterator<cg::point_2>());

  typedef
    std::ostream_iterator<triangulation_t::triangle_vertices_indices_t>
    out_iterator_t;
  std::copy(triangulation.begin(), triangulation.end(),
    out_iterator_t(std::cout, "\n"));
}
