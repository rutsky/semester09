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

#ifndef DELAUNAY_TRIANGULATION_HPP
#define DELAUNAY_TRIANGULATION_HPP

#include <vector>
#include <list>
#include <algorithm>

#include <boost/bind.hpp>

namespace dt
{
  template< class PointType >
  class delaunay_triangulation
  {
  public:
    typedef delaunay_triangulation<PointType> self_t;
    typedef PointType point_t;

  protected:
    typedef size_t vertex_handle_t;
    typedef std::vector<point_t> vertex_buffer_t;

    // Common to all infinite triangles vertex.
    static vertex_handle_t const infinite_vertex = static_cast<size_t>(-1);

    typedef std::list<size_t> points_queue_t;

    typedef size_t triangle_handle_t;
    struct triangle_t
    {
      // Infinite triangle has single infinite vertex.

      // Triangle vertices in CCW order.
      vertex_handle_t v[3];
      // Opposite to corresponding vertex triangle (for each triangle vertex).
      triangle_handle_t t[3];
    };

    typedef std::vector<triangle_t> triangles_t;

    //struct

  public:
    // Add point to triangulation.
    void add_point( point_t const &p )
    {
      
    }

    // Add points to triangulation.
    template< class FwdIt >
    void add_points( FwdIt first, FwdIt beyond )
    {
      std::for_each(first, beyond, boost::bind<size_t>(&self_t::add_point, _1));
    }

    // TODO: Use boost::filter_iterator and boost::transform_iterator for
    // outputting result triangles (triples of vertices indices).

  protected:
    //xsize_t add_point_impl()

  protected:
    vertex_buffer_t vertexBuffer_;
    triangles_t     triangles_;

    points_queue_t  pointsQueue_;
  };
}

#endif // DELAUNAY_TRIANGULATION_HPP
