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
#include <boost/tuple/tuple.hpp>
#include <boost/function.hpp>
#include <boost/iterator.hpp>
#include <boost/iterator/transform_iterator.hpp>
#include <boost/iterator/filter_iterator.hpp>

#include "point_predicates.hpp"

namespace dt
{
  template< class PointType >
  class delaunay_triangulation
  {
  public:
    typedef delaunay_triangulation<PointType> self_t;
    typedef PointType point_t;
    typedef boost::tuple<size_t, size_t, size_t> triangle_vertices_indices_t;

  protected:
    typedef size_t vertex_handle_t;
    typedef std::vector<point_t> vertex_buffer_t;

    // Common to all infinite triangles vertex.
    static vertex_handle_t const infinite_vertex = static_cast<size_t>(-1);

    typedef std::vector<vertex_handle_t> points_queue_t;

    typedef size_t triangle_handle_t;
    static triangle_handle_t const invalid_triangle = static_cast<size_t>(-1);

    struct triangle_t
    {
      // Infinite triangle has single infinite vertex.

      // Triangle vertices in CCW order.
      vertex_handle_t v[3];
      // Opposite to corresponding vertex triangle (for each triangle vertex).
      triangle_handle_t tr[3];

      triangle_t()
      {
        v[0] = infinite_vertex;
        v[1] = infinite_vertex;
        v[2] = infinite_vertex;
        tr[0] = invalid_triangle;
        tr[1] = invalid_triangle;
        tr[2] = invalid_triangle;
      }

      triangle_t( vertex_handle_t v0, 
                  vertex_handle_t v1,
                  vertex_handle_t v2,
                  triangle_handle_t tr0,
                  triangle_handle_t tr1,
                  triangle_handle_t tr2 )
      {
        v[0] = v0;
        v[1] = v1;
        v[2] = v2;
        tr[0] = tr0;
        tr[1] = tr1;
        tr[2] = tr2;
      }
    };

    typedef std::vector<triangle_t> triangles_t;

  public:
    delaunay_triangulation()
    {
      /*
      // Test data
      triangles_.push_back(triangle_t(0, 1, 2, 0, 0, 0));
      triangles_.push_back(triangle_t(3, -1, 5, 0, 0, 0));
      triangles_.push_back(triangle_t(2, 3, 5, 0, 0, 0));
       */
    }

  public:
    /*
     * Add point to triangulation.
     * Returns index of point vertex buffer.
     */
    size_t add_point( point_t const &p )
    {
      typedef vertex_buffer_t::const_iterator vertices_CI;
      if ((vertices_CI vIt = std::find(vertexBuffer_.begin(),
                                       vertexBuffer_.end(),
                                       p)) != vertexBuffer_.end())
      {
        // Point already added. Return old index.
        return std::distance(vertexBuffer_.begin(), vIt);
      }
      else
      {
        vertex_handle_t v = vertexBuffer_.size();
        vertexBuffer_.push_back(p);

        if (!is_initialized())
        {
          // Triangles structure not initialized yet.
          // This can be when number of points is less than three or all points
          // lies on same line.

          // Check wheter new point will make possible to construct triangles
          // structure.
          pointsQueue_.push_back(p);
          if (pointsQueue_.size() >= 3 &&
              !cg::exact_is_collinear(
                  point(pointsQueue_[pointsQueue_.size() - 0]),
                  point(pointsQueue_[pointsQueue_.size() - 1]),
                  point(pointsQueue_[pointsQueue_.size() - 2])))
          {
            initTrianglesStructure(
                pointsQueue_[pointsQueue_.size() - 0],
                pointsQueue_[pointsQueue_.size() - 1],
                pointsQueue_[pointsQueue_.size() - 2]);

            typedef points_queue_t::const_iterator points_CI;
            for (points_CI vIt = std::advance(pointsQueue_.rbegin(), 3);
                 vIt != pointsQueue_.rend();
                 ++vIt)
            {
              addPoint(*vIt);
            }

            pointsQueue_.clear();
          }
          else
          {
            // Still not possible to initialize triangles structure.
          }
        }
        else
        {
          addPoint(v);
        }

        return v;
      }
    }

    // Add points to triangulation.
    template< class FwdIt >
    void add_points( FwdIt first, FwdIt beyond )
    {
      std::for_each(first, beyond, boost::bind<size_t>(&self_t::add_point, _1));
    }

    size_t points_size() const
    {
      return vertexBuffer_.size();
    }
    
    point_t point( size_t idx ) const
    {
      return vertexBuffer_[idx];
    }

  protected:
    typedef boost::function<bool (triangle_t const &)>
        is_triangle_finite_pred;
    typedef boost::filter_iterator<is_triangle_finite_pred, 
                                   typename triangles_t::const_iterator>
        finite_triangles_it;
    typedef boost::function<triangle_vertices_indices_t (triangle_t const &)>
        extract_triangle_vertices_func;
    typedef boost::transform_iterator<extract_triangle_vertices_func,
                                      finite_triangles_it>
        extract_triangle_vertices_it;

  public:
    typedef extract_triangle_vertices_it triangles_const_iterator;

    triangles_const_iterator triangles_begin() const
    {
      is_triangle_finite_pred isFinitePred =
          (bool (*)(triangle_t const &))&self_t::is_finite;
      finite_triangles_it finiteTrianglesItBegin =
          finite_triangles_it(isFinitePred,
              triangles_.begin(), triangles_.end());
      extract_triangle_vertices_func extractTriangleFunc =
          &self_t::triangle_vertices;
      extract_triangle_vertices_it extractIt =
          extract_triangle_vertices_it(finiteTrianglesItBegin,
              extractTriangleFunc);
      return extractIt;
    }

    triangles_const_iterator triangles_end() const
    {
      is_triangle_finite_pred isFinitePred =
          (bool (*)(triangle_t const &))&self_t::is_finite;
      finite_triangles_it finiteTrianglesItEnd =
          finite_triangles_it(isFinitePred,
              triangles_.end(), triangles_.end());
      extract_triangle_vertices_func extractTriangleFunc =
          &self_t::triangle_vertices;
      extract_triangle_vertices_it extractIt =
          extract_triangle_vertices_it(finiteTrianglesItEnd,
              extractTriangleFunc);
      return extractIt;
    }

  protected:
    static bool is_finite( vertex_handle_t v )
    {
      return (v != infinite_vertex);
    }

    /*
     * Returns index of infinite vertex in triangle,
     * (size_t)-1 if triangle is finite.
     */
    static size_t infinite_vertex_idx( triangle_t const &tr )
    {
      if (!is_finite(tr.v[0]))
        return 0;
      else if (!is_finite(tr.v[1]))
        return 1;
      else if (!is_finite(tr.v[2]))
        return 2;
      else
        return static_cast<size_t>(-1);
    }

    static bool is_finite( triangle_t const &tr )
    {
      return (infinite_vertex_idx(tr) == static_cast<size_t>(-1));
    }

    static triangle_vertices_indices_t triangle_vertices( triangle_t const &tr )
    {
      return triangle_vertices_indices_t(tr.v[0], tr.v[1], tr.v[2]);
    }

    bool is_initialized() const
    {
      return !triangles_.empty();
    }

  protected:
    /*
     * Initializes triangles storage with single triangle (and three infinite
     * triangles).
     */
    void initTrianglesStructure( vertex_buffer_t v0,
                                 vertex_buffer_t v1,
                                 vertex_buffer_t v2 )
    {
      BOOST_ASSERT(!cg::exact_is_collinear(point(v0), point(v1), point(p2)));
    }

    void addVertex( vertex_handle_t v )
    {
      // Vertex v should not be in triangles storage.
    }

  protected:
    vertex_buffer_t vertexBuffer_;
    triangles_t     triangles_;

    points_queue_t  pointsQueue_;
  };
}

#endif // DELAUNAY_TRIANGULATION_HPP
