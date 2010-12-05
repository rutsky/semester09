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
#include <cmath>

#include <boost/bind.hpp>
#include <boost/tuple/tuple.hpp>
#include <boost/function.hpp>
#include <boost/iterator.hpp>
#include <boost/iterator/transform_iterator.hpp>
#include <boost/iterator/filter_iterator.hpp>

#include "point_predicates.hpp"
#include "utils.hpp"

namespace dt
{
  template< class PointType >
  class delaunay_triangulation
  {
  public:
    typedef delaunay_triangulation<PointType> self_t;
    typedef PointType point_t;
    typedef typename point_t::scalar_t scalar_t;
    typedef boost::tuple<size_t, size_t, size_t> triangle_vertices_indices_t;

  protected:
    typedef size_t vertex_handle_t;
    typedef std::vector<point_t> vertex_buffer_t;

    // Common to all infinite triangles vertex.
    static vertex_handle_t const invalid_vertex_handle = static_cast<size_t>(-1);

    typedef size_t triangle_handle_t;
    static triangle_handle_t const invalid_triangle_handle = static_cast<size_t>(-1);

    struct triangle_t
    {
      // Triangle vertices in CCW order.
      vertex_handle_t v[3];
      // Opposite to corresponding vertex triangle (for each triangle vertex).
      triangle_handle_t tr[3];
      // When triangle is subdivided by inserting new vertex or flipping edges
      // this field contains new overlapped triangles, which substituted
      // current triangle.
      triangle_handle_t childTr[3];

      triangle_t()
      {
        reset_triangle();
      }

      triangle_t( vertex_handle_t v0,
                  vertex_handle_t v1,
                  vertex_handle_t v2 )
      {
        reset_triangle();
        v[0] = v0;
        v[1] = v1;
        v[2] = v2;
      }

      triangle_t( vertex_handle_t v0, 
                  vertex_handle_t v1,
                  vertex_handle_t v2,
                  triangle_handle_t tr0,
                  triangle_handle_t tr1,
                  triangle_handle_t tr2 )
      {
        reset_triangle();
        v[0] = v0;
        v[1] = v1;
        v[2] = v2;
        tr[0] = tr0;
        tr[1] = tr1;
        tr[2] = tr2;
      }

      void reset_triangle()
      {
        for (size_t i = 0; i < 3; ++i)
        {
          v[i] = invalid_vertex_handle;
          tr[i] = invalid_triangle_handle;
          childTr[i] = invalid_triangle_handle;
        }
      }

      vertex_handle_t   vertex( int idx ) const
      {
        return v[(3 + (idx % 3)) % 3];
      }

      vertex_handle_t & vertex( int idx )
      {
        return v[(3 + (idx % 3)) % 3];
      }

      triangle_handle_t   triangle( int idx ) const
      {
        return tr[(3 + (idx % 3)) % 3];
      }

      triangle_handle_t & triangle( int idx )
      {
        return tr[(3 + (idx % 3)) % 3];
      }

      triangle_handle_t   child_triangle( size_t idx ) const
      {
        BOOST_ASSERT(idx < children_num());
        return childTr[idx];
      }

      triangle_handle_t & child_triangle( size_t idx )
      {
        BOOST_ASSERT(idx < children_num());
        return childTr[idx];
      }

      void set_child( triangle_handle_t ch0, triangle_handle_t ch1 )
      {
        BOOST_ASSERT(!has_children());
        childTr[0] = ch0;
        childTr[1] = ch1;
      }

      void set_child( triangle_handle_t ch0,
                      triangle_handle_t ch1,
                      triangle_handle_t ch2 )
      {
        BOOST_ASSERT(!has_children());
        childTr[0] = ch0;
        childTr[1] = ch1;
        childTr[2] = ch2;
      }

      int vertex_index( vertex_handle_t vh ) const
      {
        for (size_t i = 0; i < 3; ++i)
          if (v[i] == vh)
            return i;

        BOOST_VERIFY(false);
        return -1;
      }

      int triangle_index( triangle_handle_t trh ) const
      {
        for (size_t i = 0; i < 3; ++i)
          if (tr[i] == trh)
            return i;

        BOOST_VERIFY(false);
        return -1;
      }

      size_t children_num() const
      {
        size_t i(0);
        for (; childTr[i] != invalid_triangle_handle && i < 3; ++i)
          ;
        return i;
      }

      bool has_children() const
      {
        return children_num() != 0;
      }

      void replace_neighbor(triangle_handle_t oldTrH, triangle_handle_t newTrH)
      {
        bool found = false;
        for (size_t i = 0; i < 3; ++i)
        {
          if (tr[i] == oldTrH)
          {
            tr[i] = newTrH;
            found = true;
            break;
          }
        }
        BOOST_ASSERT(found);
      }
    };

    typedef std::vector<triangle_t> triangles_t;

  public:
    template< class PointFwdIt >
    delaunay_triangulation( PointFwdIt first, PointFwdIt beyond )
      : vertexBuffer_(first, beyond)
    {
      if (vertexBuffer_.empty())
      {
        // Empty input.
        return;
      }

      // Calculate points bounding box.
      point_t loPoint, hiPoint;
      boost::tie(loPoint, hiPoint) = 
          cg::axis_aligned_bounding_box(vertexBuffer_.begin(),
                                        vertexBuffer_.end());

      // Construct imaginary triangle that contains all points.
      
      // TODO: Not safe for floating point overflow.
      // TODO: Use something instead of sqrt(2.0) etc.
      
      scalar_t const extraSpace = 10.0;
      scalar_t const boundingSquareSize =
              std::max((hiPoint - loPoint).x, (hiPoint - loPoint).y) + extraSpace;
      point_t const center_point = (hiPoint + loPoint) / 2.0;
      // Inscribed circle radius:
      scalar_t const r = boundingSquareSize * std::sqrt(2.0) / 2.0;
      // Triangle side size:
      scalar_t const a = 2.0 * sqrt(3.0) * r;
      // Circumscribed circle radius:
      scalar_t const R = a / sqrt(3.0);
      point_t const leftAnglePoint  = center_point + point_t(-a / 2.0, -r);
      point_t const rightAnglePoint = center_point + point_t( a / 2.0, -r);
      point_t const topAnglePoint   = center_point + point_t(       0,  R);

      vertex_handle_t const leftAngleVH  = vertexBuffer_.size();
      vertexBuffer_.push_back(leftAnglePoint);
      vertex_handle_t const rightAngleVH = vertexBuffer_.size();
      vertexBuffer_.push_back(rightAnglePoint);
      vertex_handle_t const topAngleVH   = vertexBuffer_.size();
      vertexBuffer_.push_back(topAnglePoint);

      // Insert first triangle that contains all points.
      triangles_.push_back(triangle_t(leftAngleVH, rightAngleVH, topAngleVH));

      // Insert input points.
      for (vertex_handle_t vh = 0; vh < vertexBuffer_.size() - 3; ++vh)
        addVertex(vh);
    }

  public:
    size_t points_size() const
    {
      // Last 3 points from imaginary triangle that contains all points.
      return vertexBuffer_.size() - 3;
    }
    
    point_t point( size_t idx ) const
    {
      BOOST_ASSERT(idx < points_size());
      return vertexBuffer_[idx];
    }

  protected:
    triangle_t const & triangle( triangle_handle_t tr ) const
    {
      return triangles_.at(tr);
    }

    triangle_t       & triangle( triangle_handle_t tr )
    {
      return triangles_.at(tr);
    }

  protected:
    typedef boost::function<bool (triangle_t const &)>
        is_triangle_real_pred;
    typedef boost::filter_iterator<is_triangle_real_pred,
                                   typename triangles_t::const_iterator>
        real_triangles_it;
    typedef boost::function<triangle_vertices_indices_t (triangle_t const &)>
        extract_triangle_vertices_func;
    typedef boost::transform_iterator<extract_triangle_vertices_func,
                                      real_triangles_it>
        extract_triangle_vertices_it;

  public:
    typedef extract_triangle_vertices_it triangles_const_iterator;

    triangles_const_iterator triangles_begin() const
    {
      is_triangle_real_pred isTriangleRealPred =
         boost::bind(&self_t::isTriangleReal, *this, _1);
      real_triangles_it realTrianglesItBegin =
          real_triangles_it(isTriangleRealPred,
              triangles_.begin(), triangles_.end());
      extract_triangle_vertices_func extractTriangleFunc =
          &self_t::triangle_vertices;
      extract_triangle_vertices_it extractIt =
          extract_triangle_vertices_it(realTrianglesItBegin,
              extractTriangleFunc);
      return extractIt;
    }

    triangles_const_iterator triangles_end() const
    {
      is_triangle_real_pred isTriangleRealPred =
         boost::bind(&self_t::isTriangleReal, *this, _1);
      real_triangles_it realTrianglesItEnd =
          real_triangles_it(isTriangleRealPred,
              triangles_.end(), triangles_.end());
      extract_triangle_vertices_func extractTriangleFunc =
          &self_t::triangle_vertices;
      extract_triangle_vertices_it extractIt =
          extract_triangle_vertices_it(realTrianglesItEnd,
              extractTriangleFunc);
      return extractIt;
    }

  protected:
    static triangle_vertices_indices_t triangle_vertices( triangle_t const &tr )
    {
      return triangle_vertices_indices_t(tr.v[0], tr.v[1], tr.v[2]);
    }

    bool isRealTriangle( triangle_t const &tr )
    {
      return !tr.has_children() && 
              tr.vertex(0) < points_size() &&
              tr.vertex(1) < points_size() &&
              tr.vertex(2) < points_size();
    }

  protected:
    // Only flip edge that is opposite to vertex with provided index.
    void flip( triangle_handle_t trh, int const idx )
    {
      BOOST_ASSERT(exact_side_of_oriented_triangle(
              trh, triangle(trh).vertex(idx)) == cg::ON_POSITIVE_SIDE);

      triangle_t &parentTr = triangle(trh);
      triangle_t &neighTr = parentTr.triangle(idx);
      int const neighIdx = neighTr.triangle_index(trh);

      BOOST_ASSERT(!parentTr.has_children());
      BOOST_ASSERT(!neighTr.has_children());

      //
      //            *                                   *
      //           /|\                                 / \
      //          / | \                               /   \
      //         /  |  \                             /     \
      // trh -> /   |   \                           /  ch0  \
      //       /    |    \                         /         \
      //      /     |     \                       /           \
      //     *      |      *          ->         *-------------*
      // idx  \     |     /  neighIdx             \           /
      //       \    |    /                         \   ch1   /
      //        \   |   /                           \       /
      //         \  |  /                             \     /
      //          \ | /                               \   /
      //           \|/                                 \ /
      //            *                                   *
      //
      triangle_handle_t const ch0 = triangles_.size() + 0;
      triangle_handle_t const ch1 = triangles_.size() + 1;
      triangles_.push_back(triangle_t( // ch0
          parentTr.vertex(idx - 1),
              parentTr.vertex(idx),
                  neighTr.vertex(neighIdx),
          ch1,
              neighTr.triangle(neighIdx - 1),
                  parentTr.triangle(idx + 1)));
      triangles_.push_back(triangle_t( // ch1
          parentTr.vertex(idx),
              parentTr.vertex(idx + 1),
                  neighTr.vertex(neighIdx),
          neighTr.triangle(neighIdx + 1),
              ch0,
                  parentTr.triangle(idx - 1)));

      // Link neighbors.
      triangle(parentTr.triangle(idx + 1)).replace_neighbor(trh, ch0);
      triangle(parentTr.triangle(idx - 1)).replace_neighbor(trh, ch1);
      triangle(neighTr.triangle(neighIdx + 1)).replace_neighbor(neightTrH, ch1);
      triangle(neighTr.triangle(neighIdx - 1)).replace_neighbor(neightTrH, ch0);

      // Link child triangles to parent.
      parentTr.set_childs(ch0, ch1);
      neighTr. set_childs(ch0, ch1);
    }

    // Flip edge opposite to provided vertex hanlde if needed.
    void restoreDelaunay( triangle_handle_t trh, vertex_handle_t vh )
    {
      BOOST_ASSERT(trh != invalid_triangle_handle);
      BOOST_ASSERT(vh != invalid_vertex_handle);
      BOOST_ASSERT(triangle(trh).vertex_index(vh) >= 0);
      BOOST_ASSERT(!triangle(trh).has_children());

      if (exact_side_of_oriented_triangle(trh, vh) == cg::ON_POSITIVE_SIDE)
      {
        // Point inside triangle - must flip.
        flip(trh, triangle(trh).vertex_index(vh));
        BOOST_ASSERT(triangle(trh).children_num() == 2);

        // After flip 2 newly created triangles are childs of current trianle.
        restoreDelaunay(triangle(trh).childTr[0], vh);
        restoreDelaunay(triangle(trh).childTr[1], vh);
      }
      else
      {
        // Point NOT inside triangle - point is outside of triangle or
        // on its bounding - thats ok.
      }
    }

    // Add new vertex to interior of triangle.
    void addVertexToTriangleInterior( triangle_handle_t trh, vertex_handle_t vh )
    {
      BOOST_ASSERT(exact_side_of_oriented_triangle(
              trh, vh) == cg::ON_POSITIVE_SIDE);
      BOOST_ASSERT(!triangle(trh).has_children());

      // Create new 3 triangles inside parent triangle.
      //
      //                     0
      //                     *
      //                    /'\
      //                   / ' \
      //                  /  '  \
      //                 /   '   \
      //                /    '    \
      //               /     '     \
      //              /      '      \
      //             /       '       \
      //            /  ch0   '  ch2   \
      //           /         '         \
      //          /          * vh       \
      //         /        ''' '''        \
      //        /      '''       '''      \
      //       /    '''             '''    \
      //      /  '''       ch1         '''  \
      //     /'''                         '' \
      //  1 *---------------------------------* 2
      //
      triangle_handle_t const ch0 = triangles_.size() + 0;
      triangle_handle_t const ch1 = triangles_.size() + 1;
      triangle_handle_t const ch2 = triangles_.size() + 2;
      triangles_.push_back(triangle_t(
          parentTr.vertex(0), parentTr.vertex(1), vh,
          ch1,                ch2,                parentTr.tr[2]));
      triangles_.push_back(triangle_t(
          parentTr.vertex(1), parentTr.vertex(2), vh,
          ch2,                ch0,                parentTr.tr[0]));
      triangles_.push_back(triangle_t(
          parentTr.vertex(2), parentTr.vertex(0), vh,
          ch0,                ch1,                parentTr.tr[1]));

      // Link neighbors of parent triangle to new triangles.
      triangle(parentTr.tr[0]).replace_neighbor(trh, ch1);
      triangle(parentTr.tr[1]).replace_neighbor(trh, ch2);
      triangle(parentTr.tr[2]).replace_neighbor(trh, ch0);

      // Link child triangles to parent.
      parentTr.set_childs(ch0, ch1, ch2);
    }

    // Add new vertex to triangle edge.
    void addVertexToTriangleEdge( triangle_handle_t trh, vertex_handle_t vh,
                                  int idx )
    {
      BOOST_ASSERT(exact_side_of_oriented_triangle(
              trh, vh) == cg::ON_ORIENTED_BOUNDARY);
      BOOST_ASSERT(exact_orientation(
                vertex(triangle(trh).vertex(idx + 1),
                vertex(triangle(trh).vertex(idx + 2)),
                vertex(vh)) == cg::COLLINEAR);

      triangle_t &parentTr = triangle(trh);

      triangle_handle_t const neightTrH = parentTr.tr[idx];
      triangle_t &neighTr = triangle(neightTrH);
      int const neighIdx = neighTr.triangle_index(trh);

      BOOST_ASSERT(!triangle(trh).has_children());
      BOOST_ASSERT(!triangle(neightTrH).has_children());

      // Create new 4 triangles inside parent triangle and it's neighbour.
      //
      // neighIdx *-------------------*
      //           \ ''              / \
      //            \  ''    ch3    /   \
      //             \    ''       /     \
      //              \     ''  vh/  ch0  \
      //  neightTr ->  \ ch2   ' *         \  <- parentTr (trh)
      //                \       /  '''      \
      //                 \     /      ''     \
      //                  \   /   ch1    ''   \
      //                   \ /             ''  \
      //                    *------------------* idx
      //
      triangle_handle_t const ch0 = triangles_.size() + 0;
      triangle_handle_t const ch1 = triangles_.size() + 1;
      triangle_handle_t const ch2 = triangles_.size() + 2;
      triangle_handle_t const ch3 = triangles_.size() + 3;
      triangles_.push_back(triangle_t( // ch0
          parentTr.vertex(idx),
              parentTr.vertex(idx + 1),
                  vh,
          ch3,
              ch1,
                  parentTr.triangle(idx - 1)));
      triangles_.push_back(triangle_t( // ch1
          parentTr.vertex(idx - 1),
              parentTr.vertex(idx),
                  vh,
          ch0,
              ch2,
                  parentTr.triangle(idx + 1)));
      triangles_.push_back(triangle_t( // ch2
          neighTr.vertex(neighIdx),
              neighTr.vertex(neighIdx + 1),
                  vh,
          ch1,
              ch3,
                  neighTr.vertex(neighIdx - 1)));
      triangles_.push_back(triangle_t( // ch3
          neighTr.vertex(neighIdx - 1),
              neighTr.vertex(neighIdx),
                  vh,
          ch2,
              ch0,
                  neighTr.vertex(neighIdx + 1)));

      // Link neighbors.
      triangle(parentTr.triangle(idx + 1)).replace_neighbor(trh, ch1);
      triangle(parentTr.triangle(idx - 1)).replace_neighbor(trh, ch0);
      triangle(neighTr.triangle(neighIdx + 1)).replace_neighbor(neightTrH, ch3);
      triangle(neighTr.triangle(neighIdx - 1)).replace_neighbor(neightTrH, ch2);

      // Link child triangles to parent.
      parentTr.set_childs(ch0, ch1);
      neighTr. set_childs(ch2, ch3);
    }

    void addVertex( vertex_handle_t vh )
    {
      // Locate triangle in which new vertex resides.
      location_t loc;
      triangle_handle_t trh;
      boost::tie(loc, trh) = locate(vh);

      if (loc == loc_triangle)
      {
        // Vertex in interior of triangle.
        addVertexToTriangleInterior(trh, vh);
        BOOST_ASSERT(triangle(trh).children_num() == 3);

        // Restore Delaunay property.
        restoreDelaunay(triangle(trh).ch, vh);
        restoreDelaunay(ch1, vh);
        restoreDelaunay(ch2, vh);
      }
      else if (loc == loc_edge)
      {
        // Vertex on triangle edge.

        // Locate triangle edge on which vertex is lying.
        boost::optional<int> adjTrIdxPtr;
        for (size_t i = 0; i < 3; ++i)
          if (exact_orientation(
                vertex(triangle(trh).vertex(i),
                vertex(triangle(trh).vertex(i + 1)),
                vertex(vh)) == cg::COLLINEAR))
          {
            adjTrIdxPtr = i - 1;
            break;
          }
        BOOST_ASSERT(adjTrIdxPtr);

        triangle_handle_t const neighTrH = triangle(trh).triangle(*adjTrIdxPtr);
        addVertexToTriangleEdge(trh, vh, *adjTrIdxPtr);
        BOOST_ASSERT(triangle(trh).children_num() == 2);
        BOOST_ASSERT(triangle(neighTrH).children_num() == 2);

        // Restore Delaunay property.
        restoreDelaunay(triangle(trh).child_triangle(0), vh);
        restoreDelaunay(triangle(trh).child_triangle(1), vh);
        restoreDelaunay(triangle(neighTrH).child_triangle(0), vh);
        restoreDelaunay(triangle(neighTrH).child_triangle(1), vh);
      }
      else
      {
        BOOST_ASSERT(loc == loc_vertex);
        
        // Duplicate vertex. Skipping.
        // DEBUG
        std::cout << "Warning: duplicate vertex #" << vh << ": " << point(vh) << "\n";
      }
    }

    cg::orientation_t exact_side_of_oriented_triangle(
        triangle_handle_t trh, vertex_handle_t vh )
    {
      return exact_side_of_oriented_triangle(
          vertex(triangle(tr).v[0]),
          vertex(triangle(tr).v[1]),
          vertex(triangle(tr).v[2]),
          vertex(vh));
    }

    enum location_t
    {
      loc_triangle = 0,
      loc_edge,
      loc_vertex,
    };

    std::pair<location_t, triangle_handle_t> locate( vertex_handle_t vh )
    {
      BOOST_ASSERT(!triangles_.empty());

      // Start search from first imaginary triangle that contains all points.
      triangle_handle_t trh = 0;
      while (true)
      {
        triangle_t const &tr = triangle(trh);

        // Assert that vertex inside or on boundary of current triangle.
        BOOST_ASSERT(exact_side_of_oriented_triangle(trh, vh) != ON_NEGATIVE_SIDE);

        if (!tr.has_children())
        {
          // Triangle without children.
          // Determine whether vertex lies on triangle edge or in triangle
          // interior and return result.

          cg::orientation_t const orient = 
              exact_side_of_oriented_triangle(trh, vh);
          if (orient == ON_POSITIVE_SIDE)
          {
            return std::make_pair(loc_triangle, trh);
          }
          else if (orient == ON_ORIENTED_BOUNDARY)
          {
            return std::make_pair(loc_edge, trh);
          }
          else
          {
            BOOST_ASSERT(
                    vertex(vh) == vertex(tr.v[0]) ||
                    vertex(vh) == vertex(tr.v[1]) ||
                    vertex(vh) == vertex(tr.v[2]));
            return std::make_pair(loc_vertex, trh);
          }
        }
        else
        {
          // Triangle has children.
          // Determine in which child lies vertex and continue loop.

          boost::optional<vertex_buffer_t> nextVH;
          for (childIdx = 0; childIdx < tr.children_num(); ++childIdx)
          {
            if (exact_side_of_oriented_triangle(tr.child_triangle(childIdx),
                                                vh) != ON_NEGATIVE_SIDE)
            {
              // Found child triangle that contains current vertex.
              nextVH = tr.childTr[childIdx];
              break;
            }
          }
          trh = nextVH.get();
        }
      }
    }

  protected:
    // Input vertices plus three vertices of containing all points
    // imaginary triangle.
    vertex_buffer_t vertexBuffer_;
    // First triangle is containing all points imaginary triangle.
    triangles_t     triangles_;
  };
}

#endif // DELAUNAY_TRIANGULATION_HPP
