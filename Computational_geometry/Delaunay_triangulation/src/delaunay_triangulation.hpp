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

#ifndef DELAUNAY_TRIANGULATION_HPP
#define DELAUNAY_TRIANGULATION_HPP

#include <vector>
#include <list>
#include <algorithm>
#include <cmath>
#include <iostream>

#include <boost/bind.hpp>
#include <boost/tuple/tuple.hpp>
#include <boost/function.hpp>
#include <boost/iterator.hpp>
#include <boost/optional.hpp>
#include <boost/iterator/transform_iterator.hpp>
#include <boost/iterator/filter_iterator.hpp>

#include "point_predicates.hpp"
#include "point_io.hpp"
#include "point_ops.hpp"
#include "utils.hpp"

// TODO: For determined points shuffling random generator should be passed
// to triangulation.

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
    static vertex_handle_t const invalid_vertex_handle =
        static_cast<size_t>(-1);

    typedef size_t triangle_handle_t;
    static triangle_handle_t const invalid_triangle_handle =
        static_cast<size_t>(-1);

    struct triangle_t
    {
      // Triangle vertices in CCW order.
      vertex_handle_t v[3];
      // TODO: Use fixed size container, like boost::tuple or boost::array.
      // TODO: Close access to data members (access should be done using
      // getters)
      // TODO: Rename members.

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
        // TODO: Use some modular arithmetics library.
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

      void set_children( triangle_handle_t ch0, triangle_handle_t ch1 )
      {
        BOOST_ASSERT(!has_children());
        childTr[0] = ch0;
        childTr[1] = ch1;
      }

      void set_children( triangle_handle_t ch0,
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

      int infinite_vertex_index() const
      {
        for (size_t i = 0; i < 3; ++i)
          if (!isFiniteVertex(v[i]))
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

      void replace_neighbor( 
          triangle_handle_t oldTrH,
          triangle_handle_t newTrH )
      {
        triangle(triangle_index(oldTrH)) = newTrH;
      }
    };

    typedef std::vector<triangle_t> triangles_t;

  public:
    template< class PointInIt >
    delaunay_triangulation( PointInIt first, PointInIt beyond )
    {
      if (first == beyond)
      {
        // Empty input.
        return;
      }

      // Prepare space for border vertices.
      vertexBuffer_.resize(3);

      // Copy input data at end.
      std::copy(first, beyond, std::back_inserter(vertexBuffer_));

      // Calculate points bounding box.
      point_t loPoint, hiPoint;
      boost::tie(loPoint, hiPoint) = 
          cg::axis_aligned_bounding_box(vertexBuffer_.begin() + 3,
                                        vertexBuffer_.end());

      // Construct imaginary triangle that contains all points.
      
      // TODO: Not safe for floating point overflow.
      // TODO: Use something instead of sqrt(2.0) etc.
      // NOTE: Exact bounding triangle is not really needed, but when it exact
      // we can be sure that triangle is really bounding.
      
      scalar_t const extraSpace = 10.0;
      scalar_t const boundingSquareSize =
              std::max((hiPoint - loPoint).x,
                       (hiPoint - loPoint).y) + extraSpace;
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

      vertexBuffer_[0] = leftAnglePoint;
      vertexBuffer_[1] = rightAnglePoint;
      vertexBuffer_[2] = topAnglePoint;

      // Insert first triangle that contains all points.
      triangles_.push_back(triangle_t(0, 1, 2));

      // Prepare shuffled indices.
      std::vector<vertex_handle_t> shuffledIndices;
      shuffledIndices.reserve(vertexBuffer_.size() - 3);
      for (vertex_handle_t vh = 3; vh < vertexBuffer_.size(); ++vh)
        shuffledIndices.push_back(vh);
      // TODO: Not determined implementation dependent shuffling.
      std::random_shuffle(shuffledIndices.begin(), shuffledIndices.end());

      // Insert input points.
      std::for_each(shuffledIndices.begin(), shuffledIndices.end(),
        boost::bind(&self_t::addVertex, boost::ref(*this), _1));
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
      return vertexBuffer_[idx + 3];
    }

  protected:
    point_t const & vertex_point( vertex_handle_t vh ) const
    {
      return vertexBuffer_.at(vh);
    }

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

    triangles_const_iterator begin() const
    {
      is_triangle_real_pred isTriangleRealPred =
         boost::bind(&self_t::isRealTriangle, *this, _1);
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

    triangles_const_iterator end() const
    {
      is_triangle_real_pred isTriangleRealPred =
         boost::bind(&self_t::isRealTriangle, *this, _1);
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
    static 
    triangle_vertices_indices_t
        triangle_vertices( triangle_t const &tr )
    {
      // TODO: Use functions like internalIdxToOutputIdx().

      size_t idx0 = tr.vertex(0) - 3,
             idx1 = tr.vertex(1) - 3,
             idx2 = tr.vertex(2) - 3;

      BOOST_ASSERT(
              idx0 != idx1 &&
              idx0 != idx2 &&
              idx1 != idx2);

      // Sort vertices.
      // TODO: Needed only for stable testing.
      if (idx0 < idx1 && idx0 < idx2)
      {
        return triangle_vertices_indices_t(idx0, idx1, idx2);
      }
      else if (idx1 < idx0 && idx1 < idx2)
      {
        return triangle_vertices_indices_t(idx1, idx2, idx0);
      }
      else
      {
        BOOST_ASSERT(idx2 < idx0 && idx2 < idx1);
        return triangle_vertices_indices_t(idx2, idx0, idx1);
      }
    }

    static bool isFiniteVertex( vertex_handle_t vh )
    {
      BOOST_ASSERT(vh != invalid_vertex_handle);
      return vh >= 3;
    }

    size_t infiniteVerticesNum( triangle_handle_t trh )
    {
      return (int)!isFiniteVertex(triangle(trh).vertex(0)) +
             (int)!isFiniteVertex(triangle(trh).vertex(1)) +
             (int)!isFiniteVertex(triangle(trh).vertex(2));
    }

    bool isFiniteTriangle( triangle_handle_t trh )
    {
      return infiniteVerticesNum(trh) == 0;
    }

    bool isRealTriangle( triangle_t const &tr )
    {
      //return !tr.has_children();
      return !tr.has_children() && 
              isFiniteVertex(tr.vertex(0)) &&
              isFiniteVertex(tr.vertex(1)) &&
              isFiniteVertex(tr.vertex(2));
    }

  protected:
    // Only flip edge that is opposite to vertex with provided index.
    void flip( triangle_handle_t trh, int const idx )
    {
      verifyAdjancy();
      
      BOOST_ASSERT(triangle(trh).vertex(idx) != invalid_vertex_handle);

      triangle_handle_t neighTrH = triangle(trh).triangle(idx);
      int const neighIdx = triangle(neighTrH).triangle_index(trh);

      BOOST_ASSERT(is_flip_required(trh, triangle(neighTrH).vertex(neighIdx)));
      BOOST_ASSERT(!triangle(trh).has_children());
      BOOST_ASSERT(!triangle(neighTrH).has_children());

      //                                                                    //
      //            *                                   *                   //
      //           /|\                                 / \                  //
      //          / | \                               /   \                 //
      //         /  |  \                             /     \                //
      // trh -> /   |   \                           /  ch0  \               //
      //       /    |    \                         /         \              //
      //      /     |     \                       /           \             //
      //     *      |      *          ->         *-------------*            //
      // idx  \     |     /  neighIdx             \           /             //
      //       \    |    /                         \   ch1   /              //
      //        \   |   /                           \       /               //
      //         \  |  /                             \     /                //
      //          \ | /                               \   /                 //
      //           \|/                                 \ /                  //
      //            *                                   *                   //
      //                                                                    //
      triangle_handle_t const ch0 = triangles_.size() + 0;
      triangle_handle_t const ch1 = triangles_.size() + 1;
      triangles_.push_back(triangle_t( // ch0
          triangle(trh).vertex(idx - 1),
              triangle(trh).vertex(idx),
                  triangle(neighTrH).vertex(neighIdx),
          ch1,
              triangle(neighTrH).triangle(neighIdx - 1),
                  triangle(trh).triangle(idx + 1)));
      triangles_.push_back(triangle_t( // ch1
          triangle(trh).vertex(idx),
              triangle(trh).vertex(idx + 1),
                  triangle(neighTrH).vertex(neighIdx),
          triangle(neighTrH).triangle(neighIdx + 1),
              ch0,
                  triangle(trh).triangle(idx - 1)));

      // Link neighbors.
      triangle(triangle(trh).triangle(idx + 1)).
          replace_neighbor(trh, ch0);
      triangle(triangle(trh).triangle(idx - 1)).
          replace_neighbor(trh, ch1);
      triangle(triangle(neighTrH).triangle(neighIdx + 1)).
          replace_neighbor(neighTrH, ch1);
      triangle(triangle(neighTrH).triangle(neighIdx - 1)).
          replace_neighbor(neighTrH, ch0);

      // Link child triangles to parent.
      triangle(trh).set_children(ch0, ch1);
      triangle(neighTrH).set_children(ch0, ch1);

      verifyAdjancy();
    }

    // Flip edge opposite to provided vertex hanlde if needed.
    void restoreDelaunay( triangle_handle_t trh, vertex_handle_t vh )
    {
      BOOST_ASSERT(trh != invalid_triangle_handle);
      BOOST_ASSERT(vh != invalid_vertex_handle);
      BOOST_ASSERT(triangle(trh).vertex_index(vh) >= 0);
      BOOST_ASSERT(!triangle(trh).has_children());

      int const idx = triangle(trh).vertex_index(vh);
      triangle_handle_t const neighTrH = triangle(trh).triangle(idx);
      if (neighTrH == invalid_triangle_handle)
      {
        // No neighbor, must be triangle at border.

        // Two vertices of neighbor must be border vertices.
        BOOST_ASSERT(
                (int)!isFiniteVertex(triangle(trh).vertex(0)) +
                (int)!isFiniteVertex(triangle(trh).vertex(1)) +
                (int)!isFiniteVertex(triangle(trh).vertex(2)) == 2);

        return;
      }

      BOOST_ASSERT(!triangle(neighTrH).has_children());

      int const neighIdx = triangle(neighTrH).triangle_index(trh);
      BOOST_ASSERT(neighIdx >= 0);

      vertex_handle_t oppositeVH = triangle(neighTrH).vertex(neighIdx);
      
      if (is_flip_required(trh, oppositeVH))
      {
        // Must flip.
        flip(trh, idx);
        BOOST_ASSERT(triangle(trh).children_num() == 2);
        BOOST_ASSERT(triangle(neighTrH).children_num() == 2);

        // After flip 2 newly created triangles are childs of current trianle.
        restoreDelaunay(triangle(trh).child_triangle(0), vh);
        restoreDelaunay(triangle(trh).child_triangle(1), vh);
      }
      else
      {
        // Point NOT inside triangle - point is outside of triangle or
        // on its bounding - thats ok.
      }
    }

    // Add new vertex to interior of triangle.
    void addVertexToTriangleInterior( 
        triangle_handle_t trh,
        vertex_handle_t vh )
    {
      verifyAdjancy();
      
      BOOST_ASSERT(exact_side_of_oriented_triangle(
              trh, vh) == cg::or_on_positive_side);
      BOOST_ASSERT(!triangle(trh).has_children());

      // Create new 3 triangles inside parent triangle.
      //                                                                    //
      //                     0                                              //
      //                     *                                              //
      //                    /'\                                             //
      //                   / ' \                                            //
      //                  /  '  \                                           //
      //                 /   '   \                                          //
      //                /    '    \                                         //
      //               /     '     \                                        //
      //              /      '      \                                       //
      //             /       '       \                                      //
      //            /  ch0   '  ch2   \                                     //
      //           /         '         \                                    //
      //          /          * vh       \                                   //
      //         /        ''' '''        \                                  //
      //        /      '''       '''      \                                 //
      //       /    '''             '''    \                                //
      //      /  '''       ch1         '''  \                               //
      //     /'''                         '' \                              //
      //  1 *---------------------------------* 2                           //
      //                                                                    //
      triangle_handle_t const ch0 = triangles_.size() + 0;
      triangle_handle_t const ch1 = triangles_.size() + 1;
      triangle_handle_t const ch2 = triangles_.size() + 2;
      triangles_.push_back(triangle_t(
          triangle(trh).vertex(0), triangle(trh).vertex(1), vh,
          ch1,                ch2,                triangle(trh).triangle(2)));
      triangles_.push_back(triangle_t(
          triangle(trh).vertex(1), triangle(trh).vertex(2), vh,
          ch2,                ch0,                triangle(trh).triangle(0)));
      triangles_.push_back(triangle_t(
          triangle(trh).vertex(2), triangle(trh).vertex(0), vh,
          ch0,                ch1,                triangle(trh).triangle(1)));

      // Link neighbors of parent triangle to new triangles.
      if (triangle(trh).triangle(0) != invalid_triangle_handle)
        triangle(triangle(trh).triangle(0)).replace_neighbor(trh, ch1);
      if (triangle(trh).triangle(1) != invalid_triangle_handle)
        triangle(triangle(trh).triangle(1)).replace_neighbor(trh, ch2);
      if (triangle(trh).triangle(2) != invalid_triangle_handle)
        triangle(triangle(trh).triangle(2)).replace_neighbor(trh, ch0);

      // Link child triangles to parent.
      triangle(trh).set_children(ch0, ch1, ch2);

      verifyAdjancy();
    }

    // Add new vertex to triangle edge.
    void addVertexToTriangleEdge( triangle_handle_t trh, vertex_handle_t vh,
                                  int idx )
    {
      verifyAdjancy();
      
      BOOST_ASSERT(exact_side_of_oriented_triangle(
              trh, vh) == cg::or_on_boundary);
      BOOST_ASSERT(exact_orientation(
                vertex_point(triangle(trh).vertex(idx + 1)),
                vertex_point(triangle(trh).vertex(idx + 2)),
                vertex_point(vh)) == cg::or_collinear);

      triangle_handle_t const neighTrH = triangle(trh).triangle(idx);
      BOOST_ASSERT(neighTrH != invalid_triangle_handle);
      int const neighIdx = triangle(neighTrH).triangle_index(trh);

      BOOST_ASSERT(!triangle(trh).has_children());
      BOOST_ASSERT(!triangle(neighTrH).has_children());

      triangle_handle_t const ch0 = triangles_.size() + 0;
      triangle_handle_t const ch1 = triangles_.size() + 1;
      triangle_handle_t const ch2 = triangles_.size() + 2;
      triangle_handle_t const ch3 = triangles_.size() + 3;
      // Create new 4 triangles inside parent triangle and it's neighbor.
      //                                                                    //
      // neighIdx *-------------------*                                     //
      //           \ ''              / \                                    //
      //            \  ''    ch3    /   \                                   //
      //             \    ''       /     \                                  //
      //              \     ''  vh/  ch0  \                                 //
      //  neightTr ->  \ ch2   ' *         \  <- trh                        //
      //                \       /  '''      \                               //
      //                 \     /      ''     \                              //
      //                  \   /   ch1    ''   \                             //
      //                   \ /             ''  \                            //
      //                    *------------------* idx                        //
      //                                                                    //
      triangles_.push_back(triangle_t( // ch0
          triangle(trh).vertex(idx), 
              triangle(trh).vertex(idx + 1),
                  vh,
          ch3,
              ch1,
                  triangle(trh).triangle(idx - 1)));
      triangles_.push_back(triangle_t( // ch1
          triangle(trh).vertex(idx - 1),
              triangle(trh).vertex(idx),
                  vh,
          ch0,
              ch2,
                  triangle(trh).triangle(idx + 1)));
      triangles_.push_back(triangle_t( // ch2
          triangle(neighTrH).vertex(neighIdx),
              triangle(neighTrH).vertex(neighIdx + 1),
                  vh,
          ch1,
              ch3,
                  triangle(neighTrH).triangle(neighIdx - 1)));
      triangles_.push_back(triangle_t( // ch3
          triangle(neighTrH).vertex(neighIdx - 1),
              triangle(neighTrH).vertex(neighIdx),
                  vh,
          ch2,
              ch0,
                  triangle(neighTrH).triangle(neighIdx + 1)));

      // Link neighbors.
      triangle(triangle(trh).triangle(idx + 1)).
          replace_neighbor(trh, ch1);
      triangle(triangle(trh).triangle(idx - 1)).
          replace_neighbor(trh, ch0);
      triangle(triangle(neighTrH).triangle(neighIdx + 1)).
          replace_neighbor(neighTrH, ch3);
      triangle(triangle(neighTrH).triangle(neighIdx - 1)).
          replace_neighbor(neighTrH, ch2);

      // Link child triangles to parent.
      triangle(trh).set_children(ch0, ch1);
      triangle(neighTrH).set_children(ch2, ch3);

      verifyAdjancy();
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
        restoreDelaunay(triangle(trh).child_triangle(0), vh);
        restoreDelaunay(triangle(trh).child_triangle(1), vh);
        restoreDelaunay(triangle(trh).child_triangle(2), vh);
      }
      else if (loc == loc_edge)
      {
        // Vertex on triangle edge.

        // Locate triangle edge on which vertex is lying.
        boost::optional<int> adjTrIdxPtr;
        for (size_t i = 0; i < 3; ++i)
          if (cg::exact_orientation(
                vertex_point(triangle(trh).vertex(i)),
                vertex_point(triangle(trh).vertex(i + 1)),
                vertex_point(vh)) == cg::or_collinear)
          {
            adjTrIdxPtr = i - 1;
            break;
          }
        BOOST_ASSERT(adjTrIdxPtr);

        triangle_handle_t const neighTrH =
            triangle(trh).triangle(*adjTrIdxPtr);
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
        std::cerr << "Warning: duplicate vertex #" << vh << ": " <<
            point(vh) << "\n";
      }
    }

    cg::orientation_t exact_side_of_oriented_triangle(
        triangle_handle_t trh, vertex_handle_t vh )
    {
      return cg::exact_side_of_oriented_triangle(
          vertex_point(triangle(trh).vertex(0)),
          vertex_point(triangle(trh).vertex(1)),
          vertex_point(triangle(trh).vertex(2)),
          vertex_point(vh));
    }

    bool is_flip_required( triangle_handle_t trh, vertex_handle_t vh )
    {
      if (isFiniteTriangle(trh))
      {
        if (isFiniteVertex(vh))
        {
          // Finite triangle, finite vertex - normal check.

          return cg::exact_side_of_oriented_circle(
            vertex_point(triangle(trh).vertex(0)),
            vertex_point(triangle(trh).vertex(1)),
            vertex_point(triangle(trh).vertex(2)),
            vertex_point(vh)) == cg::or_on_positive_side;
        }
        else
        {
          // Finite triangle, infinite vertex - vertex always outside triangle.
          return false;
        }
      }
      else
      {
        if (!isFiniteVertex(vh))
        {
          // Infinite triangle, infinite vertex.

          // TODO: case is not so simple, but looks like flip is not
          // needed here.
          return false;
        }
        else
        {
          // Infinite triangle, finite vertex.
          size_t const nInfVert = infiniteVerticesNum(trh);
          if (nInfVert == 2)
          {
            // Flipes not needed (because after flip situation will be same -
            // edge of convex hull will remain old).
            return false;
          }
          else
          {
            BOOST_ASSERT(nInfVert == 1);
            // Should check is vertex lies in triangle half-plane.
            int const infVertexIdx = triangle(trh).infinite_vertex_index();

            if (cg::exact_orientation(
                vertex_point(triangle(trh).vertex(infVertexIdx + 1)),
                vertex_point(triangle(trh).vertex(infVertexIdx + 2)),
                vertex_point(vh)) == cg::or_counterclockwise)
            {
              // Point in triangle half-plane.
              return true;
            }
            else
            {
              // Point and infinite vertex in different triangle half-planes.
              return false;
            }
          }
        }
      }
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
        BOOST_ASSERT(exact_side_of_oriented_triangle(trh, vh) != 
                cg::or_on_negative_side);

        if (!tr.has_children())
        {
          // Triangle without children.
          // Determine whether vertex lies on triangle edge or in triangle
          // interior and return result.

          cg::orientation_t const orient = 
              exact_side_of_oriented_triangle(trh, vh);
          if (orient == cg::or_on_positive_side)
          {
            return std::make_pair(loc_triangle, trh);
          }
          else if (orient == cg::or_on_boundary)
          {
            return std::make_pair(loc_edge, trh);
          }
          else
          {
            BOOST_ASSERT((
                    vertex_point(vh) == vertex_point(tr.vertex(0)) ||
                    vertex_point(vh) == vertex_point(tr.vertex(1)) ||
                    vertex_point(vh) == vertex_point(tr.vertex(2))));
            return std::make_pair(loc_vertex, trh);
          }
        }
        else
        {
          // Triangle has children.
          // Determine in which child lies vertex and continue loop.

          boost::optional<vertex_handle_t> nextVH;
          for (size_t childIdx = 0; childIdx < tr.children_num(); ++childIdx)
          {
            if (exact_side_of_oriented_triangle(tr.child_triangle(childIdx),
                                                vh) != cg::or_on_negative_side)
            {
              // Found child triangle that contains current vertex.
              nextVH = tr.child_triangle(childIdx);
              break;
            }
          }
          trh = nextVH.get();
        }
      }
    }

    void verifyAdjancy( triangle_handle_t trh )
    {
      if (triangle(trh).has_children())
        return;

      for (int idx = 0; idx < 3; ++idx)
        if (triangle(trh).triangle(idx) != invalid_triangle_handle)
        {
          triangle(triangle(trh).triangle(idx)).triangle_index(trh);
        }
    }

    void verifyAdjancy()
    {
      #ifndef NDEBUG
      for (triangle_handle_t trh = 0; trh < triangles_.size(); ++trh)
        verifyAdjancy(trh);
      #endif // NDEBUG
    }

  protected:
    // Input vertices plus three vertices of containing all points
    // imaginary triangle (three imaginaryvertices at vector start).
    vertex_buffer_t vertexBuffer_;
    // First triangle is containing all points imaginary triangle.
    triangles_t     triangles_;
  };
}

#endif // DELAUNAY_TRIANGULATION_HPP
