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

#ifndef DELAUNAY_TRIANGULATION_VERIFICATION_HPP
#define DELAUNAY_TRIANGULATION_VERIFICATION_HPP

#include <vector>
#include <algorithm>
#include <iostream>
#include <ostream>
#include <set>

#include <boost/tuple/tuple.hpp>
#include <boost/tuple/tuple_io.hpp>
#include <boost/tuple/tuple_comparison.hpp>
#include <boost/foreach.hpp>

#include <CGAL/Exact_predicates_inexact_constructions_kernel.h>
#include <CGAL/Point_set_2.h>

#include "point_predicates.hpp"
#include "point_ops.hpp"
#include "indexed_triangle.hpp"
#include "point_utils.hpp"

namespace cg
{
  namespace verification
  {
    template< class TriangleFwdIt, class indicesOutIt >
    inline
    indicesOutIt copy_indices_from_triangle_vertices_indices(
        TriangleFwdIt first, TriangleFwdIt beyond,
        indicesOutIt out )
    {
      for (; first != beyond; ++first)
      {
        triangle_vertices_indices_t const &tr = *first;
        // COMMENTED FOR DEBUG
        *out++ = tr.get<0>();
        *out++ = tr.get<1>();
        *out++ = tr.get<2>();
      }
      
      return out;
    }

    enum triangulation_verification_result
    {
      tvr_valid                                 = 0,
      tvr_excess_triangles                      = 1,
      tvr_empty_triangulation                   = 2,
      tvr_invalid_index                         = 3,
      tvr_duplicate_vertices_in_triangulation   = 4,
      tvr_points_and_indices_not_correspond     = 5,
      tvr_singular_triangle                     = 6,
      tvr_point_in_triangle                     = 7,
      tvr_duplicate_edge                        = 8,
      tvr_duplicate_border_out_edge             = 9,
      tvr_unexpected_border_chain_end           = 10,
      tvr_border_is_not_chain                   = 11,
      tvr_border_chain_not_closed               = 12,
      tvr_more_than_one_border_chain            = 13,
      tvr_border_chain_not_convex               = 14,
      tvr_not_delaunay                          = 15,
    };

    // TODO: Output messages without dot and line feed at end.
    // TODO: Should work as O(N log N), but when all points on single circle
    // it works definetely slower, this must be a problem with used point 
    // localization tool.
    template< class PointInIt, class TriangleInIt, class MessageBuffer >
    inline
    triangulation_verification_result verify_triangulation(
        PointInIt pointsFirst, PointInIt pointsBeyond,
        TriangleInIt trianglesFirst, TriangleInIt trianglesBeyond,
        MessageBuffer &messageBuffer, bool checkDelaunay = false )
    {
      typedef typename PointInIt::value_type point_t;
      typedef std::vector<point_t> vertex_buffer_t;
      typedef std::vector<size_t> index_buffer_t;
      typedef std::vector<triangle_vertices_indices_t> triangles_t;

      // Store vertex buffer and triangles index buffer.
      vertex_buffer_t const vertexBuffer(pointsFirst, pointsBeyond);
      triangles_t triangles(trianglesFirst, trianglesBeyond);

      // DEBUG
      /*
      std::cout << "vertices:\n";
      std::copy(vertexBuffer.begin(), vertexBuffer.end(),
        std::ostream_iterator<point_t>(std::cout, "\n"));
      std::cout << "triangles:\n";
      std::copy(triangles.begin(), triangles.end(),
        std::ostream_iterator<triangle_vertices_indices_t>(std::cout, "\n"));
       */

      // Filter unique points.
      vertex_buffer_t uniquePoints(vertexBuffer.begin(), vertexBuffer.end());
      std::sort(uniquePoints.begin(), uniquePoints.end());
      typename vertex_buffer_t::iterator const uniqueEndIt =
          std::unique(uniquePoints.begin(), uniquePoints.end());
      uniquePoints.erase(uniqueEndIt, uniquePoints.end());

      // Create points localisation structure.
      typedef CGAL::Exact_predicates_inexact_constructions_kernel K;
      typedef CGAL::Point_set_2<K>::Vertex_handle vertex_handle_t;

      CGAL::Point_set_2<K> pointsSet;

      BOOST_FOREACH(point_t const &p, vertexBuffer)
        pointsSet.insert(K::Point_2(p.x, p.y));

      // Check if all points collinear.
      // TODO: Assume that empty points set IS collinear.
      BOOST_ASSERT(exact_is_collinear(uniquePoints.end(), uniquePoints.end()));
      if (exact_is_collinear(uniquePoints.begin(), uniquePoints.end()))
      {
        // No non-empty triangulation exists for set of collinear points.
        if (!triangles.empty())
        {
          messageBuffer << "All " << uniquePoints.size() <<
              " unique points collinear, "
              "so there can't be any triangles, but input has " <<
              triangles.size() << " triangle(s).\n";
          return tvr_excess_triangles;
        }
        else
        {
          return tvr_valid;
        }
      }

      // Handle empty triangulation case.
      if (triangles.empty())
      {
        messageBuffer << "Empty triangulation for set of " << 
            uniquePoints.size() << " non-collinear unique points.\n";
        return tvr_empty_triangulation;
      }

      // Extract used in triangulation indices.
      index_buffer_t usedIndices;
      copy_indices_from_triangle_vertices_indices(
          triangles.begin(), triangles.end(),
          std::back_inserter(usedIndices));
      std::sort(usedIndices.begin(), usedIndices.end());
      usedIndices.erase(std::unique(usedIndices.begin(), usedIndices.end()),
          usedIndices.end());

      // Check range of indices.
      if (usedIndices.back() >= vertexBuffer.size())
      {
        messageBuffer << "Triangulation has vertex index " <<
            usedIndices.back() << " but valid range is (0," <<
            (vertexBuffer.size() - 1) << ").\n";
        return tvr_invalid_index;
      }

      // Check is used indices reference equal vertices.
      vertex_buffer_t usedPoints;
      BOOST_FOREACH(size_t vertIdx, usedIndices)
      {
        usedPoints.push_back(vertexBuffer[vertIdx]);
      }
      std::sort(usedPoints.begin(), usedPoints.end());
      typename vertex_buffer_t::iterator equalPointsIt =
          std::unique(usedPoints.begin(), usedPoints.end());
      if (equalPointsIt != usedPoints.end())
      {
        // TODO: output incorrect indices.
        messageBuffer << 
            "Triangulation has different references to equal points:\n  ";
        // TODO: spaces after linefeed.
        std::copy(equalPointsIt, usedPoints.end(), 
          std::ostream_iterator<point_t>(messageBuffer, "\n"));
        return tvr_duplicate_vertices_in_triangulation;
      }

      // Check that number of different indices used in triangulation is equal
      // to number of different points.
      if (usedPoints.size() != uniquePoints.size())
      {
        messageBuffer <<
            "Number of unique points (" << uniquePoints.size() << ") "
            "not equal to number of used indices (" << usedPoints.size() <<
            ").\n";

        // TODO: Not sure about this, but I think it's true.
        BOOST_ASSERT(usedPoints.size() < uniquePoints.size());

        return tvr_points_and_indices_not_correspond;
      }

      // Check that all triangles are not singular and fix they orientation.
      BOOST_FOREACH(triangle_vertices_indices_t &tr, triangles)
      {
        point_t const &p0 = vertexBuffer[tr.get<0>()];
        point_t const &p1 = vertexBuffer[tr.get<1>()];
        point_t const &p2 = vertexBuffer[tr.get<2>()];
        orientation_t const orient = exact_orientation(p0, p1, p2);
        if (orient == or_collinear)
        {
          messageBuffer <<
              "Triangulation contains singular triangle:\n  " << tr <<
              "\n  " <<
              p0 << ", " << p1 << ", " << p2 << "\n";
          return tvr_singular_triangle;
        }

        if (orient == or_clockwise)
        {
          messageBuffer << "Warning: found clockwise oriented triangle:\n  " <<
                  tr << "\n  rotating it.\n";
          tr = triangle_vertices_indices_t(
                  tr.get<2>(), tr.get<1>(), tr.get<0>());
          // TODO: After this it is not very polite to output triangle indices
          // inverted in messages.
        }
      }

      // Check that each triangle doesn't has points inside.
      BOOST_FOREACH(triangle_vertices_indices_t const &tr, triangles)
      {
        point_t const &p0 = vertexBuffer[tr.get<0>()];
        point_t const &p1 = vertexBuffer[tr.get<1>()];
        point_t const &p2 = vertexBuffer[tr.get<2>()];
        
        BOOST_ASSERT(exact_orientation(p0, p1, p2) == or_counterclockwise);

        std::vector<vertex_handle_t> points;
        pointsSet.range_search(
          K::Point_2(p0.x, p0.y),
          K::Point_2(p1.x, p1.y), 
          K::Point_2(p2.x, p2.y),
          std::back_inserter(points));

        BOOST_FOREACH(vertex_handle_t const &qh, points)
        {
          point_t const q(qh->point().x(), qh->point().y());

          if (q == p0 || q == p1 || q == p2)
            continue;

          orientation_t const orient =
              exact_side_of_oriented_triangle(p0, p1, p2, q);

          // Sincle points localisation is exact.
          BOOST_ASSERT(orient != or_on_negative_side);

          if (orient != or_on_negative_side)
          {
            if (orient == or_collinear)
            {
              messageBuffer <<
                "Found point on triangle boundary:\n  " << tr << "\n  " <<
                p0 << ", " << p1 << ", " << p2 << 
                "\n  point:\n  " <<
                q << "\n";
            }
            else
            {
              BOOST_ASSERT(orient == or_on_positive_side);

              messageBuffer <<
                "Found point in triangle interior:\n  " << tr << "\n  " <<
                p0 << ", " << p1 << ", " << p2 <<
                "\n  point:\n  " <<
                q << "\n";
            }
            
            return tvr_point_in_triangle;
          }
        }
      }

      // Collect edges and check that they are unique.
      typedef boost::tuple<size_t, size_t> edge_t;
      typedef std::set<edge_t> edges_set_t;
      edges_set_t edges;
      BOOST_FOREACH(triangle_vertices_indices_t const &tr, triangles)
      {
        edge_t 
            e1(tr.get<0>(), tr.get<1>()),
            e2(tr.get<1>(), tr.get<2>()),
            e3(tr.get<2>(), tr.get<0>());

        // TODO: Store and output colliding triangles.
        if (edges.find(e1) != edges.end())
        {
          messageBuffer <<
              "Multiple triangles have single edge:\n  " << e1 << "\n";
          return tvr_duplicate_edge;
        }
        if (edges.find(e2) != edges.end())
        {
          messageBuffer <<
              "Multiple triangles have single edge:\n  " << e1 << "\n";
          return tvr_duplicate_edge;
        }
        if (edges.find(e3) != edges.end())
        {
          messageBuffer <<
              "Multiple triangles have single edge:\n  " << e1 << "\n";
          return tvr_duplicate_edge;
        }

        edges.insert(e1);
        edges.insert(e2);
        edges.insert(e3);
      }

      // Collect border edges (which don't have twin).
      typedef std::vector<edge_t> edges_t;
      edges_t borderEdges;
      BOOST_FOREACH(edge_t const &e, edges)
      {
        edge_t const twin(e.get<1>(), e.get<0>());
        if (edges.find(twin) == edges.end())
          borderEdges.push_back(e);
      }

      // Construct chain of edges.
      typedef std::map<size_t, edge_t> vertex_to_edge_map_t;
      vertex_to_edge_map_t vertexToEdge;
      BOOST_FOREACH(edge_t const &e, borderEdges)
      {
        if (vertexToEdge.find(e.get<0>()) != vertexToEdge.end())
        {
          // TODO: Output correspond triangles.
          messageBuffer <<
              "Multiple border edges going out of vertex #" << e.get<0>() << ".\n";
          return tvr_duplicate_border_out_edge;
        }
        else
        {
          vertexToEdge[e.get<0>()] = e;
        }
      }

      // Check that there is only one chain.
      std::set<edge_t> borderChainEdgesSet;
      edges_t borderChain;
      borderChain.push_back(borderEdges[0]);
      borderChainEdgesSet.insert(borderEdges[0]);
      while (true)
      {
        edge_t const e = borderChain.back();
        if (vertexToEdge.find(e.get<1>()) == vertexToEdge.end())
        {
          // TODO: Probably impossible case.
          messageBuffer <<
            "Border chain end unexpectedly at edge: " << e << "\n";
          return tvr_unexpected_border_chain_end;
        }

        edge_t const e1 = vertexToEdge[e.get<1>()];
        
        borderChain.push_back(e1);

        if (borderChainEdgesSet.find(e1) != borderChainEdgesSet.end())
        {
          // TODO: Probably impossible case.
          messageBuffer << "Border is not chain:\n";
          std::copy(borderChain.begin(), borderChain.end(), 
            std::ostream_iterator<edge_t>(messageBuffer, "\n"));
          return tvr_border_is_not_chain;
        }
        borderChainEdgesSet.insert(e1);

        if (e1.get<1>() == borderChain[0].get<0>())
        {
          // Found closed chain.
          break;
        }
      }

      if (borderChain.size() != borderEdges.size())
      {
        messageBuffer <<
            "Found more than one border chains:\n"
            "  border chain size is " << borderChain.size() << ",\n" <<
            "  number of border edges is " << borderEdges.size() << "\n" <<
            "  found chain:\n";
        std::copy(borderChain.begin(), borderChain.end(),
            std::ostream_iterator<edge_t>(messageBuffer, "\n"));
        return tvr_more_than_one_border_chain;
      }

      /*
      // DEBUG
      std::cout << "\n";
      std::copy(borderChain.begin(), borderChain.end(),
          std::ostream_iterator<edge_t>(std::cout, "\n"));
      std::cout << "\n";
       */

      // Check that border chain is convex.
      edge_t prevEdge = borderChain.back();
      for (edges_t::const_iterator it = borderChain.begin();
           it != borderChain.end();
           prevEdge = *it, ++it)
      {
        edge_t const edge = *it;
        BOOST_ASSERT(prevEdge.get<1>() == edge.get<0>());

        point_t const &p0 = vertexBuffer[prevEdge.get<0>()];
        point_t const &p1 = vertexBuffer[prevEdge.get<1>()];
        point_t const &p2 = vertexBuffer[edge.get<1>()];
        if (exact_is_right_turn(p0, p1, p2))
        {
          messageBuffer <<
            "Border chain is not convex at vertices:\n"
            "  " << p0 << ", " << p1 << ", " << p2 << "\n";
          return tvr_border_chain_not_convex;
        }
      }

      if (checkDelaunay)
      {
        // Check Delaunay property: circumscribed circle for each triangle
        // don't have any points in its interior.

        BOOST_FOREACH(triangle_vertices_indices_t const &tr, triangles)
        {
          point_t const &p0 = vertexBuffer[tr.get<0>()];
          point_t const &p1 = vertexBuffer[tr.get<1>()];
          point_t const &p2 = vertexBuffer[tr.get<2>()];

          BOOST_ASSERT(exact_orientation(p0, p1, p2) == or_counterclockwise);

          std::vector<vertex_handle_t> points;
          pointsSet.range_search(
            CGAL::Circle_2<K>(
              construct_2d_point<K::Point_2>(p0),
              construct_2d_point<K::Point_2>(p1),
              construct_2d_point<K::Point_2>(p2)),
            std::back_inserter(points));

          BOOST_FOREACH(vertex_handle_t const &qh, points)
          {
            point_t const q(qh->point().x(), qh->point().y());

            if (q == p0 || q == p1 || q == p2)
              continue;

            orientation_t const orient =
                exact_side_of_oriented_circle(p0, p1, p2, q);

            // Sincle points localisation is exact.
            // TODO:
            // Fails on this input:
            //   -0.3634838014039983 0.3433358794488259
            //   0.2429460407177192 0.437009406420027
            //   0.2512455848588854 0.4322911704961329
            //   -0.4071324779640412 -0.2902466974607282
            //   -0.3633463862938436 0.3434813001710645
            // and this output:
            //   0 3 4
            //   1 3 2
            //   1 4 3
            //
            //BOOST_ASSERT(
            //    orient == or_on_positive_side ||
            //    orient == or_on_boundary);

            if (orient == or_on_positive_side)
            {
              // TODO: Output point index.
              messageBuffer <<
                "Found point in interior of circumscribed around triangle "
                "circle:\n"
                "  " << tr << "\n"
                "  " << p0 << ", " << p1 << ", " << p2 << "\n"
                "  point:\n"
                "  " << q << "\n";
              return tvr_not_delaunay;
            }
          }
        }
      }

      return tvr_valid;
    }
  }
}

#endif // DELAUNAY_TRIANGULATION_VERIFICATION_HPP
