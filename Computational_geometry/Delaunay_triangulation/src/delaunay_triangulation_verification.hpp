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

#include "point_predicates.hpp"
#include "point_ops.hpp"

namespace cg
{
  namespace verification
  {
    typedef boost::tuple<size_t, size_t, size_t> triangle_vertices_indices_t;

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
      tvr_valid = 0,
      tvr_excess_triangles,
      tvr_empty_triangulation,
      tvr_invalid_index,
      trv_duplicate_vertices_in_triangulation,
      trv_points_and_indices_not_correspond,
      trv_singular_triangle,
      trv_point_in_triangle,
      trv_duplicate_edge,
      trv_duplicate_border_out_edge,
      trv_unexpected_border_chain_end,
      trv_border_is_not_chain,
      trv_border_chain_not_closed,
      trv_more_than_one_border_chain,
    };

    // TODO: Output messages without dot and line feed at end.
    template< class PointFwdIt, class TriangleFwdIt, class MessageBuffer >
    inline
    triangulation_verification_result verify_triangulation(
        PointFwdIt pointsFirst, PointFwdIt pointsBeyond,
        TriangleFwdIt trianglesFirst, TriangleFwdIt trianglesBeyond,
        MessageBuffer &messageBuffer )
    {
      typedef typename PointFwdIt::value_type point_t;
      typedef std::vector<point_t> vertex_buffer_t;
      typedef std::vector<size_t> index_buffer_t;
      typedef std::vector<triangle_vertices_indices_t> triangles_t;

      // Store vertex buffer and triangles index buffer.
      // TODO: Don't copy them but use provided iterators.
      vertex_buffer_t const vertexBuffer(pointsFirst, pointsBeyond);
      triangles_t triangles(trianglesFirst, trianglesBeyond);

      // Filter unique points.
      vertex_buffer_t uniquePoints(pointsFirst, pointsBeyond);
      std::sort(uniquePoints.begin(), uniquePoints.end());
      typename vertex_buffer_t::iterator const uniqueEndIt =
          std::unique(uniquePoints.begin(), uniquePoints.end());
      uniquePoints.erase(uniqueEndIt, uniquePoints.end());

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
        usedPoints.push_back(vertexBuffer[vertIdx]);
      std::sort(usedPoints.begin(), usedPoints.end());
      typename vertex_buffer_t::iterator equalPointsIt =
          std::unique(usedPoints.begin(),
                      usedPoints.end());
      if (equalPointsIt != usedPoints.end())
      {
        // TODO: output incorrect indices.
        messageBuffer << 
            "Triangulation has different references to equal points:\n  ";
        // TODO: spaces after linefeed.
        std::copy(equalPointsIt, usedPoints.end(), 
          std::ostream_iterator<point_t>(messageBuffer, "\n"));
        return trv_duplicate_vertices_in_triangulation;
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

        return trv_points_and_indices_not_correspond;
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
          return trv_singular_triangle;
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

        BOOST_FOREACH(point_t const &q, uniquePoints)
        {
          if (q == p0 || q == p1 || q == p2)
            continue;

          orientation_t const orient =
              exact_side_of_oriented_triangle(p0, p1, p2, q);
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
            
            return trv_point_in_triangle;
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
          return trv_duplicate_edge;
        }
        if (edges.find(e2) != edges.end())
        {
          messageBuffer <<
              "Multiple triangles have single edge:\n  " << e1 << "\n";
          return trv_duplicate_edge;
        }
        if (edges.find(e3) != edges.end())
        {
          messageBuffer <<
              "Multiple triangles have single edge:\n  " << e1 << "\n";
          return trv_duplicate_edge;
        }

        edges.insert(e1);
        edges.insert(e2);
        edges.insert(e3);
      }

      // Collect border edges (which don't have twin).
      std::vector<edge_t> borderEdges;
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
          return trv_duplicate_border_out_edge;
        }
        else
        {
          vertexToEdge[e.get<0>()] = e;
        }
      }

      // Check that there is only one chain.
      std::set<edge_t> borderChainEdgesSet;
      std::vector<edge_t> borderChain;
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
          return trv_unexpected_border_chain_end;
        }

        edge_t const e1 = vertexToEdge[e.get<1>()];
        
        if (e.get<1>() == borderChain[0].get<0>())
        {
          // Found closed chain.
          break;
        }

        borderChain.push_back(e1);

        if (borderChainEdgesSet.find(e1) != borderChainEdgesSet.end())
        {
          // TODO: Probably impossible case.
          messageBuffer << "Border is not chain:\n";
          std::copy(borderChain.begin(), borderChain.end(), 
            std::ostream_iterator<edge_t>(messageBuffer, "\n"));
          return trv_border_is_not_chain;
        }
        borderChainEdgesSet.insert(e1);
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
        return trv_more_than_one_border_chain;
      }

      // Check that chain is convex.
      

      return tvr_valid;
    }
  }
}

#endif // DELAUNAY_TRIANGULATION_VERIFICATION_HPP
