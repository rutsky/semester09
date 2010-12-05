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

#ifndef UTILS_HPP
#define UTILS_HPP

#include <utility>

#include <boost/assert.hpp>
#include <boost/bind.hpp>
#include <boost/iterator.hpp>
#include <boost/iterator/transform_iterator.hpp>
#include <boost/tuple/tuple.hpp>
#include <boost/algorithm/minmax.hpp>

namespace cg
{
  // Calculates axis-aligned bounding box.
  // Returns pair<lower-left point, upper-right point>
  template< class PointFwdIter >
  inline
  std::pair<typename PointFwdIter::value_type, typename PointFwdIter::value_type>
    axis_aligned_bounding_box( PointFwdIter first, PointFwdIter beyond )
  {
    using namespace boost;

    typedef typename PointFwdIter::value_type point_t;
    typedef typename point_t::scalar_t scalar_t;

    scalar_t minX, maxX;
    boost::tie(minX, maxX) = minmax(
            make_transform_iterator(first,  bind(&point_t::x, _1)),
            make_transform_iterator(beyond, bind(&point_t::x, _1)));

    scalar_t minY, maxY;
    boost::tie(minX, maxX) = minmax(
            make_transform_iterator(first,  bind(&point_t::x, _1)),
            make_transform_iterator(beyond, bind(&point_t::x, _1)));

    return std::make_pair(point_t(minX, minY), point_t(maxX, maxY));
  }
}

#endif // UTILS_HPP
