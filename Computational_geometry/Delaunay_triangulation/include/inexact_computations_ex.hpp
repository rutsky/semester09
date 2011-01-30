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

#ifndef INEXACT_COMPUTATIONS_EX_HPP
#define INEXACT_COMPUTATIONS_EX_HPP

#include <boost/type_traits.hpp>
#include <boost/exception/all.hpp>

namespace cg
{
  struct inexact_computations_exception
    : virtual boost::exception
    , virtual std::exception
  {
  };
}

#endif // INEXACT_COMPUTATIONS_EX_HPP
