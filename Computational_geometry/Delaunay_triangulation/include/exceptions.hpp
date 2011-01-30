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

#ifndef EXEPTIONS_HPP
#define EXEPTIONS_HPP

#include <stdexcept>
#include <boost/exception/all.hpp>

namespace cg
{
  class invalid_argument 
    : public virtual std::invalid_argument
    , public virtual boost::exception
  {
  public:
    invalid_argument( std::string const &what )
      : std::invalid_argument(what)
    {
    }
  };
}

#endif // EXEPTIONS_HPP
