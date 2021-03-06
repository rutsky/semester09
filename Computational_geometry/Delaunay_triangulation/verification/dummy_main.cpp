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
#include <fstream>

int main( int argc, char *argv[] )
{
  if (argc < 3)
  {
    std::cout << "Missing arguments.\n" <<
      "Usage:\n"
      "  " << argv[0] << " points_file triangles_file\n";
    return 1;
  }

  std::ifstream pointsFile(argv[1]);
  if (!pointsFile)
  {
    perror(argv[1]);
    return -1;
  }
  
  std::ifstream trianglesFile(argv[2]);
  if (!trianglesFile)
  {
    perror(argv[2]);
    return -2;
  }
  
  return 0;
}

// vim: set et ts=2 sw=2:
