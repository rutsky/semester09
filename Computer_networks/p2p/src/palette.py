#  This file is part of network emulation test model.
#
#  Copyright (C) 2010, 2011  Vladimir Rutsky <altsysrq@gmail.com>
#
#  This program is free software: you can redistribute it and/or modify
#  it under the terms of the GNU General Public License as published by
#  the Free Software Foundation, either version 3 of the License, or
#  (at your option) any later version.
#
#  This program is distributed in the hope that it will be useful,
#  but WITHOUT ANY WARRANTY; without even the implied warranty of
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#  GNU General Public License for more details.
#
#  You should have received a copy of the GNU General Public License
#  along with this program.  If not, see <http://www.gnu.org/licenses/>.

__author__  = "Vladimir Rutsky <altsysrq@gmail.com>"
__license__ = "GPL"

__all__ = ["Palette", "FixedPalette", "palette"]

import random

from PyQt4.QtCore import *
from PyQt4.QtGui import *

import config

# TODO: Rename to "color_from_rgb" etc.
# TODO: Move to separate module.
def rgb_color(r, g, b):
    return QColor(r, g, b)

def hsv01_color(h, s, v):
    color = QColor()
    color.setHsvF(h, s, v)
    return color

def random_color(generator=random):
    return hsv01_color(generator.random(), 1.0, 1.0)

# TODO: Not generic interface.
class Palette(object):
    def __init__(self, seed=0):
        super(Palette, self).__init__()

        self._generator = random.Random(seed)

        self._palette = []
        
    def __getitem__(self, idx):
        assert isinstance(idx, int) and idx >= 0
        while len(self._palette) <= idx:
            self._palette.append(random_color(self._generator))

        return self._palette[idx]

# TODO: Not generic interface.
# TODO: Tests.
class FixedPalette(object):
    def __init__(self, size, seed=0):
        super(FixedPalette, self).__init__()

        self._size = size
        self._generator = random.Random(seed)

        self._palette = []

    def __getitem__(self, idx):
        assert isinstance(idx, int) and idx >= 0
        while len(self._palette) <= idx:
            if idx < self._size:
                v = 1.0 * idx / self._size
                class G(object):
                    def random(self):
                        return v

                self._palette.append(random_color(G()))
            else:
                self._palette.append(random_color(self._generator))

        return self._palette[idx]

# TODO: Tests.
class Palette16(object):
    def __init__(self, size, seed=0):
        super(Palette16, self).__init__()

        self._size = size
        self._generator = random.Random(seed)

        c = rgb_color
        self._palette = [
            c(255, 0, 0), c(0, 255, 0), c(0, 0, 255), c(255, 255, 0),
            c(255, 0, 255), c(0, 255, 255), c(187, 187, 187), c(221, 119, 119),
            c(119, 221, 119), c(221, 221, 119), c(119, 119, 221),
            c(221, 119, 238),
            c(187, 255, 255), c(238, 187, 0), c(127, 0, 0), c(0, 127, 0)]

    def __getitem__(self, idx):
        assert isinstance(idx, int) and idx >= 0
        while len(self._palette) <= idx:
            self._palette.append(random_color(self._generator))

        return self._palette[idx]

palette = Palette16(config.max_routers_num)

# TODO: Implement binary division palette.

def _test():
    # TODO: Use in separate file to test importing functionality.

    from testing import unittest, do_tests, process_events_with_timeout

    class Tests(object):
        class TestPalette(unittest.TestCase):
            def test_main(self):
                p = Palette()
                p[10]

            def test_deterministic(self):
                p1 = Palette()
                p2 = Palette()
                p1[100]
                p2[200]
                self.assertEqual(p1[30], p2[30])

            def test_test(self):
                p1 = Palette()
                colors = [(p1[i].red(), p1[i].green(), p1[i].blue())
                    for i in xrange(10)]
                colors.sort()
                print "Must be random:", colors

        class TestFixedPalette(unittest.TestCase):
            def test_main(self):
                p = FixedPalette(4)
                p[10]

            def test_deterministic(self):
                p1 = FixedPalette(4)
                p2 = FixedPalette(4)
                p1[100]
                p2[200]
                self.assertEqual(p1[30], p2[30])

            def test_test(self):
                p1 = FixedPalette(4)
                colors = [(p1[i].red(), p1[i].green(), p1[i].blue())
                    for i in xrange(10)]
                colors.sort()
                print "Must be random:", colors

    do_tests(Tests, qt=True)

if __name__ == "__main__":
    _test()

# vim: set ts=4 sw=4 et:
