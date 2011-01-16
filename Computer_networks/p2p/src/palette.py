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

__all__ = ["Palette", "palette"]

import random

from PyQt4.QtCore import *
from PyQt4.QtGui import *

def random_color(generator=random):
    color = QColor()
    color.setHsvF(generator.random(), 1.0, 1.0)
    return color

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

palette = Palette()

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
                print colors

    do_tests(Tests, qt=True)

if __name__ == "__main__":
    _test()
