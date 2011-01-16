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

__all__ = ["is_valid"]

def is_valid(router_name):
    return isinstance(router_name, int) and 0 <= router_name < 2**32

def _test(level=None):
    # TODO: Use in separate file to test importing functionality.

    from testing import unittest, do_tests

    class Tests(object):
        class TestRouterName(unittest.TestCase):
            def test_is_valid(self):
                self.assertTrue(is_valid(0))
                self.assertTrue(is_valid(1))
                self.assertTrue(is_valid(2**32 - 1))

                self.assertFalse(is_valid(-1))
                self.assertFalse(is_valid(-2**32 - 1))
                self.assertFalse(is_valid(2**32))
                self.assertFalse(is_valid(2**32 + 1))

    do_tests(Tests, level=level)

if __name__ == "__main__":
    _test(0)
