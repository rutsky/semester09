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

__all__ = []

"""Link manager.
"""

import threading

class RouterLinkManager(object):
    """Represents router links to other routers.
    """

    def __init__(self):
        super(RouterLinkManager, self).__init__()

        # Links dictionary: {router name: frame transmitter}.
        self._links = {}
        self._links_lock = threading.Lock()

    def add_link(self, router_name, frame_transmitter):
        with self._links_lock:
            assert router_name not in self._links
            self._links[router_name] = frame_transmitter

    def remove_link(self, router_name):
        with self._links_lock:
            assert router_name in self._links
            del self._links[router_name]

    def connected_routers(self):
        """Returns list of connected router names.
        """
        with self._links_lock:
            return self._links.keys()

    def connected_links(self):
        """Returns list of pairs (router_name, frame_transmitter).
        """
        with self._links_lock:
            return self._links.items()

def _test():
    # TODO: Use in separate file to test importing functionality.

    import sys
    if sys.version_info[:2] < (2, 7):
        # Backports.
        import unittest2 as unittest
    else:
        import unittest
    import logging
    
    class Tests(object):
        class TestLinkManager(unittest.TestCase):
            def test_links(self):
                m = RouterLinkManager()

                m.add_link("1", 1)
                m.add_link("2", 2)
                m.add_link("3", 3)

                self.assertItemsEqual(m.connected_routers(), ["1", "2", "3"])
                self.assertItemsEqual(m.connected_links(),
                                 [("1", 1), ("2", 2), ("3", 3)])

                m.remove_link("2")
                self.assertItemsEqual(m.connected_routers(), ["1", "3"])

    logging.basicConfig(level=logging.DEBUG)

    suite = unittest.TestSuite()
    for k, v in Tests.__dict__.iteritems():
        if k.startswith('Test'):
            suite.addTests(unittest.TestLoader().loadTestsFromTestCase(v))

    unittest.TextTestRunner(verbosity=2).run(suite)

if __name__ == "__main__":
    _test()
