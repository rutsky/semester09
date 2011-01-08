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

"""Routing table implementation.
"""

# TODO: should abstract real table like:
#   (Destination, Gateway, Interface)
# or table according to selected network topology model

class RoutingTable(object):
    def __init__(self):
        super(RoutingTable, self).__init__()

    def next_hop(self, dest):
        """By destination network name returns name of next host to which
        datagram should be retransmitted.

        Returns None in case when next hop is undefined (and datagram should
        be destroyed).
        """
        pass

class StaticRoutingTable(RoutingTable):
    def __init__(self, dest_to_host):
        super(StaticRoutingTable, self).__init__()
        self.dest_to_host = dest_to_host

    def next_hop(self, dest):
        return self.dest_to_host.setdefault(dest, None)

def _test():
    # TODO: Use in separate file to test importing functionality.

    import unittest2 as unittest
    import logging
    
    logging.basicConfig(level=logging.DEBUG)

    class TestStaticRoutingTable(unittest.TestCase):
        def test_routing(self):
            rt = StaticRoutingTable({'A': '1', 'B': 2, 'C': 3})
            
            self.assertEqual(rt.next_hop('B'), 2)
            self.assertEqual(rt.next_hop('E'), None)

    suite = unittest.TestLoader().loadTestsFromTestCase(TestStaticRoutingTable)
    unittest.TextTestRunner(verbosity=2).run(suite)

if __name__ == "__main__":
    _test()
