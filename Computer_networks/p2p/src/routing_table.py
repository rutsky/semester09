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

__all__ = ["RoutingTable", "StaticRoutingTable", "loopback_routing_table",
    "LocalRoutingTable"]

"""Routing table implementation.

In used network model routing table is reduced to list of following tuples:
  (destination router, next router)
When router receives packet (src, dest, data) it looks up next router in
routing table and retransmits packet there.
"""

class RoutingTable(object):
    def __init__(self):
        super(RoutingTable, self).__init__()

    def next_hop(self, dest):
        """By destination router name returns name of next router to which
        datagram should be retransmitted.

        Returns None in case when next hop is undefined (and datagram should
        be destroyed).
        """
        pass

class StaticRoutingTable(RoutingTable):
    def __init__(self, dest_to_next_router):
        super(StaticRoutingTable, self).__init__()
        self.dest_to_next_router = dest_to_next_router

    def next_router(self, dest):
        return self.dest_to_next_router.setdefault(dest, None)

def loopback_routing_table(router_name):
    return StaticRoutingTable({router_name: router_name})

class LocalRoutingTable(RoutingTable):
    def __init__(self, router_name, router_link_manager):
        super(LocalRoutingTable, self).__init__()
        self._router_name = router_name
        self._link_manager = router_link_manager

    def next_router(self, dest):
        if (dest == self._router_name or
                dest in self._link_manager.connected_routers()):
            return dest
        else:
            return None

def _test():
    # TODO: Use in separate file to test importing functionality.

    import unittest2 as unittest
    import logging

    from link_manager import RouterLinkManager

    class Tests(object):
        class TestStaticRoutingTable(unittest.TestCase):
            def test_routing(self):
                rt = StaticRoutingTable({'A': '1', 'B': 2, 'C': 3})

                self.assertEqual(rt.next_router('B'), 2)
                self.assertEqual(rt.next_router('E'), None)

            def test_loopback(self):
                rt = loopback_routing_table("A")

                self.assertEqual(rt.next_router("A"), "A")
                self.assertEqual(rt.next_router("B"), None)

        class TestLocalRoutingTable(unittest.TestCase):
            def test_routing(self):
                lm = RouterLinkManager()

                rt = LocalRoutingTable(1, lm)

                self.assertEqual(rt.next_router(1), 1)
                self.assertEqual(rt.next_router(2), None)

                lm.add_link(2, None)
                self.assertEqual(rt.next_router(2), 2)

                self.assertEqual(rt.next_router(1), 1)
                self.assertEqual(rt.next_router(3), None)

    logging.basicConfig(level=logging.DEBUG)

    suite = unittest.TestSuite()
    for k, v in Tests.__dict__.iteritems():
        if k.startswith('Test'):
            suite.addTests(unittest.TestLoader().loadTestsFromTestCase(v))

    unittest.TextTestRunner(verbosity=2).run(suite)

if __name__ == "__main__":
    _test()
