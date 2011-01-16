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

    def table(self):
        """Returns dictionary: { destination router: next_router }.

        Note: subsequent calls can return different table on dynamically
        updated routing table, so use caching.
        """
        pass

    def next_router(self, dest):
        """By destination router name returns name of next router to which
        datagram should be retransmitted.

        Returns None in case when next hop is undefined (and datagram should
        be destroyed).
        """
        return self.table().setdefault(dest, None)

    def routes_through(self, next_router_name):
        """Returns list of destination routers accessible through passed next
        router name.
        """

        return [dest for (dest, next) in  self.table().items() \
            if next == next_router_name]

class StaticRoutingTable(RoutingTable):
    def __init__(self, dest_to_next_router):
        super(StaticRoutingTable, self).__init__()
        self.dest_to_next_router = dest_to_next_router

    def table(self):
        return self.dest_to_next_router

# TODO: Add tests.
class DynamicRoutingTable(RoutingTable):
    def __init__(self, dest_to_next_router, lock):
        super(DynamicRoutingTable, self).__init__()
        self.dest_to_next_router = dest_to_next_router
        self.lock = lock

    def table(self):
        with self.lock:
            return self.dest_to_next_router.copy()        

def loopback_routing_table(router_name):
    return StaticRoutingTable({router_name: router_name})

class LocalRoutingTable(RoutingTable):
    def __init__(self, router_name, router_link_manager):
        super(LocalRoutingTable, self).__init__()
        self._router_name = router_name
        self._link_manager = router_link_manager

    def table(self):
        routers = self._link_manager.connected_routers()
        routers.append(self._router_name)
        return dict(zip(routers, routers))

def _test():
    # TODO: Use in separate file to test importing functionality.

    import sys
    if sys.version_info[:2] < (2, 7):
        # Backports.
        import unittest2 as unittest
    else:
        import unittest
    import logging

    from link_manager import RouterLinkManager

    class Tests(object):
        class TestStaticRoutingTable(unittest.TestCase):
            def test_routing(self):
                table = {1: 1, 2: 2, 3: 3, 6:2}
                rt = StaticRoutingTable(table)

                self.assertItemsEqual(rt.table(), table)
                self.assertEqual(rt.next_router(2), 2)
                self.assertEqual(rt.next_router(4), None)
                self.assertItemsEqual(rt.routes_through(2), [2, 6])

            def test_loopback(self):
                rt = loopback_routing_table(1)

                self.assertEqual(rt.next_router(1), 1)
                self.assertEqual(rt.next_router(2), None)

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
