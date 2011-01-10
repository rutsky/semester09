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

__all__ = ["Router"]

from link_manager import RouterLinkManager
from datagram import DatagramRouter
from rip import RIPService
from service_manager import RouterServiceManager

class Router(object):
    def __init__(self, name):
        super(Router, self).__init__()

        assert isinstance(name, int) and 0 <= name < 2**32
        self._name = name

        self._link_manager = RouterLinkManager()

        self._datagram_router = DatagramRouter(
            router_name=self._name,
            link_manager=self._link_manager)

        self._service_manager = RouterServiceManager(self._datagram_router)

        self._rip_service_transmitter = \
            self._service_manager.register_service(RIPService.protocol)

        self._rip_service = RIPService(self._name, self._link_manager,
            self._rip_service_transmitter)

        self._datagram_router.set_routing_table(
            self._rip_service.dynamic_routing_table())

    # TODO
    def terminate(self):
        self._rip_service.terminate()
        self._service_manager.terminate()
        self._datagram_router.terminate()

    @property
    def name(self):
        return self._name

    @property
    def link_manager(self):
        return self._link_manager

def _test():
    # TODO: Use in separate file to test importing functionality.

    import unittest2 as unittest
    import logging

    class Tests(object):
        class TestRouter(unittest.TestCase):
            def test_constructor(self):
                name = 1
                rr = Router(name)

                self.assertEqual(rr.name, name)
                self.assertEqual(rr.link_manager.connected_routers(), [])

                rr.terminate()

    logging.basicConfig(level=logging.DEBUG)

    suite = unittest.TestSuite()
    for k, v in Tests.__dict__.iteritems():
        if k.startswith('Test'):
            suite.addTests(unittest.TestLoader().loadTestsFromTestCase(v))

    unittest.TextTestRunner(verbosity=2).run(suite)

if __name__ == "__main__":
    _test()
