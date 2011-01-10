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

"""RIP (Routing Information Protocol) implementation in current network model.
"""

import threading
import pickle
import time
import logging

from recordtype import recordtype

from routing_table import DynamicRoutingTable
from service_manager import Packet
from timer import Timer, DummyTimer

class RIPData(recordtype('RIPDataBase', 'distances')):
    def __init__(self, *args, **kwargs):
        super(RIPData, self).__init__(*args, **kwargs)

    def serialize(self):
        return pickle.dumps(self.distances)

    @staticmethod
    def deserialize(raw_data):
        distances = pickle.loads(raw_data)
        return RIPData(distances)

class RIPService(object):
    def __init__(self, router_name, router_link_manager, service_transmitter,
            **kwargs):
        self._inf_dist       = kwargs.pop('inf_dist',       16)
        self._update_period  = kwargs.pop('update_period',   1)
        self._inf_timeout    = kwargs.pop('inf_timeout',     2)
        self._remove_timeout = kwargs.pop('remove_timeout', 12)
        super(RIPService, self).__init__()

        self._router_name = router_name
        self._link_manager = router_link_manager
        self._service_transmitter = service_transmitter

        self._dest_to_next_router = {router_name: router_name}
        self._dest_to_next_router_lock = threading.Lock()

        # If working thread will be able to acquire the lock, then it should
        # terminate himself.
        self._exit_lock = threading.RLock()
        self._exit_lock.acquire()

        self._working_thread = threading.Thread(target=self._work)
        self._working_thread.start()

    # TODO
    def terminate(self):
        # Release exit lock and wait until working thread will not terminate.
        self._exit_lock.release()
        self._working_thread.join()

    def dynamic_routing_table(self):
        return DynamicRoutingTable(self._dest_to_next_router,
            self._dest_to_next_router_lock)

    def _work(self):
        def update_connected_routers_info():
            new_connected_routers = \
                connected_routers - prev_connected_routers
            new_disconnected_routers = \
                prev_connected_routers - connected_routers

            if new_connected_routers:
                logger.debug("Connected to routers: {0}".format(
                    new_connected_routers))
            if new_disconnected_routers:
                logger.debug("Disconnected from routers: {0}".format(
                    new_disconnected_routers))

            # Remove disconnected routers from list.
            for router_name in new_disconnected_routers:
                assert router_name in connected_routers_info
                del connected_routers_info[router_name]

            # Set distance to infinity for destination routers route to which
            # leaded through disconnected routers.
            for to_router, dest_router_info in dest_routers_info.iteritems():
                if dest_router_info.next_router in new_disconnected_routers:
                    dest_router_info.dist = self._inf_dist

            # Add connected hosts to according list.
            for router_name in new_connected_routers:
                router_name not in connected_routers_info
                connected_routers_info[router_name] = \
                    ConnectedRouterInfo(Timer())

            # Update routing information for directly connected destination
            # routers.
            for router_name in new_connected_routers:
                dest_routers_info[router_name] = DestRouterInfo(
                    dist=1, next_router=router_name,
                    timer=Timer(self._inf_timeout))

        def connected_routers_with_timeout():
            for router_name, connected_router_info in connected_routers_info:
                if connected_router_info.timer.is_expired():
                    yield router_name

        def set_infinite_timeout_distances():
            for dest, dest_router_info in dest_routers_info.iteritems():
                if (dest_router_info.dist < self._inf_dist and 
                        dest_router_info.timer.is_expired()):
                    dest_router_info.dist = self._inf_dist
                    dest_router_info.timer = Timer(self._remove_timeout)

        def remove_timeout_distances():
            for dest, dest_router_info in dest_routers_info.iteritems():
                if (dest_router_info.dist == self._inf_dist and
                        dest_router_info.timer.is_expired()):
                    del dest_routers_info[dest]

        def distances_for_sending(to_router):
            distances = []
            for dest, dest_router_info in dest_routers_info.iteritems():
                if dest_router_info.next_router == to_router:
                    # Rule 1A from [vasilev04netsoft]:
                    # For router R: if packets to destination router X are sent
                    # through router G, then distance to router X that being
                    # sent to router G is infinity.
                    #
                    #   R ----------------- G - ... - X
                    #       X:(inf, G) ->
                    #
                    d = (self._inf_dist, dest)
                    distances.append(d)
                else:
                    d = (dest_router_info.dist, dest)
                    distances.append(d)
            return distances

        def send_distances(routers):
            for to_router in routers:
                # Prepare data to send.
                distances = distances_for_sending(to_router)
                raw_data = RIPData(distances).serialize()

                # Send data.
                self._service_transmitter.send_data(to_router, raw_data)

                # Mark time data was sent.
                connected_routers_info[to_router].timer.restart()

        def handle_receive():
            while True:
                result = self._service_transmitter.receive_data(block=False)
                if result is None:
                    break
                src, raw_data = result

                rip_data = RIPData.deserialize(raw_data)

                for dist, dest in rip_data.distances:
                    dist = max(dist + 1, self._inf_dist)
                    if (dest not in dest_routers_info or
                            dest_routers_info[dist].dist > dist or
                            dest_routers_info[dist].next_router == src):
                        dest_routers_info[dist] = DestRouterInfo(
                            dist=dist, next_router=src,
                            timer=Timer(self._inf_timeout
                                if dist != self._inf_dist
                                else self._remove_timeout))

        def update_routing_table():
            with self._dest_to_next_router_lock:
                self._dest_to_next_router.clear()

                for dest, dest_rr_info in dest_routers_info.iteritems():
                    if dest_rr_info.dist < self._inf_dist:
                        assert dest not in self._dest_to_next_router
                        assert (dest_rr_info.next_router in connected_routers or
                            dest_rr_info.next_router == self._router_name)
                        self._dest_to_next_router[dest] = \
                            dest_rr_info.next_router

        logger = logging.getLogger("{0}._work".format(self))

        logger.info("Working thread started")

        DestRouterInfo = recordtype(
            'DestRouterInfo', 'dist next_router timer')
        ConnectedRouterInfo = recordtype(
            'ConnectedRouterInfo', 'timer')

        # {destination router name: DestRouterInfo()}
        # `timer' member is for last time information about destination router
        # was updated,
        dest_routers_info = {self._router_name:
            DestRouterInfo(dist=0, next_router=self._router_name, timer=DummyTimer())}

        # {connected router: ConnectedRouterInfo()}
        # `timer' member if for last time information packet was sent to
        # router}
        connected_routers_info = {}

        connected_routers = frozenset()
        while True:
            if self._exit_lock.acquire(False):
                # Obtained exit lock. Terminate.

                self._exit_lock.release()
                logger.info("Exit working thread")
                return

            # Prepare data for detecting changes in current router connectivity.
            prev_connected_routers = connected_routers
            connected_routers = \
                frozenset(self._link_manager.connected_routers())
                
            # Remove information about disconnected routers and add information
            # about newly connected routers.
            update_connected_routers_info()

            # Send distances information to all who needs it.
            send_distances(list(connected_routers_with_timeout()))

            # Update distances according to received packets.
            handle_receive()

            set_infinite_timeout_distances()
            remove_timeout_distances()

            update_routing_table()

            time.sleep(1e-3)

def _test():
    # TODO: Use in separate file to test importing functionality.

    import unittest2 as unittest
    import logging

    from link_manager import RouterLinkManager
    from datagram import DatagramRouter
    from service_manager import RouterServiceManager

    class Tests(object):
        class TestRIPData(unittest.TestCase):
            def test_main(self):
                distances = [(1, 1), (2, 2)]
                rd = RIPData(distances)
                self.assertEqual(rd.distances, distances)

                raw_rd = rd.serialize()
                new_rd = RIPData.deserialize(raw_rd)

                self.assertEqual(rd, new_rd)
                self.assertEqual(new_rd.distances, distances)

        class TestRIPServiceBasic(unittest.TestCase):
            def setUp(self):
                self.lm1 = RouterLinkManager()

                self.dt1 = DatagramRouter(
                    router_name=1,
                    link_manager=self.lm1)

                self.sm1 = RouterServiceManager(self.dt1)
                self.rip_st1 = self.sm1.register_service(520)

            def test_constructor(self):
                rs1 = RIPService(1, self.lm1, self.rip_st1)

                rs1.terminate()

            def test_main(self):
                rs1 = RIPService(1, self.lm1, self.rip_st1)

                self.assertEqual(rs1.dynamic_routing_table().next_router(1), 1)
                self.assertEqual(rs1.dynamic_routing_table().next_router(2),
                    None)

                rs1.terminate()

            def tearDown(self):
                self.sm1.terminate()
                self.dt1.terminate()

        class TestRIPService1(unittest.TestCase):
            def setUp(self):
                self.lm1 = RouterLinkManager()

                self.dt1 = DatagramRouter(
                    router_name=1,
                    link_manager=self.lm1)

                self.sm1 = RouterServiceManager(self.dt1)
                self.rip_st1 = self.sm1.register_service(520)

                self.rs1 = RIPService(1, self.lm1, self.rip_st1,
                    update_period=0.3, inf_timeout=0.6, remove_timeout=1)

            def test_dynamic_routing(self):
                self.dt1.set_routing_table(self.rs1.dynamic_routing_table())

                time.sleep(5)

            def test_dynamic_routing_transfer(self):
                self.dt1.set_routing_table(self.rs1.dynamic_routing_table())
                #time.sleep(0.5)

                s10 = self.sm1.register_service(10)
                s15 = self.sm1.register_service(15)

                unreach_p10 = Packet(1, 2, "unreachable test (10)")
                s10.send(unreach_p10)

                p10_1 = Packet(1, 1, "test (10)")
                s10.send(p10_1)

                self.assertEqual(s10.receive(), p10_1)

                self.assertEqual(s10.receive(block=False), None)

                p15_1 = Packet(1, 1, "test (15)")
                p10_2 = Packet(1, 1, "test 2 (10)")

                s10.send(p10_1)
                s15.send(p15_1)
                s10.send(p10_2)

                self.assertEqual(s15.receive(), p15_1)
                self.assertEqual(s15.receive(block=False), None)
                self.assertEqual(s10.receive(), p10_1)
                self.assertEqual(s10.receive(), p10_2)
                self.assertEqual(s10.receive(block=False), None)

                text = "".join(map(chr, xrange(256)))
                p15_2 = Packet(1, 1, text * 10)
                s15.send(p15_2)
                s10.send(p10_1)
                self.assertEqual(s10.receive(), p10_1)
                self.assertEqual(s15.receive(), p15_2)

            def tearDown(self):
                self.rs1.terminate()
                self.sm1.terminate()
                self.dt1.terminate()

    logging.basicConfig(level=logging.DEBUG)

    suite = unittest.TestSuite()
    for k, v in Tests.__dict__.iteritems():
        if k.startswith('Test'):
            suite.addTests(unittest.TestLoader().loadTestsFromTestCase(v))

    unittest.TextTestRunner(verbosity=2).run(suite)

if __name__ == "__main__":
    _test()
