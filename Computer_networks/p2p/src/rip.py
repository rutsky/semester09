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
import pprint

from recordtype import recordtype

import config
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
    protocol = 520

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

        self._logger = logging.getLogger("RIPService.router={0}".format(
            self._router_name))

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
                self._logger.debug("Connected to routers: {0}".format(
                    list(new_connected_routers)))
            if new_disconnected_routers:
                self._logger.debug("Disconnected from routers: {0}".format(
                    list(new_disconnected_routers)))

            # Remove disconnected routers from list.
            for router_name in new_disconnected_routers:
                assert router_name in connected_rrs_info
                del connected_rrs_info[router_name]

            # Set distance to infinity for destination routers route to which
            # leaded through disconnected routers.
            for to_router, dest_router_info in dest_routers_info.iteritems():
                if dest_router_info.next_router in new_disconnected_routers:
                    dest_router_info.dist = self._inf_dist
                    self._logger.debug(
                        "Remove route: Due to disconnection: "
                        "{dest}:(d={dist}, n={next})".format(
                            dest=to_router, dist=dest_router_info.dist,
                            next=dest_router_info.next_router))

            # Add connected hosts to according list.
            for router_name in new_connected_routers:
                router_name not in connected_rrs_info
                connected_rrs_info[router_name] = \
                    ConnectedRouterInfo(Timer(self._update_period))

            # Update routing information for directly connected destination
            # routers.
            for router_name in new_connected_routers:
                dest_routers_info[router_name] = DestRouterInfo(
                    dist=1, next_router=router_name,
                    timer=DummyTimer())
                self._logger.debug(
                    "Add route: Directly connected: "
                    "{dest}:(d={dist}, n={next})".format(
                        dest=router_name,
                        dist=dest_routers_info[router_name].dist,
                        next=dest_routers_info[router_name].next_router))

            table_changed = new_connected_routers or new_disconnected_routers
            if table_changed:
                update_routing_table()

        def connected_routers_with_timeout():
            for rr_name, connected_rr_info in connected_rrs_info.iteritems():
                if connected_rr_info.timer.is_expired():
                    yield rr_name

        def set_infinite_timeout_distances():
            routing_table_updated = False
            for dest, dest_router_info in dest_routers_info.iteritems():
                if (dest_router_info.dist < self._inf_dist and 
                        dest_router_info.timer.is_expired()):
                    dest_router_info.dist = self._inf_dist
                    dest_router_info.timer = Timer(self._remove_timeout)
                    routing_table_updated = True

                    self._logger.debug(
                        "Remove route: Due to timeout: "
                        "{dest}:(d={dist}, n={next})".format(
                            dest=dest, dist=dest_router_info.dist,
                            next=dest_router_info.next_router))

            if routing_table_updated:
                update_routing_table()

        def remove_timeout_distances():
            routing_table_updated = False
            for dest, dest_router_info in dest_routers_info.items():
                if (dest_router_info.dist == self._inf_dist and
                        dest_router_info.timer.is_expired()):
                    del dest_routers_info[dest]

                    routing_table_updated = True

                    self._logger.debug(
                        "Due to big timeout removing target: {dest}".format(
                            dest=dest))

            # TODO: Not actually needed.
            if routing_table_updated:
                update_routing_table()

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
                connected_rrs_info[to_router].timer.restart()

                # TODO: Assume that computer is not slow.
                assert not connected_rrs_info[to_router].timer.is_expired()

        def handle_receive():
            while True:
                result = self._service_transmitter.receive_data(block=False)
                if result is None:
                    break
                src, raw_data = result

                rip_data = RIPData.deserialize(raw_data)

                self._logger.debug(
                    "Received vector from {0}:\n  {1}".format(
                        src,
                        pprint.pformat(rip_data.distances)))

                routing_table_updated = False
                for dist, dest in rip_data.distances:
                    dist = min(dist + 1, self._inf_dist)

                    if dest not in dest_routers_info:
                        # Route to new router.

                        if dist < self._inf_dist:
                            dest_routers_info[dest] = DestRouterInfo(
                                dist=dist, next_router=src,
                                timer=Timer(self._inf_timeout))

                            routing_table_updated = True

                            self._logger.debug(
                                "Received route to new router: "
                                "{dest}:(d={dist}, n={next})".format(
                                    dest=dest, dist=dist,
                                    next=src))
                        else:
                            # Ignore.
                            pass

                    elif dist < dest_routers_info[dest].dist:
                        # Received shorter then all known path to router.
                        
                        dest_routers_info[dest].dist = dist
                        dest_routers_info[dest].next_router = src
                        dest_routers_info[dest].timer = \
                            Timer(self._inf_timeout)

                        routing_table_updated = True

                        self._logger.debug(
                            "Found shorter path: "
                            "{dest}:(d={dist}, n={next})".format(
                                dest=dest, dist=dist,
                                next=src))

                    elif (dest_routers_info[dest].next_router == src and
                            dest_routers_info[dest].dist != dist):
                        # Received route update from source.

                        dest_routers_info[dest].dist = dist

                        timer = Timer(self._inf_timeout) \
                            if dist < self._inf_dist \
                            else Timer(self._remove_timeout)
                        dest_routers_info[dest].timer = timer

                        routing_table_updated = True

                        self._logger.debug(
                            "Received route update from source: "
                            "{dest}:(d={dist}, n={next})".format(
                                dest=dest, dist=dist,
                                next=src))
                    else:
                        if dist < self._inf_dist:
                            # Update timer.
                            dest_routers_info[dest].timer.restart()
                        else:
                            # Don't update timer for infinite paths.
                            pass

                if routing_table_updated:
                    update_routing_table()

        def update_routing_table():
            with self._dest_to_next_router_lock:
                old_routing_table = self._dest_to_next_router.copy()
                
                self._dest_to_next_router.clear()

                for dest, dest_rr_info in dest_routers_info.iteritems():
                    if dest_rr_info.dist < self._inf_dist:
                        assert dest not in self._dest_to_next_router
                        self._dest_to_next_router[dest] = \
                            dest_rr_info.next_router

                if old_routing_table != self._dest_to_next_router:
                    self._logger.debug("New routing table:\n  {0}".format(
                        pprint.pformat(self._dest_to_next_router)))

        self._logger.info("Working thread started")

        DestRouterInfo = recordtype(
            'DestRouterInfo', 'dist next_router timer')
        ConnectedRouterInfo = recordtype('ConnectedRouterInfo', 'timer')

        # {destination router name: DestRouterInfo()}
        # `timer' member is for last time information about destination router
        # was updated,
        dest_routers_info = {self._router_name:
            DestRouterInfo(dist=0, next_router=self._router_name,
                timer=DummyTimer())}

        # {connected router: ConnectedRouterInfo()}
        # `timer' member if for last time information packet was sent to
        # router}
        connected_rrs_info = {}

        connected_routers = frozenset()
        while True:
            if self._exit_lock.acquire(False):
                # Obtained exit lock. Terminate.

                self._exit_lock.release()
                self._logger.info("Exit working thread")
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

            time.sleep(config.thread_sleep_time)

def _test(init_logging=True, level=None, disabled_loggers=None):
    # TODO: Use in separate file to test importing functionality.

    from testing import unittest, do_tests

    from duplex_link import FullDuplexLink, LossFunc
    from frame import SimpleFrameTransmitter
    from sliding_window import FrameTransmitter
    from link_manager import RouterLinkManager
    from datagram import DatagramRouter
    from service_manager import RouterServiceManager
    from routing_table import loopback_routing_table, LocalRoutingTable

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
                self.rip_st1 = self.sm1.register_service(RIPService.protocol)

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
                self.rip_st1 = self.sm1.register_service(RIPService.protocol)

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

        class TestRIPService2(unittest.TestCase):
            def setUp(self):
                l1, l2 = FullDuplexLink()

                sft1 = SimpleFrameTransmitter(node=l1)
                sft2 = SimpleFrameTransmitter(node=l2)

                self.ft1 = FrameTransmitter(simple_frame_transmitter=sft1,
                    debug_src=1, debug_dest=2)
                self.ft2 = FrameTransmitter(simple_frame_transmitter=sft2,
                    debug_src=2, debug_dest=1)

                rlm1 = RouterLinkManager()
                rlm2 = RouterLinkManager()

                self.dr1 = DatagramRouter(
                    router_name=1,
                    link_manager=rlm1,
                    routing_table=LocalRoutingTable(1, rlm1))
                self.dr2 = DatagramRouter(
                    router_name=2,
                    link_manager=rlm2,
                    routing_table=LocalRoutingTable(2, rlm2))

                rlm1.add_link(2, self.ft1)
                rlm2.add_link(1, self.ft2)

                self.sm1 = RouterServiceManager(self.dr1)
                self.sm2 = RouterServiceManager(self.dr2)

                self.rip_st1 = self.sm1.register_service(RIPService.protocol)
                self.rip_st2 = self.sm2.register_service(RIPService.protocol)

                self.rs1 = RIPService(1, rlm1, self.rip_st1,
                    update_period=0.5, inf_timeout=0.9, remove_timeout=1.6)
                self.rs2 = RIPService(2, rlm2, self.rip_st2,
                    update_period=0.5, inf_timeout=0.9, remove_timeout=1.6)

                self.dr1.set_routing_table(self.rs1.dynamic_routing_table())
                self.dr2.set_routing_table(self.rs2.dynamic_routing_table())

            def test_transmit(self):
                s1_77 = self.sm1.register_service(77)
                s2_77 = self.sm2.register_service(77)

                d12 = Packet(1, 2, "test")
                s1_77.send(d12)
                print 1
                self.assertEqual(s2_77.receive(), d12)
                print 2
                s2_77.send(d12)
                self.assertEqual(s2_77.receive(), d12)
                print 3

                s1_33 = self.sm1.register_service(33)
                s2_33 = self.sm2.register_service(33)

                d21 = Packet(2, 1, "test 2")
                s2_33.send(d21)
                print 4
                self.assertEqual(s1_33.receive(), d21)
                s1_33.send(d21)
                self.assertEqual(s1_33.receive(), d21)
                print 5

                text = "".join(map(chr, xrange(256)))
                d_big = Packet(1, 2, text * 5)
                s1_33.send(d_big)
                self.assertEqual(s2_33.receive(), d_big)
                print 6

                d12_2 = Packet(1, 2, "test 2")
                d12_3 = Packet(1, 2, "test 3")

                s1_33.send(d12)
                s1_33.send(d12_2)
                self.assertEqual(s2_33.receive(), d12)
                print 7
                s1_77.send(d12_3)
                self.assertEqual(s2_77.receive(), d12_3)
                print 8
                self.assertEqual(s2_33.receive(), d12_2)
                print 10

            def tearDown(self):
                self.rs1.terminate()
                self.rs2.terminate()

                self.sm1.terminate()
                self.sm2.terminate()

                self.dr1.terminate()
                self.dr2.terminate()

                self.ft1.terminate()
                self.ft2.terminate()

        class TestRIPService2WithLosses(TestRIPService2):
            def setUp(self):
                l1, l2 = FullDuplexLink(loss_func=LossFunc(0.001, 0.001, 0.001))

                sft1 = SimpleFrameTransmitter(node=l1)
                sft2 = SimpleFrameTransmitter(node=l2)

                self.ft1 = FrameTransmitter(simple_frame_transmitter=sft1,
                    debug_src=1, debug_dest=2)
                self.ft2 = FrameTransmitter(simple_frame_transmitter=sft2,
                    debug_src=2, debug_dest=1)

                rlm1 = RouterLinkManager()
                rlm2 = RouterLinkManager()

                self.dr1 = DatagramRouter(
                    router_name=1,
                    link_manager=rlm1,
                    routing_table=LocalRoutingTable(1, rlm1))
                self.dr2 = DatagramRouter(
                    router_name=2,
                    link_manager=rlm2,
                    routing_table=LocalRoutingTable(2, rlm2))

                rlm1.add_link(2, self.ft1)
                rlm2.add_link(1, self.ft2)

                self.sm1 = RouterServiceManager(self.dr1)
                self.sm2 = RouterServiceManager(self.dr2)

                self.rip_st1 = self.sm1.register_service(RIPService.protocol)
                self.rip_st2 = self.sm2.register_service(RIPService.protocol)

                self.rs1 = RIPService(1, rlm1, self.rip_st1,
                    update_period=0.5, inf_timeout=0.9, remove_timeout=1.6)
                self.rs2 = RIPService(2, rlm2, self.rip_st2,
                    update_period=0.5, inf_timeout=0.9, remove_timeout=1.6)

                self.dr1.set_routing_table(self.rs1.dynamic_routing_table())
                self.dr2.set_routing_table(self.rs2.dynamic_routing_table())

    do_tests(Tests, level=level, disabled_loggers=disabled_loggers)

if __name__ == "__main__":
    disable_loggers = [
        "DatagramRouter.router=1",
        "DatagramRouter.router=2",
        "FrameTransmitter.1->2",
        "FrameTransmitter.2->1"
        ]
    
    _test(disabled_loggers=disable_loggers, level=0)
