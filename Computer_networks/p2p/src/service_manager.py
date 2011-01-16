import threading
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

__all__ = ["Packet", "RouterServiceManager"]

"""Manager for services built on top of DatagramRouter.
"""

import Queue
import threading
import time
import logging
from collections import namedtuple

from recordtype import recordtype

import config
from datagram import datagram

class Packet(recordtype('Packet', 'src dest data')):
    def __init__(self, *args, **kwargs):
        super(Packet, self).__init__(*args, **kwargs)

    def __eq__(self, other):
        return (
            self.src == other.src and
            self.dest == other.dest and
            self.data == other.data)

    def __ne__(self, other):
        return not self == other

def packet_to_datagram(packet, protocol):
    return datagram(type=protocol, src=packet.src,
        dest=packet.dest, data=packet.data)

def datagram_to_packet(datagram):
    return datagram.type, Packet(src=datagram.src, dest=datagram.dest,
        data=datagram.data)

class RouterServiceManager(object):
    # `_receive_queue' and `_send_queue' are queues for received and send
    # ServiceDatagram's accordingly.
    # TODO: rename to something like `ServiceTransmitter'.
    class _ServiceInfo(
            namedtuple('_ServiceInfoBase', 'name receive_queue send_queue')):
        def send(self, packet):
            assert isinstance(packet, Packet)

            self.send_queue.put(packet)

        def receive(self, block=True):
            try:
                return self.receive_queue.get(block)
            except Queue.Empty:
                return None

        def send_data(self, dest, data):
            self.send(Packet(self.name, dest, data))

        def receive_data(self, block=True):
            packet = self.receive(block)
            if packet is not None:
                return (packet.src, packet.data)
            else:
                return None

    def __init__(self, datagram_router):
        super(RouterServiceManager, self).__init__()

        self._datagram_router = datagram_router
        # { protocol: ServiceInfo() }
        self._services = {}
        self._services_lock = threading.Lock()

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

    @property
    def name(self):
        return self._datagram_router.name

    def register_service(self, protocol):
        service_info = \
            RouterServiceManager._ServiceInfo(self.name, Queue.Queue(), Queue.Queue())

        with self._services_lock:
            assert protocol not in self._services
            self._services[protocol] = service_info
        
        return service_info

    def _work(self):
        def deliver_to_network():
            with self._services_lock:
                services = self._services.items()[:]
                
            for protocol, service_info in services:
                while True:
                    try:
                        packet = service_info.send_queue.get(False)
                    except Queue.Empty:
                        break
                    datagram = packet_to_datagram(packet, protocol)
                    self._datagram_router.send(datagram)

        def deliver_from_network():
            while True:
                datagram = self._datagram_router.receive(block=False)
                if datagram is None:
                    break
                else:
                    protocol, packet = datagram_to_packet(datagram)

                    with self._services_lock:
                        if protocol in self._services:
                            self._services[protocol].receive_queue.put(packet)
                        else:
                            logger.warning(
                                "Packet for unregistered service {0} "
                                "unhandled:\n  {1}".format(
                                    protocol, packet))

        logger = logging.getLogger("{0}._work".format(self))

        logger.info("Working thread started")

        while True:
            if self._exit_lock.acquire(False):
                # Obtained exit lock. Terminate.

                self._exit_lock.release()
                logger.info("Exit working thread")
                return

            deliver_to_network()
            deliver_from_network()

            time.sleep(config.thread_sleep_time)

def _test(level=None):
    # TODO: Use in separate file to test importing functionality.

    from testing import unittest, do_tests
    
    from duplex_link import FullDuplexLink, LossFunc
    from frame import SimpleFrameTransmitter
    from sliding_window import FrameTransmitter
    from link_manager import RouterLinkManager
    from routing_table import loopback_routing_table, LocalRoutingTable
    from datagram import DatagramRouter

    class Tests(object):
        class TestPacket(unittest.TestCase):
            def test_main(self):
                p1 = Packet(    1,      2,      "3")
                p2 = Packet(src=1, dest=2, data="3")
                self.assertEqual(p1, p2)
                self.assertEqual(p1.src,  1)
                self.assertEqual(p1.dest, 2)
                self.assertEqual(p1.data, "3")

                d1 = packet_to_datagram(p1, 30)
                self.assertEqual(d1,
                    datagram(30, p1.src, p1.dest, p1.data))

                self.assertEqual(datagram_to_packet(d1), (d1.type, p1))

        class Test_ServiceInfo(unittest.TestCase):
            def test_main(self):
                sm = RouterServiceManager._ServiceInfo(0, 1, 2)
                self.assertEqual(sm.name, 0)
                self.assertEqual(sm.receive_queue, 1)
                self.assertEqual(sm.send_queue, 2)

        class TestRouterServiceManagerBasic(unittest.TestCase):
            def setUp(self):
                self.lm1 = RouterLinkManager()

                self.dt1 = DatagramRouter(
                    router_name=1,
                    link_manager=self.lm1)

            def test_constructor(self):
                sm = RouterServiceManager(self.dt1)

                sm.terminate()

            def test_main(self):
                sm = RouterServiceManager(self.dt1)

                s10 = sm.register_service(10)

                sm.terminate()
                
            def tearDown(self):
                self.dt1.terminate()

        class TestRouterServiceManager1(unittest.TestCase):
            def setUp(self):
                self.lm1 = RouterLinkManager()

                self.dt1 = DatagramRouter(
                    router_name=1,
                    link_manager=self.lm1)

                self.sm1 = RouterServiceManager(self.dt1)

            def test_send_receive_data(self):
                self.s30 = self.sm1.register_service(30)

                text = "Some text text."
                self.s30.send_data(1, text)
                self.assertEqual(self.s30.receive_data(), (1, text))
                self.assertEqual(self.s30.receive_data(False), None)

            def test_main(self):
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
                self.sm1.terminate()
                self.dt1.terminate()

        class TestRouterServiceManager2(unittest.TestCase):
            def setUp(self):
                l1, l2 = FullDuplexLink()

                sft1 = SimpleFrameTransmitter(node=l1)
                sft2 = SimpleFrameTransmitter(node=l2)

                self.ft1 = FrameTransmitter(simple_frame_transmitter=sft1)
                self.ft2 = FrameTransmitter(simple_frame_transmitter=sft2)

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

            def test_transmit(self):
                s1_77 = self.sm1.register_service(77)
                s2_77 = self.sm2.register_service(77)

                d12 = Packet(1, 2, "test")
                s1_77.send(d12)
                self.assertEqual(s2_77.receive(), d12)
                s2_77.send(d12)
                self.assertEqual(s2_77.receive(), d12)

                s1_33 = self.sm1.register_service(33)
                s2_33 = self.sm2.register_service(33)

                d21 = Packet(2, 1, "test 2")
                s2_33.send(d21)
                self.assertEqual(s1_33.receive(), d21)
                s1_33.send(d21)
                self.assertEqual(s1_33.receive(), d21)

                text = "".join(map(chr, xrange(256)))
                d_big = Packet(1, 2, text * 10)
                s1_33.send(d_big)
                self.assertEqual(s2_33.receive(), d_big)

                d12_2 = Packet(1, 2, "test 2")
                d12_3 = Packet(1, 2, "test 3")

                s1_33.send(d12)
                s1_33.send(d12_2)
                self.assertEqual(s2_33.receive(), d12)
                s1_77.send(d12_3)
                self.assertEqual(s2_77.receive(), d12_3)
                self.assertEqual(s2_33.receive(), d12_2)

            def tearDown(self):
                self.sm1.terminate()
                self.sm2.terminate()

                self.dr1.terminate()
                self.dr2.terminate()

                self.ft1.terminate()
                self.ft2.terminate()

        class TestRouterServiceManager2WithLosses(unittest.TestCase):
            def setUp(self):
                l1, l2 = FullDuplexLink(loss_func=LossFunc(0.001, 0.001, 0.001))

                sft1 = SimpleFrameTransmitter(node=l1)
                sft2 = SimpleFrameTransmitter(node=l2)

                self.ft1 = FrameTransmitter(simple_frame_transmitter=sft1)
                self.ft2 = FrameTransmitter(simple_frame_transmitter=sft2)

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

            def test_transmit(self):
                s1_77 = self.sm1.register_service(77)
                s2_77 = self.sm2.register_service(77)

                d12 = Packet(1, 2, "test")
                s1_77.send(d12)
                self.assertEqual(s2_77.receive(), d12)
                s2_77.send(d12)
                self.assertEqual(s2_77.receive(), d12)

                s1_33 = self.sm1.register_service(33)
                s2_33 = self.sm2.register_service(33)

                d21 = Packet(2, 1, "test 2")
                s2_33.send(d21)
                self.assertEqual(s1_33.receive(), d21)
                s1_33.send(d21)
                self.assertEqual(s1_33.receive(), d21)

                text = "".join(map(chr, xrange(256)))
                d_big = Packet(1, 2, text * 10)
                s1_33.send(d_big)
                self.assertEqual(s2_33.receive(), d_big)

                d12_2 = Packet(1, 2, "test 2")
                d12_3 = Packet(1, 2, "test 3")

                s1_33.send(d12)
                s1_33.send(d12_2)
                self.assertEqual(s2_33.receive(), d12)
                s1_77.send(d12_3)
                self.assertEqual(s2_77.receive(), d12_3)
                self.assertEqual(s2_33.receive(), d12_2)

            def tearDown(self):
                self.sm1.terminate()
                self.sm2.terminate()

                self.dr1.terminate()
                self.dr2.terminate()

                self.ft1.terminate()
                self.ft2.terminate()

    do_tests(Tests, level=level)

if __name__ == "__main__":
    _test(level=0)
