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

__all__ = ["DatagramRouter", "Datagram", "datagram"]

"""Transmit datagram between two connected hosts.
"""

import itertools
import struct
import binascii
import threading
import logging
import Queue
import pprint
from recordtype import recordtype

from sliding_window import FrameTransmitter
from routing_table import loopback_routing_table

class InvalidDatagramException(Exception):
    def __init__(self, *args, **kwargs):
        super(InvalidDatagramException, self).__init__(*args, **kwargs)

# TODO: Inherit from recordtype.
class Datagram(object):
    # Datagram:
    #    1      4     4      4             4     - field size
    # *------*-----*------*-----*--  --*-------*
    # | type | src | dest | len | data | CRC32 |
    # *------*-----*------*-----*--  --*-------*

    format_string = '<BLLL{0}sL'
    empty_datagram_size = struct.calcsize(format_string.format(0))

    def __init__(self, *args, **kwargs):
        self.type = kwargs.pop('type')
        self.src  = kwargs.pop('src')
        self.dest = kwargs.pop('dest')
        self.data = kwargs.pop('data')
        super(Datagram, self).__init__(*args, **kwargs)

    def crc(self):
        return binascii.crc32(self.serialize(0)) & 0xffffffff

    def serialize(self, crc = None):
        """Returns string representing datagram."""

        if crc is not None:
            return struct.pack(
                self.format_string.format(len(self.data)),
                self.type, self.src, self.dest, len(self.data),
                self.data, crc)
        else:
            return self.serialize(self.crc())

    @staticmethod
    def deserialize(datagram_str):
        # TODO: Add datagram dump into InvalidDatagramException error message.

        data_len = len(datagram_str) - Datagram.empty_datagram_size
        if data_len < 0:
            raise InvalidDatagramException(
                "Datagram too small, not enough fields")

        datagram_type, datagram_src, datagram_dest, read_data_len, \
            datagram_data, datagram_crc = \
                struct.unpack(Datagram.format_string.format(data_len), datagram_str)
        
        if read_data_len != data_len:
            raise InvalidDatagramException(
                "Invalid data length: {0}, expected {1}".format(
                    read_data_len, data_len))

        datagram = Datagram(type=datagram_type, src=datagram_src,
            dest=datagram_dest, data=datagram_data)

        if datagram_crc != datagram.crc():
            raise InvalidDatagramException(
                "Invalid ckecksum: {0:04X}, correct one is {1:04X}".format(
                    datagram_crc, datagram.crc()))

        return datagram

    def __str__(self):
        return \
            "Datagram(type={type}, src={src}, dest={dest}, 0x{data})".format(
                type=self.type, src=self.src, dest=self.dest,
                data=self.data.encode('hex'))

    def __eq__(self, other):
        return (
            self.type == other.type and
            self.src  == other.src  and
            self.dest == other.dest and
            self.data == other.data)

    def __ne__(self, other):
        return not self == other

def datagram(type, src, dest, data):
    return Datagram(type=type, src=src, dest=dest, data=data)

class DatagramRouter(object):
    def __init__(self, *args, **kwargs):
        self._router_name       = kwargs.pop('router_name')
        self._link_manager      = kwargs.pop('link_manager')
        self._routing_table     = kwargs.pop('routing_table', 
            loopback_routing_table(self._router_name))
        self._routing_table_lock = threading.RLock()

        super(DatagramRouter, self).__init__(*args, **kwargs)

        # Queue of Datagram's.
        self._datagrams_to_send = Queue.Queue()
        # Queue of Datagram's.
        self._received_datagrams = Queue.Queue()

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

    # TODO: currently exposed datagram has exposed parts of low level
    # implementation, like serialize().
    def send(self, datagram):
        self._datagrams_to_send.put(datagram)

    def receive(self, block=True):
        try:
            return self._received_datagrams.get(block)
        except Queue.Empty:
            return None

    def set_routing_table(self, new_routing_table):
        with self._routing_table_lock:
            self._routing_table = new_routing_table

    def _work(self):
        def handle_datagram(from_router, datagram):
            # Detect next router for retransmitting.
            with self._routing_table_lock:
                next_router = self._routing_table.next_router(datagram.dest)
            logger.debug("  next router is {0}".format(next_router))

            if next_router == self._router_name:
                logger.debug("  datagram is addressed for this router, "
                    "pass it up for processing ")

                # Diagram addressed to current host.
                self._received_datagrams.put(datagram)
            else:
                if next_router in connected_routers:
                    # Retransmit to next router

                    logger.debug("  retransmit datagram")

                    connected_routers[next_router].send(
                        datagram.serialize())
                else:
                    # Next host is unreachable. Destroy datagram.
                    logger.warning(
                        "Datagram next router is unreachable. "
                        "Received from {0}, "
                        "next router {1}, "
                        "datagram:\n{2}".
                            format(from_router, next_router, str(datagram)))
                    logger.debug("Routing table:\n{0}".format(
                        pprint.pformat(connected_routers)))

        def handle_in_traffic():
            for from_router, frame_transmitter in connected_routers.iteritems():
                while True:
                    raw_datagram = frame_transmitter.receive(block=False)
                    if raw_datagram is None:
                        break

                    datagram = Datagram.deserialize(raw_datagram)

                    logger.debug("Received datagram from {0}:\n{1}".format(
                        from_router, str(datagram)))

                    handle_datagram(from_router, datagram)

        def handle_send_requests():
            while True:
                try:
                    datagram = self._datagrams_to_send.get(block=False)

                    logger.debug(
                        "Handling send request for datagram:\n{0}".format(
                            str(datagram)))

                    handle_datagram(self._router_name, datagram)
                except Queue.Empty:
                    break

        logger = logging.getLogger("{0}._work<router={1}>".format(
            self, self._router_name))

        logger.info("Working thread started")

        while True:
            if self._exit_lock.acquire(False):
                # Obtained exit lock. Terminate.

                self._exit_lock.release()
                logger.info("Exit working thread")
                return

            connected_routers = dict(self._link_manager.connected_links())

            handle_in_traffic()
            handle_send_requests()

def _test():
    # TODO: Use in separate file to test importing functionality.

    import unittest2 as unittest
    
    from duplex_link import FullDuplexLink, LossFunc
    from frame import SimpleFrameTransmitter
    from link_manager import RouterLinkManager
    from routing_table import loopback_routing_table, LocalRoutingTable

    class Tests(object):
        class TestDatagram(unittest.TestCase):
            def test_datagram(self):
                id = 13804
                data = "Some test data for Datagram class (12334567890)."
                p = Datagram(type=12, src=100, dest=200, data=data)
                s = p.serialize()
                np = Datagram.deserialize(s)
                self.assertEqual(p.type, np.type)
                self.assertEqual(p.src, np.src)
                self.assertEqual(p.dest, np.dest)
                self.assertEqual(p.data, np.data)

                p = Datagram(type=12, src=100, dest=200, data="")
                s = p.serialize()
                np = Datagram.deserialize(s)
                self.assertEqual(p.type, np.type)
                self.assertEqual(p.src, np.src)
                self.assertEqual(p.dest, np.dest)
                self.assertEqual("", np.data)

            def test_datagram_func(self):
                d = datagram(1, 2, 3, "test")
                self.assertEqual(d.type, 1)
                self.assertEqual(d.src, 2)
                self.assertEqual(d.dest, 3)
                self.assertEqual(d.data, "test")

        class TestDatagramRouterBasic(unittest.TestCase):
            def test_basic(self):
                lm = RouterLinkManager()

                dt10 = DatagramRouter(
                    router_name=10,
                    link_manager=lm)

                dt10.terminate()

        class TestDatagramRouter1(unittest.TestCase):
            def setUp(self):
                self.lm1 = RouterLinkManager()

                self.dt1 = DatagramRouter(
                    router_name=1,
                    link_manager=self.lm1)

            def test_set_routing_table(self):
                self.dt1.set_routing_table(loopback_routing_table(1))
                self.dt1.set_routing_table(LocalRoutingTable(1, self.lm1))

            def test_transmit(self):
                self.dt1.send(datagram(1, 1, 2, "unreachable test"))

                self.assertEqual(self.dt1.receive(block=False), None)

                self.dt1.send(datagram(13, 1, 1, "test"))
                d = self.dt1.receive()
                self.assertEqual(d.type, 13)
                self.assertEqual(d.src, 1)
                self.assertEqual(d.dest, 1)
                self.assertEqual(d.data, "test")

                self.dt1.send(datagram(14, 1, 1, "test 1"))
                self.dt1.send(datagram(15, 1, 1, "test 2"))

                d = self.dt1.receive()
                self.assertEqual(d.type, 14)
                self.assertEqual(d.src, 1)
                self.assertEqual(d.dest, 1)
                self.assertEqual(d.data, "test 1")

                d = self.dt1.receive()
                self.assertEqual(d.type, 15)
                self.assertEqual(d.src, 1)
                self.assertEqual(d.dest, 1)
                self.assertEqual(d.data, "test 2")

            def tearDown(self):
                self.dt1.terminate()

        class TestDatagramRouter2(unittest.TestCase):
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

            def test_transmit(self):
                d12 = datagram(12, 1, 2, "test")
                self.dr1.send(d12)
                self.assertEqual(self.dr2.receive(), d12)

                self.dr2.send(d12)
                self.assertEqual(self.dr2.receive(), d12)

                d21 = datagram(13, 2, 1, "test 2")
                self.dr2.send(d21)
                self.assertEqual(self.dr1.receive(), d21)

                self.dr1.send(d21)
                self.assertEqual(self.dr1.receive(), d21)

                text = "".join(map(chr, xrange(256)))
                d_big = datagram(130, 1, 2, text * 10)
                self.dr1.send(d_big)
                self.assertEqual(self.dr2.receive(), d_big)

                d12_2 = datagram(14, 1, 2, "test 2")
                d12_3 = datagram(14, 1, 2, "test 3")

                self.dr1.send(d12)
                self.dr1.send(d12_2)
                self.assertEqual(self.dr2.receive(), d12)
                self.dr1.send(d12_3)
                self.assertEqual(self.dr2.receive(), d12_2)
                self.assertEqual(self.dr2.receive(), d12_3)

            def tearDown(self):
                self.dr1.terminate()
                self.dr2.terminate()

                self.ft1.terminate()
                self.ft2.terminate()

        class TestDatagramRouter2WithLosses(unittest.TestCase):
            def setUp(self):
                l1, l2 = FullDuplexLink(loss_func=LossFunc(0.002, 0.002, 0.002))

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

            def test_transmit(self):
                d12 = datagram(12, 1, 2, "test")
                self.dr1.send(d12)
                self.assertEqual(self.dr2.receive(), d12)

                self.dr2.send(d12)
                self.assertEqual(self.dr2.receive(), d12)

                d21 = datagram(13, 2, 1, "test 2")
                self.dr2.send(d21)
                self.assertEqual(self.dr1.receive(), d21)

                self.dr1.send(d21)
                self.assertEqual(self.dr1.receive(), d21)

                text = "".join(map(chr, xrange(256)))
                d_big = datagram(130, 1, 2, text * 10)
                self.dr1.send(d_big)
                self.assertEqual(self.dr2.receive(), d_big)

                d12_2 = datagram(14, 1, 2, "test 2")
                d12_3 = datagram(14, 1, 2, "test 3")

                self.dr1.send(d12)
                self.dr1.send(d12_2)
                self.assertEqual(self.dr2.receive(), d12)
                self.dr1.send(d12_3)
                self.assertEqual(self.dr2.receive(), d12_2)
                self.assertEqual(self.dr2.receive(), d12_3)

            def tearDown(self):
                self.dr1.terminate()
                self.dr2.terminate()

                self.ft1.terminate()
                self.ft2.terminate()

    #logging.basicConfig(level=logging.DEBUG)
    logging.basicConfig()

    suite = unittest.TestSuite()
    for k, v in Tests.__dict__.iteritems():
        if k.startswith('Test'):
            suite.addTests(unittest.TestLoader().loadTestsFromTestCase(v))

    unittest.TextTestRunner(verbosity=2).run(suite)

if __name__ == "__main__":
    _test()
