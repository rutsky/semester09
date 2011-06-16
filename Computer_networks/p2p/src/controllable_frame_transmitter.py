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

__all__ = ["ControllableFrameTransmitter"]

"""Wrapper around FrameTransmitter to watch for transmitted frames.
"""

import logging
import itertools
import time
import heapq
import Queue

from recordtype import recordtype

import config
from sliding_window import FrameTransmitter
from service_manager import Packet, datagram_to_packet, InvalidPacketException
from datagram import Datagram, InvalidDatagramException

class ControllableFrameTransmitter(FrameTransmitter):
    class _HeapItem(recordtype('HeapItemBase',
            'delivery_time id raw_datagram packet')):
        pass

    def __init__(self, *args, **kwargs):
        self._src_name  = kwargs.pop('src_name')
        self._dest_name = kwargs.pop('dest_name')

        # TODO: Overflow-vulnerable.
        # DEBUG
        import random
        self._id_it = itertools.count(random.randint(0, 10000))
        #self._id_it = itertools.count(0)

        self._transmitting_heap = []
        self._delivered_frames_queue = []

        # Tuples (local packet id, start transmit time (in seconds),
        # end transmit time (in seconds), protocol, packet).
        # Tuples (local packet id, is packet successfully transmitted).
        self.send_receive_queue = Queue.Queue()

        self._logger = logging.getLogger(
            "ControllableFrameTransmitter.{0}->{1}".format(
                self._src_name, self._dest_name))

        super(ControllableFrameTransmitter, self).__init__(*args, **kwargs)

    def _link_down(self):
        for heap_item in self._transmitting_heap:
            self._logger.debug(
                "Deferred packet with id={0} delivered with failure due to link down: "
                "{1}".format(heap_item.id, str(heap_item.packet)))
            self.send_receive_queue.put((heap_item.id, False))
        self._transmitting_heap = []
        self._delivered_frames_queue = []
        super(ControllableFrameTransmitter, self)._link_down()
        
    def _non_blocking_receive(self):
        """Returns raw datagram if any received."""

        # Update internal state.
        # TODO: Updates done only when this function is called.


        # Check for delivered packets.
        current_time = time.time()
        while self._transmitting_heap:
            delivery_time, id_, raw_datagram, packet = self._transmitting_heap[0]

            if delivery_time <= current_time:
                # Packet delivery time reached --- put it in delivered packets
                # queue.
                self._delivered_frames_queue.append(raw_datagram)
                heapq.heappop(self._transmitting_heap)

                self._logger.debug("Deferred packet with id={0} " \
                    "delivered: {1}".format(id_, str(packet)))
                self.send_receive_queue.put((id_, True))
            else:
                break

        # Check for actual received packets.
        raw_datagram = \
            super(ControllableFrameTransmitter, self).receive(block=False)
        if raw_datagram is not None:
            # Try to decode frame as packet.

            try:
                datagram = Datagram.deserialize(raw_datagram)
                current_time = time.time()
                protocol, packet = datagram_to_packet(datagram, self._src_name)

                # Decoded packet --- put it on queue and emit signal about
                # new packet transmission.
                packet.time = current_time - packet.time

                real_transmit_time = current_time - datagram.time
                assert real_transmit_time >= 0

                transmit_time = real_transmit_time * \
                    config.packets_delivery_time_factor
                delivery_time = current_time + transmit_time

                heap_item = ControllableFrameTransmitter._HeapItem(
                    delivery_time,
                    self._id_it.next(),
                    raw_datagram,
                    packet)
                heapq.heappush(self._transmitting_heap, heap_item)

                self._logger.debug(
                    "Start transmission of deferred packet "
                    "(deliver in {0} seconds) with id={1}: {2}".format(
                        transmit_time, heap_item.id, str(packet)))

                self.send_receive_queue.put((heap_item.id,
                    current_time, delivery_time, protocol, packet))
            except InvalidDatagramException, InvalidPacketException:
                self._logger.warning(
                    "Received raw datagram is not packet: 0x{0}".format(
                        raw_datagram.encode('hex')))
                self._delivered_frames_queue.append(raw_datagram)

        if self._delivered_frames_queue:
            return self._delivered_frames_queue.pop(0)
        else:
            return None

    def receive(self, block=True):
        """Returns raw datagram if any received."""

        if block:
            while True:
                raw_datagram = self._non_blocking_receive()
                if raw_datagram is not None:
                    return raw_datagram
                else:
                    time.sleep(config.thread_sleep_time)
        else:
            return self._non_blocking_receive()

def _test(level=None, timeout=None):
    # TODO: Use in separate file to test importing functionality.

    from testing import unittest, do_tests, process_events_with_timeout

    from duplex_link import FullDuplexLink, LossFunc
    from sliding_window import SimpleFrameTransmitter
    from service_manager import packet_to_datagram
    
    class Tests(object):
        class TestControllableFrameTransmitterConstructor(unittest.TestCase):
            def setUp(self):
                self.a, self.b = FullDuplexLink()

                self.at = SimpleFrameTransmitter(node=self.a)
                self.bt = SimpleFrameTransmitter(node=self.b)

            def tearDown(self):
                process_events_with_timeout(timeout)

            def test_constructor(self):
                aft = ControllableFrameTransmitter(
                    src_name=1, dest_name=2,
                    simple_frame_transmitter=self.at,
                    debug_src=1, debug_dest=2)
                bft = ControllableFrameTransmitter(
                    src_name=2, dest_name=1,
                    simple_frame_transmitter=self.bt,
                    debug_src=2, debug_dest=1)

                aft.terminate()
                bft.terminate()

        class TestControllableFrameTransmitter(unittest.TestCase):
            def setUp(self):
                self.a, self.b = FullDuplexLink()

                self.at = SimpleFrameTransmitter(node=self.a)
                self.bt = SimpleFrameTransmitter(node=self.b)

                self.aft = ControllableFrameTransmitter(
                    src_name=1, dest_name=2,
                    simple_frame_transmitter=self.at,
                    debug_src=1, debug_dest=2)
                self.bft = ControllableFrameTransmitter(
                    src_name=2, dest_name=1,
                    simple_frame_transmitter=self.bt,
                    debug_src=2, debug_dest=1)

            def tearDown(self):
                self.aft.terminate()
                self.bft.terminate()

            def test_transmission(self):
                text = "Test!"
                self.aft.send(text)
                self.assertEqual(self.bft.receive(), text)

                self.assertEqual(self.bft.receive(block=False), None)

                text2 = "".join(map(chr, xrange(256)))
                self.bft.send(text2)
                self.assertEqual(self.aft.receive(), text2)

                self.assertEqual(self.aft.receive(block=False), None)

                text3 = "test"
                self.bft.send(text3)

                text_a = text2
                text_b = "".join(reversed(text2))
                self.aft.send(text_a)
                self.aft.send(text_b)
                self.assertEqual(self.aft.receive(), text3)
                self.assertEqual(self.bft.receive(), text_a)
                self.assertEqual(self.bft.receive(), text_b)

                text4 = text2 * 10
                self.aft.send(text4)
                self.assertEqual(self.bft.receive(), text4)

                self.assertEqual(self.aft.receive(block=False), None)
                self.assertEqual(self.bft.receive(block=False), None)

            def test_packet_transmission(self):
                packet = Packet(1, 2, "test", 1)
                datagram = packet_to_datagram(packet, 100)

                self.aft.send(datagram.serialize())

                self.assertEqual(self.bft.receive(), datagram.serialize())
                self.assertEqual(self.bft.receive(block=False), None)

            # TODO: Test signals.

    do_tests(Tests, level=level, qt=True)

if __name__ == "__main__":
    _test(level=0)

# vim: set ts=4 sw=4 et:
