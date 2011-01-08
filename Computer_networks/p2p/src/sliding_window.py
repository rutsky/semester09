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

__all__ = ["FrameTransmitter"]

"""Transmit frame between two connected hosts with acknowledge.
"""

import itertools
import struct
import binascii
import threading
import time
import logging
import Queue
import StringIO
from collections import deque
from recordtype import recordtype

from frame import SimpleFrameTransmitter

# TODO: So `Packet' of `Frame'?

class PacketType(object):
    data = 1
    ack  = 2

class InvalidPacketException(Exception):
    def __init__(self, *args, **kwargs):
        super(InvalidPacketException, self).__init__(*args, **kwargs)

# TODO: Inherit from recordtype.
class Packet(object):
    # Packet:
    #    1     2     4             4     - field size
    # *------*----*-----*--  --*-------*
    # | type | id | len | data | CRC32 |
    # *------*----*-----*--  --*-------*

    format_string = '<BHL{0}sL'
    empty_packet_size = struct.calcsize(format_string.format(0))

    def __init__(self, *args, **kwargs):
        self.type = kwargs.pop('type')
        self.id = kwargs.pop('id')
        if self.type == PacketType.data:
            self.data = kwargs.pop('data')
        else:
            self.data = ""
            if 'data' in kwargs:
                kwargs.pop('data')
        super(Packet, self).__init__(*args, **kwargs)

    def crc(self):
        return binascii.crc32(self.serialize(0)) & 0xffffffff

    def serialize(self, crc = None):
        """Returns string representing packet."""

        if crc is not None:
            return struct.pack(
                self.format_string.format(len(self.data)),
                self.type, self.id, len(self.data),
                self.data, crc)
        else:
            return self.serialize(self.crc())

    @staticmethod
    def deserialize(packet_str):
        data_len = len(packet_str) - Packet.empty_packet_size
        if data_len < 0:
            raise InvalidPacketException(
                "Packet too small, not enough fields")

        packet_type, packet_id, read_data_len, packet_data, packet_crc = \
                struct.unpack(Packet.format_string.format(data_len), packet_str)
        
        if packet_type not in [PacketType.data, PacketType.ack]:
            raise InvalidPacketException(
                "Invalid packet type '{0}'".format(packet_type))

        if read_data_len != data_len:
            raise InvalidPacketException(
                "Invalid data length: {0}, expected {1}".format(
                    read_data_len, data_len))

        packet = Packet(type=packet_type, id=packet_id, data=packet_data)

        if packet_crc != packet.crc():
            raise InvalidPacketException(
                "Invalid ckecksum: {0:04X}, correct one is {1:04X}".format(
                    packet_crc, packet.crc()))

        return packet

    def __str__(self):
        if self.type == PacketType.data:
            return "Data({id}, 0x{data})".format(id=self.id,
                data=self.data.encode('hex'))
        elif self.type == PacketType.ack:
            return "Ack({id})".format(id=self.id)
        else:
            assert False

class FrameTransmitter(object):
    #_frame_id_period = 32768
    _frame_id_period = 200 # DEBUG

    def __init__(self, *args, **kwargs):
        self._simple_frame_transmitter = kwargs.pop('simple_frame_transmitter')
        self._max_packet = kwargs.pop('max_packet_data', 100)
        self._window_size = kwargs.pop('window_size', 100)
        self._ack_timeout = kwargs.pop('ack_timeout', 0.2)
        super(FrameTransmitter, self).__init__(*args, **kwargs)

        # Queue of tuples (id, frame).
        self._frames_to_send = Queue.Queue()

        # Queue of characters.
        self._received_data = Queue.Queue()

        # If working thread will be able to acquire the lock, that it should
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

    def write(self, data_string):
        # Subdivide data string on frames and put them into working queue.
        for frame_part in [data_string[i:i + self._max_packet]
                for i in xrange(0, len(data_string), self._max_packet)]:
            self._frames_to_send.put(frame_part)

    def read(self, size=0, block=True):
        assert size >= 0

        in_str = StringIO.StringIO()

        while size == 0 or len(in_str.getvalue()) < size:
            try:
                in_str.write(self._received_data.get(block and (size > 0)))
            except Queue.Empty:
                break

        return in_str.getvalue()

    def _work(self):
        class SendWindow(object):
            SendItem = recordtype('SendItem', 'id time packet ack_received')

            def __init__(self, logger, maxlen, frame_id_it, timeout):
                super(SendWindow, self).__init__()

                self.logger = logger
                self.maxlen = maxlen
                self.queue = deque(maxlen=maxlen)
                self.frame_id_it = frame_id_it
                self.timeout = timeout

            def can_add_next(self):
                return len(self.queue) < self.maxlen

            def add_next(self, data, curtime=time.time()):
                assert self.can_add_next()

                frame_id = self.frame_id_it.next()                
                p = Packet(type=PacketType.data, id=frame_id, data=data)
                item = SendWindow.SendItem(frame_id, curtime, p, False)
                self.queue.append(item)

                return item

            def timeout_items(self, curtime=time.time()):
                for item in self.queue:
                    if item.time + self.timeout < curtime:
                        yield item

            def ack_received(self, frame_id):
                # TODO: Performance issue.
                for item in self.queue:
                    if item.id == frame_id:
                        item.ack_received = True
                        break
                else:
                    self.logger.warning(
                        "Received ack for frame outside working window: {0}".
                            format(frame_id))

                while len(self.queue) > 0 and self.queue[0].ack_received:
                    self.queue.popleft()

        class ReceiveWindow(object):
            ReceiveItem = recordtype('ReceiveItem', 'id packet')

            def __init__(self, logger, maxlen, frame_id_it):
                super(ReceiveWindow, self).__init__()

                self.logger = logger
                self.queue = deque(maxlen=maxlen)
                self.frame_id_it = frame_id_it
                
                # Fill receive window with placeholders for receiving frames.
                for idx in xrange(maxlen):
                    item = ReceiveWindow.ReceiveItem(self.frame_id_it.next(), None)
                    self.queue.append(item)

            def receive_frame(self, packet):
                # TODO: Performance issue.
                for item in self.queue:
                    if item.id == packet.id:
                        item.packet = packet
                        break
                else:
                    self.logger.warning(
                        "Received packet outside working window: {0}".
                            format(packet))

                while self.queue[0].packet is not None:
                    for ch in self.queue[0].packet.data:
                        yield ch

                    self.queue.popleft()
                    new_item = ReceiveWindow.ReceiveItem(self.frame_id_it.next(), None)
                    self.queue.append(new_item)

        logger = logging.getLogger("{0}._work".format(self))

        logger.debug("Working thread started")

        send_window = SendWindow(logger, self._window_size,
            itertools.cycle(xrange(self._frame_id_period)),
            self._ack_timeout)
        receive_window = ReceiveWindow(logger, self._window_size,
            itertools.cycle(xrange(self._frame_id_period)))

        while True:
            if self._exit_lock.acquire(False):
                # Obtained exit lock. Terminate.

                self._exit_lock.release()
                logger.debug("Exit working thread")
                return

            # Send frames.
            if not self._frames_to_send.empty() and send_window.can_add_next():
                # Have frame for sending in queue and free space in send
                # window. Send frame.

                frame = self._frames_to_send.get()

                item = send_window.add_next(frame)

                logger.debug("Sending:\n{0}".format(str(item.packet)))
                self._simple_frame_transmitter.write_frame(
                    item.packet.serialize())

            # Handle timeouts.
            curtime = time.time()
            for item in send_window.timeout_items(curtime):
                # TODO: Currently it is selective repeat.

                logger.debug("Resending due to timeout:\n{0}".format(
                    str(item.packet)))
                self._simple_frame_transmitter.write_frame(
                    item.packet.serialize())
                item.time = curtime
            assert len(list(send_window.timeout_items(curtime))) == 0

            # Handle receiving data.
            frame = self._simple_frame_transmitter.read_frame(block=False)
            if frame is not None:
                # Received frame.

                try:
                    p = Packet.deserialize(frame)
                except InvalidPacketException as ex:
                    logger.warning("Received invalid packet: {0}".format(
                        str(ex)))
                    continue
                else:
                    logger.debug("Received:\n{0}".format(p))

                if p.type == PacketType.data:
                    # Received data.

                    # Send ACK (even if packet already received before).
                    ack = Packet(type=PacketType.ack, id=p.id, data="")
                    logger.debug("Sending acknowledge:\n{0}".format(ack))
                    self._simple_frame_transmitter.write_frame(ack.serialize())

                    for ch in receive_window.receive_frame(p):
                        self._received_data.put(ch)

                elif p.type == PacketType.ack:
                    # Received ACK.

                    send_window.ack_received(p.id)
                    
                else:
                    assert False

def _test():
    # TODO: Use in separate file to test importing functionality.

    import unittest2 as unittest
    import gc
    
    from duplex_link import FullDuplexLink, LossFunc

    logging.basicConfig(level=logging.DEBUG)

    class TestPacket(unittest.TestCase):
        def test_packet(self):
            id = 13804
            data = "Some test data for Packet class (12334567890)."
            p = Packet(type=PacketType.data, id=id, data=data)
            s = p.serialize()
            np = Packet.deserialize(s)
            self.assertEqual(p.type, np.type)
            self.assertEqual(p.id, np.id)
            self.assertEqual(p.data, np.data)

            p = Packet(type=PacketType.data, id=id, data="")
            s = p.serialize()
            np = Packet.deserialize(s)
            self.assertEqual(p.type, np.type)
            self.assertEqual(p.id, np.id)
            self.assertEqual("", np.data)

    class TestFrameTransmitter(unittest.TestCase):
        def test_transmit(self):
            a, b = FullDuplexLink()

            at = SimpleFrameTransmitter(node=a)
            bt = SimpleFrameTransmitter(node=b)

            aft = FrameTransmitter(simple_frame_transmitter=at)
            bft = FrameTransmitter(simple_frame_transmitter=bt)

            text = "Test!"
            aft.write(text)
            self.assertEqual(bft.read(len(text)), text)

            self.assertEqual(bft.read(block=False), "")

            text2 = "".join(map(chr, xrange(256)))
            bft.write(text2)
            self.assertEqual(aft.read(len(text2)), text2)

            self.assertEqual(aft.read(block=False), "")

            text3 = "test"
            bft.write(text3)
            
            text_a = text2
            text_b = "".join(reversed(text2))
            aft.write(text_a)
            aft.write(text_b)
            self.assertEqual(aft.read(len(text3)), text3)
            self.assertEqual(bft.read(len(text_a + text_b)), text_a + text_b)

            text4 = text2 * 10
            aft.write(text4)
            self.assertEqual(bft.read(len(text4)), text4)

            self.assertEqual(aft.read(block=False), "")
            self.assertEqual(bft.read(block=False), "")

            aft.terminate()
            bft.terminate()

        def test_transmit_with_losses(self):
            a, b = FullDuplexLink(loss_func=LossFunc(0.002, 0.002, 0.002))

            at = SimpleFrameTransmitter(node=a)
            bt = SimpleFrameTransmitter(node=b)

            aft = FrameTransmitter(simple_frame_transmitter=at)
            bft = FrameTransmitter(simple_frame_transmitter=bt)

            text = "Test!"
            aft.write(text)
            self.assertEqual(bft.read(len(text)), text)

            self.assertEqual(bft.read(block=False), "")

            text2 = "".join(map(chr, xrange(256)))
            bft.write(text2)
            self.assertEqual(aft.read(len(text2)), text2)

            self.assertEqual(aft.read(block=False), "")

            text3 = "test"
            bft.write(text3)

            text_a = text2
            text_b = "".join(reversed(text2))
            aft.write(text_a)
            aft.write(text_b)
            self.assertEqual(aft.read(len(text3)), text3)
            self.assertEqual(bft.read(len(text_a + text_b)), text_a + text_b)

            #text4 = text2 * 100
            #aft.write(text4)
            #self.assertEqual(bft.read(len(text4)), text4)

            self.assertEqual(aft.read(block=False), "")
            self.assertEqual(bft.read(block=False), "")

            aft.terminate()
            bft.terminate()

    #unittest.main()

    suite = unittest.TestLoader().loadTestsFromTestCase(TestPacket)
    unittest.TextTestRunner(verbosity=2).run(suite)
    suite = unittest.TestLoader().loadTestsFromTestCase(TestFrameTransmitter)
    unittest.TextTestRunner(verbosity=2).run(suite)

    gc.collect()

if __name__ == "__main__":
    _test()
