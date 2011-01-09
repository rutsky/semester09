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

__all__ = ["DatagramTransmitter", "Datagram"]

"""Transmit datagram between two connected hosts.
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

from sliding_window import DatagramTransmitter

class DatagramType(object):
    pass

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

class DatagramRouter(object):
    def __init__(self, *args, **kwargs):
        self._frame_transmitter = kwargs.pop('frame_transmitter')
        super(DatagramTransmitter, self).__init__(*args, **kwargs)

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

    def receive(self, size=0, block=True):
        assert size >= 0

        nreceived = 0
        while size == 0 or nreceived < size:
            try:
                yield self._received_data.get(block and (size > 0))
                nreceived += 1
            except Queue.Empty:
                break

    # TODO: Draft.
    def add_link(self, router_name, frame_transmitter):
        pass

    def remove_link(self, router_name):
        pass

    def _work(self):
        logger = logging.getLogger("{0}._work".format(self))

        logger.debug("Working thread started")

        while True:
            if self._exit_lock.acquire(False):
                # Obtained exit lock. Terminate.

                self._exit_lock.release()
                logger.debug("Exit working thread")
                return

def _test():
    # TODO: Use in separate file to test importing functionality.

    import unittest2 as unittest
    import gc
    
    from duplex_link import FullDuplexLink, LossFunc

    logging.basicConfig(level=logging.DEBUG)

    class TestDatagram(unittest.TestCase):
        def test_datagram(self):
            id = 13804
            data = "Some test data for Datagram class (12334567890)."
            p = Datagram(type=DatagramType.data, id=id, data=data)
            s = p.serialize()
            np = Datagram.deserialize(s)
            self.assertEqual(p.type, np.type)
            self.assertEqual(p.id, np.id)
            self.assertEqual(p.data, np.data)

            p = Datagram(type=DatagramType.data, id=id, data="")
            s = p.serialize()
            np = Datagram.deserialize(s)
            self.assertEqual(p.type, np.type)
            self.assertEqual(p.id, np.id)
            self.assertEqual("", np.data)

    class TestDatagramTransmitter(unittest.TestCase):
        def test_transmit(self):
            a, b = FullDuplexLink()

            at = SimpleDatagramTransmitter(node=a)
            bt = SimpleDatagramTransmitter(node=b)

            aft = DatagramTransmitter(simple_datagram_transmitter=at)
            bft = DatagramTransmitter(simple_datagram_transmitter=bt)

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

            at = SimpleDatagramTransmitter(node=a)
            bt = SimpleDatagramTransmitter(node=b)

            aft = DatagramTransmitter(simple_datagram_transmitter=at)
            bft = DatagramTransmitter(simple_datagram_transmitter=bt)

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

    suite = unittest.TestLoader().loadTestsFromTestCase(TestDatagram)
    unittest.TextTestRunner(verbosity=2).run(suite)
    suite = unittest.TestLoader().loadTestsFromTestCase(TestDatagramTransmitter)
    unittest.TextTestRunner(verbosity=2).run(suite)

    gc.collect()

if __name__ == "__main__":
    _test()
