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

__all__ = ["FrameTransmitter", "FrameTransmitterWorker", "worker"]

"""Transmit frame between two connected hosts with acknowledge.
"""

import itertools
import struct
import binascii
import threading
import time
import logging
import Queue
from collections import deque
from recordtype import recordtype

import config
from frame import SimpleFrameTransmitter

class FrameType(object):
    data = 1
    ack  = 2

class InvalidFrameException(Exception):
    # TODO: Remove dummy constructor.
    def __init__(self, *args, **kwargs):
        super(InvalidFrameException, self).__init__(*args, **kwargs)

# TODO: Inherit from recordtype.
class Frame(object):
    # Frame:
    #    1     2     1      4             4     - field size
    # *------*----*------*-----*--  --*-------*
    # | type | id | last | len | data | CRC32 |
    # *------*----*------*-----*--  --*-------*

    format_string = '<BHBL{0}sL'
    empty_frame_size = struct.calcsize(format_string.format(0))

    def __init__(self, *args, **kwargs):
        self.type = kwargs.pop('type')
        self.id = kwargs.pop('id')
        if self.type == FrameType.data:
            self.data    = kwargs.pop('data')
            self.is_last = kwargs.pop('is_last')
        else:
            self.data = ""
            if 'data' in kwargs:
                kwargs.pop('data')
            self.is_last = False
            if 'is_last' in kwargs:
                kwargs.pop('is_last')
        super(Frame, self).__init__(*args, **kwargs)

    def crc(self):
        return binascii.crc32(self.serialize(0)) & 0xffffffff

    def serialize(self, crc = None):
        """Returns string representing frame."""

        if crc is not None:
            return struct.pack(
                self.format_string.format(len(self.data)),
                self.type, self.id, self.is_last, len(self.data),
                self.data, crc)
        else:
            return self.serialize(self.crc())

    @staticmethod
    def deserialize(frame_str):
        # TODO: Add frame dump into InvalidFrameException error message.

        data_len = len(frame_str) - Frame.empty_frame_size
        if data_len < 0:
            raise InvalidFrameException(
                "Frame too small, not enough fields")

        frame_type, frame_id, is_last, read_data_len, frame_data, frame_crc = \
                struct.unpack(Frame.format_string.format(data_len), frame_str)
        
        if frame_type not in [FrameType.data, FrameType.ack]:
            raise InvalidFrameException(
                "Invalid frame type '{0}'".format(frame_type))

        if read_data_len != data_len:
            raise InvalidFrameException(
                "Invalid data length: {0}, expected {1}".format(
                    read_data_len, data_len))

        frame = Frame(type=frame_type, id=frame_id, is_last=is_last,
            data=frame_data)

        if frame_crc != frame.crc():
            raise InvalidFrameException(
                "Invalid ckecksum: {0:04X}, correct one is {1:04X}".format(
                    frame_crc, frame.crc()))

        return frame

    def __str__(self):
        if self.type == FrameType.data:
            return "Data({id}, is_last={is_last}, 0x{data})".format(
                id=self.id, is_last=self.is_last,
                data=self.data.encode('hex'))
        elif self.type == FrameType.ack:
            return "Ack({id})".format(id=self.id)
        else:
            assert False

    # TODO: Implement __eq__(), __ne__().

def clear_queue(q):
    while True:
        try:
            q.get(block=False)
        except Queue.Empty:
            break

class FrameTransmitterWorker(object):
    def __init__(self):
        super(FrameTransmitterWorker, self).__init__()

        self._logger = logging.getLogger("FrameTransmitterWorker")

        self._frame_transmitters = set()
        self._frame_transmitters_lock = threading.RLock()

        self._working_thread = None
        self._exit_lock = threading.RLock()

    def add_frame_transmitter(self, frame_transmitter):
        with self._frame_transmitters_lock:
            if self._working_thread is None:
                # If working thread will be able to acquire the lock, then it
                # should terminate himself.
                self._exit_lock.acquire()

                self._working_thread = threading.Thread(target=self._work)
                self._working_thread.start()

            self._frame_transmitters.add(frame_transmitter)

    def remove_frame_transmitter(self, frame_transmitter):
        with self._frame_transmitters_lock:
            self._frame_transmitters.remove(frame_transmitter)

            if not self._frame_transmitters:
                # Release exit lock and wait until working thread will not
                # terminate.

                # If _exit_lock already released then somebody already called
                # terminate().
                self._exit_lock.release()
                self._working_thread.join()

                self._working_thread = None        

    def _work(self):
        self._logger.info("Working thread started")
        
        while True:
            if self._exit_lock.acquire(False):
                # Obtained exit lock. Terminate.

                self._exit_lock.release()
                self._logger.info("Exit working thread")
                return

            with self._frame_transmitters_lock:
                for frame_transmitter in self._frame_transmitters:
                    frame_transmitter.update()

            time.sleep(config.frame_transmitter_thread_sleep_time)

worker = FrameTransmitterWorker()

class FrameTransmitter(object):
    _frame_id_period = 32768

    class _SendWindow(object):
        SendItem = recordtype('SendItem', 'id time frame ack_received')

        def __init__(self, logger, maxlen, frame_id_it, timeout):
            super(FrameTransmitter._SendWindow, self).__init__()

            self._logger = logger
            self.maxlen = maxlen
            self.queue = deque(maxlen=maxlen)
            self.frame_id_it = frame_id_it
            self.timeout = timeout

        def can_add_next(self):
            return len(self.queue) < self.maxlen

        def add_next(self, is_last, data, curtime=None):
            assert self.can_add_next()

            using_curtime = curtime if curtime is not None else time.time()

            frame_id = self.frame_id_it.next()
            p = Frame(type=FrameType.data, id=frame_id, is_last=is_last,
                data=data)
            item = FrameTransmitter._SendWindow.SendItem(
                frame_id, using_curtime, p, False)
            self.queue.append(item)

            return item

        def timeout_items(self, curtime=None):
            using_curtime = curtime if curtime is not None else time.time()
            for item in self.queue:
                if item.time + self.timeout < using_curtime:
                    yield item

        def ack_received(self, frame_id):
            # TODO: Performance issue.
            for item in self.queue:
                if item.id == frame_id:
                    item.ack_received = True
                    break
            else:
                self._logger.warning(
                    "Received ack for frame outside working window: {0}".
                        format(frame_id))

            while len(self.queue) > 0 and self.queue[0].ack_received:
                self.queue.popleft()

    class _ReceiveWindow(object):
        ReceiveItem = recordtype('ReceiveItem', 'id frame')

        def __init__(self, logger, maxlen, frame_id_it):
            super(FrameTransmitter._ReceiveWindow, self).__init__()

            self._logger = logger
            self.queue = deque(maxlen=maxlen)
            self.frame_id_it = frame_id_it

            # Fill receive window with placeholders for receiving frames.
            for idx in xrange(maxlen):
                item = FrameTransmitter._ReceiveWindow.ReceiveItem(
                    self.frame_id_it.next(), None)
                self.queue.append(item)

        def receive_frame(self, frame):
            # TODO: Performance issue.
            for item in self.queue:
                if item.id == frame.id:
                    item.frame = frame
                    break
            else:
                self._logger.warning(
                    "Received frame outside working window: {0}".
                        format(frame))

            while self.queue[0].frame is not None:
                yield self.queue[0].frame

                self.queue.popleft()
                new_item = FrameTransmitter._ReceiveWindow.ReceiveItem(
                    self.frame_id_it.next(), None)
                self.queue.append(new_item)

    def __init__(self, *args, **kwargs):
        self._simple_frame_transmitter = kwargs.pop('simple_frame_transmitter')
        self._max_frame_data = kwargs.pop('max_frame_data', 100)
        self._window_size = kwargs.pop('window_size', 100)
        self._ack_timeout = kwargs.pop('ack_timeout', 0.5)

        global worker
        self._worker = kwargs.pop('worker', worker)

        self._debug_src = kwargs.pop('debug_src', '?')
        self._debug_dest = kwargs.pop('debug_dest', '?')
        super(FrameTransmitter, self).__init__(*args, **kwargs)

        if not hasattr(self, "_logger"):
            self._logger = logging.getLogger(
                "FrameTransmitter.{0}->{1}".format(
                    self._debug_src, self._debug_dest))

        # Queue of tuples (is_last, frame_data).
        self._frames_data_to_send = Queue.Queue()
        # Queue of tuples (is_last, frame_data).
        self._received_data = Queue.Queue()

        self._received_frames_buffer = []

        self._send_window = FrameTransmitter._SendWindow(
            self._logger, self._window_size,
            itertools.cycle(xrange(self._frame_id_period)),
            self._ack_timeout)
        self._receive_window = FrameTransmitter._ReceiveWindow(
            self._logger, self._window_size,
            itertools.cycle(xrange(self._frame_id_period)))

        self._enabled = True
        self._enabled_lock = threading.RLock()

        self._worker.add_frame_transmitter(self)

    @property
    def enabled(self):
        return self._enabled

    @enabled.setter
    def enabled(self, value):
        with self._enabled_lock:
            if self._enabled != bool(value):
                self._enabled = bool(value)

                if self._enabled:
                    # Link up.
                    self._link_up()
                else:
                    # Link down.
                    self._link_down()

    def _link_up(self):
        pass

    def _link_down(self):
        clear_queue(self._frames_data_to_send)
        clear_queue(self._received_data)

    # TODO
    def terminate(self):
        self._worker.remove_frame_transmitter(self)

    def send(self, data_string):
        with self._enabled_lock:
            if self._enabled:
                # Subdivide data string on frames and put them into working
                # queue.
                frame_data_parts = \
                    [data_string[i:i + self._max_frame_data]
                        for i in xrange(
                            0, len(data_string), self._max_frame_data)]
                for frame_data_part in frame_data_parts[:-1]:
                    self._frames_data_to_send.put((False, frame_data_part))
                self._frames_data_to_send.put((True, frame_data_parts[-1]))
            else:
                # Link is down.
                pass

    def receive(self, block=True):
        with self._enabled_lock:
            if self._enabled:
                while True:
                    try:
                        is_last, frame = self._received_data.get(block)
                        self._received_frames_buffer.append(frame)
                        if is_last:
                            data_string = "".join(self._received_frames_buffer)
                            self._received_frames_buffer = []
                            return data_string
                    except Queue.Empty:
                        break
            else:
                # Link is down.
                assert self._received_data.empty()
                assert not self._received_frames_buffer
                return None

    def update(self):
        """Send/receive frames. Called from working thread."""
        # Send frames.
        if (not self._frames_data_to_send.empty() and
                self._send_window.can_add_next()):
            # Have frame for sending in queue and free space in send
            # window. Send frame.

            is_last, frame_data = self._frames_data_to_send.get()

            item = self._send_window.add_next(is_last, frame_data)

            self._logger.debug("Sending:\n  {0}".format(str(item.frame)))
            self._simple_frame_transmitter.write_frame(
                item.frame.serialize())

        # Handle timeouts.
        curtime = time.time()
        for item in self._send_window.timeout_items(curtime):
            # TODO: Currently it is selective repeat.

            self._logger.warning("Resending due to timeout:\n  {0}".format(
                str(item.frame)))
            self._simple_frame_transmitter.write_frame(
                item.frame.serialize())
            item.time = curtime
        assert len(list(self._send_window.timeout_items(curtime))) == 0

        # Handle receiving data.
        frame = self._simple_frame_transmitter.read_frame(block=False)
        if frame is not None:
            # Received frame.

            try:
                p = Frame.deserialize(frame)
            except InvalidFrameException as ex:
                self._logger.warning("Received invalid frame: {0}".format(
                    str(ex)))
            else:
                self._logger.debug("Received:\n  {0}".format(p))

                if p.type == FrameType.data:
                    # Received data.

                    # Send ACK (even if frame already received before).
                    ack = Frame(type=FrameType.ack, id=p.id, data="")
                    self._logger.debug("Sending acknowledge:\n  {0}".format(ack))
                    self._simple_frame_transmitter.write_frame(
                        ack.serialize())

                    for frame in self._receive_window.receive_frame(p):
                        self._received_data.put((frame.is_last, frame.data))

                elif p.type == FrameType.ack:
                    # Received ACK.

                    self._send_window.ack_received(p.id)

                else:
                    assert False
# --- cut here in report ---

def experiment(window_size, max_frame_data, data_list, loss_prob=None):
    from duplex_link import FullDuplexLink, LossFunc

    if loss_prob is not None:
        loss_func = LossFunc(
            loss_prob / 3.0, loss_prob / 3.0, loss_prob / 3.0)
        a, b = FullDuplexLink(loss_func=loss_func)
    else:
        a, b = FullDuplexLink()

    at = SimpleFrameTransmitter(node=a)
    bt = SimpleFrameTransmitter(node=b)

    aft = FrameTransmitter(window_size=window_size,
        max_frame_data=max_frame_data, simple_frame_transmitter=at,
        debug_src=1, debug_dest=2)
    bft = FrameTransmitter(window_size=window_size,
        max_frame_data=max_frame_data, simple_frame_transmitter=bt,
        debug_src=2, debug_dest=1)

    receive_list = []

    start_time = time.time()
    for data in data_list:
        aft.send(data)

        while True:
            recv_data = bft.receive(False)
            if recv_data is None:
                break
            receive_list.append(recv_data)

    while len(receive_list) != len(data_list):
        recv_data = bft.receive()
        receive_list.append(recv_data)
    end_time = time.time()

    aft.terminate()
    bft.terminate()

    return (end_time - start_time,
        at.write_frames_count + bt.write_frames_count)

def average_experiment(window_size, max_frame_data, data_list, loss_prob=None,
        tries=3):
    results = []
    for i in xrange(tries):
        results.append(experiment(
            window_size, max_frame_data, data_list, loss_prob))

    avg_time  = sum(zip(*results)[0]) / float(len(results))
    avg_count = sum(zip(*results)[1]) / float(len(results))

    return avg_time, avg_count

def _test(level=None):
    # TODO: Use in separate file to test importing functionality.

    from testing import unittest, do_tests
    
    from duplex_link import FullDuplexLink, LossFunc

    class Tests(object):
        class TestFrame(unittest.TestCase):
            def test_frame(self):
                id = 13804
                data = "Some test data for Frame class (12334567890)."
                p = Frame(type=FrameType.data, id=id, is_last=True, data=data)
                s = p.serialize()
                np = Frame.deserialize(s)
                self.assertEqual(p.type, np.type)
                self.assertEqual(p.id, np.id)
                self.assertEqual(p.data, np.data)

                p = Frame(type=FrameType.data, id=id, is_last=True, data="")
                s = p.serialize()
                np = Frame.deserialize(s)
                self.assertEqual(p.type, np.type)
                self.assertEqual(p.id, np.id)
                self.assertEqual("", np.data)

        class TestFrameTransmitterConstructor(unittest.TestCase):
            def setUp(self):
                self.a, self.b = FullDuplexLink()

                self.at = SimpleFrameTransmitter(node=self.a)
                self.bt = SimpleFrameTransmitter(node=self.b)

            def test_constructor(self):
                aft = FrameTransmitter(simple_frame_transmitter=self.at,
                    debug_src=1, debug_dest=2)
                bft = FrameTransmitter(simple_frame_transmitter=self.bt,
                    debug_src=2, debug_dest=1)

                aft.terminate()
                bft.terminate()

            @unittest.expectedFailure
            def test_terminate(self):
                aft = FrameTransmitter(simple_frame_transmitter=self.at)
                aft.terminate()
                aft.terminate()

        class TestFrameTransmitter(unittest.TestCase):
            def setUp(self):
                self.a, self.b = FullDuplexLink()

                self.at = SimpleFrameTransmitter(node=self.a)
                self.bt = SimpleFrameTransmitter(node=self.b)

                self.aft = FrameTransmitter(simple_frame_transmitter=self.at,
                    debug_src=1, debug_dest=2)
                self.bft = FrameTransmitter(simple_frame_transmitter=self.bt,
                    debug_src=2, debug_dest=1)

            def tearDown(self):
                self.aft.terminate()
                self.bft.terminate()

            def test_transmit(self):
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

            def test_enabled(self):
                self.assertTrue(self.aft.enabled)

                text = "Test!"
                self.aft.send(text)
                self.assertEqual(self.bft.receive(), text)

                self.aft.enabled = False
                self.assertFalse(self.aft.enabled)

                self.aft.send(text)
                self.assertEqual(self.bft.receive(block=False), None)

                self.aft.enabled = True

                self.aft.send(text)
                self.assertEqual(self.bft.receive(block=False), None)

                self.aft.send(text)
                self.aft.enabled = False
                self.assertFalse(self.aft.enabled)

                self.aft.enabled = True
                self.assertEqual(self.bft.receive(block=False), None)
                
        class TestFrameTransmitterWithLosses(unittest.TestCase):
            def setUp(self):
                self.a, self.b = FullDuplexLink(
                    loss_func=LossFunc(0.001, 0.001, 0.001))

                self.at = SimpleFrameTransmitter(node=self.a)
                self.bt = SimpleFrameTransmitter(node=self.b)

                self.aft = FrameTransmitter(simple_frame_transmitter=self.at,
                    debug_src=1, debug_dest=2)
                self.bft = FrameTransmitter(simple_frame_transmitter=self.bt,
                    debug_src=2, debug_dest=1)

            def tearDown(self):
                self.aft.terminate()
                self.bft.terminate()

            def test_transmit_with_losses(self):
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

                #text4 = text2 * 10
                #self.aft.send(text4)
                #self.assertEqual(self.bft.receive(), text4)

                self.assertEqual(self.aft.receive(block=False), None)
                self.assertEqual(self.bft.receive(block=False), None)

        class TestExperiment(unittest.TestCase):
            def test_main(self):
                time_, sent = experiment(100, 100, ["data"], loss_prob=None)
                # TODO: Assume that computer is not very slow.
                self.assertLess(time_, 5.0)
                self.assertEqual(sent, 2)

                time_, sent = experiment(100, 100, ["data", "another"],
                    loss_prob=None)

                # TODO: Assume that computer is not very slow.
                self.assertLess(time_, 5.0)
                self.assertEqual(sent, 4)

    do_tests(Tests, level=level)

def _statistics():
    import time
    import csv

    import config

    config.thread_sleep_time = 1e-3
    config.frame_transmitter_thread_sleep_time = 1e-3

    data = "".join(map(chr, xrange(256))) * 8
    base_wsize = 100
    base_max_frame = 100
    base_loss_prob = 0.003

    with open("data_wsize.csv", "w") as f:
        csv_writer = csv.writer(f, lineterminator='\n')
        for wsize in range(1, 102, 3):
            time_, frames_count = \
                average_experiment(wsize, base_max_frame, [data],
                    loss_prob=None)
            print "{0} - time={1}, frames count={2}".format(
                wsize, time_, frames_count)
            csv_writer.writerow((wsize, time_, frames_count))

    with open("data_wsize_loss.csv", "w") as f:
        csv_writer = csv.writer(f, lineterminator='\n')
        for wsize in range(1, 102, 3):
            time_, frames_count = \
                average_experiment(wsize, base_max_frame, [data],
                    loss_prob=base_loss_prob)
            print "{0} - time={1}, frames count={2}".format(
                wsize, time_, frames_count)
            csv_writer.writerow((wsize, time_, frames_count))

    with open("data_maxframe.csv", "w") as f:
        csv_writer = csv.writer(f, lineterminator='\n')
        for maxframe in range(10, 402, 10):
            time_, frames_count = \
                average_experiment(base_wsize, maxframe, [data],
                    loss_prob=None)
            print "{0} - time={1}, frames count={2}".format(
                maxframe, time_, frames_count)
            csv_writer.writerow((maxframe, time_, frames_count))
            
    with open("data_maxframe_loss.csv", "w") as f:
        csv_writer = csv.writer(f, lineterminator='\n')
        for maxframe in range(10, 402, 10):
            time_, frames_count = \
                average_experiment(base_wsize, maxframe, [data],
                    loss_prob=base_loss_prob)
            print "{0} - time={1}, frames count={2}".format(
                maxframe, time_, frames_count)
            csv_writer.writerow((maxframe, time_, frames_count))

    with open("data_loss.csv", "w") as f:
        csv_writer = csv.writer(f, lineterminator='\n')
        for prob in [1e-5, 1e-4, 1e-3, 3e-3, 6e-3, 9e-3, 1e-2]:
            time_, frames_count = \
                average_experiment(base_wsize, base_max_frame, [data],
                    loss_prob=prob)
            print "{0} - time={1}, frames count={2}".format(
                prob, time_, frames_count)
            csv_writer.writerow((prob, time_, frames_count))

if __name__ == "__main__":
    _test(level=None)
    #_statistics()

# vim: set ts=4 sw=4 et:
