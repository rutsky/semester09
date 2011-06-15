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

__all__ = ["DataSendService"]

"""Simple data transfer service.
"""

import threading
import pickle
import time
import logging
import pprint
import Queue

from recordtype import recordtype
from total_ordering import total_ordering

import config
from routing_table import DynamicRoutingTable, RouteToDestination
from service_manager import Packet
from timer import Timer, DummyTimer

class TransferData(recordtype('TransferDataBase',
                               'session_key data')):
    def __init__(self, *args, **kwargs):
        super(TransferData, self).__init__(*args, **kwargs)

    def serialize(self):
        return pickle.dumps((self.session_key, self.data))

    @staticmethod
    def deserialize(raw_data):
        data_tuple = pickle.loads(raw_data)
        return TransferData(*data_tuple)

class DataSendService(object):
    protocol = 3000

    def __init__(self, router_name, router_link_manager, service_transmitter,
            dest_router_name, **kwargs):
        self._send_period  = kwargs.pop('send_period',
            config.image_transfer_send_period)
        super(DataSendService, self).__init__()

        self._router_name = router_name
        self._link_manager = router_link_manager
        self._service_transmitter = service_transmitter

        self._dest_router_name = dest_router_name
        self._session_key = 1 # TODO: is lock required?

        self._logger = logging.getLogger("DataSendService.router={0}".format(
            self._router_name))

        self._transfer_data_queue = Queue.Queue()

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

    def reset_transfer_queue(self):
        while True:
            try:
                self._transfer_data_queue.get_nowait()
            except Queue.Empty:
                break

    def append_to_transfer_queue(self, data_it):
        for data in data_it:
            self._transfer_data_queue.put(data)

    def new_session(self):
        # TODO: Is lock required?
        self._session_key += 1

    def _work(self):
        def handle_send():
            try:
                data = self._transfer_data_queue.get_nowait()
            except Queue.Empty:
                do_transfer = False
            else:
                do_transfer = True

            if do_transfer:
                self._logger.debug("Send data packet")
                raw_data = TransferData(self._session_key, data).serialize()
                self._service_transmitter.send_data(
                    self._dest_router_name, raw_data)

        self._logger.info("Working thread started")

        while True:
            if self._exit_lock.acquire(False):
                # Obtained exit lock. Terminate.

                self._exit_lock.release()
                self._logger.info("Exit working thread")
                return

            handle_send()

            # TODO: Should "sleep" in timer: restart timer after each send
            # packet.
            time.sleep(self._send_period)

            time.sleep(config.thread_sleep_time)

class DataReceiveService(object):
    def __init__(self, router_name, router_link_manager, service_transmitter,
            **kwargs):
        super(DataReceiveService, self).__init__()

        self._router_name = router_name
        self._link_manager = router_link_manager
        self._service_transmitter = service_transmitter

        # TODO: Initial state should be undefined.
        self._session_key = 0 # TODO: is lock required?

        self._logger = logging.getLogger("DataReceiveService.router={0}".format(
            self._router_name))

        self._transfer_data_queue = Queue.Queue()

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

    # TODO
    def receive_queue(self):
        return self._transfer_data_queue

    def _work(self):
        def handle_receive():
            try:
                data = self._transfer_data_queue.get_nowait()
            except Queue.Empty:
                have_data = False
            else:
                have_data = True

            if have_data:
                self._logger.debug("Receive data packet")
                # TODO
                
                #raw_data = TransferData(self._session_key, data).serialize()
                #self._service_transmitter.send_data(
                #    self._dest_router_name, raw_data)

        self._logger.info("Working thread started")

        while True:
            if self._exit_lock.acquire(False):
                # Obtained exit lock. Terminate.

                self._exit_lock.release()
                self._logger.info("Exit working thread")
                return

            handle_receive()

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
        class TestMain(unittest.TestCase):
            def test_main(self):
                pass


    do_tests(Tests, level=level, disabled_loggers=disabled_loggers)

if __name__ == "__main__":
    disabled_loggers = [
        "DatagramRouter.router=1",
        "DatagramRouter.router=2",
        "FrameTransmitter.1->2",
        "FrameTransmitter.2->1"
        ]
    
    _test(disabled_loggers=disabled_loggers, level=0)

# vim: set ts=4 sw=4 et:
