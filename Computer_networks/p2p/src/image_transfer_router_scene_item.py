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

__all__ = ["SendImageRouterItem", "ReceiveImageRouterItem"]

import time
import logging
import Queue
from collections import deque

from PyQt4.QtGui import *
from PyQt4.QtCore import *

import palette
import router_name
from link_manager import RouterLinkManager
from datagram import DatagramRouter
from service_manager import RouterServiceManager
from rip import RIPService
from router_scene_item import RouterItem
from data_transfer import DataSendService, DataReceiveService

class SendImageRouterItem(RouterItem):
    def __init__(self, name, dest_name, parent=None, enabled=True):
        self._dest_name = dest_name
        self._transfer_service = None
        self._transfer_service_transmitter = None
        super(SendImageRouterItem, self).__init__(name, parent, enabled)

    def _start_networking(self):
        #print self, "_start_networking" # DEBUG
        super(SendImageRouterItem, self)._start_networking()

        self._transfer_service_transmitter = self._service_manager.register_service(
            DataSendService.protocol)

        self._transfer_service = DataSendService(self.name, self._link_manager,
            self._transfer_service_transmitter, self._dest_name)

    def _stop_networking(self):
        #print self, "_stop_networking" # DEBUG
        super(SendImageRouterItem, self)._stop_networking()

        assert self._transfer_service is not None
        self._transfer_service.terminate()

        self._transfer_service = None

    def send_data(self, data_it):
        print "send_data" # DEBUG
        self._transfer_service.reset_transfer_queue()
        self._transfer_service.new_session()
        self._transfer_service.append_to_transfer_queue(data_it)

class ReceiveImageRouterItem(RouterItem):
    def __init__(self, name, parent=None, enabled=True):
        self._transfer_service = None
        self._transfer_service_transmitter = None
        super(ReceiveImageRouterItem, self).__init__(name, parent, enabled)

    def _start_networking(self):
        #print self, "_start_networking" # DEBUG
        super(ReceiveImageRouterItem, self)._start_networking()

        self._transfer_service_transmitter = self._service_manager.register_service(
            DataSendService.protocol)

        self._transfer_service = DataReceiveService(self.name, self._link_manager,
            self._transfer_service_transmitter)

    def _stop_networking(self):
        #print self, "_stop_networking" # DEBUG
        super(ReceiveImageRouterItem, self)._stop_networking()

        assert self._transfer_service is not None
        self._transfer_service.terminate()

        self._transfer_service = None

    def receive_TODO(self):
        pass

def _test(timeout=1, level=None):
    # TODO: Use in separate file to test importing functionality.

    from testing import unittest, do_tests, process_events_with_timeout

    class Tests(object):
        class TestRouterItemGUI(unittest.TestCase):
            def setUp(self):
                self.view = QGraphicsView()
                self.scene = QGraphicsScene()
                self.scene.setSceneRect(-150, -105, 300, 210)
                self.scene.addRect(-150, -105, 300 - 1, 210 - 1, QPen(Qt.black))
                self.view.setScene(self.scene)

                self.finished = False

            def tearDown(self):
                if self.finished:
                    self.view.show()

                    process_events_with_timeout(timeout)

            def test_main(self):
                ri = SendImageRouterItem(1)
                self.assertEqual(ri.name, 1)
                self.scene.addItem(ri)

                self.finished = True

            def test_change_position(self):
                ri = RouterItem(1)
                self.scene.addItem(ri)

                ri.setPos(50, 50)

                self.finished = True

            def _test_add_link(self):
                ri = RouterItem(1)
                link = "dummy"
                ri.add_link(link)
                self.assertItemsEqual(ri.links, [link])

                self.finished = True

            def _test_add_link_with_adjustment(self):
                ri = RouterItem(1)
                class Link(object):
                    def __init__(self):
                        self.adjusted = False

                    def adjust(self):
                        self.adjusted = True

                link = Link()

                self.assertFalse(link.adjusted)
                ri.add_link(link)
                self.assertFalse(link.adjusted)
                self.assertItemsEqual(ri.links, [link])

                # TODO
                #ri.setPos(10, 10)
                #self.assertTrue(link.adjusted)
                
                self.finished = True

        class TestRouterItem(unittest.TestCase):
            def tearDown(self):
                process_events_with_timeout(timeout)

            def test_start_stop_networking(self):
                ri = SendImageRouterItem(1)

                #self.assertEqual(ri._rip_service, None)
                #ri.start_networking()
                self.assertNotEqual(ri._rip_service, None)
                #ri.stop_networking()
                #self.assertEqual(ri._rip_service, None)

        class TestRouterItemGUIMoving(unittest.TestCase):
            def setUp(self):
                self.view = QGraphicsView()
                self.scene = QGraphicsScene()
                self.scene.setSceneRect(-150, -105, 300, 210)
                self.scene.addRect(self.scene.sceneRect(), QPen(Qt.black))
                self.view.setScene(self.scene)

                self.finished = False

            def tearDown(self):
                if self.finished:
                    self.view.show()

                    self.lastUpdate = time.time()
                    def update():
                        t = time.time()
                        self.ri.advance(t - self.lastUpdate)
                        self.lastUpdate = t

                    process_events_with_timeout(timeout, callback=update)

            def test_main(self):
                self.ri = SendImageRouterItem(1)
                self.scene.addItem(self.ri)

                self.finished = True

    do_tests(Tests, qt=True, level=level)

if __name__ == "__main__":
    _test(None, level=0)

# vim: set ts=4 sw=4 et:
