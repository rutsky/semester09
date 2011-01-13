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

__all__ = ["MainWindow"]

import random
import logging
import threading
import itertools
import time

import PyQt4.uic
from PyQt4.QtGui import *
from PyQt4.QtCore import *
from PyQt4.Qt import *

from router_scene_item import RouterItem
from link_scene_item import LinkItem

def random_velocity(min, max):
    return QLineF.fromPolar(random.uniform(min, max),
        random.uniform(0, 360.0)).p2()

class MainWindow(QMainWindow):
    def __init__(self, parent=None):
        super(MainWindow, self).__init__(parent)

        PyQt4.uic.loadUi('main_window.ui', self)

        # Scene working rectangle.
        self.scene_rect = QRectF(-150, -105, 300, 210)

        self.scene = QGraphicsScene()
        self.graphicsView.setScene(self.scene)
        self.scene.setSceneRect(self.scene_rect)

        # Disable spatial indexing since all objects will be moving.
        self.scene.setItemIndexMethod(QGraphicsScene.NoIndex)

        self.graphicsView.setCacheMode(QGraphicsView.CacheBackground)
        self.graphicsView.setViewportUpdateMode(
            QGraphicsView.BoundingRectViewportUpdate)
        self.graphicsView.setRenderHint(QPainter.Antialiasing)
        #self.graphicsView.setTransformationAnchor(QGraphicsView.AnchorUnderMouse)
        self.graphicsView.setResizeAnchor(QGraphicsView.AnchorViewCenter)
        
        # Disable scrollbars. Seems this is required for correct fitInView()
        # work in resizeEvent(). See fitInView() documentation for details.
        self.graphicsView.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
        self.graphicsView.setVerticalScrollBarPolicy(Qt.ScrollBarAlwaysOff)

        #self.scene.addText("Hello, world!")

        # debug
        self.scene_rect_item = self.scene.addRect(self.scene.sceneRect())

        self.name_it = itertools.count(0)
        self.routers = []

        # (src, dest) -> link
        self.links = {}

        self.connection_distance = 50
        self.disconnection_distance = 70

        # Routers
        self.router_velocity_range = (0.0, 20.0)

        self.dt = 1 / 30.0
        self.timer_id = self.startTimer(int(1000 * self.dt))

        # If working thread will be able to acquire the lock, then it should
        # terminate himself.
        self._exit_lock = threading.RLock()
        self._exit_lock.acquire()

        self._working_thread = threading.Thread(target=self._work)
        self._working_thread.start()

    def closeEvent(self, event):
        # Release exit lock and wait until working thread will not terminate.
        self._exit_lock.release()
        self._working_thread.join()
        super(MainWindow, self).closeEvent(event)

    def showEvent(self, event):
        super(MainWindow, self).showEvent(event)
        self.graphicsView.fitInView(self.scene_rect, Qt.KeepAspectRatio)

    def resizeEvent(self, event):
        super(MainWindow, self).resizeEvent(event)
        self.graphicsView.fitInView(self.scene_rect, Qt.KeepAspectRatio)

    def timerEvent(self, event):
        for router in self.routers:
            router.advance(self.dt)

        for (r1, r2), link in self.links.iteritems():
            if r1.distance(r2) >= self.disconnection_distance:
                link.enabled = False

        for idx, r1 in enumerate(self.routers):
            for r2 in self.routers[idx + 1:]:
                if r1.distance(r2) <= self.connection_distance:
                    self.links[(r1, r2)].enabled = True

    def add_router(self, pos=None):
        name = self.name_it.next()

        if pos is None:
            scene_rect = self.scene.sceneRect()
            router_pos = QPointF(
                random.randrange(scene_rect.left(), scene_rect.width()),
                random.randrange(scene_rect.top(), scene_rect.height()))
        else:
            router_pos = pos

        router = RouterItem(name)
        self.scene.addItem(router)
        router.setPos(router_pos)

        for r in self.routers:
            link = LinkItem(r, router)
            self.scene.addItem(link)
            self.links[(r, router)] = link

        self.routers.append(router)

        return name

    def shake_routers(self):
        for router in self.routers:
            router.velocity = random_velocity(*self.router_velocity_range)

    def _work(self):
        logger = logging.getLogger("{0}._work".format(self))

        logger.info("Working thread started")

        while True:
            if self._exit_lock.acquire(False):
                # Obtained exit lock. Terminate.

                self._exit_lock.release()
                logger.info("Exit working thread")
                return

            time.sleep(1e-3)

def _test():
    # TODO: Use in separate file to test importing functionality.

    from testing import unittest, do_tests, process_events_with_timeout

    class Tests(object):
        class TestMainWindow(unittest.TestCase):
            def setUp(self):
                self.finished = False
            
            def tearDown(self):
                if self.finished:
                    process_events_with_timeout(timeout)

            def test_main(self):
                self.w = MainWindow()
                self.w.show()

                for i in xrange(20):
                    self.w.add_router()

                self.w.shake_routers()

                self.finished = True

    timeout = None
    do_tests(Tests, qt=True, level=0)

if __name__ == "__main__":
    _test()
