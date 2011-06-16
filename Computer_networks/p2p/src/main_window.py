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
import collections
import time

import PyQt4.uic
from PyQt4.QtGui import *
from PyQt4.QtCore import *
from PyQt4.Qt import *

import config
from router_scene_item import RouterItem
from link_scene_item import LinkItem
from main_dockable_panel import MainDockableWidget
from transmission_widget import TransmissionWidget
from statistics_widget import StatisticsWidget
from image_transfer_router_scene_item import SendImageRouterItem, \
    ReceiveImageRouterItem

if config.use_openGL:
    from PyQt4.QtOpenGL import *

def random_velocity():
    return QLineF.fromPolar(max(0, random.gauss(1, 0.1)),
        random.uniform(0, 360.0)).p2()

# TODO: Move almost all functionality from MainWindow to GraphicsView.
class GraphicsView(QGraphicsView):
    def __init__(self):
        super(GraphicsView, self).__init__()

        self.setCacheMode(QGraphicsView.CacheBackground)
        self.setViewportUpdateMode(QGraphicsView.BoundingRectViewportUpdate)
        self.setRenderHint(QPainter.Antialiasing)
        self.setTransformationAnchor(QGraphicsView.AnchorUnderMouse)
        self.setResizeAnchor(QGraphicsView.AnchorViewCenter)

        if config.use_openGL:
            self.setViewport(QGLWidget())

        self._scale_view(2.0)

    def wheelEvent(self, event):
        self._scale_view(2 ** (-event.delta() / 240.0))

    def _scale_view(self, scale_factor):
        # Number of pixels per unit?
        factor = self.matrix().scale(scale_factor, scale_factor).\
            mapRect(QRectF(0, 0, 1, 1)).width()
        if factor < 0.07 or factor > 100:
            return

        self.scale(scale_factor, scale_factor)

class MainWindow(QMainWindow):
    def __init__(self, parent=None):
        super(MainWindow, self).__init__(parent)

        PyQt4.uic.loadUi('forms/main_window.ui', self)

        # Scene working rectangle.
        self.scene_rect = QRectF(
            -config.scene_width / 2, -config.scene_height / 2,
            config.scene_width, config.scene_height)

        self.scene = QGraphicsScene()
        self.graphicsView = GraphicsView()
        self.setCentralWidget(self.graphicsView)
        self.graphicsView.setScene(self.scene)
        self.scene.setSceneRect(self.scene_rect)

        # Disable spatial indexing since all objects will be moving.
        self.scene.setItemIndexMethod(QGraphicsScene.NoIndex)

        self.scene_rect_item = self.scene.addRect(self.scene.sceneRect())

        self.name_it = itertools.count(0)
        self.routers = []
        self.visible_routers = 0

        # Symmetrical matrix of links between routers.
        self.links = [
            [None for c in xrange(config.max_routers_num)]
                for r in xrange(config.max_routers_num)]
        # List of all links.
        self.links_list = []

        # Routers
        self._dt = 1 / 20.0
        self._refresh_timer_id = self.startTimer(int(1000 * self._dt))

        link_update_rate = 5 # times per second
        self._update_link_timer_id = \
            self.startTimer(int(1000 / link_update_rate))

        transmitting_image_refresh_rate = 5 # times per second
        self._update_transmitting_image_timer_id = \
            self.startTimer(int(1000 / transmitting_image_refresh_rate))

        statistics_refresh_rate = 1 # times per second
        self._statistics_timer_id = \
            self.startTimer(int(1000 / statistics_refresh_rate))

        self.generate_routers()

        # Statistics widget.
        self.statistics = StatisticsWidget(self)
        # TODO: Better if it will be statically floatable.
        self.addDockWidget(Qt.RightDockWidgetArea, self.statistics)

        # Main panel.
        # TODO: Rename to `control_panel'.
        self.panel = MainDockableWidget(self)
        self.addDockWidget(Qt.RightDockWidgetArea, self.panel)
        self.panel.nRoutersSlider.valueChanged.connect(
            self.on_routers_num_changed)
        self.panel.shakeRoutersButton.clicked.connect(
            self.shake_routers)
        self.panel.stopRoutersButton.clicked.connect(
            self.stop_routers)
        self.panel.renderNodesRangeCheckBox.stateChanged.connect(
            self.on_display_router_connection_range_changed)
        self.panel.connectionDistSlider.valueChanged.connect(
            self.on_display_router_connection_range_changed)
        self.panel.disconnectionDistSlider.valueChanged.connect(
            self.on_display_router_connection_range_changed)

        # Transmission widget.
        self.transmission = TransmissionWidget()
        self.addDockWidget(Qt.RightDockWidgetArea, self.transmission)
        self.transmission.restartTransmissionButton.clicked.connect(
            self.on_restart_transmission)
        self.transmission.load_image("images/forest.jpg")
        self.transmission.openImageButton.clicked.connect(self.on_new_image)

        self._transmitted_parts = 0
        self._topology_change_times = collections.deque(
            maxlen=config.num_of_topology_changes_in_stat)

        # TODO: Tabs order.
        self.tabifyDockWidget(self.transmission, self.panel)

        # If working thread will be able to acquire the lock, then it should
        # terminate himself.
        self._exit_lock = threading.RLock()
        self._exit_lock.acquire()

        self._working_thread = threading.Thread(target=self._work)
        self._working_thread.start()

    def __del__(self):
        #super(MainWindow, self).__del__()
        print self, "__del__" # DEBUG

        for l in self.links_list:
#            l.enabled = False
            assert l is not None
            l.terminate()

        for r in self.routers:
            # TODO
            r._stop_networking()

        #import sliding_window
        #print sliding_window.worker._frame_transmitters

    def closeEvent(self, event):
        # TODO: It is possible to hit close button twice. Must do
        # deinitialization on destroy event.

        # Release exit lock and wait until working thread will not terminate.
        self._exit_lock.release()
        self._working_thread.join()
        super(MainWindow, self).closeEvent(event)

    def timerEvent(self, event):
        if event.timerId() == self._refresh_timer_id:
            for router in self.routers[:self.visible_routers]:
                router.advance(self._dt)

        elif event.timerId() == self._update_link_timer_id:
            self._first_update_link_timer_id = \
                not hasattr(self, "_first_update_link_timer_id")

            # Disconnect routers that are far away each other.
            for r1_idx in xrange(self.visible_routers):
                for r2_idx in xrange(r1_idx + 1, self.visible_routers):
                    r1 = self.routers[r1_idx]
                    r2 = self.routers[r2_idx]
                    link = self.links[r1_idx][r2_idx]
                    if link.enabled and \
                            r1.distance(r2) >= config.disconnection_distance:
                        link.enabled = False

                        # TODO: Misses case when number of routers changed
                        # dynamically.
                        if not self._first_update_link_timer_id:
                            self._topology_change_times.append(time.time())

            # Connect close routers.
            for r1_idx in xrange(self.visible_routers):
                for r2_idx in xrange(r1_idx + 1, self.visible_routers):
                    r1 = self.routers[r1_idx]
                    r2 = self.routers[r2_idx]
                    link = self.links[r1_idx][r2_idx]
                    
                    if not link.enabled and \
                            r1.distance(r2) <= config.connection_distance:
                        link.enabled = True

                        if not self._first_update_link_timer_id:
                            self._topology_change_times.append(time.time())

            self._first_update_link_timer_id = False

        elif event.timerId() == self._update_transmitting_image_timer_id:
            self._update_transmitting_image()

        elif event.timerId() == self._statistics_timer_id:
            self._update_statistics()

    def _update_statistics(self):
        if self._topology_change_times:
            average_time = (time.time() - self._topology_change_times[0]) / \
                len(self._topology_change_times)

            self.statistics.timeBetweenChangesLabel.setText(
                str(self.tr("{0:.2f} s")).format(1.0 / average_time))

    def _update_transmitting_image(self):
        new_positions = []
        while True:
            data = self.receive_image_router.receive()

            if data is None:
                break

            print "Receive!!" # DEBUG
            print data # DEBUG

            new_positions.append(data)
            self._transmitted_parts += 1

        if new_positions:
            w = self.transmission.transmitted_pixmap.width()
            h = self.transmission.transmitted_pixmap.height()
            dw = w / config.image_cut_columns
            dh = h / config.image_cut_rows

            painter = QPainter(self.transmission.transmitted_pixmap)
            for x, y in new_positions:
                painter.drawImage(x * dw, y * dh,
                    self.transmission.source_pixmap.toImage(),
                    x * dw, y * dh, dw, dh)
            painter.end()
            del painter

            self.transmission.transmitted_image_item.setPixmap(
                self.transmission.transmitted_pixmap)

        self.transmission.successRatioLabel.setText("{0:2.1f} %".format(
            100.0 * self._transmitted_parts /
                (config.image_cut_columns * config.image_cut_rows)))

    def generate_routers(self):
        def send_wrapper(name, **kwargs):
            return SendImageRouterItem(name, 1, **kwargs)

        self._generate_router(router_class=send_wrapper)
        self._generate_router(router_class=ReceiveImageRouterItem)
        self.send_image_router = self.routers[0]
        self.receive_image_router = self.routers[1]

        for i in xrange(2, config.max_routers_num):
            self._generate_router()

    def _generate_router(self, pos=None, router_class=RouterItem):
        name = self.name_it.next()

        if pos is None:
            scene_rect = self.scene.sceneRect()
            router_pos = QPointF(
                random.uniform(
                    scene_rect.left(), scene_rect.left() + scene_rect.width()),
                random.uniform(
                    scene_rect.top(),  scene_rect.top()  + scene_rect.height()))
        else:
            router_pos = pos

        router = router_class(name, enabled=False)
        self.scene.addItem(router)
        router.setPos(router_pos)

        r_idx = len(self.routers)
        for r2_idx in xrange(len(self.routers)):
            r2 = self.routers[r2_idx]

            link = LinkItem(router, r2, enabled=False)
            self.scene.addItem(link)
            self.links_list.append(link)
            self.links[r_idx][r2_idx] = link
            self.links[r2_idx][r_idx] = link

        self.routers.append(router)

        return name

    def add_router(self):
        if self.visible_routers < config.max_routers_num:
            r = self.routers[self.visible_routers]
            r.enabled = True
            #for r2_idx in xrange(self.visible_routers):
            #    self.links[self.visible_routers][r2_idx].enabled = True
            self.visible_routers += 1

    def remove_router(self):
        if self.visible_routers > 2: # 2 --- number of predefined routers
            r = self.routers[self.visible_routers - 1]
            r.enabled = False
            for r2_idx in xrange(self.visible_routers - 1):
                self.links[self.visible_routers - 1][r2_idx].enabled = False
            self.visible_routers -= 1

    @pyqtSlot()
    def stop_routers(self):
        for router in self.routers:
            router.velocity = QPointF()

    @pyqtSlot()
    def shake_routers(self):
        for router in self.routers:
            router.velocity = random_velocity()

    @pyqtSlot(int)
    def on_routers_num_changed(self, nRouters):
        while nRouters > self.visible_routers:
            self.add_router()
        while nRouters < self.visible_routers:
            self.remove_router()

    @pyqtSlot()
    def on_restart_transmission(self):
        self._transmitted_parts = 0

        self.transmission.reload_image()
        
        data = [(x, y) for y in xrange(config.image_cut_rows)
                            for x in xrange(config.image_cut_columns)]
        # TODO: Race condition.
        session_key = self.send_image_router.send_data(data)
        self.receive_image_router.set_active_session(session_key)

    @pyqtSlot()
    def on_new_image(self):
        self._transmitted_parts = 0

        # TODO
        self.receive_image_router.set_active_session(-1)
        self.send_image_router.stop_data_transfer()

    @pyqtSlot(int)
    def on_display_router_connection_range_changed(self, value):
        self._update_routers()

    def _update_routers(self):
        for router in self.routers:
            router.update()

    def _work(self):
        # TODO: move to __init__()
        logger = logging.getLogger("{0}._work".format(self))

        logger.info("Working thread started")

        while True:
            if self._exit_lock.acquire(False):
                # Obtained exit lock. Terminate.

                self._exit_lock.release()
                logger.info("Exit working thread")
                return

            time.sleep(config.thread_sleep_time)

def _test(timeout=1, disabled_loggers=None, level=None):
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
                w = MainWindow()
                w.show()

                for i in xrange(2):
                    w.add_router()

                w.shake_routers()

                #w.send_image_router.send_data(range(100))

                self.finished = True

    do_tests(Tests, qt=True, disabled_loggers=disabled_loggers, level=level)

if __name__ == "__main__":
    disabled_loggers = []
    for r in xrange(config.max_routers_num):
        disabled_loggers.append("DatagramRouter.router={0}".format(r))
        disabled_loggers.append("RIPService.router={0}".format(r))
        disabled_loggers.append("RouterServiceManager.router={0}".format(r))

        for rr in xrange(config.max_routers_num):
            disabled_loggers.append("FrameTransmitter.{0}->{1}".format(r, rr))
            #disabled_loggers.append("ControllableFrameTransmitter.{0}->{1}".format(r, rr))
            #disabled_loggers.append("LinkItem.{0}->{1}".format(r, rr))
    
    _test(timeout=None, disabled_loggers=disabled_loggers, level=0)

# vim: set ts=4 sw=4 et:
