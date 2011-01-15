import timer
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

__all__ = ["RouterItem"]

import time
from collections import deque

from PyQt4.QtGui import *
from PyQt4.QtCore import *

from link_manager import RouterLinkManager
from datagram import DatagramRouter
from service_manager import RouterServiceManager
from rip import RIPService
import palette

class RouterItem(QGraphicsObject):
    def __init__(self, name, parent=None):
        super(RouterItem, self).__init__(parent)

        assert isinstance(name, int) and 0 <= name < 2**32
        self.name = name

        self.setFlag(QGraphicsItem.ItemIsMovable)
        self.setFlag(QGraphicsItem.ItemSendsGeometryChanges)
        self.setCacheMode(QGraphicsItem.DeviceCoordinateCache)
        self.setZValue(1)

        # Circle color.
        self.color = palette.palette[self.name]

        # Circle radius.
        self.radius = 5.0
        # Circle (width, height).
        self.size = QSizeF(2 * self.radius, 2 * self.radius)
        self.size_rect = QRectF(
            QPointF(-self.size.width() / 2.0, -self.size.height() / 2.0),
            self.size)

        self.links = {}

        self._link_manager = RouterLinkManager()
        self.datagram_router = None
        self.service_manager = None
        self.rip_service_transmitter = None
        self.rip_service = None

        self.velocity = QPointF()
        self.max_mouse_move_velocity = 100

        self._drag_points = deque(maxlen=10)

    def start_networking(self):
        self.datagram_router = DatagramRouter(
            router_name=self.name,
            link_manager=self._link_manager)
        self.service_manager = RouterServiceManager(self.datagram_router)
        self.rip_service_transmitter = self.service_manager.register_service(
            RIPService.protocol)

        self.rip_service = RIPService(self.name, self._link_manager,
            self.rip_service_transmitter)

        self.datagram_router.set_routing_table(
            self.rip_service.dynamic_routing_table())

    def stop_networking(self):
        self.rip_service.terminate()
        self.service_manager.terminate()
        self.datagram_router.terminate()

        self.datagram_router = None
        self.service_manager = None
        self.rip_service_transmitter = None
        self.rip_service = None

    @property
    def link_manager(self):
        return self._link_manager

    def boundingRect(self):
        adjust = 2

        return self.size_rect.adjusted(-adjust, -adjust, adjust, adjust)

    # TODO: Is circular shape really needed?
    def shape(self):
        path = QPainterPath()
        path.addEllipse(self.size_rect)
        return path

    def paint(self, painter, style_option, widget):
        painter.setPen(QPen(Qt.black, 0))
        painter.setBrush(QBrush(self.color))
        painter.drawEllipse(self.size_rect)

    def itemChange(self, change, value):
        if change == QGraphicsItem.ItemPositionHasChanged and self.scene():
            self.adjust_links()

            # Value is the new position.
            pos = value.toPointF()

            pos_in_scene = self._return_to_scene(pos)
            if pos_in_scene != pos:
                # FIXME: Return value not respected in PyQt (this is a bug).
                self.setPos(pos_in_scene)
                
                return pos_in_scene
            
        return super(RouterItem, self).itemChange(change, value)

    def mousePressEvent(self, event):
        self._drag_points.clear()
        self.velocity = QPointF()

        #self._timer_id = self.startTimer(int(1000 / 10))

        super(RouterItem, self).mousePressEvent(event)

    def mouseReleaseEvent(self, event):
        t = time.time()
        while self._drag_points and self._drag_points[0][0] + 0.1 < t:
            self._drag_points.popleft()

        if len(self._drag_points) >= 2:
            new_velocity = \
                ((self._drag_points[-1][1] - self._drag_points[0][1]) /
                 (self._drag_points[-1][0] - self._drag_points[0][0]))

            l = QVector2D(new_velocity).length()
            if l > self.max_mouse_move_velocity:
                new_velocity *= self.max_mouse_move_velocity / l

            self.velocity = new_velocity
        super(RouterItem, self).mouseReleaseEvent(event)

    def mouseMoveEvent(self, event):
        self._drag_points.append((time.time(), event.scenePos()))

        super(RouterItem, self).mouseMoveEvent(event)

    def _return_to_scene(self, pos):
        new_pos = QPointF(pos)
        
        scene_rect = self.scene().sceneRect()
        scene_rect.adjust(
            self.radius, self.radius, -self.radius, -self.radius)
        assert scene_rect.isValid()
        if not scene_rect.contains(new_pos):
            # Keep the item inside the scene rect.
            new_pos.setX(min(scene_rect.right(),
                max(new_pos.x(), scene_rect.left())))
            new_pos.setY(min(scene_rect.bottom(),
                max(new_pos.y(), scene_rect.top())))
            assert scene_rect.contains(new_pos)
        return new_pos

    def add_link(self, link):
        self.links[link.link_end(self)] = link

    def adjust_links(self):
        for dest, link in self.links.iteritems():
            link.adjust()

    def advance(self, dt):
        new_pos = self.pos() + self.velocity * dt
        new_pos_in_scene = self._return_to_scene(new_pos)

        if new_pos.x() != new_pos_in_scene.x():
            self.velocity.setX(-self.velocity.x())
        if new_pos.y() != new_pos_in_scene.y():
            self.velocity.setY(-self.velocity.y())
       
        if self.pos() != new_pos_in_scene:
            self.setPos(new_pos_in_scene)

        # Returns is something changed.
        return self.velocity != 0 and dt != 0

    def distance(self, other_router):
        return QLineF(
            self.mapFromItem(self, 0, 0),
            self.mapFromItem(other_router, 0, 0)).length()

            
def _test():
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
                ri = RouterItem(1)
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
                self.assertEqual(ri.links, set([link]))

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
                self.assertEqual(ri.links, set([link]))

                # TODO
                #ri.setPos(10, 10)
                #self.assertTrue(link.adjusted)
                
                self.finished = True

        class TestRouterItem(unittest.TestCase):
            def tearDown(self):
                process_events_with_timeout(timeout)

            def test_start_stop_networking(self):
                ri = RouterItem(1)

                self.assertEqual(ri.rip_service, None)
                ri.start_networking()
                self.assertNotEqual(ri.rip_service, None)
                ri.stop_networking()
                self.assertEqual(ri.rip_service, None)

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

            def test_start_stop_networking(self):
                self.ri = RouterItem(1)
                self.scene.addItem(self.ri)

                self.finished = True

    timeout = None
    do_tests(Tests, qt=True)

if __name__ == "__main__":
    _test()
