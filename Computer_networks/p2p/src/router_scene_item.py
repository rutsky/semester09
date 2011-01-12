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

from itertools import ifilter

from PyQt4.QtGui import *
from PyQt4.QtCore import *

from link_manager import RouterLinkManager
from datagram import DatagramRouter
from service_manager import RouterServiceManager
from rip import RIPService

class RouterItem(QGraphicsItem):
    def __init__(self, name, parent=None):
        super(RouterItem, self).__init__(parent)

        assert isinstance(name, int) and 0 <= name < 2**32
        self.name = name

        self.setFlag(QGraphicsItem.ItemIsMovable)
        self.setFlag(QGraphicsItem.ItemSendsGeometryChanges)
        self.setCacheMode(QGraphicsItem.DeviceCoordinateCache)
        self.setZValue(-1)

        # Circle color
        self.color = QColor(255, 0, 0)

        # Circle radius.
        self.radius = 10.0
        # Circle (width, height).
        self.size = QSizeF(2 * self.radius, 2 * self.radius)
        self.size_rect = QRectF(
            QPointF(-self.size.width() / 2.0, -self.size.height() / 2.0),
            self.size)

        self.links = set()

        self.link_manager = RouterLinkManager()
        self.datagram_router = None
        self.service_manager = None
        self.rip_service_transmitter = None
        self.rip_service = None

    def start_networking(self):
        self.datagram_router = DatagramRouter(
            router_name=self.name,
            link_manager=self.link_manager)
        self.service_manager = RouterServiceManager(self.datagram_router)
        self.rip_service_transmitter = self.service_manager.register_service(
            RIPService.protocol)

        self.rip_service = RIPService(self.name, self.link_manager,
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
            new_pos = value.toPointF()

            scene_rect = self.scene().sceneRect()
            scene_rect.adjust(
                self.radius, self.radius, -self.radius, -self.radius)
            assert scene_rect.isValid()
            if not scene_rect.contains(new_pos):
                # Keep the item inside the scene rect.
                new_pos.setX(min(scene_rect.right() - 1,
                    max(new_pos.x(), scene_rect.left())))
                new_pos.setY(min(scene_rect.bottom() - 1,
                    max(new_pos.y(), scene_rect.top())))

                # FIXME: Return value not respected in PyQt (this is a bug).
                self.setPos(new_pos)
                
                return new_pos
            
        return super(RouterItem, self).itemChange(change, value)

    def add_link(self, link):
        self.links.add(link)

    def adjust_links(self):
        for link in self.links:
            link.adjust()
            
def _test():
    # TODO: Use in separate file to test importing functionality.

    import sys
    if sys.version_info[:2] < (2, 7):
        # Backports.
        import unittest2 as unittest
    else:
        import unittest
    import logging

    from timer import Timer

    def process_events_with_timeout(timeout):
        app = QCoreApplication.instance()
        timer = Timer(timeout)
        while any(map(lambda w: w.isVisible(),
                app.topLevelWidgets())):
            app.processEvents()
            if timer.is_expired():
                for w in ifilter(lambda w: w.isVisible(),
                        app.topLevelWidgets()):
                    w.close()

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
                self.view.show()

                process_events_with_timeout(timeout)

            def test_main(self):
                ri = RouterItem(1)
                self.assertEqual(ri.name, 1)
                self.scene.addItem(ri)

            def test_change_position(self):
                ri = RouterItem(1)
                self.scene.addItem(ri)

                ri.setPos(50, 50)

            def test_add_link(self):
                ri = RouterItem(1)
                link = "dummy"
                ri.add_link(link)
                self.assertEqual(ri.links, set([link]))

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

    # Only one instance QApplication should exist.
    app = QApplication(sys.argv)
    timeout = 1

    logging.basicConfig(level=logging.DEBUG)

    suite = unittest.TestSuite()
    for k, v in Tests.__dict__.iteritems():
        if k.startswith('Test'):
            suite.addTests(unittest.TestLoader().loadTestsFromTestCase(v))

    unittest.TextTestRunner(verbosity=2).run(suite)

    app.exit()

if __name__ == "__main__":
    _test()
