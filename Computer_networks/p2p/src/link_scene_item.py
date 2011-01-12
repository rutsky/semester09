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

__all__ = ["LinkItem"]

from PyQt4.QtGui import *
from PyQt4.QtCore import *

class LinkItem(QGraphicsItem):
    def __init__(self, src_router, dest_router, parent=None):
        super(LinkItem, self).__init__(parent)

        self.src = src_router
        self.dest = dest_router

        self.src.add_link(self)
        self.dest.add_link(self)

        self.src_point = None
        self.dest_point = None

        # Circle color
        self.color = Qt.black

        self.adjust()

    def adjust(self):
        line = QLineF(
            self.mapFromItem(self.src, 0, 0),
            self.mapFromItem(self.dest, 0, 0))
        length = line.length()

        self.prepareGeometryChange()

        if length > self.src.radius + self.dest.radius:
            unit = QVector2D(line.p2() - line.p1()).normalized()
            self.src_point  = line.p1() + (unit * self.src.radius).toPointF()
            self.dest_point = line.p2() - (unit * self.dest.radius).toPointF()
        else:
            self.src_point  = None
            self.dest_point = None

    def is_singular(self):
        return self.src_point is None or self.dest_point is None

    def boundingRect(self):
        if self.is_singular():
            return QRectF()

        extra = 1

        return QRectF(self.src_point,
            QSizeF(self.dest_point.x() - self.src_point.x(),
                   self.dest_point.y() - self.src_point.y())) \
                        .normalized() \
                        .adjusted(-extra, -extra, extra, extra)

    def paint(self, painter, style_option, widget):
        if self.is_singular():
            return;

        line = QLineF(self.src_point, self.dest_point)
        assert not qFuzzyCompare(line.length(), 0.)

        painter.setPen(QPen(Qt.black, 2, Qt.SolidLine, Qt.RoundCap, Qt.RoundJoin))
        painter.drawLine(line)

def _test():
    # TODO: Use in separate file to test importing functionality.

    import sys
    if sys.version_info[:2] < (2, 7):
        # Backports.
        import unittest2 as unittest
    else:
        import unittest
    import logging
    from itertools import ifilter

    from router_scene_item import RouterItem
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
        class TestLinkItem(unittest.TestCase):
            def setUp(self):
                self.view = QGraphicsView()
                self.scene = QGraphicsScene()
                self.scene.setSceneRect(-150, -105, 300, 210)
                self.scene.addRect(-150, -105, 300 - 1, 210 - 1, QPen(Qt.black))
                self.view.setScene(self.scene)

            def tearDown(self):
                self.view.show()

                process_events_with_timeout(timeout)

            def test_main(self):
                ri1 = RouterItem(1)
                ri2 = RouterItem(2)
                
                self.scene.addItem(ri1)
                self.scene.addItem(ri2)

                ri1.setPos(-100, -50)
                ri2.setPos(100, 50)

                li = LinkItem(ri1, ri2)
                self.scene.addItem(li)

                self.finished = True

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
