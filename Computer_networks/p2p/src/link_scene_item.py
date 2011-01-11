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

        painter.setPen(QPen(Qt.black, 1, Qt.SolidLine, Qt.RoundCap, Qt.RoundJoin))
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

    from router_scene_item import RouterItem

    class Tests(object):
        class TestLinkItem(unittest.TestCase):
            def setUp(self):
                self.app = QApplication(sys.argv)
                self.view = QGraphicsView()
                self.scene = QGraphicsScene()
                self.scene.setSceneRect(-150, -105, 300, 210)
                self.view.setScene(self.scene)

            def tearDown(self):
                self.view.show()
                self.app.exec_()

            def test_main(self):
                ri1 = RouterItem()
                ri2 = RouterItem()
                

                self.scene.addItem(ri1)
                self.scene.addItem(ri2)

                ri1.setPos(-100, -50)
                ri2.setPos(100, 50)

                li = LinkItem(ri1, ri2)
                self.scene.addItem(li)

    logging.basicConfig(level=logging.DEBUG)

    suite = unittest.TestSuite()
    for k, v in Tests.__dict__.iteritems():
        if k.startswith('Test'):
            suite.addTests(unittest.TestLoader().loadTestsFromTestCase(v))

    unittest.TextTestRunner(verbosity=2).run(suite)

if __name__ == "__main__":
    _test()
