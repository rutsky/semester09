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

from PyQt4.QtGui import *
from PyQt4.QtCore import *

class RouterItem(QGraphicsItem):
    def __init__(self, parent=None):
        super(RouterItem, self).__init__(parent)

        # Circle color
        self.color = QColor(255, 0, 0)

        # Circle radius.
        self.radius = 15
        # Circle (width, height).
        self.size = QSizeF(2 * self.radius, 2 * self.radius)
        self.size_rect = QRectF(
            QPointF(-self.size.width() / 2.0, -self.size.height() / 2.0),
            self.size)

        self.links = set()

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
        if change == QGraphicsItem.ItemPositionHasChanged:
            for link in self.links:
                link.adjust()
        return super(RouterItem, self).itemChange(change, value)

    def add_link(self, link):
        self.link.insert(link)

def _test():
    # TODO: Use in separate file to test importing functionality.

    import sys
    if sys.version_info[:2] < (2, 7):
        # Backports.
        import unittest2 as unittest
    else:
        import unittest
    import logging

    class Tests(object):
        class TestRouterItem(unittest.TestCase):
            def setUp(self):
                self.app = QApplication(sys.argv)
                self.view = QGraphicsView()
                self.scene = QGraphicsScene()
                self.scene.setSceneRect(-150, -105, 300, 210)
                self.view.setScene(self.scene)

            def test_main(self):
                self.scene.addItem(RouterItem())

                self.view.show()
                self.app.exec_()

            def test_change_position(self):
                ri = RouterItem()
                self.scene.addItem(ri)

                ri.setPos(50, 50)

                self.view.show()
                self.app.exec_()

    logging.basicConfig(level=logging.DEBUG)

    suite = unittest.TestSuite()
    for k, v in Tests.__dict__.iteritems():
        if k.startswith('Test'):
            suite.addTests(unittest.TestLoader().loadTestsFromTestCase(v))

    unittest.TextTestRunner(verbosity=2).run(suite)

if __name__ == "__main__":
    _test()
