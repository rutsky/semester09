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

__all__ = ["RIPPacketItem"]

import time

from PyQt4.QtGui import *
from PyQt4.QtCore import *

import palette

class RIPPacketItem(QGraphicsObject):
    def __init__(self, packet, parent=None):
        super(RIPPacketItem, self).__init__(parent)

        self._packet = packet

        self.setCacheMode(QGraphicsItem.DeviceCoordinateCache)
        self.setZValue(2)

        self.src_color  = palette.palette[self._packet.src]
        self.dest_color = palette.palette[self._packet.dest]

        self.width = 1.0
        self.height = 1.3
        
        self.size = QSizeF(self.width, self.height)
        self.size_rect = QRectF(
            QPointF(-self.size.width() / 2.0, -self.size.height() / 2.0),
            self.size)

        self.src_rect = QRectF(
            QPointF(-self.width / 2.0, -self.height / 2.0),
            QSizeF(self.width, self.height / 2.0))
        self.dest_rect = QRectF(
            QPointF(-self.width / 2.0, 0),
            QSizeF(self.width, self.height / 2.0))

    def boundingRect(self):
        adjust = 1

        return self.size_rect.adjusted(-adjust, -adjust, adjust, adjust)

    def paint(self, painter, style_option, widget):
        painter.setPen(QPen(self.src_color, 0))
        painter.setBrush(QBrush(self.src_color))
        painter.drawRect(self.src_rect)

        painter.setPen(QPen(self.dest_color, 0))
        painter.setBrush(QBrush(self.dest_color))
        painter.drawRect(self.dest_rect)

def _test(timeout=1):
    # TODO: Use in separate file to test importing functionality.

    from testing import unittest, do_tests, process_events_with_timeout

    import time
    
    from service_manager import Packet

    class Tests(object):
        class TestRIPPacketItemGUI(unittest.TestCase):
            def setUp(self):
                self.view = QGraphicsView()
                self.scene = QGraphicsScene()
                self.scene.setSceneRect(-150, -105, 300, 210)
                self.scene.addRect(-150, -105, 300 - 1, 210 - 1, QPen(Qt.black))
                self.view.setScene(self.scene)
                self.view.scale(10, 10)

                self.p = Packet(1, 2, "test", time.time())

                self.finished = False

            def tearDown(self):
                if self.finished:
                    self.view.show()

                    process_events_with_timeout(timeout)

            def test_main(self):
                rpi = RIPPacketItem(self.p)
                self.assertEqual(rpi._packet, self.p)

                self.scene.addItem(rpi)

                self.finished = True

    do_tests(Tests, qt=True)

if __name__ == "__main__":
    _test(None)
