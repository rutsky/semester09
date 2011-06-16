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

__all__ = ["ImageTransferPacketItem"]

import time

from PyQt4 import QtGui
from PyQt4.QtGui import *
from PyQt4.QtCore import *

import palette

class ImageTransferPacketItem(QtGui.QGraphicsObject):
    def __init__(self, packet, parent=None):
        super(ImageTransferPacketItem, self).__init__(parent)

        self._packet = packet

        self.setCacheMode(QGraphicsItem.DeviceCoordinateCache)
        self.setZValue(2)

        self._src_color  = palette.palette[self._packet.src]
        self._dest_color = palette.palette[self._packet.dest]

        self._width = 1.0 * 3
        self._height = 1.3 * 3
        
        self._size = QSizeF(self._width, self._height)
        self._size_rect = QRectF(
            QPointF(-self._size.width() / 2.0, -self._size.height() / 2.0),
            self._size)

        self._src_rect = QRectF(
            QPointF(-self._width / 2.0, -self._height / 2.0),
            QSizeF(self._width, self._height / 2.0))
        self._dest_rect = QRectF(
            QPointF(-self._width / 2.0, 0),
            QSizeF(self._width, self._height / 2.0))

        self._src_pen = QPen(self._src_color, 0)
        self._src_brush = QBrush(self._src_color)
        self._dest_pen = QPen(self._dest_color, 0)
        self._dest_brush = QBrush(self._dest_color)

    def boundingRect(self):
        adjust = 1

        return self._size_rect.adjusted(-adjust, -adjust, adjust, adjust)

    def paint(self, painter, style_option, widget):
        painter.setPen(self._src_pen)
        painter.setBrush(self._src_brush)
        painter.drawRect(self._src_rect)

        painter.setPen(self._dest_pen)
        painter.setBrush(self._dest_brush)
        painter.drawRect(self._dest_rect)

def _test(timeout=1):
    # TODO: Use in separate file to test importing functionality.

    from testing import unittest, do_tests, process_events_with_timeout

    import time
    
    from service_manager import Packet

    class Tests(object):
        class TestImageTransferPacketItemGUI(unittest.TestCase):
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
                rpi = ImageTransferPacketItem(self.p)
                self.assertEqual(rpi._packet, self.p)

                self.scene.addItem(rpi)

                self.finished = True

    do_tests(Tests, qt=True)

if __name__ == "__main__":
    _test(None)

# vim: set ts=4 sw=4 et:
