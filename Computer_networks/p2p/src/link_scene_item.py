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

from duplex_link import FullDuplexLink
from frame import SimpleFrameTransmitter
from sliding_window import FrameTransmitter

class LinkItem(QGraphicsObject):
    def __init__(self, src_router, dest_router, enabled=False,
            loss_func=None, parent=None):
        super(LinkItem, self).__init__(parent)

        self.src = src_router
        self.dest = dest_router

        self.src.add_link(self)
        self.dest.add_link(self)

        self.src_point = None
        self.dest_point = None

        # Edge color.
        self.color = Qt.black

        # Initial state is disabled.
        self._enabled = False
        self.hide()
        l1, l2 = FullDuplexLink(loss_func=loss_func)
        sft1 = SimpleFrameTransmitter(node=l1)
        sft2 = SimpleFrameTransmitter(node=l2)
        self._src_frame_transmitter = \
            FrameTransmitter(simple_frame_transmitter=sft1,
            debug_src=self.src.name, debug_dest=self.dest.name)
        self._dest_frame_transmitter = \
            FrameTransmitter(simple_frame_transmitter=sft2)

        self.enabled = enabled

        self.destroyed.connect(self.on_destroy)

    @pyqtSlot()
    def on_destroy(self):
        # FIXME: never called.
        print "{0}.on_destroy()".format(self)
        self._src_frame_transmitter.terminate()
        self._dest_frame_transmitter.terminate()

    @property
    def enabled(self):
        return self._enabled

    @enabled.setter
    def enabled(self, value):
        if self._enabled != bool(value):
            self._enabled = bool(value)

            if self._enabled:
                # Link up.
                self._link_up()
            else:
                # Link down.
                self._link_down()
                
    def _link_up(self):
        self._src_frame_transmitter.enabled = True
        self._dest_frame_transmitter.enabled = True

        self.src.link_manager.add_link(self.dest.name,
            self._src_frame_transmitter)
        self.dest.link_manager.add_link(self.src.name,
            self._dest_frame_transmitter)

        self.adjust()
        self.show()

    def _link_down(self):
        self._src_frame_transmitter.enabled = False
        self._dest_frame_transmitter.enabled = False

        self.src.link_manager.remove_link(self.dest.name)
        self.dest.link_manager.remove_link(self.src.name)

        self.hide()

    def length(self):
        return QLineF(
            self.mapFromItem(self.src, 0, 0),
            self.mapFromItem(self.dest, 0, 0)).length()

    def adjust(self):
        if self._enabled:
            line = QLineF(
                self.mapFromItem(self.src, 0, 0),
                self.mapFromItem(self.dest, 0, 0))

            self.prepareGeometryChange()

            if line.length() > self.src.radius + self.dest.radius:
                unit = QVector2D(line.p2() - line.p1()).normalized()
                self.src_point  = \
                    line.p1() + (unit * self.src.radius).toPointF()
                self.dest_point = \
                    line.p2() - (unit * self.dest.radius).toPointF()
            else:
                self.src_point  = None
                self.dest_point = None

    def link_end(self, src):
        if self.src == src:
            return self.dest
        else:
            assert self.dest == src
            return self.src

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

    def _paint_next_router(self):
        pass

    def _paint_next_routers(self):
        # From source to destination.
        #self.src.
        pass

    def paint(self, painter, style_option, widget):
        if self.is_singular():
            return;

        line = QLineF(self.src_point, self.dest_point)
        assert not qFuzzyCompare(line.length(), 0.)

        painter.setPen(QPen(Qt.black, 2, Qt.SolidLine, Qt.RoundCap, Qt.RoundJoin))
        painter.drawLine(line)

def _test(timeout=1):
    # TODO: Use in separate file to test importing functionality.

    from testing import unittest, do_tests, process_events_with_timeout
    
    from router_scene_item import RouterItem

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

                li = LinkItem(ri1, ri2, enabled=True)
                self.scene.addItem(li)

                self.finished = True

    do_tests(Tests, qt=True)

if __name__ == "__main__":
    _test(timeout=None)
