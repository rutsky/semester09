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

import time
import math

from PyQt4.QtGui import *
from PyQt4.QtCore import *

from recordtype import recordtype

import routing_table
import palette
import config
from duplex_link import FullDuplexLink
from frame import SimpleFrameTransmitter
from sliding_window import FrameTransmitter
from rip import RIPService
from rip_packet_scene_item import RIPPacketItem
from data_transfer import DataSendService
from image_transfer_packet_scene_item import ImageTransferPacketItem

class LinkItem(QGraphicsObject):
    TransmittingPacket = recordtype('TransmittingPacket',
            'packet start_time end_time packet_item')
            
    def __init__(self, src_router, dest_router, enabled=False,
            loss_func=None, parent=None):
        super(LinkItem, self).__init__(parent)

        self.src = src_router
        self.dest = dest_router

        self.src.add_link(self)
        self.dest.add_link(self)

        self.src_point = None
        self.dest_point = None

        # List of LinkItem.TransmittingPacket
        self._transmitting_packets = []

        # Edge color.
        self.color = Qt.black

        self._visual_link_width = 2
        self._visual_route_start_offset = 2.5
        self._visual_route_offset_step = 0.8
        self._visual_route_line_width = 0.5
        self._visual_route_draw_fraction = 2.0 / 3
        self._visual_packet_offset = 5

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
            FrameTransmitter(simple_frame_transmitter=sft2,
                debug_src=self.dest.name, debug_dest=self.src.name)

        self.enabled = enabled

        self.src_table = self.src.rip_service.dynamic_routing_table().table()
        self.dest_table = self.dest.rip_service.dynamic_routing_table().table()
        self._recalculate_routes()

        update_rate = 10 # frames per second
        self._timer_id = self.startTimer(int(1000.0 / update_rate))

    def __del__(self):
        print self, "__del__()" # DEBUG
        super(LinkItem, self).__del__()
        self.terminate()

    # TODO
    def terminate(self):
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

        for tr_packet in self._transmitting_packets:
            tr_packet.packet_item.setParent(None)
            self.link_end_by_name(tr_packet.packet.dest).\
                deliver_packet(tr_packet.packet, True)
        self._transmitting_packets = []

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

    def link_end_by_name(self, name):
        if self.src.name == name:
            return self.src
        else:
            assert self.dest.name == name
            return self.dest

    def is_singular(self):
        return self.src_point is None or self.dest_point is None

    def boundingRect(self):
        if self.is_singular():
            return QRectF()

        # TODO: Take in account transmitting packets.

        routes_count = max(len(self._routes_through_dest),
            len(self._routes_through_src))
        extra = max(self._visual_link_width,
            self._visual_route_start_offset +
                routes_count * self._visual_route_offset_step +
                    self._visual_route_line_width) * math.sqrt(2) # magic const

        return QRectF(self.src_point,
            QSizeF(self.dest_point.x() - self.src_point.x(),
                   self.dest_point.y() - self.src_point.y())) \
                        .normalized() \
                        .adjusted(-extra, -extra, extra, extra)

    def _paint_next_router(self, painter, line, offset, dest_router, distance):
        unit_vector = line.unitVector().p2() - line.unitVector().p1()
        normal_vector = line.normalVector().unitVector().p1() - \
            line.normalVector().unitVector().p2()

        line_to_draw = QLineF(
            line.unitVector().p1(),
            line.unitVector().p1() + 
                unit_vector * line.length() * self._visual_route_draw_fraction)
        line_to_draw.translate(normal_vector * offset)

        color = palette.palette[dest_router]
        saturation = \
            (1.0 * (RIPService.inf_distance - distance) /
                float(RIPService.inf_distance))
        color.setHsvF(color.hueF(), saturation, color.valueF())

        painter.setPen(QPen(color, self._visual_route_line_width,
            Qt.SolidLine, Qt.RoundCap, Qt.RoundJoin))
        painter.drawLine(line_to_draw)

    def _paint_next_routers(self, painter):
        # From source to destination.
        line = QLineF(self.src_point, self.dest_point)
        for idx, (dest, route) in enumerate(self._routes_through_dest):
            offset = self._visual_route_start_offset + \
                idx * self._visual_route_offset_step
            self._paint_next_router(painter,
                line, offset, dest, route.distance)

        # From destination to source.
        line = QLineF(line.p2(), line.p1())
        for idx, (dest, route) in enumerate(self._routes_through_src):
            offset = self._visual_route_start_offset + \
                idx * self._visual_route_offset_step
            self._paint_next_router(painter,
                line, offset, dest, route.distance)

    def paint(self, painter, style_option, widget):
        if self.is_singular():
            return

        line = QLineF(self.src_point, self.dest_point)
        assert not qFuzzyCompare(line.length(), 0.)

        painter.setPen(QPen(Qt.black, self._visual_link_width,
            Qt.SolidLine, Qt.RoundCap, Qt.RoundJoin))
        painter.drawLine(line)

        self._paint_next_routers(painter)

    def _recalculate_routes(self):
        # TODO: may be call prepareGeometryChange()?
        
        through_dest_routers = \
                routing_table.routes_through(self.src_table, self.dest.name)
        through_src_routers = \
            routing_table.routes_through(self.dest_table, self.src.name)

        self._routes_through_dest = [(dest, self.src_table[dest]) \
            for dest in through_dest_routers]
        self._routes_through_src = [(dest, self.dest_table[dest]) \
            for dest in through_src_routers]

        # Sort by destination.
        self._routes_through_dest.sort(cmp=lambda a, b: cmp(a[0], b[0]))
        self._routes_through_src.sort (cmp=lambda a, b: cmp(a[0], b[0]))

    def _adjust_transmitting_packet(self, tr_packet):
        # TODO: may be call prepareGeometryChange()?

        if self.is_singular():
            tr_packet.packet_item.hide()
            return
        else:
            tr_packet.packet_item.show()

        curtime = time.time()
        progress = min(1.0, 
            (curtime - tr_packet.start_time) /
                (tr_packet.end_time - tr_packet.start_time))

        if tr_packet.packet.src == self.src.name:
            line = QLineF(self.src_point, self.dest_point)
        else:
            line = QLineF(self.dest_point, self.src_point)
        assert not qFuzzyCompare(line.length(), 0.)

        unit_vector = line.unitVector().p2() - line.unitVector().p1()
        normal_vector = line.normalVector().unitVector().p1() - \
            line.normalVector().unitVector().p2()

        position = line.p1() + unit_vector * line.length() * progress + \
            normal_vector * self._visual_packet_offset
        tr_packet.packet_item.setPos(position)
        tr_packet.packet_item.setRotation(-line.angle() - 90.0)

        if isinstance(tr_packet.packet_item, ImageTransferPacketItem):
            print tr_packet

    def timerEvent(self, event):
        old_src_table = self.src_table
        old_dest_table = self.dest_table

        # TODO
        if self.src.rip_service is None or self.dest.rip_service is None:
            return

        self.src_table = self.src.rip_service.dynamic_routing_table().table()
        self.dest_table = self.dest.rip_service.dynamic_routing_table().table()

        if old_src_table != self.src_table or old_dest_table != self.dest_table:
            self._recalculate_routes()
            self.update()

        new_transmitting_packets = []
        for transmitting_packet in self._transmitting_packets:
            if transmitting_packet.end_time <= time.time():
                # Packet delivered.
                transmitting_packet.packet_item.setParent(None)
                self.link_end_by_name(transmitting_packet.packet.dest).\
                    deliver_packet(transmitting_packet.packet, False)
            else:
                new_transmitting_packets.append(transmitting_packet)
        self._transmitting_packets = new_transmitting_packets

        for tr_packet in self._transmitting_packets:
            self._adjust_transmitting_packet(tr_packet)

    def transmit_packet(self, protocol, packet):
        transmit_time = packet.time * config.packets_delivery_time_factor

        current_time = time.time()
        if protocol == RIPService.protocol:
            packet_item = RIPPacketItem(packet, self)
            transmitting_packet = LinkItem.TransmittingPacket(
                packet, current_time, current_time + transmit_time, packet_item)
            self._transmitting_packets.append(transmitting_packet)

            self._adjust_transmitting_packet(transmitting_packet)
        elif protocol == DataSendService.protocol:
            print "Image transfer!", packet # DEBUG
            packet_item = ImageTransferPacketItem(packet, self)
            transmitting_packet = LinkItem.TransmittingPacket(
                packet, current_time, current_time + transmit_time, packet_item)
            self._transmitting_packets.append(transmitting_packet)

            self._adjust_transmitting_packet(transmitting_packet)
        else:
            # TODO: Log this case.
            pass

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

# vim: set ts=4 sw=4 et:
