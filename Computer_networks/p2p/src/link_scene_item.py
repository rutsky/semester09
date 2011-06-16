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

import logging
import time
import math
import Queue

from PyQt4.QtGui import *
from PyQt4.QtCore import *

from recordtype import recordtype

import routing_table
import palette
import config
from duplex_link import FullDuplexLink
from frame import SimpleFrameTransmitter
from controllable_frame_transmitter import ControllableFrameTransmitter
from rip import RIPService
from rip_packet_scene_item import RIPPacketItem
from data_transfer import DataSendService
from image_transfer_packet_scene_item import ImageTransferPacketItem
from service_manager import Packet

class LinkItem(QGraphicsObject):
    TransmittingPacket = recordtype('TransmittingPacket',
            'packet start_time end_time packet_item')
            
    def __init__(self, src_router, dest_router, enabled=False,
            loss_func=None, parent=None):
        super(LinkItem, self).__init__(parent)

        self._logger = logging.getLogger(
            "LinkItem.{0}->{1}".format(src_router.name, dest_router.name))

        self.src = src_router
        self.dest = dest_router

        self.src.add_link(self)
        self.dest.add_link(self)

        self.src_point = None
        self.dest_point = None

        # { id: LinkItem.TransmittingPacket }
        self._transmitting_direct_packets = {}
        self._transmitting_reverse_packets = {}

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
            ControllableFrameTransmitter(
                src_name=self.src.name, dest_name=self.dest.name,
                simple_frame_transmitter=sft1,
                debug_src=self.src.name, debug_dest=self.dest.name)
        self._dest_frame_transmitter = \
            ControllableFrameTransmitter(
                src_name=self.dest.name, dest_name=self.src.name,
                simple_frame_transmitter=sft2,
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
        #assert not self._transmitting_direct_packets
        self._dest_frame_transmitter.enabled = False
        #assert not self._transmitting_reverse_packets

        self.src.link_manager.remove_link(self.dest.name)
        self.dest.link_manager.remove_link(self.src.name)

        self.hide()

    def _create_transmitting_packet_scene_item(self, protocol, packet):
        if protocol == RIPService.protocol:
            return RIPPacketItem(packet, self)
        elif protocol == DataSendService.protocol:
            return ImageTransferPacketItem(packet, self)
        else:
            self._logger.warning(
                "Request to create scene item for unknown protocol {0}. "
                "Packet: {1}".format(protocol, packet))

    @pyqtSlot(int, float, float, int, Packet)
    def _on_src_packet_send(self, id_, send_time, deliver_time, protocol,
                            packet):
        # TODO
        self._logger.debug("_on_src_packet_send: {0} {1} {2} {3}".format(
            id_, send_time, deliver_time, packet))

        scene_item = self._create_transmitting_packet_scene_item(
            protocol, packet)
        #scene_item.setParent(self)

        tr_packet = LinkItem.TransmittingPacket(
            packet, send_time, deliver_time, scene_item)
        self._adjust_transmitting_packet(tr_packet)

        self._transmitting_direct_packets[id_] = tr_packet

    @pyqtSlot(int, bool)
    def _on_src_packet_received(self, id_, is_success):
        # TODO
        self._logger.debug("_on_src_packet_received: {0}".format(id_))

        self._transmitting_direct_packets[id_].packet_item.setParent(None)
        del self._transmitting_direct_packets[id_]

    @pyqtSlot(int, float, float, int, Packet)
    def _on_dest_packet_send(self, id_, send_time, deliver_time, protocol,
                            packet):
        # TODO
        self._logger.debug("_on_dest_packet_send: {0} {1} {2} {3}".format(
            id_, send_time, deliver_time, packet))

        scene_item = self._create_transmitting_packet_scene_item(
            protocol, packet)
        #scene_item.setParent(self)

        tr_packet = LinkItem.TransmittingPacket(
            packet, send_time, deliver_time, scene_item)
        self._adjust_transmitting_packet(tr_packet)

        self._transmitting_reverse_packets[id_] = tr_packet

    @pyqtSlot(int, bool)
    def _on_dest_packet_received(self, id_, is_success):
        # TODO
        self._logger.debug("_on_dest_packet_received: {0}".format(id_))

        self._transmitting_reverse_packets[id_].packet_item.setParent(None)
        del self._transmitting_reverse_packets[id_]

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

        #self._logger.debug("_adjust_transmitting_packet: {0}".format(tr_packet))

        if self.is_singular():
            tr_packet.packet_item.hide()
            return
        else:
            tr_packet.packet_item.show()

        curtime = time.time()
        assert curtime >= tr_packet.start_time
        assert tr_packet.end_time >= tr_packet.start_time
        progress = min(1.0, 
            (curtime - tr_packet.start_time) /
                (tr_packet.end_time - tr_packet.start_time))

        # TODO: Currently packets delivered faster then they poped from queue.
        if progress == 1.0:
            tr_packet.packet_item.hide()
            return

        if tr_packet.packet.delivered_from == self.dest.name:
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

        # DEBUG
        #if isinstance(tr_packet.packet_item, ImageTransferPacketItem):
        #    print tr_packet

    def timerEvent(self, event):
        old_src_table = self.src_table
        old_dest_table = self.dest_table

        # TODO
        if self.src.rip_service is None or self.dest.rip_service is None:
            return

        # Update packets.
        while True:
            try:
                msg = self._src_frame_transmitter.send_receive_queue.get_nowait()
            except Queue.Empty:
                break
            # TODO!
            if len(msg) > 2:
                self._on_src_packet_send(*msg)
            else:
                self._on_src_packet_received(*msg)

        while True:
            try:
                msg = self._dest_frame_transmitter.send_receive_queue.get_nowait()
            except Queue.Empty:
                break
            # TODO!
            if len(msg) > 2:
                self._on_dest_packet_send(*msg)
            else:
                self._on_dest_packet_received(*msg)


        self.src_table = self.src.rip_service.dynamic_routing_table().table()
        self.dest_table = self.dest.rip_service.dynamic_routing_table().table()

        if old_src_table != self.src_table or old_dest_table != self.dest_table:
            self._recalculate_routes()
            self.update()

        for tr_packet in self._transmitting_direct_packets.values() + \
                self._transmitting_reverse_packets.values():
            self._adjust_transmitting_packet(tr_packet)

def _test(level=None, timeout=1):
    # TODO: Use in separate file to test importing functionality.

    from testing import unittest, do_tests, process_events_with_timeout
    
    from router_scene_item import RouterItem
    from image_transfer_router_scene_item import SendImageRouterItem, \
        ReceiveImageRouterItem

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

                self.li.terminate()
                self.ri1._stop_networking() # TODO
                self.ri2._stop_networking() # TODO

            def test_main(self):
                self.ri1 = RouterItem(1)
                self.ri2 = RouterItem(2)
                
                self.scene.addItem(self.ri1)
                self.scene.addItem(self.ri2)

                self.ri1.setPos(-100, -50)
                self.ri2.setPos(100, 50)

                self.li = LinkItem(self.ri1, self.ri2, enabled=True)
                self.scene.addItem(self.li)

                self.finished = True

            def test_image_transfer(self):
                self.ri1 = SendImageRouterItem(0, 1)
                self.ri2 = ReceiveImageRouterItem(1)

                self.scene.addItem(self.ri1)
                self.scene.addItem(self.ri2)

                self.ri1.setPos(-100, -50)
                self.ri2.setPos(100, 50)

                self.li = LinkItem(self.ri1, self.ri2, enabled=True)
                self.scene.addItem(self.li)

                self.ri1.send_data(range(100))

                self.finished = True

    do_tests(Tests, level=level, qt=True)

if __name__ == "__main__":
    _test(level=0, timeout=None)

# vim: set ts=4 sw=4 et:
