#  This file is part of network emulation test model.
#
#  Copyright (C) 2010  Vladimir Rutsky <altsysrq@gmail.com>
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

import struct
import binascii
from collections import namedtuple

class FrameTransmitter(object):
    # Similar to SLIP.
    frame_end       = "\xC0"
    esc_char        = "\xDB"
    frame_end_subst = esc_char + "\xDC"
    esc_subst       = esc_char + "\xDD"

    def __init__(self, *args, **kwargs):
        self.node = kwargs.pop('node')
        super(FrameTransmitter, self).__init__(*args, **kwargs)

    def write_frame(self, frame):
        raw_data = (
            # Replace escape characters.
            frame.replace(esc_char, esc_subst)
            # Replace frame end characters inside frame.
                .replace(frame_end, frame_end_subst) +
            # Append frame end at end.
            frame_end)
        self.node.write(raw_data)

    def read_frame(self):
        while True:
            ch = self.node.read(1)
            if ch == "":
                # No more characters for now.
                return None
            elif ch == frame_end:
                # Read till frame end. Decode and return it.
                self._read_buffer.replace(frame_end_subst, frame_end).\
                    replace(esc_subst, esc_char)
                return self._read_buffer
            else:
                self._read_buffer.append(ch)

class PacketTypes(object):
    data = 1
    ack  = 2

class DataPacket(namedtuple('DataPacket', 'type id data')):
    def __init__(self):
        super(DataPacket, self).__init__(*args, **kwargs)

    def serialize(self):
        # Packet:
        #   4 byte   4 byte   4 byte    data     4 byte
        # *--------*--------*--------*--     --*--------*
        # |  type  |   id   |   len  |   ...   |  CRC32 |
        # *--------*--------*--------*---------*--------*

        packet_str = struct.pack("LLL",
            PacketTypes.data, self.id, len(self.data)) + \
            self.data
        
        packet_str += struct.pack("L", binascii.crc32(packet_str) & 0xffffffff)
        return packet_str

class ChannelSender(object):
    def __init__(self, *args, **kwargs):
        self.frame_transmitter = FrameTransmitter(node=kwargs.pop('node'))
        self.max_packet = kwds.pop('max_packet_data', 100)
        self.max_window_size = kwds.pop('max_window_size', 100)
        super(ChannelSender, self).__init__(*args, **kwargs)

        self._next_packet_id = 0
        self._window = []

    class _Packet(object):
        def __init__(self, id):
            super(_Packet, self).__init__()
            self.id = id


    def _transmit(self, string):
        pass

    def write(self, string):
        # Subdivide string to few packets.
        for string_part in [string[i:i + self.max_packet]
                for i in xrange(0, len(string), self.max_packet)]:
            self._transmit(string_part)

    def update(self):
        

class ChannelReceiver(object):
    def __init__(self, *args, **kwargs):
        super(ChannelReceiver, self).__init__(*args, **kwargs)

    def read(self, size=0):
        pass
