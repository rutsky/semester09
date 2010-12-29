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

class FrameTransmitter(object):
    # Similar to SLIP.
    frame_end       = "\xC0"
    esc_char        = "\xDB"
    frame_end_subst = esc_str + "\xDC"
    esc_subst       = esc_str + "\xDD"

    def __init__(self, *args, **kwargs):
        self.node = kwds.pop('node')
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

class ChannelSender(object):

    def __init__(self, *args, **kwargs):
        self.node = kwds.pop('send_node')
        self.max_packet = kwds.pop('max_packet_data', 100)
        self.max_window_size = kwds.pop('max_window_size', 100)
        super(ChannelSender, self).__init__(*args, **kwargs)

        self._read_buffer = ""

    class _Packet(object):
        def __init__(self, id):
            super(_Packet, self).__init__()
            self.id = id


    def transmit(self, string):
        pass

    def write(self, string):
        for string_part in [string[i:i+self.max_packet]
                for i in xrange(0, len(string), self.max_packet)]:
            self.transmit(string_part)
        pass

class ChannelReceiver(object):
    def __init__(self, *args, **kwargs):
        super(ChannelReceiver, self).__init__(*args, **kwargs)

    def read(self, size=0):
        pass
