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

__author__ = "Vladimir Rutsky"

__all__ = ["HalfDuplexReceivingNode", "HalfDuplexSendingNode",
    "FullDuplexNode", "FullDuplexLink"]

import Queue

class HalfDuplexReceivingNode(object):
    def __init__(self, *args):
        self._receive_queue = args[0]
        args = args[1:]
        super(HalfDuplexReceivingNode, self).__init__(*args)

    def read(self, size=0):
        chars = []
        while size <= 0 or len(chars) < size:
            try:
                chars.append(self._receive_queue.get(False))
            except Queue.Empty:
                break
        return "".join(chars)

class HalfDuplexSendingNode(object):
    def __init__(self, *args):
        self._send_queue = args[0]
        args = args[1:]
        super(HalfDuplexSendingNode, self).__init__(*args)

    def write(self, string):
        assert isinstance(string, str)
        for ch in string:
            self._send_queue.put(ch)

class FullDuplexNode(HalfDuplexSendingNode, HalfDuplexReceivingNode):
    def __init__(self, send_queue, receive_queue):
        super(FullDuplexNode, self).__init__(send_queue, receive_queue)

class FullDuplexLink(object):
    def __init__(self):
        self._queue_a_to_b = Queue.Queue()
        self._queue_b_to_a = Queue.Queue()
        self._node_a = FullDuplexNode(self._queue_a_to_b, self._queue_b_to_a)
        self._node_b = FullDuplexNode(self._queue_b_to_a, self._queue_a_to_b)

    def node_a(self):
        return self._node_a

    def node_b(self):
        return self._node_b

if __name__ == "__main__":
    link = FullDuplexLink()
    a = link.node_a()
    b = link.node_b()
    a.write("test")
    assert b.read() == "test"
    b.write("1234")
    assert a.read(2) == "12"
    assert a.read() == "34"
    a.write("789")
    a.write("098")
    assert b.read() == "789098"
