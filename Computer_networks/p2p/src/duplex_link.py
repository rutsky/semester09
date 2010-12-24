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

__all__ = ["ReceivingNode", "SendingNode", "FullDuplexNode", "FullDuplexLink",
    "LossFunc"]

import Queue
import bisect
import random

# TODO: Should transfer stream of bits not bytes.

class SendingNode(object):
    def __init__(self, **kwds):
        self.send_queue = kwds.pop('send_queue', None)
        if self.send_queue is None:
            self.send_queue = Queue.Queue()
        super(SendingNode, self).__init__(**kwds)

    def write_ch(self, ch):
        assert isinstance(ch, str)
        assert len(ch) == 1
        self.send_queue.put(ch)

    def write(self, string):
        assert isinstance(string, str)
        for ch in string:
            self.write_ch(ch)

class ReceivingNode(object):
    def __init__(self, **kwds):
        self.receive_queue = kwds.pop('receive_queue', None)
        if self.receive_queue is None:
            self.receive_queue = Queue.Queue()
        super(ReceivingNode, self).__init__(**kwds)

    def read(self, size=0):
        chars = []
        while size <= 0 or len(chars) < size:
            try:
                chars.append(self.receive_queue.get(False))
            except Queue.Empty:
                break
        return "".join(chars)

class LossFunc(object):
    def __init__(self, skip_ch_prob, modify_ch_prob, new_ch_prob):
        super(LossFunc, self).__init__()
        self.configure(skip_ch_prob, modify_ch_prob, new_ch_prob)

    def configure(self, skip_ch_prob, modify_ch_prob, new_ch_prob):
        assert 0 <= skip_ch_prob <= 1
        assert 0 <= modify_ch_prob <= 1
        assert 0 <= new_ch_prob <= 1
        assert 0 <= skip_ch_prob + modify_ch_prob + new_ch_prob <= 1

        # Construct array so that by finding upper bound of random number in it
        # will be possible to select random modification.
        self._selection_array = [0, skip_ch_prob, modify_ch_prob, new_ch_prob]
        for i, v in enumerate(self._selection_array[1:]):
            self._selection_array[i + 1] = self._selection_array[i] + v
        self._selection_array.append(1)

    def __call__(self, ch):
        """Takes single character and returns transformed string."""
        choice = bisect.bisect_right(self._selection_array, random.random())

        random_ch = lambda: chr(random.randint(0, 255))

        if choice == 1:
            # Skip character.
            return ""
        elif choice == 2:
            # Modify character.
            return random_ch()
        elif choice == 3:
            # Append new character.
            return ch + random_ch()
        else:
            assert choice == 4
            # Don't modify character.
            return ch

class SendingWithLossNode(SendingNode):
    def __init__(self, **kwds):
        self._loss_func = kwds.pop('loss_func', None)
        if self._loss_func is None:
            self._loss_func = LossFunc(0, 0, 0)
        super(SendingWithLossNode, self).__init__(**kwds)

    def write_ch(self, ch):
        for new_ch in self._loss_func(ch):
            super(SendingWithLossNode, self).write_ch(new_ch)

class FullDuplexNode(SendingWithLossNode, ReceivingNode):
    def __init__(self, **kwds):
        super(FullDuplexNode, self).__init__(**kwds)

class FullDuplexLink(object):
    def __init__(self, loss_func=None):
        self._queue_a_to_b = Queue.Queue()
        self._queue_b_to_a = Queue.Queue()
        self._node_a = FullDuplexNode(
            send_queue=self._queue_a_to_b,
            receive_queue=self._queue_b_to_a,
            loss_func=loss_func)
        self._node_b = FullDuplexNode(
            send_queue=self._queue_b_to_a,
            receive_queue=self._queue_a_to_b,
            loss_func=loss_func)

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

    text = "This is quite long text, do you agree?"
    print "Working with text: '{0}'".format(text)

    link = FullDuplexLink(LossFunc(0.2, 0, 0))
    link.node_a().write(text)
    print "Skipping:          '{0}'".format(link.node_b().read())

    link = FullDuplexLink(LossFunc(0, 0.2, 0))
    link.node_a().write(text)
    print "Modify:            '{0}'".format(link.node_b().read())

    link = FullDuplexLink(LossFunc(0, 0, 0.2))
    link.node_a().write(text)
    print "New:               '{0}'".format(link.node_b().read())

    link = FullDuplexLink(LossFunc(0.2, 0.2, 0.2))
    link.node_a().write(text)
    print "All:               '{0}'".format(link.node_b().read())

    print
