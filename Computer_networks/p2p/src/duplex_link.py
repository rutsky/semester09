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

__all__ = ["ReceivingNode", "SendingNode", "FullDuplexNode", 
    "FullDuplexLink", "LossFunc"]

"""Byte channel implementation.
"""

import Queue
import bisect
import random
import StringIO

# TODO: May be loss function will loose bits, not bytes?

class SendingNode(object):
    def __init__(self, **kwds):
        self.send_queue = kwds.pop('send_queue')
        super(SendingNode, self).__init__(**kwds)

    def _write_ch(self, ch):
        assert isinstance(ch, str)
        assert len(ch) == 1
        self.send_queue.put(ch)

    def write(self, string):
        assert isinstance(string, str)
        for ch in string:
            self._write_ch(ch)

class ReceivingNode(object):
    def __init__(self, **kwds):
        self.receive_queue = kwds.pop('receive_queue')
        super(ReceivingNode, self).__init__(**kwds)

    def read(self, size=0, block=True):
        """Read bytes from input queue.
        If `size' equal to zero it reads all available in queue characters.
        Assumed that this function is the only reader from queue.

        Otherwise if `block' is True it reads exactly `size' elements.
        If `block' is False it reads not more that `size' elements depending
        on how much is currently available in queue.
        """

        assert size >= 0

        in_str = StringIO.StringIO()

        while size == 0 or len(in_str.getvalue()) < size:
            try:
                in_str.write(self.receive_queue.get(block and (size > 0)))
            except Queue.Empty:
                break

        return in_str.getvalue()

# TODO: May be not "loss" but "noise"?
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

    def _write_ch(self, ch):
        for new_ch in self._loss_func(ch):
            super(SendingWithLossNode, self)._write_ch(new_ch)

class FullDuplexNode(SendingWithLossNode, ReceivingNode):
    def __init__(self, **kwds):
        super(FullDuplexNode, self).__init__(**kwds)

def FullDuplexLink(a_to_b_queue=None, b_to_a_queue=None, loss_func=None):
    queue1 = a_to_b_queue if a_to_b_queue is not None else Queue.Queue()
    queue2 = b_to_a_queue if b_to_a_queue is not None else Queue.Queue()

    node_a = FullDuplexNode(
        send_queue   =queue1,
        receive_queue=queue2,
        loss_func=loss_func)
    node_b = FullDuplexNode(
        send_queue   =queue2,
        receive_queue=queue1,
        loss_func=loss_func)
    return node_a, node_b

def _test():
    # TODO: Use in separate file to test importing functionality.

    import sys
    if sys.version[:2] < (2, 7):
        # Backports.
        import unittest2 as unittest
    else:
        import unittest

    class Tests(object):
        class TestDuplexLink(unittest.TestCase):
            def test_link(self):
                a, b = FullDuplexLink()

                self.assertEqual(a.read(), "")
                a.write("test")
                self.assertEqual(b.read(), "test")
                b.write("1234")
                self.assertEqual(a.read(2), "12")
                self.assertEqual(a.read(), "34")
                a.write("789")
                a.write("098")
                self.assertEqual(b.read(), "789098")
                self.assertEqual(b.read(), "")

        class TestLossFunc(unittest.TestCase):
            def test_losses(self):
                # TODO: Non determinant tests.

                text = "This is quite long text, do you agree?"
                print "Working with text: '{0}'".format(text)

                a, b = FullDuplexLink(loss_func=LossFunc(0.2, 0, 0))
                a.write(text)
                result = b.read()
                print "Skipping:          '{0}'".format(result)
                self.assertLess(len(result), len(text))

                a, b = FullDuplexLink(loss_func=LossFunc(0, 0.2, 0))
                a.write(text)
                result = b.read()
                print "Modify:            '{0}'".format(result)
                self.assertEqual(len(result), len(text))
                self.assertNotEqual(result, text)

                a, b = FullDuplexLink(loss_func=LossFunc(0, 0, 0.2))
                a.write(text)
                result = b.read()
                print "New:               '{0}'".format(result)
                self.assertGreater(len(result), len(text))

                a, b = FullDuplexLink(loss_func=LossFunc(0.2, 0.2, 0.2))
                a.write(text)
                result = b.read()
                print "All:               '{0}'".format(result)
                self.assertNotEqual(result, text)

    suite = unittest.TestSuite()
    for k, v in Tests.__dict__.iteritems():
        if k.startswith('Test'):
            suite.addTests(unittest.TestLoader().loadTestsFromTestCase(v))

    unittest.TextTestRunner(verbosity=2).run(suite)

if __name__ == "__main__":
    _test()
