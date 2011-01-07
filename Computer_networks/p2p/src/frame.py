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

__all__ = ["SimpleFrameTransmitter"]

import StringIO

class SimpleFrameTransmitter(object):
    # Similar to SLIP.
    frame_end       = "\xC0"
    esc_char        = "\xDB"
    frame_end_subst = esc_char + "\xDC"
    esc_subst       = esc_char + "\xDD"

    def __init__(self, *args, **kwargs):
        self.node = kwargs.pop('node')
        super(SimpleFrameTransmitter, self).__init__(*args, **kwargs)
        self._read_buffer = StringIO.StringIO()

    def write_frame(self, frame):
        raw_data = (
            # Replace escape characters.
            frame.replace(self.esc_char, self.esc_subst)
            # Replace frame end characters inside frame.
                .replace(self.frame_end, self.frame_end_subst) +
            # Append frame end at end.
            self.frame_end)
        self.node.write(raw_data)

    def read_frame(self, block=True):
        """Read single frame from input channel.
        Assumed that this is the only reader from channel.
        """
        while True:
            ch = self.node.read(1, block=block)
            if ch == "":
                # No more characters for now.
                return None
            elif ch == self.frame_end:
                # Read till frame end. Decode and return it.

                # Obtain encoded frame.
                encoded_frame = self._read_buffer.getvalue()

                # Reset input buffer.
                self._read_buffer = StringIO.StringIO()

                # Decode frame.
                frame = encoded_frame.replace(self.frame_end_subst,
                                              self.frame_end).\
                    replace(self.esc_subst, self.esc_char)

                return frame
            else:
                self._read_buffer.write(ch)

def _test():
    # TODO: Use in separate file to test importing functionality.

    import unittest2 as unittest
    from duplex_link import FullDuplexLink

    class TestFrameTransmitter(unittest.TestCase):
        def test_link(self):
            a, b = FullDuplexLink()

            at = SimpleFrameTransmitter(node=a)
            bt = SimpleFrameTransmitter(node=b)

            self.assertEqual(at.read_frame(block=False), None)
            self.assertEqual(bt.read_frame(block=False), None)

            at.write_frame("")
            self.assertEqual(bt.read_frame(), "")

            bt.write_frame("A")
            self.assertEqual(at.read_frame(), "A")

            self.assertEqual(at.read_frame(block=False), None)

            test = "Th{fes}is is{es} the {fe} te{ec}st! 12345".format(
                fe=SimpleFrameTransmitter.frame_end,
                ec=SimpleFrameTransmitter.esc_char,
                fes=SimpleFrameTransmitter.frame_end_subst,
                es=SimpleFrameTransmitter.esc_subst)
            at.write_frame(test)
            self.assertEqual(bt.read_frame(), test)

    #unittest.main()

    suite = unittest.TestLoader().loadTestsFromTestCase(TestFrameTransmitter)
    unittest.TextTestRunner(verbosity=2).run(suite)
    
if __name__ == "__main__":
    _test()
