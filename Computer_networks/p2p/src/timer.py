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

__all__ = ["Timer", "DummyTimer"]

import time

# TODO: Pretty ungeneric and ugly timers.

class Timer(object):
    def __init__(self, period, start=True, start_time=None):
        super(Timer, self).__init__()
        self.period = period
        if start:
            self.start_time = \
                start_time if start_time is not None else time.time()
        else:
            self.start_time = None

    def is_expired(self):
        """Returns is timer expired or is timer not started.
        """
        return (self.start_time is None or
            self.start_time + self.period <= time.time())

    def restart(self, restart_time=None):
        self.start_time = \
            restart_time if restart_time is not None else time.time()

    def reset(self):
        self.start_time = None

class DummyTimer(object):
    def __init__(self):
        super(DummyTimer, self).__init__()

    def is_expired(self):
        return False

def _test():
    # TODO: Use in separate file to test importing functionality.

    import sys
    if sys.version[:2] < (2, 7):
        # Backports.
        import unittest2 as unittest
    else:
        import unittest
    import logging

    class Tests(object):
        # TODO: Assume that computer is not very slow.
                
        class TestTimer(unittest.TestCase):
            def test_constructor(self):
                t = Timer(0.3)

            def test_with_time(self):
                t = Timer(0.3)

                self.assertEqual(t.is_expired(), False)
                self.assertEqual(t.is_expired(), False)
                self.assertEqual(t.is_expired(), False)
                self.assertEqual(t.is_expired(), False)

                time.sleep(0.3)
                self.assertEqual(t.is_expired(), True)
                self.assertEqual(t.is_expired(), True)

            def test_without_time(self):
                t = Timer(0.3, start=False)

                self.assertEqual(t.is_expired(), True)

                t.restart()
                self.assertEqual(t.is_expired(), False)

                time.sleep(0.3)
                self.assertEqual(t.is_expired(), True)

                t.restart()
                self.assertEqual(t.is_expired(), False)

                time.sleep(0.3)
                self.assertEqual(t.is_expired(), True)

                t.restart()
                self.assertEqual(t.is_expired(), False)

                t.reset()
                self.assertEqual(t.is_expired(), True)

        class TestDummyTimer(unittest.TestCase):
            def test_main(self):
                t = DummyTimer()
                self.assertEqual(t.is_expired(), False)

    logging.basicConfig(level=logging.DEBUG)

    suite = unittest.TestSuite()
    for k, v in Tests.__dict__.iteritems():
        if k.startswith('Test'):
            suite.addTests(unittest.TestLoader().loadTestsFromTestCase(v))

    unittest.TextTestRunner(verbosity=2).run(suite)

if __name__ == "__main__":
    _test()
