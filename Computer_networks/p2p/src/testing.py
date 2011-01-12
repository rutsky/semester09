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

import sys
if sys.version_info[:2] < (2, 7):
    # Backports.
    import unittest2 as unittest
else:
    import unittest
import logging
from itertools import ifilter

from PyQt4.QtGui import *
from PyQt4.QtCore import *

def process_events_with_timeout(timeout=None):
    from timer import Timer, DummyTimer

    app = QCoreApplication.instance()
    timer = Timer(timeout) if timeout is not None else DummyTimer()
    while any(map(lambda w: w.isVisible(),
            app.topLevelWidgets())):
        app.processEvents()
        if timer.is_expired():
            for w in ifilter(lambda w: w.isVisible(),
                    app.topLevelWidgets()):
                w.close()

def do_tests(tests_class, qt=False, level=logging.CRITICAL):
    if qt:
        # Only one instance QApplication should exist.
        app = QApplication(sys.argv)

    logging.basicConfig(level=level)

    suite = unittest.TestSuite()
    for k, v in tests_class.__dict__.iteritems():
        if k.startswith('Test'):
            suite.addTests(unittest.TestLoader().loadTestsFromTestCase(v))

    unittest.TextTestRunner(verbosity=2).run(suite)

    if qt:
        app.exit()
