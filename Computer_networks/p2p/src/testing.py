import os.path
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

def process_events_with_timeout(timeout=None, callback=None):
    from timer import Timer, DummyTimer

    app = QCoreApplication.instance()
    timer = Timer(timeout) if timeout is not None else DummyTimer()
    while any(map(lambda w: w.isVisible(),
            app.topLevelWidgets())):
        if callback is not None:
            callback()

        app.processEvents()
        if timer.is_expired():
            for w in ifilter(lambda w: w.isVisible(),
                    app.topLevelWidgets()):
                w.close()

def do_tests(tests_class, qt=False, init_logging=True,
        level=logging.CRITICAL):
    if qt:
        # Only one instance QApplication should exist.
        app = QApplication(sys.argv)

    if init_logging:
        logging.basicConfig(level=level)

    suite = unittest.TestSuite()
    for k, v in tests_class.__dict__.iteritems():
        if k.startswith('Test'):
            suite.addTests(unittest.TestLoader().loadTestsFromTestCase(v))

    unittest.TextTestRunner(verbosity=2).run(suite)

    if qt:
        app.exit()

def _main_test():
    import glob
    import re
    import traceback
    import multiprocessing

    def test_file(file_name):
        module_name = re.match("(.*)\.py", file_name).group(1)

        print "Testing {0}.".format(module_name)
        m = __import__(module_name, globals().copy(), locals().copy())
        try:
            test_func = m._test
        except AttributeError:
            print "Note: {0}._test() not found. Skipping.".format(module_name)
        else:
            try:
                #print test_func
                test_func()
            except:
                traceback.print_exc()

    # Run all modules.
    ignore_files = frozenset([os.path.basename(__file__), "setup.py",
        "setup_cx-freeze.py", "main.py"])
    for file_name in glob.iglob("*.py"):
        if file_name in ignore_files:
            continue

        # TODO: Mess with output from different processes.
        sys.stdout.flush()
        sys.stderr.flush()

        p = multiprocessing.Process(target=lambda: test_file(file_name))
        p.start()
        p.join()
        
        sys.stdout.flush()
        sys.stderr.flush()

# TODO: Add tests for this module.
if __name__ == "__main__":
    _main_test()
