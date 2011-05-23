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
import signal
import traceback

from PyQt4.QtGui import *
from PyQt4.QtCore import *

from main_window import MainWindow

def handle_int_signal(signum, frame):
    """Ask windows to close if Ctrl+C pressed."""
    print "test" # DEBUG
    qt4.qApp.closeAllWindows()

class IgnoreException(Exception):
    """A special exception class to be ignored by the exception handler."""

def excepthook(excepttype, exceptvalue, tracebackobj):
    """Show exception dialog if an exception occurs."""
    if not isinstance(exceptvalue, IgnoreException):
        # Next exception is ignored to clear out the stack frame of the
        # previous exception.

        full_exception_text = "".join(traceback.format_exception(
            excepttype, exceptvalue, tracebackobj))
        exception_text = "".join(traceback.format_exception_only(
            excepttype, exceptvalue))

        sys.stderr.write(full_exception_text)

        msg_box = qt4.QMessageBox(
            qt4.QMessageBox.Critical,
            "Unhandled exception",
            "Unhandled exception.",
            qt4.QMessageBox.Close,
            # TODO: Fails with:
            # TypeError: arguments did not match any overloaded call:
            #   QMessageBox(QWidget parent=None): argument 1 has unexpected type 'Icon'
            #   QMessageBox(QMessageBox.Icon, QString, QString, QMessageBox.StandardButtons buttons=QMessageBox.NoButton, QWidget parent=None, Qt.WindowFlags flags=Qt.Dialog|Qt.MSWindowsFixedSizeDialogHint): argument 5 has unexpected type 'WindowFlags'
            #   QMessageBox(QString, QString, QMessageBox.Icon, int, int, int, QWidget parent=None, Qt.WindowFlags flags=Qt.Dialog|Qt.MSWindowsFixedSizeDialogHint): argument 1 has unexpected type 'Icon'
            #qt4.Qt.WindowFlags(qt4.Qt.Dialog)
            #qt4.QtCore.Qt.WindowFlags(0)
            )
        # Looks like it's quite hard to make QMessageBox normally resizable,
        # see <http://bugreports.qt.nokia.com/browse/QTBUG-3696> for details.
        #msg_box.setWindowFlags(qt4.Qt.Window)
        msg_box.setInformativeText(exception_text)
        msg_box.setDetailedText(full_exception_text)
        #msg_box.setSizeGripEnabled(True)
        #msg_box.adjustSize()
        msg_box.setDefaultButton(qt4.QMessageBox.Close)

        msg_box.exec_()
        #raise IgnoreException

def main():
    # Load translator.
    translator = QTranslator()
    translator.load('i18n/ru_RU')

    # Create Qt application.
    app = QApplication(sys.argv)

    # Close application when all windows closed.
    app.lastWindowClosed.connect(app.quit)

    # Handle exceptions in Qt threads.
    sys.excepthook = excepthook

    # Register a signal handler to catch ctrl+C
    # TODO: Don't work
    signal.signal(signal.SIGINT, handle_int_signal)

    # Apply translator.
    app.installTranslator(translator)

    w = MainWindow()

    for i in xrange(16):
        w.add_router()

    w.shake_routers()

    w.show()

    sys.exit(app.exec_())
    
if __name__ == "__main__":
    main()

# vim: set ts=4 sw=4 et:
