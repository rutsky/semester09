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
import time

from PyQt4 import QtGui, QtCore, uic

class MainWindow(QtGui.QMainWindow):
    def __init__(self, parent=None):
        super(MainWindow, self).__init__(parent)

        uic.loadUi('main_window.ui', self)

def main():
    app = QtGui.QApplication(sys.argv)

    w = MainWindow()
    w.show()

    #scene = QtGui.QGraphicsScene()
    #scene.addText("Hello, world!")

    #view = QtGui.QGraphicsView(scene)
    #view.show()

    sys.exit(app.exec_())
    
if __name__ == "__main__":
    main()
