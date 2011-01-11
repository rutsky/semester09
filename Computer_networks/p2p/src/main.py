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

import PyQt4.uic
from PyQt4.QtGui import *
from PyQt4.QtCore import *
from PyQt4.Qt import *

class MainWindow(QMainWindow):
    def __init__(self, parent=None):
        super(MainWindow, self).__init__(parent)

        PyQt4.uic.loadUi('main_window.ui', self)

class RouterItem(QGraphicsItem):
    def __init__(self, parent=None):
        super(RouterItem, self).__init__(parent)

        # Circle color
        self.color = QColor(255, 0, 0)

        # Circle (width, height).
        self.size = QSizeF(10, 10)
        self.size_rect = QRectF(
            QPointF(-self.size.width() / 2.0, -self.size.height() / 2.0),
            self.size)

    def boundingRect(self):
        adjust = 2

        return self.size_rect.adjusted(-adjust, -adjust, adjust, adjust)

    def shape(self):
        path = QPainterPath()
        path.addEllipse(self.size_rect)
        return path

    def paint(self, painter, style_option, widget):
        painter.setPen(QPen(Qt.black, 0))
        painter.setBrush(QBrush(self.color))
        painter.drawEllipse(self.size_rect)

def main():
    app = QApplication(sys.argv)

    w = MainWindow()

    scene = QGraphicsScene()

    scene.setItemIndexMethod(QGraphicsScene.NoIndex)
    scene.setSceneRect(-150, -105, 300, 210)
    
    w.graphicsView.setCacheMode(QGraphicsView.CacheBackground)
    w.graphicsView.setViewportUpdateMode(
        QGraphicsView.BoundingRectViewportUpdate)
    w.graphicsView.setRenderHint(QPainter.Antialiasing)
    w.graphicsView.setTransformationAnchor(QGraphicsView.AnchorUnderMouse)
    w.graphicsView.setResizeAnchor(QGraphicsView.AnchorViewCenter)

    scene.addText("Hello, world!")
    scene.addItem(RouterItem())

    w.graphicsView.setScene(scene)

    w.show()

    sys.exit(app.exec_())
    
if __name__ == "__main__":
    main()
