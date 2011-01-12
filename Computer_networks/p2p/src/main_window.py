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

__all__ = ["MainWindow"]

import random

import PyQt4.uic
from PyQt4.QtGui import *
from PyQt4.QtCore import *
from PyQt4.Qt import *

from router_scene_item import RouterItem

class MainWindow(QMainWindow):
    def __init__(self, parent=None):
        super(MainWindow, self).__init__(parent)

        PyQt4.uic.loadUi('main_window.ui', self)

        # Scene working rectangle.
        self.scene_rect = QRectF(-150, -105, 300, 210)

        self.scene = QGraphicsScene()
        self.graphicsView.setScene(self.scene)
        self.scene.setSceneRect(self.scene_rect)

        # Disable spatial indexing since all objects will be moving.
        self.scene.setItemIndexMethod(QGraphicsScene.NoIndex)

        self.graphicsView.setCacheMode(QGraphicsView.CacheBackground)
        self.graphicsView.setViewportUpdateMode(
            QGraphicsView.BoundingRectViewportUpdate)
        self.graphicsView.setRenderHint(QPainter.Antialiasing)
        #self.graphicsView.setTransformationAnchor(QGraphicsView.AnchorUnderMouse)
        self.graphicsView.setResizeAnchor(QGraphicsView.AnchorViewCenter)
        
        # Disable scrollbars. Seems this is required for correct fitInView()
        # work in resizeEvent(). See fitInView() documentation for details.
        self.graphicsView.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
        self.graphicsView.setVerticalScrollBarPolicy(Qt.ScrollBarAlwaysOff)

        #self.scene.addText("Hello, world!")

        # debug
        self.scene_rect_item = self.scene.addRect(
            QRectF(self.scene_rect.topLeft(), QSizeF(
                self.scene_rect.width() - 1,
                self.scene_rect.height() - 1)))
                
        self.routers = set()

        self.timer_id = self.startTimer(1000 / 25.0)

    def showEvent(self, event):
        super(MainWindow, self).showEvent(event)
        self.graphicsView.fitInView(self.scene_rect, Qt.KeepAspectRatio)

    def resizeEvent(self, event):
        super(MainWindow, self).resizeEvent(event)
        self.graphicsView.fitInView(self.scene_rect, Qt.KeepAspectRatio)

    def timerEvent(self, event):
        pass

    def add_router(self, name, pos=None):
        assert isinstance(name, int) and 0 <= name < 2**32
        assert self.scene

        if pos is None:
            scene_rect = self.scene.sceneRect()
            router_pos = QPointF(
                random.randrange(scene_rect.left(), scene_rect.width()),
                random.randrange(scene_rect.top(), scene_rect.height()))
        else:
            router_pos = pos

        router = RouterItem(name)
        self.scene.addItem(router)
        router.setPos(router_pos)
        self.routers.add(router)

def _test():
    # TODO: Use in separate file to test importing functionality.

    import sys
    if sys.version_info[:2] < (2, 7):
        # Backports.
        import unittest2 as unittest
    else:
        import unittest
    import logging

    class Tests(object):
        class TestMainWindow(unittest.TestCase):
            def setUp(self):
                self.app = QApplication(sys.argv)
                self.finished = False

            def tearDown(self):
                if self.finished:
                    self.app.exec_()

            def test_main(self):
                self.w = MainWindow()
                self.w.show()

                self.w.add_router(1)
                self.w.add_router(2)
                self.w.add_router(3)

                self.finished = True

    #logging.basicConfig(level=logging.DEBUG)
    logging.basicConfig(level=logging.CRITICAL)

    suite = unittest.TestSuite()
    for k, v in Tests.__dict__.iteritems():
        if k.startswith('Test'):
            suite.addTests(unittest.TestLoader().loadTestsFromTestCase(v))

    unittest.TextTestRunner(verbosity=2).run(suite)

if __name__ == "__main__":
    _test()
