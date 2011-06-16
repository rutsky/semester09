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

__all__ = ["TransmissionWidget"]

import PyQt4.uic
from PyQt4.QtGui import *
from PyQt4.QtCore import *
from PyQt4.Qt import *

import config

class SourceGraphicsView(QGraphicsView):
    def __init__(self, parent=None):
        super(SourceGraphicsView, self).__init__(parent)

    def resizeEvent(self, event):
        super(SourceGraphicsView, self).resizeEvent(event)

        self.fitInView(self.scene().sceneRect(), Qt.KeepAspectRatio)

class TransmittedGraphicsView(QGraphicsView):
    def __init__(self, parent=None):
        super(TransmittedGraphicsView, self).__init__(parent)

    def resizeEvent(self, event):
        super(TransmittedGraphicsView, self).resizeEvent(event)

        self.fitInView(self.scene().sceneRect(), Qt.KeepAspectRatio)

class TransmissionWidget(QDockWidget):
    def __init__(self, parent=None):
        super(TransmissionWidget, self).__init__(parent)

        PyQt4.uic.loadUi('forms/transmission_widget.ui', self)

        self.sourceGraphicsView = SourceGraphicsView()
        self.sourceGroupVBox.addWidget(self.sourceGraphicsView)

        self.source_pixmap = None

        self.source_scene = QGraphicsScene()
        self.sourceGraphicsView.setScene(self.source_scene)
        self.source_image_item = None

        self.transmittedGraphicsView = TransmittedGraphicsView()
        self.transmittedGroupVBox.addWidget(self.transmittedGraphicsView)

        self.transmitted_pixmap = None

        self.transmitted_scene = QGraphicsScene()
        self.transmittedGraphicsView.setScene(self.transmitted_scene)
        self.transmitted_image_item = None

        self.openImageButton.clicked.connect(self.on_open_image)

        self.last_image_path = None

    def reload_image(self):
        self.load_image(self.last_image_path)

    def load_image(self, path):
        self.last_image_path = path

        if self.source_image_item is not None:
            self.source_scene.removeItem(self.source_image_item)
            self.source_image_item = None

        pixmap = QPixmap(path)
        self.source_pixmap = pixmap

        if self.source_image_item is not None:
            self.source_scene.removeItem(self.source_image_item)
            self.source_image_item = None

        self.source_image_item = QGraphicsPixmapItem()
        self.source_scene.addItem(self.source_image_item)
        self.source_image_item.setVisible(True)
        self.source_image_item.setPixmap(pixmap)
        self.source_scene.setSceneRect(0, 0, pixmap.width(), pixmap.height())

        self.sourceGraphicsView.fitInView(self.source_image_item,
            Qt.KeepAspectRatio)

        self.transmitted_pixmap = QPixmap(pixmap.size())
        self.transmitted_pixmap.fill(QColor(200, 200, 200))

        if self.transmitted_image_item is not None:
            self.transmitted_scene.removeItem(self.transmitted_image_item)
            self.transmitted_image_item = None

        self.transmitted_image_item = QGraphicsPixmapItem()
        self.transmitted_scene.addItem(self.transmitted_image_item)
        self.transmitted_image_item.setVisible(True)
        self.transmitted_image_item.setPixmap(self.transmitted_pixmap)
        self.transmitted_scene.setSceneRect(0, 0,
            self.transmitted_pixmap.width(), self.transmitted_pixmap.height())

        self.sourceGraphicsView.fitInView(self.transmitted_image_item,
            Qt.KeepAspectRatio)

    @pyqtSlot()
    def on_open_image(self):
        file_name = QFileDialog.getOpenFileName(self, self.tr("Open Image"),
            "images", self.tr("Image Files (*.png *.jpg *.jpeg *.bmp)"))

        self.load_image(file_name)

def _test(timeout=1, disabled_loggers=None, level=None):
    # TODO: Use in separate file to test importing functionality.

    from testing import unittest, do_tests, process_events_with_timeout

    class Tests(object):
        class TestMainWindow(unittest.TestCase):
            def setUp(self):
                self.finished = False
            
            def tearDown(self):
                if self.finished:
                    process_events_with_timeout(timeout)

            def test_main(self):
                w = TransmissionWidget()
                w.show()

                self.finished = True

    do_tests(Tests, qt=True, disabled_loggers=disabled_loggers, level=level)

if __name__ == "__main__":
    disabled_loggers = []
    for r in xrange(20):
        disabled_loggers.append("DatagramRouter.router={0}".format(r))
        disabled_loggers.append("RIPService.router={0}".format(r))
        disabled_loggers.append("RouterServiceManager.router={0}".format(r))

        for rr in xrange(20):
            disabled_loggers.append("FrameTransmitter.{0}->{1}".format(r, rr))
    
    _test(timeout=None, disabled_loggers=disabled_loggers, level=0)

# vim: set ts=4 sw=4 et:
