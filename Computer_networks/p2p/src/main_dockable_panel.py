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

__all__ = ["MainDockableWidget"]

import PyQt4.uic
from PyQt4.QtGui import *
from PyQt4.QtCore import *
from PyQt4.Qt import *

import config

class MainDockableWidget(QDockWidget):
    def __init__(self, parent=None):
        super(MainDockableWidget, self).__init__(parent)

        PyQt4.uic.loadUi('forms/main_dockable_panel.ui', self)

        self.sceneTraverseTimeSlider.valueChanged.connect(
            self.on_scene_traverse_time_changed)

        self.renderNodesRangeCheckBox.stateChanged.connect(
            self.on_render_routers_changed)

        self.connectionDistSlider.valueChanged.connect(
            self.on_connection_dist_changed)

        self.disconnectionDistSlider.valueChanged.connect(
            self.on_disconnection_dist_changed)

    @pyqtSlot(int)
    def on_scene_traverse_time_changed(self, value):
        config.router_velocity_factor = config.scene_width / value

    @pyqtSlot(int)
    def on_render_routers_changed(self, value):
        config.display_router_connection_range = bool(value)

    @pyqtSlot(int)
    def on_connection_dist_changed(self, value):
        if value > self.disconnectionDistSlider.value():
            value = self.disconnectionDistSlider.value()
            self.connectionDistSlider.setValue(value)
        else:
            ratio = value / 100.0
            self.connectionDistLabel.setText("{0:.2}".format(ratio))
            config.connection_distance = 0.5 * config.scene_width * ratio

    @pyqtSlot(int)
    def on_disconnection_dist_changed(self, value):
        if value < self.connectionDistSlider.value():
            value = self.connectionDistSlider.value()
            self.disconnectionDistSlider.setValue(value)
        else:
            ratio = value / 100.0
            self.disconnectionDistLabel.setText("{0:.2}".format(ratio))
            config.disconnection_distance = 0.5 * config.scene_width * ratio

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
                w = MainDockableWidget()
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
