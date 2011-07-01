#!/usr/bin/env python

import sys

import cv

from PySide import QtCore
from PySide import QtGui
from PySide import QtUiTools

class MyQUiLoader(QtUiTools.QUiLoader):
    def __init__(self, baseinstance):
        super(MyQUiLoader, self).__init__()
        self.baseinstance = baseinstance

    def createWidget(self, className, parent=None, name=""):
        widget = QtUiTools.QUiLoader.createWidget(self, className, parent, 
                name)
        if parent is None:
            return self.baseinstance
        else:
            setattr(self.baseinstance, name, widget)
            return widget

def loadUi(uifile, baseinstance=None):
    loader = MyQUiLoader(baseinstance)
    ui = loader.load(uifile)
    QtCore.QMetaObject.connectSlotsByName(ui)
    return ui

class MainWidget(QtGui.QWidget):
    def __init__(self, parent=None):
        super(MainWidget, self).__init__(parent)

        loadUi("main_widget.ui", self)

def main():
    # Create a Qt application.
    app = QtGui.QApplication(sys.argv)

    w = MainWidget()
    w.show()

    app.exec_()
    sys.exit()

if __name__ == '__main__':
    main()

# vim: ts=4 sw=4 et:
