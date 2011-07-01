#!/usr/bin/env python

import cv
import numpy
import pylab

def main():
    src = cv.LoadImage("data/gorskaya/images/1/g126.jpg")

    pylab.rc('image', interpolation='nearest')
    pylab.subplot(111)
    pylab.imshow(src[:, :])

    pylab.show()

if __name__ == '__main__':
    main()

# vim: ts=4 sw=4 et:
