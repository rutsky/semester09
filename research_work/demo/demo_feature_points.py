#!/usr/bin/env python

import cv
import numpy
import pylab
from numpy import array

def main():
    src_cv_img = cv.LoadImage("data/gorskaya/images/1/g126.jpg")

    src_arr = array(src_cv_img[:, :]) 

    pylab.rc('image', interpolation='nearest')
    pylab.subplot(111)
    pylab.imshow(src_arr)

    pylab.show()

if __name__ == '__main__':
    main()

# vim: ts=4 sw=4 et:
