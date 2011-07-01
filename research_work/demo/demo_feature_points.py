#!/usr/bin/env python

import cv
import numpy
import pylab
from numpy import array

def main():
    src_cv_img = cv.LoadImage("data/gorskaya/images/1/g126.jpg")
    src_cv_img_gray = cv.LoadImage("data/gorskaya/images/1/g126.jpg", 
        cv.CV_LOAD_IMAGE_GRAYSCALE)

    (keypoints, descriptors) = \
        cv.ExtractSURF(src_cv_img_gray, None, cv.CreateMemStorage(), 
            (0, 30000, 3, 1))

    print("Found {0} keypoints".format(len(keypoints)))

    src_arr = array(src_cv_img[:, :])[:, :, ::-1]

    pylab.rc('image', interpolation='nearest')
    pylab.subplot(111)
    pylab.imshow(src_arr)
    pylab.plot(*[k[0] for k in keypoints], marker='o', color='r', ls='')

    pylab.show()

if __name__ == '__main__':
    main()

# vim: ts=4 sw=4 et:
