#!/usr/bin/env python

import cv
import numpy
import pylab
from numpy import array

def main():
    src_cv_img_1 = cv.LoadImage("data/gorskaya/images/1/g126.jpg")
    src_cv_img_gray_1 = cv.LoadImage("data/gorskaya/images/1/g126.jpg", 
        cv.CV_LOAD_IMAGE_GRAYSCALE)

    src_cv_img_2 = cv.LoadImage("data/gorskaya/images/1/g127.jpg")
    src_cv_img_gray_2 = cv.LoadImage("data/gorskaya/images/1/g127.jpg", 
        cv.CV_LOAD_IMAGE_GRAYSCALE)

    (keypoints_1, descriptors_1) = \
        cv.ExtractSURF(src_cv_img_gray_1, None, cv.CreateMemStorage(), 
            (0, 30000, 3, 1))
    (keypoints_2, descriptors_2) = \
        cv.ExtractSURF(src_cv_img_gray_2, None, cv.CreateMemStorage(), 
            (0, 30000, 3, 1))

    print("Found {0} and {1} keypoints".format(
        len(keypoints_1), len(keypoints_2)))

    src_arr_1 = array(src_cv_img_1[:, :])[:, :, ::-1]
    src_arr_2 = array(src_cv_img_2[:, :])[:, :, ::-1]

    pylab.rc('image', interpolation='nearest')

    pylab.subplot(121)
    pylab.imshow(src_arr_1)
    pylab.plot(*zip(*[k[0] for k in keypoints_1]), 
        marker='.', color='r', ls='')

    pylab.subplot(122)
    pylab.imshow(src_arr_2)
    pylab.plot(*zip(*[k[0] for k in keypoints_2]), 
        marker='.', color='r', ls='')

    pylab.show()

if __name__ == '__main__':
    main()

# vim: ts=4 sw=4 et:
