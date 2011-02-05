import sys
import random

if len(sys.argv) == 6:
    n = int(sys.argv[1])
    minx = int(sys.argv[2])
    maxx = int(sys.argv[3])
    miny = int(sys.argv[4])
    maxy = int(sys.argv[5])
else:
    print "Usage:\n  {0} number_of_points min_x max_x min_y max_y".\
    	format(sys.argv[0])
    sys.exit(0)

gen_range = 1000
min_val = -gen_range / 2.0
max_val = +gen_range / 2.0
for i in xrange(n):
    x = int(round(random.uniform(minx, maxx)))
    y = int(round(random.uniform(miny, maxy)))
    print x, y

# vim: set ts=4 sw=4 et:
