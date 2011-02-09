import sys
import random
import math

if len(sys.argv) == 2:
    n = int(sys.argv[1])
else:
    print "Usage:\n  {0} <Number of points>".format(sys.argv[0])
    sys.exit(0)

a = 9000
b = 7000
for i in xrange(n):
    t = random.uniform(0, 2 * math.pi)
    x = int(round(a * math.cos(t)))
    y = int(round(b * math.sin(t)))
    print x, y

# vim: set ts=4 sw=4 et: 
