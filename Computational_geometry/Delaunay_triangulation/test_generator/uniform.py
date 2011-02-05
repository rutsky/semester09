import sys
import random

if len(sys.argv) == 2:
    n = int(sys.argv[1])
else:
    print "Usage:\n  {0} <Number of points>".format(sys.argv[0])
    sys.exit(0)

gen_range = 1000
min_val = -gen_range / 2.0
max_val = +gen_range / 2.0
for i in xrange(n):
    print random.uniform(min_val, max_val), random.uniform(min_val, max_val)

# vim: set ts=4 sw=4 et: 
