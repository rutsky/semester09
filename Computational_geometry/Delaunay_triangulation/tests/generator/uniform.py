import sys
import random

if len(sys.argv) >= 2:
    n = int(sys.argv[1])
else:
    n = 1000

gen_range = 1000
min_val = -gen_range / 2.0
max_val = +gen_range / 2.0
for i in xrange(n):
    print random.uniform(min_val, max_val), random.uniform(min_val, max_val)
