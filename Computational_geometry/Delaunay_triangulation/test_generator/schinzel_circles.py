import sys
import math

if len(sys.argv) >= 2:
    n = int(sys.argv[1])
else:
    print "Usage:\n  {0} <Number of points>".format(sys.argv[0])
    sys.exit(0)

# Schinzel circles:
# http://mathworld.wolfram.com/SchinzelCircle.html

assert n > 0

def lattice_points(n):
    # TODO: Slow.
    if n % 2 == 0:
        # n == 2 * k
        k = n / 2

        # (x - 1/2)**2 + y**2 == 1/4 * 5**(k - 1)
        # 4 * y**2 == 5**(k - 1) - (2 * x - 1)**2
        r = 1 / 4.0 * 5**(k - 1)
        #print r
        for x in xrange(int(math.floor(0.5 - r)) - 1, 
                        int(math.ceil(0.5 + r)) + 2):
            v = 5**(k - 1) - (2 * x - 1)**2
            if v % 4 != 0 or v < 0:
                continue
            v /= 4
            y = int(round(v**0.5))
            if y**2 == v:
                yield (x, y)
                if y != 0:
                    yield (x, -y)
    else:
        # n == 2 * k + 1
        k = (n - 1) / 2

        # (x - 1/3)**2 + y**2 == 1/9 * 5**(2 * k)
        # 9 * y**2 == 5**(2 * k) - (3 * x - 1)**2
        r = 1 / 9.0 * 5**(2 * k)
        #print r
        for x in xrange(int(math.floor(1/3.0 - r)) - 1, 
                        int(math.ceil(1/3.0 + r)) + 2):
            v = 5**(2 * k) - (3 * x - 1)**2
            if v % 9 != 0 or v < 0:
                continue
            v /= 9
            y = int(round(v**0.5))
            if y**2 == v:
                yield (x, y)
                if y != 0:
                    yield (x, -y)
 
for (x, y) in lattice_points(n):
    print x, y    

# vim: set ts=4 ts=4 sw=4 et
