import sys
import random
import math

# TODO: Draft. Not tested.

# Each point generator assume that input arguments are float and correctly 
# ordered.

def point_on_ellipse(minx, maxx, miny, maxy):
    center = (minx + maxx) / 2.0
    a = maxx - minx
    b = maxy - miny
    angle = random.uniform(0, 2 * math.pi)
    x = a * math.cos(alpha)
    y = b * math.sin(alpha)
    return (x, y)

def point_on_parabola(minx, maxx, miny, maxy):
    x_range = maxx - minx
    y_range = maxy - miny
    x0 = random.uniform(0, x_range)
    y0 = x0**2 * (y_range / x_range**2)
    x = minx + x0
    y = miny + y0
    return (x, y)

def uniform_point(minx, maxx, miny, maxy):
    x = random.uniform(minx, maxx)
    y = random.uniform(miny, maxy)
    return (x, y)

def generate_points(generator, n, 
                    minx=-1000, maxx=1000, miny=-1000, maxy=1000):
    assert minx <= maxx and miny <= maxy
    for i in xrange(n):
        yield generator(float(minx), float(maxx), float(miny), float(maxy))

def combine_generators(pairs_generator_nonnormalized_ratio, n,
                       minx=-1000, maxx=1000, miny=-1000, maxy=1000):
    generators, ratios = zip(*pairs_generator_nonnormalized_ratio)
    ratios_sum = sum(ratios)
    
    # TODO: Yield points, don't store them in list.
    points = []
    for generator, ratio in zip(generators, ratios):
        n0 = n * float(ratio) / ratio_sum
        n0 = min(n0, n - len(points))
        points.extend(generate_points(generator, n0))
    if len(points) != n:
        assert len(points) < n
        points.extend(generate_points(generator, n - len(points)))
    assert len(points) == n
    return points

def round_points(points):
    for x, y in points:
        yield (round(x), round(y))

if __name__ == '__main__':
    import argparse

    parser = argparse.ArgumentParser(description='Generate points.')
    
    # TODO

# vim: set ts=4 sw=4 et:
