"""
Total ordering class decorator recipe

Downloaded from http://code.activestate.com/recipes/576685/
Created by Raymond Hettinger on Tue, 10 Mar 2009, distributed under
MIT License.
"""

import sys as _sys
if _sys.version_info[:2] >= (2, 7):
    # Use functools total_ordering().
    from functools import total_ordering
else:
    def total_ordering(cls):
        'Class decorator that fills-in missing ordering methods'
        convert = {
            '__lt__': [('__gt__', lambda self, other: other < self),
                       ('__le__', lambda self, other: not other < self),
                       ('__ge__', lambda self, other: not self < other)],
            '__le__': [('__ge__', lambda self, other: other <= self),
                       ('__lt__', lambda self, other: not other <= self),
                       ('__gt__', lambda self, other: not self <= other)],
            '__gt__': [('__lt__', lambda self, other: other > self),
                       ('__ge__', lambda self, other: not other > self),
                       ('__le__', lambda self, other: not self > other)],
            '__ge__': [('__le__', lambda self, other: other >= self),
                       ('__gt__', lambda self, other: not other >= self),
                       ('__lt__', lambda self, other: not self >= other)]
        }
        if hasattr(object, '__lt__'):
            roots = [op for op in convert
                if getattr(cls, op) is not getattr(object, op)]
        else:
            roots = set(dir(cls)) & set(convert)
        assert roots, 'must define at least one ordering operation: < > <= >='
        root = max(roots)       # prefer __lt __ to __le__ to __gt__ to __ge__
        for opname, opfunc in convert[root]:
            if opname not in roots:
                opfunc.__name__ = opname
                opfunc.__doc__ = getattr(int, opname).__doc__
                setattr(cls, opname, opfunc)
        return cls

def _test():
    from testing import unittest, do_tests

    class Tests:
        class TestTotalOrdering(unittest.TestCase):
            def test_main(self):
                # TODO
                pass

    do_tests(Tests)

if __name__ == '__main__':
    _test()
