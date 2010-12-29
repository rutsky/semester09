#  This file is part of network emulation test model.
#
#  Copyright (C) 2010  Vladimir Rutsky <altsysrq@gmail.com>
#
#  This program is free software: you can redistribute it and/or modify
#  it under the terms of the GNU General Public License as published by
#  the Free Software Foundation, either version 3 of the License, or
#  (at your option) any later version.
#
#  This program is distributed in the hope that it will be useful,
#  but WITHOUT ANY WARRANTY; without even the implied warranty of
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#  GNU General Public License for more details.
#
#  You should have received a copy of the GNU General Public License
#  along with this program.  If not, see <http://www.gnu.org/licenses/>.

__author__  = "Vladimir Rutsky <altsysrq@gmail.com>"
__license__ = "GPL"

__all__ = []

class Clock(object):
    def __init__(self):
        super(Clock, self).__init__()
        self._time = 0
        # TODO: Use some priority queue.
        # Dictionary: end_time -> [timer_object].
        self._timers = {}

    def time(self):
        return self._time;

    class _Timer(self):
        def __init__(self, clock, time_interval):
            assert time_interval >= 0
            self._clock = clock
            self._end_time = self._clock.time() + time_interval

        def end_time(self):
            return self._end_time

        def __bool__(self):
            return self._clock >= self._end_time

    def create_timer(self, time_interval):
        assert time_interval >= 0
        timer = _Timer(self, time_interval)
        self._timers.setdefault(timer.end_time(), []).append(timer)

    def wait(self, time_interval):
        assert time_interval >= 0
        self._time += time_interval
        while self._timers:
            t = sorted(self._timers.keys())[0]
            if t <= self.time():
                del self._timers[t]
