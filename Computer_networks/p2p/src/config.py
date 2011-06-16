#  This file is part of network emulation test model.
#
#  Copyright (C) 2010, 2011  Vladimir Rutsky <altsysrq@gmail.com>
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

default_log_format = "%(asctime)-15s %(levelname)-8s %(name)-30s %(message)s"

thread_sleep_time = 0.1
frame_transmitter_thread_sleep_time = 0.04
use_openGL = False
packets_delivery_time_factor = 10

# RIP.
rip_update_period = 7
rip_inf_timeout = 30
rip_remove_timeout = 60

max_routers_num = 16
image_cut_rows = 10
image_cut_columns = 10

image_transfer_send_period = 1

scene_width = 300
scene_height = 210

num_of_topology_changes_in_stat = 10

# Not constant values:
router_velocity_factor = 1
display_router_connection_range = False
connection_distance = 50
disconnection_distance = 70

def _test():
    # TODO: Use in separate file to test importing functionality.

    from testing import unittest, do_tests
    
    class Tests(object):
        class TestConfig(unittest.TestCase):
            pass

    do_tests(Tests)

if __name__ == "__main__":
    _test()

# vim: set ts=4 sw=4 et:
