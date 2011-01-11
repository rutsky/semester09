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

# TODO
print "NOTE! setup.py is not complete and exists for testing purposes only!"

from distutils.core import setup

setup(
    name='network_model',
    version='0.1',
    description="Network emulation test model",
    author='Vladimir Rutsky',
    author_email='altsysrq@gmail.com',
    #data_files=[('', ['main_window.ui'])], # don't work
    py_modules = ['main'],
    )
