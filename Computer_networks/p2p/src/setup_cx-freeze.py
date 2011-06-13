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

# Based on examples provided with cx_Freeze.

import sys
import os

from cx_Freeze import setup, Executable

base = None
if sys.platform == "win32":
    base = "Win32GUI"

include_files = [
    (os.path.join('forms', 'main_window.ui'), 
            os.path.join('forms', 'main_window.ui')),
    (os.path.join('forms', 'main_dockable_panel.ui'), 
            os.path.join('forms', 'main_dockable_panel.ui')),
    ]
includes = ['sip', 'encodings.ascii', 'encodings.utf_8', 'encodings.hex_codec']

setup(
    name="network_model",
    version="0.2",
    description="Network emulation test model",
    author='Vladimir Rutsky',
    author_email='altsysrq@gmail.com',
    options={
        'build_exe': {
            'include_files': include_files,
            'includes': includes,
            },
        },
    executables=[Executable("main.py", base=base)],
    )

# vim: set ts=4 sw=4 et:
