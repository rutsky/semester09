#  This file is part of risk calculation suite.
#
#  Copyright (C) 2011  Vladimir Rutsky <altsysrq@gmail.com>
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

SOURCES = main.py \
  config.py \
  main_window.py \
  datagram.py \
  duplex_link.py \
  echo_packet_scene_item.py \
  frame.py \
  link_manager.py \
  link_scene_item.py \
  palette.py \
  recordtype.py \
  rip_packet_scene_item.py \
  rip.py \
  router_name.py \
  router.py \
  router_scene_item.py \
  routing_table.py \
  service_manager.py \
  sliding_window.py \
  testing.py \
  timer.py \
  total_ordering.py \
  main_dockable_panel.py \
  transmission_widget.py \
  image_transfer_router_scene_item.py \
  data_transfer.py \
  image_transfer_packet_scene_item.py \
  controllable_frame_transmitter.py \
  statistics_widget.py
TRANSLATIONS = i18n/ru_RU.ts
FORMS = forms/main_window.ui \
  forms/main_dockable_panel.ui \
  forms/transmission_widget.ui \
  forms/statistics_widget.ui

# vim: ts=2 sw=2 et:
