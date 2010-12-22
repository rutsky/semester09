#!/bin/sh

spin -a main.pml

# Safety
gcc -DMEMLIM=2048 -O2 -DNFAIR=4 -DSAFETY -DNOCLAIM -w -o pan pan.c

./pan -m2000000  -c1

# Acceptance cycles.
gcc -DMEMLIM=2048 -O2 -DNFAIR=4 -w -o pan pan.c

./pan -m2000000 -a -c0 -N safe_green_01
./pan -m2000000 -a -c0 -N safe_green_02
./pan -m2000000 -a -c0 -N safe_green_03
./pan -m2000000 -a -c0 -N safe_green_13
./pan -m2000000 -a -c0 -N safe_green_23

./pan -m2000000 -a -c0 -N car_will_pass_0
./pan -m2000000 -a -c0 -N car_will_pass_1
./pan -m2000000 -a -c0 -N car_will_pass_2
./pan -m2000000 -a -c0 -N car_will_pass_3

