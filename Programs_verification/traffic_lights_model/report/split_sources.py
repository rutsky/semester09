#!/usr/bin/env python

with open("data/main.pml", 'r') as f:
    contents = f.read()
    
cut_string = "/*** cut here ***/"

parts = contents.split(cut_string)
assert len(parts) == 6

locations = {
    0: "data/begin.pml_",
    1: "data/car_generators.pml_",
    2: "data/intersections.pml_",
    3: "data/traffic_lights.pml_",
    4: "data/main.pml_",
    5: "data/correctness.pml_",
    }

for idx, path in locations.iteritems():
    with open(path, 'w') as f:
        f.write(parts[idx].strip("\n"))

with open("data/main.pml_", 'w') as f:
    f.write(contents.replace("\n" + cut_string + "\n", ""))
