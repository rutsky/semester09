import graph;

size(200, 150, IgnoreAspect);

string file_name="../src/data_wsize.csv";

file in = input(file_name).line().csv();

real[][] a = in.dimension(0, 0);
a = transpose(a);

real[] wsize = a[0];
real[] time = a[1];
real[] frame_count = a[2];

draw(graph(wsize, time), blue, "Time");

xaxis("Window size", BottomTop, LeftTicks);
yaxis(Left, blue, RightTicks);

picture secondary=secondaryY(new void(picture pic) {
    scale(pic, Linear(true), Linear(true));
    draw(pic, graph(pic,wsize, frame_count), red, "Frames");
    yaxis(pic, Right, red, LeftTicks(begin=false, end=false));
  });

add(secondary);

attach(legend(),truepoint(E),20E,UnFill);
