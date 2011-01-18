from "draw_graph.asy" access draw_graph;

draw_graph("../src/data_loss.csv", "Loss probability");

/*
import graph;

void draw_graph(string data_file_name, string ch_label)
{
  size(200, 150, IgnoreAspect);

  file in = input(data_file_name).line().csv();

  real[][] a = in.dimension(0, 0);
  a = transpose(a);

  real[] ch_var = a[0];
  real[] time = a[1];
  real[] frame_count = a[2];

  draw(graph(ch_var, time), blue, "Time");

  xaxis(ch_label, BottomTop, LeftTicks);
  yaxis(Left, blue, RightTicks);

  picture secondary = secondaryY(new void(picture pic) {
      scale(pic, Log(true), Linear(true));
      draw(pic, graph(pic, ch_var, frame_count), red, "Frames");
    yaxis(pic, Right, red, LeftTicks(begin=false, end=false));
  });

  add(secondary);

  attach(legend(), truepoint(E), 20E, UnFill);
}

draw_graph("../src/data_loss.csv", "Loss probability");
*/