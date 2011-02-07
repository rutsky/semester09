import graph;

// TODO: Draw O point.

void draw_graph(string data_file_name, string data_label, string graph_label)
{
  size(600, 400, IgnoreAspect);

  file in = input(data_file_name).line().csv();

  real[][] a = in.dimension(0, 0);
  a = transpose(a);

  real[] npoints = a[0];
  real[] val = a[1];

  draw(graph(npoints, val), blue);

  xaxis("Number Of Points", Bottom, LeftTicks);
  yaxis(data_label, Left, RightTicks);

  label(shift(5mm * N) * graph_label, point(N), E);
}
