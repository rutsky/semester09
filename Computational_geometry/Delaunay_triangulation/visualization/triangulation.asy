import graph;

// TODO: Don't draw duplicate points.

void draw_triangulation(string points_file_name, string triangles_file_name)
{
  size(800, 800);
  
  // Read points.
  file points_in = input(points_file_name);
  real[][] points = points_in.dimension(0, 2);
  
  // Read triangles.
  file triangles_in = input(triangles_file_name).line();
  int[][] triangles = (int[][])triangles_in.dimension(0, 3);
  
  // Draw triangles.
  for (int[] tr : triangles)
  {
    pair p0 = (points[tr[0]][0], points[tr[0]][1]);
    pair p1 = (points[tr[1]][0], points[tr[1]][1]);
    pair p2 = (points[tr[2]][0], points[tr[2]][1]);
    
    draw(p0--p1--p2--cycle);
  }
  
  // Draw points.
  int idx = 0;
  for (real[] p : points)
  {
    pair v = (p[0], p[1]);
  
    dot(v, red);
    label(string(idx) + " (" + string(p[0]) + "," + string(p[1]) + ")", 
        v, E, red);
    
    idx += 1;
  }
}
