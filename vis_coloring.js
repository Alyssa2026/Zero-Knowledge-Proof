function fam(expr) {
  if (!expr.empty()) return expr.tuples()[0].atoms()[0];
  return "none";
}

const stage = new Stage();
const RAD = 150;
const NODE_RAD = 22;
const CEN_X = 300;
const CEN_Y = 300;

const nodes = Node.atoms().map((ltup) => fam(ltup));
const num_nodes = nodes.length;
const degrees = 360 / num_nodes;
var poses = [];

nodes.forEach((nodeVal, nodeIdx) => {
  var node_deg = (nodeIdx * degrees * Math.PI) / 180;
  var pos_x = Math.cos(node_deg) * RAD + CEN_X;
  var pos_y = Math.sin(node_deg) * RAD + CEN_Y;
  poses.push([pos_x, pos_y]);
});

nodes.forEach((nodeVal, nodeIdx) => {
  var pos_x = poses[nodeIdx][0];
  var pos_y = poses[nodeIdx][1];
  var indexed_nbrs = nodeVal.neighbors.tuples().map((ltup) => fam(ltup));

  // Create the lines connecting to neighbors
  indexed_nbrs.forEach((nbr, idx) => {
    var nbr_num = nbr.toString().replace(/[^0-9]/g, "");
    start_coords = { x: poses[nodeIdx][0], y: poses[nodeIdx][1] };
    end_coords = { x: poses[nbr_num][0], y: poses[nbr_num][1] };
    var line = new Line({ points: [start_coords, end_coords] });
    stage.add(line);
  });

  // Create the circle and label
  var circle = new TextBox({
    text: "●",
    color: nodeVal.color.toString().replace(/[^a-zA-Z]/g, ""),
    coords: { x: pos_x, y: pos_y },
    fontSize: 150,
    fontWeight: "bold",
  });
  var label = new TextBox({
    text: nodeIdx,
    coords: { x: pos_x, y: pos_y + 10 },
    fontSize: 25,
    fontWeight: "bold",
  });
  stage.add(circle);
  stage.add(label);
});

stage.render(svg);
