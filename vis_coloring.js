function fam(expr) {
  if (!expr.empty()) return expr.tuples()[0].atoms()[0];
  return "none";
}

var current_state = 0;

function cs_turn() {
  return `Current Turn: ${instances[current_state]
    .atom("ProofState0")
    .turn.toString()
    .replace("]", "")
    .replace(/[^a-zA-Z]/g, "")}`;
}
function cs_color(node) {
  var node = instances[current_state].atom(node);
  var covered = node.hat.toString() == "Hat0";
  if (covered) {
    return "black";
  } else {
    return node.color.toString().replace(/[^a-zA-Z]/g, "");
  }
}
function cs_str() {
  return `Current State: ${current_state}`;
}
function cs_line_color(ndA, ndB) {
  var ndAString = "Node" + ndA;
  var ndBString = "Node" + ndB;
  var nodeA = instances[current_state].atom(ndAString);
  var nodeB = instances[current_state].atom(ndBString);
  var nodeACovered = nodeA.hat.toString() == "Hat0";
  var nodeBCovered = nodeB.hat.toString() == "Hat0";
  if (
    instances[current_state].atom("ProofState0").turn.toString() == "Prover0"
  ) {
    return "black";
  } else if (!nodeACovered && !nodeBCovered) {
    return "gray";
  }
  return "black";
}

const stage = new Stage();
const RAD = 150;
const NODE_RAD = 22;
const CEN_X = 300;
const CEN_Y = 250;

function incrementState() {
  var last_state = instances.length - 1;
  if (current_state < last_state) {
    current_state += 1;
  }
  stage.render(svg);
}

function decrementState() {
  if (current_state != 0) {
    current_state -= 1;
  }
  stage.render(svg);
}

// TURN LABEL
var turn_label = new TextBox({
  text: () => cs_turn(),
  coords: { x: 300, y: 475 },
  fontSize: 20,
  fontWeight: "Bold",
  color: "black",
});
stage.add(turn_label);

// STATE LABEL
var state_label = new TextBox({
  text: () => cs_str(),
  coords: { x: 300, y: 510 },
  fontSize: 20,
  fontWeight: "Bold",
  color: "black",
});
stage.add(state_label);

// PREV BUTTON
var prev_button = new TextBox({
  text: "▬",
  color: "gray",
  coords: { x: 225, y: 550 },
  fontSize: 200,
  events: [
    {
      event: "click",
      callback: function (ele, ev, d) {
        decrementState();
      },
    },
  ],
});
stage.add(prev_button);

var prev_button_label = new TextBox({
  text: "Previous State",
  coords: { x: 225, y: 570 },
  fontSize: 15,
  fontWeight: "Bold",
  color: "white",
  events: [
    {
      event: "click",
      callback: function (ele, ev, d) {
        decrementState();
      },
    },
  ],
});
stage.add(prev_button_label);

// NEXT BUTTON
var next_button = new TextBox({
  text: "▬",
  color: "gray",
  coords: { x: 375, y: 550 },
  fontSize: 200,
  events: [
    {
      event: "click",
      callback: function (ele, ev, d) {
        incrementState();
      },
    },
  ],
});
stage.add(next_button);

var next_button_label = new TextBox({
  text: "Next State",
  coords: { x: 375, y: 570 },
  fontSize: 15,
  fontWeight: "Bold",
  color: "white",
  events: [
    {
      event: "click",
      callback: function (ele, ev, d) {
        incrementState();
      },
    },
  ],
});
stage.add(next_button_label);

const nodes = Node.atoms().map((ltup) => fam(ltup));
const num_nodes = nodes.length;
const degrees = 360 / num_nodes;
var poses = [];

// Get a list of all positions of nodes
nodes.forEach((nodeVal, nodeIdx) => {
  var node_deg = (nodeIdx * degrees * Math.PI) / 180;
  var pos_x = Math.cos(node_deg) * RAD + CEN_X;
  var pos_y = Math.sin(node_deg) * RAD + CEN_Y;
  poses.push([pos_x, pos_y]);
});

// Add all lines
nodes.forEach((nodeVal, nodeIdx) => {
  var indexed_nbrs = nodeVal.neighbors.tuples().map((ltup) => fam(ltup));

  // Create the lines connecting to neighbors
  indexed_nbrs.forEach((nbr, idx) => {
    var nbr_num = nbr.toString().replace(/[^0-9]/g, "");
    start_coords = { x: poses[nodeIdx][0], y: poses[nodeIdx][1] };
    end_coords = { x: poses[nbr_num][0], y: poses[nbr_num][1] };
    var line = new Line({
      points: [start_coords, end_coords],
      color: () => cs_line_color(nodeIdx, nbr_num),
      width: 10,
    });
    stage.add(line);
  });
});

// Add all nodes
nodes.forEach((nodeVal, nodeIdx) => {
  var pos_x = poses[nodeIdx][0];
  var pos_y = poses[nodeIdx][1];
  var indexed_nbrs = nodeVal.neighbors.tuples().map((ltup) => fam(ltup));
  var node_name = nodeVal.toString().replace("[", "");

  // Create the circle and label
  var circle = new TextBox({
    text: "●",
    //color: nodeVal.color.toString().replace(/[^a-zA-Z]/g, ""),
    color: () => cs_color(node_name),
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
