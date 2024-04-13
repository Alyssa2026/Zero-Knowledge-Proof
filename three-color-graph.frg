#lang forge/temporal

option max_tracelength 10
option min_tracelength 10

---------- Definitions ----------
// Color of the Node 
abstract sig Color{}
one sig colorOne extends Color{}
one sig colorTwo extends Color{}
one sig colorThree extends Color{}

// Nodes in a graph
sig Node{
    // set of nodes that it connects to
    var connectedNodes: set Node,
    // Each node has one color 
    var color: one Color
}

// Create a valid graph 
pred connected{
    all n1, n2: Node | {
        n1 != n2 => (n1 in n2.nodes or n2 in n1.nodes)
    }
}
pred validGraph{
    // Connection is symmetric 
    all disj n1, n2: Node |{
        n1 in n2.connectedNodes implies n2 in n1.connectedNodes 
    } 
    // Connected: all vertices reachable from other vertices
    // all node:Node|{
    //     all disj
    // }
    // Ensure number of nodes ?
}
// Run statement for testing
run {
    validGraph
} for exactly 3 Node


