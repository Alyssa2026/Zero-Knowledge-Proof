#lang forge/temporal

option max_tracelength 10
option min_tracelength 10

---------- Definitions ----------
// color of the Node 
abstract sig Color {}
one sig Red extends Color {}
one sig Green extends Color {}
one sig Blue extends Color {}

// nodes in the graph
sig Node {
    // set of nodes that it connects to
    neighbors : set Node,

    // each node has one color 
    var color: one Color

    // visibility field
    // lone var hat : Hat
}

// create a valid graph 
pred validGraph {
    all disj n1, n2: Node | {
        // ensures connectivity
        n1->n2 in ^neighbors

        // connection is symmetric 
        n1 in n2.neighbors iff n2 in n1.neighbors 
    } 

    // Don't self loop
    all n1, n2 : Node | {
        n1 = n2=> (n1 not in n2.neighbors and n2 not in n1.neighbors)
    }
}

pred validThreeColor {
    all n1, n2 : Node | {
        n1 in n2.neighbors implies{
            n2.color != n1.color
        }
    }
}

// run statement for testing
run {
    validGraph
    validThreeColor
} for exactly 6 Node


