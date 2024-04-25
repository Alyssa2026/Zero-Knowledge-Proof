#lang forge/temporal
option run_sterling "./vis_coloring.js"

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

abstract sig Participant {}
one sig Prover extends Participant {}
one sig Verifier extends Participant {}

one sig ProofState {
    // tracks current turn
    var turn : one Participant,
    
    // challenged edge
    var nodeA: lone Node,
    var nodeB: lone Node
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
        n1 = n2 implies (n1 not in n2.neighbors and n2 not in n1.neighbors)
    }
}

// enforces proper 3-coloring of a graph
pred validThreeColor {
    all n1, n2 : Node | {
        n1 in n2.neighbors implies {
            n2.color != n1.color
        }
    }
}

pred proverTurn {
    // permute the nodes' colors
    all c1 : Color, node : Node | {
        some c2 : Color | {
            // NOTE: c1 and c2 can be the same
            node.color = c1 implies node.color' = c2
        }
    }

    ProofState.nodeA = none
    ProofState.nodeB = none

    // maintain injectivity (better? - Khalil)
    all disj n1, n2 : Node | {
        all disj c1, c2 : Color | n1.color = c1 and n2.color = c2 implies {
            n1.color' != n2.color'
        }
    }
}

pred verifierTurn {
    // choose random edge 
    some disj n1, n2 : Node | {
        n1 in n2.neighbors and n2 in n1.neighbors
        // Selected edge in verifier turn
        n1 = ProofState.nodeA
        n2 = ProofState.nodeB
    }

    // frame condition: all nodes have to stay the same color
    all node: Node | {
        node.color = node.color'
    }
}

pred init {
    ProofState.turn = Verifier
}

pred move {
    ProofState.turn = Prover implies ProofState.turn' = Verifier
    ProofState.turn = Verifier implies ProofState.turn' = Prover

    ProofState.turn = Prover implies proverTurn 
    ProofState.turn = Verifier implies verifierTurn
}

pred validTraces {
    init
    validGraph
    validThreeColor
    always move
}

// Future 

pred invalidTraces{
    
}

// run statement for testing
run {
    // validGraph
    // validThreeColor
    validTraces
} for exactly 6 Node