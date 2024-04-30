#lang forge/temporal

option run_sterling "vis_coloring.js"

option max_tracelength 32
option min_tracelength 32

---------- Definitions ----------
// color of the Node 
abstract sig Color {}
one sig Red extends Color {}
one sig Green extends Color {}
one sig Blue extends Color {}

one sig Hat{}

// nodes in the graph
sig Node {
    // set of nodes that it connects to
    neighbors : set Node,

    // each node has one color 
    var color: one Color,

    // visibility field
    var hat : lone Hat
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

pred verifierToProver {
    // current state: verifier
    // next state: prover

    // permute the nodes' colors
    all c1 : Color {
        one c2 : Color | {
            all node: Node | {
                // NOTE: c1 and c2 can be the same
                node.color = c1 implies node.color' = c2
            }
        }
    }

    
    // choose random edge 
    some disj n1, n2 : Node | {
        n1 in n2.neighbors and n2 in n1.neighbors
        
        // selected edge in verifier turn
        n1 = ProofState.nodeA
        n2 = ProofState.nodeB

        // we uncover the
        n1.hat = none
        n2.hat = none
        all node : Node | {
            (node != n1 and node != n2) implies node.hat = Hat
        }
    }

    // maintain injectivity (better? - Khalil)
    all disj n1, n2 : Node | {
        all disj c1, c2 : Color | n1.color = c1 and n2.color = c2 implies {
            n1.color' != n2.color'
        }
    }
}

pred proverToVerifier {
    // current state: prover
    // next state: verifier

    ProofState.nodeA = none
    ProofState.nodeB = none

    // frame condition: all nodes have to stay the same color
    all node: Node | {
        node.color = node.color'
        node.hat = none
    }

}

pred init {
    ProofState.turn = Prover
}


pred move {
    ProofState.turn = Prover implies ProofState.turn' = Verifier
    ProofState.turn = Verifier implies ProofState.turn' = Prover

    ProofState.turn = Prover implies proverToVerifier 
    ProofState.turn = Verifier implies verifierToProver
}

pred validTraces {
    init
    validGraph
    validThreeColor
    always move
}

// INVALID 

pred verifierToProverInvalid {
    // current state: verifier
    // next state: prover

    // permute the nodes' colors however the prover wants (SO NO RULE FOR THIS)
    
    // choose random edge 
    some disj n1, n2 : Node | {
        n1 in n2.neighbors and n2 in n1.neighbors
        
        // selected edge in verifier turn
        n1 = ProofState.nodeA
        n2 = ProofState.nodeB

        // we uncover the
        n1.hat = none
        n2.hat = none
        all node : Node | {
            (node != n1 and node != n2) implies node.hat = Hat
        }
    }

    // maintain injectivity (better? - Khalil)
    all disj n1, n2 : Node | {
        all disj c1, c2 : Color | {
            n1.color = c1 and n2.color = c2 implies {
                n1.color' != n2.color'
            }
        }
    }
}

pred moveInvalid {
    ProofState.turn = Prover implies ProofState.turn' = Verifier
    ProofState.turn = Verifier implies ProofState.turn' = Prover

    ProofState.turn = Prover implies proverToVerifier 
    ProofState.turn = Verifier implies verifierToProverInvalid
}

pred invalidTraces{
    init
    validGraph
    not validThreeColor
    always moveInvalid
}

// run statement for testing
run {
    validTraces
    //invalidTraces
    //always passesChallenge
} for exactly 6 Node

pred passesChallenge {
    (no ProofState.nodeA and no ProofState.nodeB) or
    ProofState.nodeA.color != ProofState.nodeB.color
}

pred failsChallenge {
    some ProofState.nodeA.color and some ProofState.nodeB.color
    ProofState.nodeA.color = ProofState.nodeB.color
}

test expect {
    notSound: {
        invalidTraces
        always passesChallenge
    } is sat

    canBeSound: {
        invalidTraces
        eventually failsChallenge
    } is sat

    complete: {
        validTraces implies always passesChallenge
    } is theorem
}