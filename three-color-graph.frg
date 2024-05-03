#lang forge/temporal

option run_sterling "vis_coloring.js"

// We constrain for this example to m = 5 edges.
// We must have m^2 trials, so 25 trials. Each trial spans two states, so we
// must have traces of length 25*2 = 50. 
option max_tracelength 50
option min_tracelength 50

-----------------------------------------------------------
---------------------- SIGNATURES -------------------------
-----------------------------------------------------------

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

-----------------------------------------------------------
------------------ GENERAL PREDICATES ---------------------
-----------------------------------------------------------

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

pred init {
    ProofState.turn = Prover
}

-----------------------------------------------------------
-------------- PREDICATES FOR HONEST PROVER ---------------
-----------------------------------------------------------

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

-----------------------------------------------------------
------------ PREDICATES FOR DISHONEST PROVER --------------
-----------------------------------------------------------

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

// For our examples, we are constraining to 5 edges so that we can hard-code
// the tracelength as 50 (5^2 = 25, 25 * 2 = 50 because in each trial, of which
// we must have edges^2, there are two states, the prover and verifier).
pred fiveEdges{
    // Neighbor relation goes both ways, and 5 * 2 = 10
    #{n1, n2: Node | n2 in n1.neighbors} = 10
}

-----------------------------------------------------------
------------------------- RUN! ----------------------------
-----------------------------------------------------------

// run statement for testing
run {
    fiveEdges
    // validTraces
    invalidTraces
    always passesChallenge
} for exactly 6 Node, 6 Int

-----------------------------------------------------------
------------- INTERESTING PROPERTIES OF ZKPS --------------
-----------------------------------------------------------

pred passesChallenge {
    (no ProofState.nodeA and no ProofState.nodeB) or
    ProofState.nodeA.color != ProofState.nodeB.color
}

pred failsChallenge {
    some ProofState.nodeA.color and some ProofState.nodeB.color
    ProofState.nodeA.color = ProofState.nodeB.color
}

// Proves some interesting properties we expect of our proof system
test expect {
    // Proving unsoundness:
    // It is possible that a dishonest prover will always pass the verifier's challenges
    notSound: {
        invalidTraces
        always passesChallenge
    } is sat

    // Demonstrating that being caught is possible
    canBeSound: {
        invalidTraces
        eventually failsChallenge
    } is sat

    // Proving completeness:
    // An honest prover will always pass the verifier's challenges and convince the verifier
    complete: {
        validTraces implies always passesChallenge
    } is theorem
}