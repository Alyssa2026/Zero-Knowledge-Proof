#lang forge/temporal

open "three-color-graph.frg"

// Creating valid graphs tests

// Positive predicates
// There are no self loops
pred noSelfLoops {
    all n1, n2 : Node | {
         n1 = n2 implies (n1 not in n2.neighbors and n2 not in n1.neighbors)
    }
}

// A node can reach another node (connectivity)
pred everyNodeReaches {
    all disj n1, n2 : Node | {
        // ensures connectivity
        n1->n2 in ^neighbors
    } 
}

// Node A reaching node B means node B reaches node A (symmetric)
pred everyNodeSymmetric {
    all disj n1, n2 : Node | {
        // connection is symmetric 
        n1 in n2.neighbors iff n2 in n1.neighbors 
    } 
}

// Node A reaching node B and node B reaching node C means node A reaches node C (transitive)
pred nodeTransitive {
    all disj n1, n2, n3 : Node | {
        // connection is transitive
        n1 in n2.neighbors and n2 in n3.neighbors implies  n1->n3 in ^neighbors
    } 
}

// An empty graph is valid 
pred emptyGraph {
    all n : Node | { 
        n = none
    }
}
// A full connected graph is valid 
pred fullyConnectedValid {
    all n1, n2: Node | {
        n1->n2 in ^neighbors
    }   
}

// Negative predicates
// A graph with a self loop in invalid 
pred selfLoop {
    some n1 : Node | {
        n1 in n1.neighbors
    }
}

// A graph that is not fully connected in invalid 
pred cantReach {
    some disj n1, n2 : Node | {
        not n1->n2 in ^neighbors
    }
}

// A graph where there is no symmetric relationship
pred notSymmetric {
    some n1, n2 : Node | {
        n1 in n2.neighbors 
        n2 not in n1.neighbors
    }
}

test suite for validGraph {
    // Positive tests 
    // There are no self loops within the valid graph
    assert noSelfLoops is necessary for validGraph
    assert validGraph is sufficient for noSelfLoops
    // Every node can reach every other node
    assert everyNodeReaches is necessary for validGraph
    assert validGraph is sufficient for everyNodeReaches
    // Every node is symmetrically reachable 
    assert everyNodeSymmetric is necessary for validGraph
    assert validGraph is sufficient for everyNodeSymmetric
    // Every node has transitive relationship 
    assert nodeTransitive is necessary for validGraph
    assert validGraph is sufficient for nodeTransitive

    test expect{
        // It is valid to have an empty graph
        emptyGraphValid : {emptyGraph and validGraph} is sat
        // A graph where every node is a neighbor with another node is valid 
        fullConnectedIsValid : {validGraph and fullyConnectedValid} is sat
    }

    // Negative tests
    test expect{
        // Having self loops is not valid
        selfLoopInvalie : {selfLoop and validGraph} is unsat
        // A node that can not reach another node is not valid
        UnreachableInvalid : {validGraph and cantReach} is unsat
        // A node that is not symmetric is not valid
        notSymmetricInvalid : {validGraph and notSymmetric} is unsat
    }
}

// Tests for creating valid three color graph

// Positive predicates 
// All neighboring colors must be different
pred colorDiff {
    all n1, n2 : Node | {
        n1 in n2.neighbors implies {
            n2.color != n1.color
        }
    }
}

// Negative predicates 
pred sharingColor {
    some disj n1, n2 : Node | {
        n1 in n2.neighbors
        n2 in n1.neighbors
        n1.color = n2.color
    }
}

test suite for validThreeColor {
    // Positive tests
    // All neighboring colors must be different
    assert colorDiff is necessary for validThreeColor
    assert validThreeColor is sufficient for colorDiff

    test expect {
        // An empty three color is valid 
        emptyThreeColorGraphValid:{emptyGraph and validThreeColor} is sat
    }

    // Negative test
    test expect {
        // neighbors sharing color is invalid
        sharingColorInvalid: {validThreeColor and sharingColor } is unsat
    }
}

// Tests the moves when the prover is telling the truth 

// Positive predicates 
// The graph colors must be "permuted"
pred permutateGraph {
     all c1 : Color {
        one c2 : Color | {
            all node : Node | {
                // NOTE: c1 and c2 can be the same
                node.color = c1 implies node.color' = c2
            }
        }
    }
    all disj n1, n2 : Node | {
        all disj c1, c2 : Color | n1.color = c1 and n2.color = c2 implies {
            n1.color' != n2.color'
        }
    }
}
// Verifier must choose a random edge
pred chooseRandomEdge {
    some disj n1, n2 : Node | {
        n1 in n2.neighbors and n2 in n1.neighbors
        
        // selected edge in verifier turn
        n1 = ProofState.nodeA
        n2 = ProofState.nodeB

        // we uncover the nodes
        n1.hat = none
        n2.hat = none
        all node : Node | {
            (node != n1 and node != n2) implies node.hat = Hat
        }
    }
}

// The graph does not have to change next state
pred sameGraphValid {
     all n1 : Node | {
        n1.color' = n1.color
    }
}

// The graph colors can change next state
pred notSameGraphValid {
    all n1, n2 : Node | {
       n1.color' != n1.color
    }
}

// The edge picked has neighboring ndoes
pred pickRandomEdge {
    validGraph
    validThreeColor
    some n1, n2 : Node | {
        n1 = ProofState.nodeA and  n2 = ProofState.nodeA implies n2 in n1.neighbors and n1 in n2.neighbors
    }
}

// Negative predicates 
// The graph permutation is invalid 
pred invalidPermutation {
   some n1 : Node | {
        #{n1.color} != #{n1.color'}
    }
}

test suite for verifierToProver {
    // Positive tests
    // The graph must be permutated
    assert permutateGraph is necessary for verifierToProver
    assert verifierToProver is sufficient for permutateGraph
    
    // verifier must select randome edge 
    assert chooseRandomEdge is necessary for verifierToProver
    assert verifierToProver is sufficient for chooseRandomEdge

    test expect {
        // the graph after permutation can be the same
        graphNotChangedValid:{sameGraphValid and verifierToProver} is sat
        // the graph after permutation can NOT be the same
        graphChangedValid:{notSameGraphValid and verifierToProver} is sat
        // The edge selected implies teh two edges are nieghbords
        EdgeNeighborNdde:{pickRandomEdge and verifierToProver} is sat
    }

    // Negative 
    test expect {
        // The graph permutation is invalid 
        permutationIsInvalid : {invalidPermutation and verifierToProver} is unsat
    }
}

// no edge is selected in proof state
pred noSelectedEdge {
    ProofState.nodeA = none
    ProofState.nodeB = none
}

test suite for proverToVerifier {
    // assert tests
    assert proverToVerifier is sufficient for noSelectedEdge


}
