#lang forge/temporal

open "ZKP.frg"

-----------------------------------------------------------
--------------- TESTING FULL MODEL BEHAVIOR ---------------
-----------------------------------------------------------

test expect {
    // valid traces are possible
    validTracesCombination : {
        init
        validGraph
        validThreeColor
        always move
    } is sat
    // invalid traces are possible
    invalidTracesCombination : {
        init
        validGraph
        not validThreeColor
        always moveInvalid
    } is sat
    // always passing challenge with five edges is possible
    fiveEdgesValidSat : {
        fiveEdges
        validTraces
        always passesChallenge
    } for 6 Node, 6 Int is sat
    // always passing challenge with valid graph of five edges is theorem
    fiveEdgesValidTheorem : {
        {fiveEdges and validTraces} implies {
            always passesChallenge
        }
    } for 6 Node, 6 Int is theorem
    // always passing challenge with invalid graph of five edges is sat
    fiveEdgesInvalidNotCaught : {
        fiveEdges
        invalidTraces
        always passesChallenge
    } for 6 Node, 6 Int is sat
    // eventually failing challenge with invalid graph of five edges is sat
    fiveEdgesInvalidCaught : {
        fiveEdges
        invalidTraces
        eventually failsChallenge
    } for 6 Node, 6 Int is sat
    // cannot both always pass and eventually fail
    caughtOrNot : {
        always passesChallenge
        eventually failsChallenge
    } is unsat
}

-----------------------------------------------------------
---------- TESTING INDIVIDUAL PREDICATE BEHAVIOR ----------
-----------------------------------------------------------

// valid graph structure testing

// There are no self loops
pred noSelfLoops {
    all n1, n2 : Node | {
         n1 = n2 implies (n1 not in n2.neighbors and n2 not in n1.neighbors)
    }
}

// a node can reach another node (connectivity)
pred everyNodeReaches {
    all disj n1, n2 : Node | {
        // ensures connectivity
        n1->n2 in ^neighbors
    } 
}

// node A reaching node B means node B reaches node A (symmetric)
pred everyNodeSymmetric {
    all disj n1, n2 : Node | {
        // connection is symmetric 
        n1 in n2.neighbors iff n2 in n1.neighbors 
    } 
}

// node A reaching node B and node B reaching node C means node A reaches node C (transitivity)
pred nodeTransitive {
    all disj n1, n2, n3 : Node | {
        // connection is transitive
        n1 in n2.neighbors and n2 in n3.neighbors implies  n1->n3 in ^neighbors
    } 
}

// an empty graph is valid 
pred emptyGraph {
    all n : Node | { 
        n = none
    }
}
// a full connected graph is valid 
pred fullyConnectedValid {
    all n1, n2: Node | {
        n1->n2 in ^neighbors
    }   
}

// negative predicates
// a graph with a self loop in invalid 
pred selfLoop {
    some n1 : Node | {
        n1 in n1.neighbors
    }
}

// a graph that is not fully connected in invalid 
pred cantReach {
    some disj n1, n2 : Node | {
        not n1->n2 in ^neighbors
    }
}

// a graph where there is no symmetric relationship
pred notSymmetric {
    some n1, n2 : Node | {
        n1 in n2.neighbors 
        n2 not in n1.neighbors
    }
}

test suite for validGraph {
    // positive tests 
    // there are no self loops within the valid graph
    assert noSelfLoops is necessary for validGraph
    assert validGraph is sufficient for noSelfLoops
    // every node can reach every other node
    assert everyNodeReaches is necessary for validGraph
    assert validGraph is sufficient for everyNodeReaches
    // every node is symmetrically reachable 
    assert everyNodeSymmetric is necessary for validGraph
    assert validGraph is sufficient for everyNodeSymmetric
    // every node has transitive relationship 
    assert nodeTransitive is necessary for validGraph
    assert validGraph is sufficient for nodeTransitive

    test expect{
        // it is valid to have an empty graph
        emptyGraphValid : {emptyGraph and validGraph} is sat
        // a graph where every node is a neighbor with another node is valid 
        fullConnectedIsValid : {validGraph and fullyConnectedValid} is sat
    }

    // negative tests
    test expect{
        // having self loops is not valid
        selfLoopInvalie : {selfLoop and validGraph} is unsat
        // a node that can not reach another node is not valid
        UnreachableInvalid : {validGraph and cantReach} is unsat
        // a node that is not symmetric is not valid
        notSymmetricInvalid : {validGraph and notSymmetric} is unsat
    }
}

// valid graph 3-coloring testing

// all neighboring colors must be different
pred colorDiff {
    all n1, n2 : Node | {
        n1 in n2.neighbors implies {
            n2.color != n1.color
        }
    }
}

// should be false --- NO two nodes should share colors
pred sharingColor {
    some disj n1, n2 : Node | {
        n1 in n2.neighbors
        n2 in n1.neighbors
        n1.color = n2.color
    }
}

test suite for validThreeColor {
    // positive tests
    // all neighboring colors must be different
    assert colorDiff is necessary for validThreeColor
    assert validThreeColor is sufficient for colorDiff

    test expect {
        // an empty three color is valid 
        emptyThreeColorGraphValid:{emptyGraph and validThreeColor} is sat
    }

    // negative test
    test expect {
        // neighbors sharing color is invalid
        sharingColorInvalid: {validThreeColor and sharingColor } is unsat
    }
}

// tests valid prover behavior

// the graph colors must be "permuted"
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

// verifier must choose a random edge
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

// the graph does not have to change next state
pred sameGraphValid {
     all n1 : Node | {
        n1.color' = n1.color
    }
}

// the graph colors can change next state
pred notSameGraphValid {
    all n1, n2 : Node | {
       n1.color' != n1.color
    }
}

// the edge picked has neighboring ndoes
pred pickRandomEdge {
    validGraph
    validThreeColor
    some n1, n2 : Node | {
        n1 = ProofState.nodeA and  n2 = ProofState.nodeA implies n2 in n1.neighbors and n1 in n2.neighbors
    }
}

// should be false --- the graph permutation should NOT be invalid 
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

// all colors stay the same
pred sameColors {
    all n : Node | {
        n.color = n.color'
    }
}

// all hats are cleared
pred clearedHats {
    all n : Node | {
        n.hat = none
    }
}

test suite for proverToVerifier {
    // asserts
    assert proverToVerifier is sufficient for noSelectedEdge
    assert proverToVerifier is sufficient for sameColors
    assert proverToVerifier is sufficient for clearedHats

    test expect {
        // vacuity test
        proverToVerifierSat : {proverToVerifier} is sat
        // sat with init
        initProverToVerifierSat : {init proverToVerifier} is sat
    }
}

// the game state is never the same twice in a row
pred switching {
    ProofState.turn = Prover implies ProofState.turn' != Prover
}

// Prover state means proverToVerifier
// Verifier state means verifierToProver
pred stateAligns {
    ProofState.turn = Prover implies proverToVerifier
    ProofState.turn = Verifier implies verifierToProver
}

test suite for move {
    // asserts
    assert move is sufficient for switching
    assert move is sufficient for stateAligns

    test expect {
        // vacuity test
        moveIsSat : {move} is sat
        // vacuity in perpetuity
        alwaysMoveIsSat : {init always {move}} is sat
        // there's perpetual switching
        alwaysSwitching : {always {move} implies always {switching}} is theorem
    }
} 

// the prover/verifier take turns every state
pred alwaysMove {
    always {move}
}

test suite for validTraces {
    // asserts
    assert validTraces is sufficient for init
    assert validTraces is sufficient for validGraph
    assert validTraces is sufficient for validThreeColor
    assert validTraces is sufficient for alwaysMove
    
    // individual predicates already tested, expectations for lack of soundness,
    // completeness and more already in main file

    test expect {
        // vacuity
        validTracesIsSat : {validTraces} is sat
    }
}




test suite for verifierToProverInvalid {
        test expect {
        // vacuity 
        verifierToProverInvalidIsSat : {verifierToProverInvalid} is sat
    }
}

// for the invalid case, Prover means proverToVerifier
// Verifier means verifierToProverInvalid
pred stateAlignsInvalid {
    ProofState.turn = Prover implies proverToVerifier
    ProofState.turn = Verifier implies verifierToProverInvalid
}

test suite for moveInvalid {
    // assert testing
    assert moveInvalid is sufficient for switching
    assert moveInvalid is sufficient for stateAlignsInvalid

    test expect {
        // vacuity
        moveInvalidIsSat : {moveInvalid} is sat
        // vacuity in perpetuity
        alwaysMoveInvalidIsSat : {init always {moveInvalid}} is sat
    }
}

// there are some edges in the graph --- i.e. nodes who have each other in neighbors
pred someEdges {
    some n1, n2: Node | {
        n2 in n1.neighbors
        n1 in n2.neighbors
    }
}

// there are exactly 8 pairs (double counting each orientation) who share
// each other in the neighbor relation
pred fourEdges {
     #{n1, n2: Node | n2 in n1.neighbors} = 8
}

test suite for fiveEdges {
    // asserts
    assert fiveEdges is sufficient for someEdges for 6 Int

    test expect {
        // vacuity 
        fiveEdgesTest : {fiveEdges} for 6 Int is sat 
        // vacuity in perpetuity
        alwaysFiveEdges : {init always {fiveEdges}} for 6 Int is sat 
        // cannot be four edges
        notFourEdges : {fourEdges fiveEdges} for 6 Int is unsat
    }
}