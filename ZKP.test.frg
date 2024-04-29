#lang forge/temporal

open "three-color-graph.frg"

// Creating valid graphs tests

// Positive predicates
// There are no self loops
pred noSelfLoops{
    all n1,n2:Node|{
         n1 = n2 implies (n1 not in n2.neighbors and n2 not in n1.neighbors)
    }
}
// A node can reach another node (connectivity)
pred everyNodeReaches{
    all disj n1, n2: Node | {
        // ensures connectivity
        n1->n2 in ^neighbors
    } 
}
// Node A reaching node B means node B reaches node A (symmetric)
pred everyNodeSymmetric{
    all disj n1, n2: Node | {
        // connection is symmetric 
        n1 in n2.neighbors iff n2 in n1.neighbors 
    } 
}
// Node A reaching node B and node B reaching node C means node A reaches node C (transitive)
pred nodeTransitive{
    all disj n1, n2, n3: Node | {
        // connection is transitive
        n1 in n2.neighbors and n2 in n3.neighbors implies  n1->n3 in ^neighbors
    } 
}
// An empty graph is valid 
pred emptyGraph{
    all n:Node|{
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
pred selfLoop{
    some n1:Node|{
        n1 in n1.neighbors
    }
}
// A graph that is not fully connected in invalid 
pred cantReach{
    some disj n1,n2:Node|{
        not n1->n2 in ^neighbors
    }
}
// A graph where there is no symmetric relationship
pred notSymmetric{
    some n1,n2:Node|{
        n1 in n2.neighbors 
        n2 not in n1.neighbors
    }
}
test suite for validGraph{
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
        emptyGraphValid:{emptyGraph and validGraph} is sat
        // A graph where every node is a neighbor with another node is valid 
        fullConnectedIsValid:{validGraph and fullyConnectedValid} is sat
    }

    // Negative tests
    test expect{
        // Having self loops is not valid
        selfLoopInvalie:{selfLoop and validGraph} is unsat
        // A node that can not reach another node is not valid
        UnreachableInvalid:{validGraph and cantReach} is unsat
        // A node that is not symmetric is not valid
        notSymmetricInvalid:{validGraph and notSymmetric} is unsat
    }

}





// invalid --> Khalil