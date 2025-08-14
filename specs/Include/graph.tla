---- MODULE graph ----
EXTENDS TLC, Integers, FiniteSets, Sequences, dag


\* `TRUE` if `edgeSet` is a set of pairs, each element in `nodeSet`
IsSetOfEdges(edgeSet, nodeSet) == edgeSet \in SUBSET (nodeSet \X nodeSet)

\* Get set of nodes that have incoming edges from a given node
OutgoingEdges(node, edgeSet) == {e \in edgeSet: e[1] = node}

\* Get set of nodes that we can hop to from end of a path without creating a cycle
PathNextHops(path, nodeSet, edgeSet) == {n \in nodeSet: /\ <<path[Len(path)], n>> \in edgeSet
                                                        /\ ~\E x \in DOMAIN path: path[x] = n}

\* Extend an existing path without creating a cycle
RECURSIVE _ExtendPath(_, _, _)
_ExtendPath(path, nextHops, newPaths) ==
    IF Cardinality(nextHops) = 0
        THEN newPaths
        ELSE LET nextHop == CHOOSE x \in nextHops: TRUE
             IN _ExtendPath(path, nextHops \ {nextHop}, newPaths \cup {path \o <<nextHop>>})
ExtendPath(path, nodeSet, edgeSet) ==
    LET nextHops == PathNextHops(path, nodeSet, edgeSet)
    IN _ExtendPath(path, nextHops, {})

\* Extend a set of existing paths of the same length without creating a cycle
RECURSIVE _NextLengthPaths(_, _, _, _)
_NextLengthPaths(paths, nodeSet, edgeSet, nextPaths) ==
    IF Cardinality(paths) = 0
        THEN nextPaths
        ELSE LET currentPath == CHOOSE path \in paths: TRUE
             IN _NextLengthPaths(paths \ {currentPath}, nodeSet, edgeSet, nextPaths \cup ExtendPath(currentPath, nodeSet, edgeSet))
NextLengthPaths(paths, nodeSet, edgeSet) == _NextLengthPaths(paths, nodeSet, edgeSet, {})
    
\* Get set of shortest paths between a `start` and `finish` node in a graph over set of
\* nodes `nodeSet` with edge set `edgeSet`.
\* Another operator returns paths between any two members of a given set
RECURSIVE _ShortestPathsBetween(_, _, _, _, _)
_ShortestPathsBetween(start, finish, nodeSet, edgeSet, paths) ==
    LET completedPaths == {p \in paths: p[Len(p)] = finish}
    IN IF Cardinality(completedPaths) > 0
        THEN completedPaths
        ELSE LET nextPaths == NextLengthPaths(paths, nodeSet, edgeSet)
             IN _ShortestPathsBetween(start, finish, nodeSet, edgeSet, nextPaths)
ShortestPathsBetween(start, finish, nodeSet, edgeSet) ==
    LET lengthOnePaths == OutgoingEdges(start, edgeSet)
    IN _ShortestPathsBetween(start, finish, nodeSet, edgeSet, lengthOnePaths)

RECURSIVE _ShortestPathsFrom(_, _, _, _, _)
_ShortestPathsFrom(start, finishSet, nodeSet, edgeSet, paths) ==
    IF Cardinality(finishSet) = 0
        THEN paths
        ELSE LET 
                currentFinish == CHOOSE x \in finishSet: TRUE
                currentPathsToFinish == ShortestPathsBetween(start, currentFinish, nodeSet, edgeSet)
             IN _ShortestPathsFrom(start, finishSet \ {currentFinish}, nodeSet, edgeSet, paths \cup currentPathsToFinish)
ShortestPathsFrom(start, finishSet, nodeSet, edgeSet) ==
    _ShortestPathsFrom(start, finishSet \ {start}, nodeSet, edgeSet, {})

RECURSIVE _ShortestPaths(_, _, _, _, _)
_ShortestPaths(startSet, finishSet, nodeSet, edgeSet, paths) ==
    IF Cardinality(startSet) = 0
        THEN paths
        ELSE LET 
                currentStart == CHOOSE x \in startSet: TRUE
                currentPaths == ShortestPathsFrom(currentStart, finishSet, nodeSet, edgeSet)
             IN _ShortestPaths(startSet \ {currentStart}, finishSet, nodeSet, edgeSet, paths \cup currentPaths)
ShortestPaths(endpoints, nodeSet, edgeSet) == 
    _ShortestPaths(endpoints, endpoints, nodeSet, edgeSet, {})

\* Given a set of edges, pick only edges that never cross a particular node, as if
\* they belong to a graph that does not have that node.
RemoveNodeFromEdgeSet(nodeToRemove, edgeSet) == {e \in edgeSet: /\ e[1] # nodeToRemove
                                                                /\ e[2] # nodeToRemove}
RECURSIVE RemoveNodesFromGraph(_, _)
RemoveNodesFromGraph(nodeSetToRemove, edgeSet) ==
    IF Cardinality(nodeSetToRemove) = 0
        THEN edgeSet
        ELSE LET currentNode == CHOOSE x \in nodeSetToRemove: TRUE
             IN RemoveNodesFromGraph(nodeSetToRemove \ {currentNode}, RemoveNodeFromEdgeSet(currentNode, edgeSet))

\* Generate IRs for the current path (or set of paths) at a given priority
\* while also creating a reversed chain for the DAG.
\* It traverses the paths in _reverse_ order to build the DAG concurrently.
RECURSIVE _GeneratePathIRs(_, _, _, _, _, _, _) 
_GeneratePathIRs(path, startingIR, index, priority, irSet, edgeSet, nodeSet) ==
    IF index = Cardinality(DOMAIN path)
        THEN [irs |-> irSet, edges |-> edgeSet, nodes |-> nodeSet]
        ELSE LET 
                newIRIndex == startingIR + index
                pathIndex == Len(path) - index + 1
                newIRObject == [sw |-> path[pathIndex], ir |-> newIRIndex, priority |-> priority]
                newDagEdge == IF index = 1
                                THEN <<>>
                                ELSE <<newIRIndex-1, newIRIndex>>
             IN IF Len(newDagEdge) = 0
                    THEN
                        _GeneratePathIRs(
                                path, startingIR, index+1, priority, 
                                irSet \cup {newIRObject}, 
                                edgeSet, 
                                nodeSet \cup {newIRIndex})
                    ELSE
                        _GeneratePathIRs(
                                path, startingIR, index+1, priority, 
                                irSet \cup {newIRObject}, 
                                edgeSet \cup {newDagEdge},
                                nodeSet \cup {newIRIndex})
GeneratePathIRs(path, startingIR, priority) == _GeneratePathIRs(path, startingIR, 1, priority, {}, {}, {})

RECURSIVE _GeneratePathSetIRs(_, _, _, _, _, _)
_GeneratePathSetIRs(pathSet, startingIR, priority, irSet, edgeSet, nodeSet) ==
    IF Cardinality(pathSet) = 0
        THEN [irs |-> irSet, edges |-> edgeSet, nodes |-> nodeSet]
        ELSE LET 
                nextPath == CHOOSE x \in pathSet: TRUE
                nextPathIRsAndDAG == GeneratePathIRs(nextPath, startingIR, priority)
             IN _GeneratePathSetIRs(
                    pathSet \ {nextPath}, 
                    startingIR + Cardinality(nextPathIRsAndDAG.irs), 
                    priority, 
                    irSet \cup nextPathIRsAndDAG.irs, 
                    edgeSet \cup nextPathIRsAndDAG.edges,
                    nodeSet \cup nextPathIRsAndDAG.nodes)
GeneratePathSetIRs(pathSet, startingIR, priority) == _GeneratePathSetIRs(pathSet, startingIR, priority, {}, {}, {})

\* A swiss knife operator that generates everything the drain application needs to know
GenerateDrainApplicationData(NodeSet, EdgeSet, NodeToDrain, Endpoints) ==
    LET 
        drainedNodeSet == NodeSet \ {NodeToDrain}
        drainedEdgeSet == RemoveNodeFromEdgeSet(NodeToDrain, EdgeSet)
        originalPaths == ShortestPaths(Endpoints, NodeSet, EdgeSet)
        drainedPaths == ShortestPaths(Endpoints \ {NodeToDrain}, drainedNodeSet, drainedEdgeSet)
        originalIRs == GeneratePathSetIRs(originalPaths, 0, 1)
        numberOfOriginalIRs == Cardinality(originalIRs.nodes)
        drainedIRs == GeneratePathSetIRs(drainedPaths, numberOfOriginalIRs, 10)
    IN
        [
            OriginalPaths |-> originalPaths,
            DrainedPaths |-> drainedPaths,
            OriginalIRs |-> originalIRs,
            DrainedIRs |-> drainedIRs,
            TotalNumberOfIRs |-> (Cardinality(originalIRs.nodes) + Cardinality(drainedIRs.nodes))
        ]

\* Get children/parents of a node
NodeChildren(nodeSet, edgeSet, node) == {n \in (nodeSet \ {node}): <<node, n>> \in edgeSet}
NodeParents(nodeSet, edgeSet, node) == {n \in (nodeSet \ {node}): <<n, node>> \in edgeSet}
\* Get children/parents of a set of nodes
RECURSIVE _NodeSetChildren(_, _, _, _)
_NodeSetChildren(nodeSet, edgeSet, parentSet, childrenSet) ==
    IF Cardinality(parentSet) = 0
        THEN childrenSet
        ELSE LET 
                parent == CHOOSE parent \in parentSet: TRUE
                newChildren == NodeChildren(nodeSet, edgeSet, parent)
                newParentSet == parentSet \ {parent}
             IN _NodeSetChildren(nodeSet, edgeSet, newParentSet, childrenSet \cup newChildren)
NodeSetChildren(nodeSet, edgeSet, parentSet) == _NodeSetChildren(nodeSet, edgeSet, parentSet, {})
RECURSIVE _NodeSetParents(_, _, _, _)
_NodeSetParents(nodeSet, edgeSet, childrenSet, parentSet) ==
    IF Cardinality(childrenSet) = 0
        THEN parentSet
        ELSE LET 
                child == CHOOSE child \in childrenSet: TRUE
                newParents == NodeParents(nodeSet, edgeSet, child)
                newChildrenSet == childrenSet \ {child}
             IN _NodeSetParents(nodeSet, edgeSet, newChildrenSet, parentSet \cup newParents)
NodeSetParents(nodeSet, edgeSet, childrenSet) == _NodeSetParents(nodeSet, edgeSet, childrenSet, {})

\* Get the root(s) of a DAG, the set of all nodes with no parents
GetDAGRoot(nodeSet, edgeSet) == {node \in nodeSet: \A x \in (nodeSet \ {node}): <<x, node>> \notin edgeSet}
\* Get the leaves of a DAG, the set of all nodes with no children
GetDAGLeaves(nodeSet, edgeSet) == {node \in nodeSet: \A x \in (nodeSet \ {node}): <<node, x>> \notin edgeSet}

\* Do BFS on a DAG (useful for abstract core)
RECURSIVE _GetDAGLevels(_, _, _, _, _)
_GetDAGLevels(nodeSet, edgeSet, currentLevel, visited, levels) ==
    LET nextLevel == (NodeSetChildren(nodeSet, edgeSet, currentLevel) \ visited)
    IN IF Cardinality(nextLevel) = 0
        THEN levels
        ELSE _GetDAGLevels(nodeSet, edgeSet, nextLevel, (visited \cup nextLevel), levels \o <<nextLevel>>)
GetDAGLevels(nodeSet, edgeSet) ==
    LET 
        roots == GetDAGRoot(nodeSet, edgeSet)
        levels == <<roots>>
    IN _GetDAGLevels(nodeSet, edgeSet, roots, roots, levels)

\* A utility that adds a whole level to a DAG (i.e. the new nodes will have the whole previous DAG
\* as their dependency)
RECURSIVE AddDependentNodeToDAG(_, _, _)
AddDependentNodeToDAG(dag, leaves, newNode) ==
    IF Cardinality(leaves) = 0
        THEN [v |-> dag.v \cup {newNode}, e |-> dag.e]
        ELSE LET currentLeaf == CHOOSE x \in leaves: TRUE
             IN AddDependentNodeToDAG(
                [v |-> dag.v, e |-> dag.e \cup {<<currentLeaf, newNode>>}], 
                leaves \ {currentLeaf}, 
                newNode)

RECURSIVE _ExpandDAG(_, _, _)
_ExpandDAG(dag, leaves, newNodes) ==
    IF Cardinality(newNodes) = 0
        THEN dag
        ELSE LET currentNode == CHOOSE x \in newNodes: TRUE
             IN _ExpandDAG(AddDependentNodeToDAG(dag, leaves, currentNode), leaves, newNodes \ {currentNode})

ExpandDAG(dag, newNodes) ==
    LET leaves == GetDAGLeaves(dag.v, dag.e)
    IN _ExpandDAG(dag, leaves, newNodes)

RECURSIVE _SetToSeq(_, _)
_SetToSeq(someSet, seq) ==
    IF Cardinality(someSet) = 0
        THEN seq
        ELSE LET currentElement == CHOOSE x \in someSet: TRUE
             IN _SetToSeq(someSet \ {currentElement}, seq \o <<currentElement>>)
SetToSeq(someSet) == _SetToSeq(someSet, <<>>)

RECURSIVE _BFS(_, _)
_BFS(levels, list) ==
    IF Len(levels) = 0
        THEN list
        ELSE _BFS(Tail(levels), list \o <<SetToSeq(Head(levels))>>)
DAGBFS(nodeSet, edgeSet) == 
    LET levels == GetDAGLevels(nodeSet, edgeSet)
    IN _BFS(levels, <<>>)

\* Creates a mapping from nodeSet to the set of parents for each node
RECURSIVE _GetParents(_, _, _, _)
_GetParents(nodeSet, edgeSet, nodesLeft, mapping) ==
    IF Cardinality(nodesLeft) = 0
        THEN mapping
        ELSE LET 
                currentNode == CHOOSE node \in nodesLeft: TRUE
                currentParents == NodeParents(nodeSet, edgeSet, currentNode)
             IN _GetParents(nodeSet, edgeSet, nodesLeft \ {currentNode}, mapping @@ (currentNode :> currentParents))
RECURSIVE _InitialParentMap(_, _)
_InitialParentMap(roots, mapping) ==
    IF Cardinality(roots) = 0
        THEN mapping
        ELSE LET currentRoot == CHOOSE root \in roots: TRUE
             IN _InitialParentMap(roots \ {currentRoot}, mapping @@ (currentRoot :> {}))
InitialParentMap(roots) ==
    LET firstRoot == CHOOSE root \in roots: TRUE
    IN _InitialParentMap(roots \ {firstRoot}, (firstRoot :> {}))
GetParents(nodeSet, edgeSet) ==
    LET roots == GetDAGRoot(nodeSet, edgeSet)
    IN _GetParents(nodeSet, edgeSet, nodeSet \ roots, InitialParentMap(roots))

GetSetOfScheduleableNodes(satisfiedNodes, parentMap) ==
    {node \in DOMAIN parentMap: parentMap[node] \subseteq satisfiedNodes}

RECURSIVE _GetDAGScheduleLevels(_, _, _, _, _)
_GetDAGScheduleLevels(nodeSet, edgeSet, parentMap, satisfiedSet, levels) ==
    IF satisfiedSet = nodeSet
        THEN levels
        ELSE LET nextLevel == GetSetOfScheduleableNodes(satisfiedSet, parentMap) \ satisfiedSet
             IN _GetDAGScheduleLevels(nodeSet, edgeSet, parentMap, satisfiedSet \cup nextLevel, levels \o <<SetToSeq(nextLevel)>>)
GetDAGScheduleLevels(nodeSet, edgeSet) ==
    LET 
        roots == GetDAGRoot(nodeSet, edgeSet)
        parentMap == GetParents(nodeSet, edgeSet)
    IN _GetDAGScheduleLevels(nodeSet, edgeSet, parentMap, roots, <<SetToSeq(roots)>>)

====