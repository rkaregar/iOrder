// This is the class for validating I/I OC candidates.
// This class corresponds to Section 4 in the paper.

package od;

import it.unimi.dsi.fastutil.longs.LongBigArrayBigList;
import it.unimi.dsi.fastutil.objects.ObjectBigArrayBigList;

import java.io.*;
import java.util.*;


public class SOCGeneralCase {
    private List<Map<Long, Long>> TAU_reverseMap;
    private int B_index;
    private int A_index;
    private Map<Long, Set<WeightedEdge>> flakyMap;
    private ObjectBigArrayBigList<ObjectBigArrayBigList<LongBigArrayBigList>> TAU_XA;
    private ObjectBigArrayBigList<ObjectBigArrayBigList<LongBigArrayBigList>> TAU_XB;
    public List<Graph> allBipGraphs;
    public ArrayList<List<Map<Long, Set<Long>>>> allChains;
    public boolean isTheOrderConditional; // depending on the config file and the found order, this will be set to sth
    
    public SOCGeneralCase(List<Map<Long, Long>> TAU_reverseMap,
                          int A_index, int B_index,
                          ObjectBigArrayBigList<ObjectBigArrayBigList<LongBigArrayBigList>> TAU_XA,
                          ObjectBigArrayBigList<ObjectBigArrayBigList<LongBigArrayBigList>> TAU_XB,
                          Map<Long, Set<WeightedEdge>> flakyMap) {
        this.TAU_reverseMap = TAU_reverseMap;
        this.B_index = B_index;
        this.A_index = A_index;
        this.TAU_XA = TAU_XA;
        this.TAU_XB = TAU_XB;
        this.flakyMap = flakyMap;
    }
    
    public ArrayList<List<Map<Long, Set<Long>>>> execute() {
        isTheOrderConditional = true;
        ArrayList<List<Map<Long, Set<Long>>>> finalFlakes = new ArrayList<>();
        long startTime;
        
        startTime = System.nanoTime();
        boolean cycleFree = deriveChains();
        long chainDuration = System.nanoTime() - startTime;
        
        if (!cycleFree) {
            MainClass.ODAlgorithm.writeNewReductionGeneralCaseRunTimeToCSV(MainClass.DatasetFileName, true, chainDuration,
                    false, false, -1, -1, -1, false);
            return null;
        }
        // at this point have all the chains
        if (allChains != null) {
            boolean wasSatSuccessful = false;
            long reductionDuration = -1, satDuration = -1;
            int maxUniqVals = -1;
            if (!MainClass.OnlyCheckConditionalIIOC) {
                Map<Long, Long> mergeTrail = new HashMap<>();
                flakyMap = module1(allChains, mergeTrail);
                
                if (flakyMap != null) {
                    flakyMap = mapToUltimateDest(mergeTrail, flakyMap);
                    ODAlgorithm.flakeCount = flakyMap.size();
                    if (flakyMap.size() == 0) {
                        MainClass.ODAlgorithm.writeNewReductionGeneralCaseRunTimeToCSV(MainClass.DatasetFileName, false, chainDuration,
                                true, false, -1, -1, -1, true);
                        isTheOrderConditional = false;
                        return allChains;
                    } else {
                        // to see how close to the "hard case" we got, check the size of flakyMap
                        // Then analyze it with respect to the cardinality of the columns involved
                        updateWeightedEdges(flakyMap, allChains);
                        
                        // only this part is required if we want to ditch mod1
                        if (allChains.size() > 0) {
                            NewCPP2SATReducer ncppr = new NewCPP2SATReducer(allBipGraphs, allChains);
                            wasSatSuccessful = ncppr.newReduceAndSolve(10_000, 200);
                            
                            maxUniqVals = ncppr.maxCardinality;
                            reductionDuration = ncppr.reductionTime;
                            satDuration = ncppr.satTime;
                            
                            if (ncppr.satAnswer) {
                                MainClass.ODAlgorithm.writeNewReductionGeneralCaseRunTimeToCSV(MainClass.DatasetFileName, false, chainDuration,
                                        true, true, ncppr.reductionTime, ncppr.satTime, ncppr.maxCardinality, true);
                                isTheOrderConditional = false;
                                return ncppr.finalOrder;
                            }
                        }
                    }
                }
            }
            MainClass.ODAlgorithm.writeNewReductionGeneralCaseRunTimeToCSV(MainClass.DatasetFileName, true, chainDuration,
                    true, wasSatSuccessful, reductionDuration, satDuration, maxUniqVals, true);

        } else {
            System.out.println("SOC non-empty context invalid");
        }
        for (List<Map<Long, Set<Long>>> chain : allChains) {
            if (chain.get(0).size() > 0) {
                finalFlakes.add(chain);
            }
        }
        
        return finalFlakes;
    }
    
    //derives chains and returns true if all individual chains were acyclic, and false otherwise
    private boolean deriveChains() {
        allBipGraphs = new ArrayList<>();
        allChains = new ArrayList<>();
        
        for (int i = 0; i < TAU_XA.size64(); i++) { // or TAU_XB -- iterating over eq. classes on X
            ObjectBigArrayBigList<LongBigArrayBigList> sorted_TAU_LHS = TAU_XA.get(i);
            ObjectBigArrayBigList<LongBigArrayBigList> sorted_TAU_RHS = TAU_XB.get(i);
            Map<Long, Integer> rhsMap = new HashMap<>(); // will include the mapping from Tuple ID (tID) to the eq class within sorted_TAU_RHS that it falls under
            int loopC = 0; // counter keeping the index for the eq class we're on
            
            for (LongBigArrayBigList eqC_rhs : sorted_TAU_RHS) { // building the reverse mapping (from tID to equivalence class index)
                for (long tID : eqC_rhs) {
                    rhsMap.put(tID, loopC);
                }
                // create the status array for bipartite graph
                loopC++;
            }
            
            Map<String, Node> nodesMap = new HashMap<>();
            long tID = -1;
            loopC = 0;
            int eqC_rhs_idx = -1;
            
            for (LongBigArrayBigList eqC_lhs : sorted_TAU_LHS) { // now within the eq. class on X, iterating over eq. classes on LHS
                Node curr_lhs_node = new Node();
                
                tID = eqC_lhs.get(0);
                curr_lhs_node.name = String.format("l-%d", loopC);
                
                curr_lhs_node.tID = (long) TAU_reverseMap.get(A_index - 1).get(tID);
                nodesMap.put(curr_lhs_node.name, curr_lhs_node);
                
                int j = 0;
                Set<Long> seenBefore = new HashSet<>();
                while (j < eqC_lhs.size64()) {
                    tID = eqC_lhs.getLong(j);
                    if (!seenBefore.contains(tID)) {
                        try {
                            eqC_rhs_idx = rhsMap.get(tID);
                            LongBigArrayBigList eqC_rhs = sorted_TAU_RHS.get(eqC_rhs_idx);
                            String rhsNodeKey = String.format("r-%d", eqC_rhs_idx);
                            
                            Node curr_rhs_node = nodesMap.get(rhsNodeKey);
                            if (curr_rhs_node == null) {
                                curr_rhs_node = new Node();
                                curr_rhs_node.name = rhsNodeKey;
                                curr_rhs_node.tID = (long) TAU_reverseMap.get(B_index - 1).get(tID);
                                nodesMap.put(curr_rhs_node.name, curr_rhs_node);
                            }
                            Edge lhsEdge = new Edge();
                            lhsEdge.start = curr_lhs_node;
                            lhsEdge.end = curr_rhs_node;
                            curr_lhs_node.connections.add(lhsEdge);
                            
                            Edge rhsEdge = lhsEdge.reverseEdge();
                            curr_rhs_node.connections.add(rhsEdge);
                            
                            seenBefore.addAll(eqC_rhs);
                        } catch (Exception e) {
                            eqC_rhs_idx = -1;
                        }
                    }
                    j++;
                }
                loopC++;
            }
            
            Graph bipGraph = new Graph();
            bipGraph.nodes = new ArrayList<>(nodesMap.values());
            List<Node> nodes = new ArrayList<>();
            nodes.addAll(bipGraph.nodes); // a local deep copy of bipGraph.nodes
            
            //find and remove singleton nodes in the graph (preferably in a way that is efficient in the sense that least modifications have to be made)
            for (Node node : bipGraph.nodes) {
                if (node.connections.size() == 1) {
                    node.status = 0;
                }// node should be tagged as "to be removed"
            }
            bipGraph.initialize();
            if (bipGraph.isCyclic()) {
                return false;
            }
            ArrayList<ArrayList<Map<Long, Set<Long>>>> chains = bipGraph.getChainAdjs();
            allBipGraphs.add(bipGraph);
            allChains.addAll(chains);
        }
        return true;
    }
    
    
    // This is used to perform a preprocessing step and invalidate NP-hard instance as early as possible,
    // by checking and merging pairs of grpahs extracted from different partition groups.
    private Map<Long, Set<WeightedEdge>> module1(ArrayList<List<Map<Long, Set<Long>>>> allChains, Map<Long, Long> mergeTrail) {
        System.out.println("Module 1 SIZE all chains === " + allChains.size());
        Map<Long, Set<WeightedEdge>> flakyMap = new HashMap<>();
        ArrayList<Long> emptyComps = new ArrayList<>();
        long prevEmptCnt = 0;
        while (true) {
            long i = 0;
            OuterLoop:
            while (i < allChains.size()) {
                if (!emptyComps.contains(i)) {
                    long j = i + 1;
                    while (j < allChains.size()) {
                        if (!emptyComps.contains(j)) {
                            // If they share at least two elements on the LHS side:
                            boolean resolved = false;
                            Map<Long, Set<Long>> mergeStraightLHS;
                            Map<Long, Set<Long>> mergeReverseLHS;
                            List<Map<Long, Set<Long>>> compi = allChains.get((int) i);
                            List<Map<Long, Set<Long>>> compj = allChains.get((int) j);
                            boolean isCycleFreeStraightLHS;
                            boolean isCycleFreeReverseLHS;
                            
                            // get intersection of the two keySets (ith and jth) on LHS side:
                            Set<Long> commonKeysLHS = new HashSet<>(compi.get(0).keySet());
                            commonKeysLHS.retainAll(compj.get(0).keySet());
                            if (commonKeysLHS.size() >= 2) {
                                mergeStraightLHS = mergeAdjs(compi.get(0), compj.get(0), false);
                                mergeReverseLHS = mergeAdjs(compi.get(0), compj.get(0), true);
                                // do cycle detection on both
                                isCycleFreeStraightLHS = !(new Graph2(mergeStraightLHS)).isCyclic();
                                isCycleFreeReverseLHS = !(new Graph2(mergeReverseLHS)).isCyclic();
                                if (!isCycleFreeReverseLHS && !isCycleFreeStraightLHS) { // none of them are cycle free
                                    return null; // INVALID
                                } else if (isCycleFreeStraightLHS && !isCycleFreeReverseLHS) { // only straight is cycle free
                                    // check RHS with the same direction merge
                                    Map<Long, Set<Long>> mergeStraightRHS = mergeAdjs(compi.get(1), compj.get(1), false);
                                    if (!(new Graph2(mergeStraightRHS)).isCyclic()) {
                                        mergeComps(i, j, mergeStraightLHS, mergeStraightRHS, allChains, emptyComps, mergeTrail);
                                        resolved = true;
                                    } else { // INVALID
                                        return null;
                                    }
                                } else if (!isCycleFreeStraightLHS) { // only reverse is cycle free
                                    // check RHS with the same direction merge
                                    Map<Long, Set<Long>> mergeReverseRHS = mergeAdjs(compi.get(1), compj.get(1), true);
                                    if (!(new Graph2(mergeReverseRHS)).isCyclic()) {
                                        mergeComps(i, j, mergeReverseLHS, mergeReverseRHS, allChains, emptyComps, mergeTrail);
                                        resolved = true;
                                    } else { // INVALID
                                        return null;
                                    }
                                } else { // both are cycle free
                                    // do nothing for now
                                    flakyMap = addUndirEdge(flakyMap, i, j, 1);
                                    resolved = false;
                                }
                            }
                            
                            if (resolved) {
                                break OuterLoop;
                            }
                            // If they share at least two elements on the RHS side:
                            Set<Long> commonKeysRHS = new HashSet<>(compi.get(1).keySet());
                            commonKeysRHS.retainAll(compj.get(1).keySet());
                            Map<Long, Set<Long>> mergeStraightRHS;
                            Map<Long, Set<Long>> mergeReverseRHS;
                            boolean isCycleFreeStraightRHS;
                            boolean isCycleFreeReverseRHS;
                            if (commonKeysRHS.size() >= 2 && !resolved) {
                                mergeStraightRHS = mergeAdjs(compi.get(1), compj.get(1), false);
                                mergeReverseRHS = mergeAdjs(compi.get(1), compj.get(1), true);
                                // do cycle detection on both
                                isCycleFreeStraightRHS = !(new Graph2(mergeStraightRHS)).isCyclic();
                                isCycleFreeReverseRHS = !(new Graph2(mergeReverseRHS)).isCyclic();
                                if (!isCycleFreeReverseRHS && !isCycleFreeStraightRHS) { // none of them are cycle free
                                    return null; // INVALID
                                } else if (isCycleFreeStraightRHS && !isCycleFreeReverseRHS) { // only straight is cycle free
                                    // check RHS with the same direction merge
                                    mergeStraightLHS = mergeAdjs(compi.get(0), compj.get(0), false);
                                    if (!(new Graph2(mergeStraightLHS)).isCyclic()) {
                                        mergeComps(i, j, mergeStraightLHS, mergeStraightRHS, allChains, emptyComps, mergeTrail);
                                        resolved = true;
                                    } else {
                                        return null;
                                    }
                                } else if (!isCycleFreeStraightRHS) { // only reverse is cycle free
                                    // check LHS with the same direction merge
                                    mergeReverseLHS = mergeAdjs(compi.get(0), compj.get(0), true);
                                    if (!(new Graph2(mergeReverseLHS)).isCyclic()) {
                                        mergeComps(i, j, mergeReverseLHS, mergeReverseRHS, allChains, emptyComps, mergeTrail);
                                        resolved = true;
                                    } else {
                                        return null;
                                    }
                                } else { // both are cycle free
                                    // make flaky connection
                                    flakyMap = addUndirEdge(flakyMap, i, j, 1);
                                    resolved = false;
                                }
                            }
                            // At this point, i and j don't share more than two elements on either side
                            if ((commonKeysLHS.size() == 1 || commonKeysRHS.size() == 1) && !resolved) {
                                flakyMap = addUndirEdge(flakyMap, i, j, 1);
                            } else if (commonKeysLHS.size() == 0 && commonKeysRHS.size() == 0 && !resolved) {
                                // if they don't share anything
                            } else if (resolved) {
                                break OuterLoop;
                            } else {
                            }
                        }
                        j++;
                    }
                }
                i++;
            }
            if (prevEmptCnt == emptyComps.size()) {
                return flakyMap;
            }
            prevEmptCnt = emptyComps.size();
        }
    }
    
    // This adds an edge to the flakyMap, storing co-occurrances of tuple values together.
    private Map<Long, Set<WeightedEdge>> addUndirEdge(Map<Long, Set<WeightedEdge>> flakyMap, Long i, Long j, int weight) {
        if (!flakyMap.containsKey(i)) {
            flakyMap.put(i, new HashSet<>());
        }
        if (!flakyMap.containsKey(j)) {
            flakyMap.put(j, new HashSet<>());
        }
        flakyMap.get(i).add(new WeightedEdge(j, weight));
        flakyMap.get(j).add(new WeightedEdge(i, weight));
        return flakyMap;
    }
    
    // Takes Map "flakyMap" and converts everything in it to what it was ultimately merged with based on "mergeTrail".
    private Map<Long, Set<WeightedEdge>> mapToUltimateDest(Map<Long, Long> mergeTrail, Map<Long, Set<WeightedEdge>> flakyMap) {
        Map<Long, Set<WeightedEdge>> ultimateMap = new HashMap<>();
        
        int i = 0;
        ArrayList<Set<WeightedEdge>> destValueses = new ArrayList<>();
        
        for (long key : flakyMap.keySet()) {
            destValueses.add(new HashSet<>());
            for (WeightedEdge value : flakyMap.get(key)) {
                destValueses.get(i).add(new WeightedEdge(findUltimateDest(value.getDest(), mergeTrail), 1));
            }
            long ultimateKey = findUltimateDest(key, mergeTrail);
            try {
                destValueses.get(i).addAll(ultimateMap.get(ultimateKey));
            } catch (Exception E) {
            }
            
            destValueses.get(i).remove(new WeightedEdge(ultimateKey, 1));
            if (destValueses.get(i).size() != 0) {
                ultimateMap.put(ultimateKey, destValueses.get(i));
            }
            i++;
        }
        return ultimateMap;
    }
    
    private void updateWeightedEdges(Map<Long, Set<WeightedEdge>> adj, ArrayList<List<Map<Long, Set<Long>>>> allChains) {
        for (long from :
                adj.keySet()) {
            for (WeightedEdge edge :
                    adj.get(from)) {
                long to = edge.getDest();
                
                List<Map<Long, Set<Long>>> compFrom = allChains.get((int) from);  //index 0 will give chain for LHS
                List<Map<Long, Set<Long>>> compTo = allChains.get((int) to);  //index 1 will give chain for RHS
                
                Set<Long> commonKeysLHS = new HashSet<>(compFrom.get(0).keySet());
                commonKeysLHS.retainAll(compTo.get(0).keySet());
                edge.setCommonLHS(commonKeysLHS);
                Set<Long> commonKeysRHS = new HashSet<>(compFrom.get(1).keySet());
                commonKeysRHS.retainAll(compTo.get(1).keySet());
                edge.setCommonRHS(commonKeysRHS);
                
                edge.setWeight(Math.max(commonKeysLHS.size(), commonKeysRHS.size()));
            }
        }
    }
    
    private long findUltimateDest(long source, Map<Long, Long> mergeTrail) {
        long destination = source;
        while (mergeTrail.containsKey(destination)) {
            destination = mergeTrail.get(destination);
        }
        return destination;
    }
    
    public Map<Long, Long> calculateNodeWeights(Map<Long, Set<WeightedEdge>> adj) {
        HashMap<Long, Long> nodeWeights = new HashMap<>();
        for (Long node :
                adj.keySet()) {
            Long weight = 0L;
            for (WeightedEdge edge :
                    adj.get(node)) {
                weight += edge.getWeight();
            }
            nodeWeights.put(node, weight);
        }
        return nodeWeights;
    }
    
    // These function corresponds to module 2 and includes the heuristics used when solving 
    // an NP-hard instance.
    public ArrayList<List<Map<Long, Set<Long>>>> module2(Map<Long, Set<WeightedEdge>> adj, ArrayList<List<Map<Long, Set<Long>>>> allChains) {
        System.out.println("Module 2 SIZE looseConns === " + adj.size());
        System.out.println(adj);
        long mod2startTime = System.nanoTime();
        
        // HEURISTIC on/off
        Map<Long, Set<WeightedEdge>> heavyEdgeAdj = getHeavyEdgeAdjFromAdj(adj);
        
        Map<Long, Long> nodeWeights = calculateNodeWeights(heavyEdgeAdj); // could use either adj or heavy adj
        // Mark all the vertices as not visited(By default set as false)
        Map<Long, Boolean> visited = new HashMap<>();
        ArrayList<Long> unvisited = new ArrayList<>();
        for (long key : adj.keySet()) {
            visited.put(key, false);
            unvisited.add(key);
        }
        // Create a queue for improved BFS, sort descending according to weight of ALL edges (could it be better to consider only >1 weight edges?)
        // HEURISTIC on/off
        PriorityQueue<WeightedNode> pq = new PriorityQueue<>(10, (x, y) -> (int) (y.getWeight() - x.getWeight()));
        
        ArrayList<List<Map<Long, Set<Long>>>> finalFlakes = new ArrayList<>();
        // Mark the current node as visited and enqueue it
        
        int totalIterations = 0;
        while (unvisited.size() != 0) {
            Stack<Long> mainStack = new Stack<>();
            Stack<Long> sideStack = new Stack<>();
            
            // HEURISTIC on/off
            Long max_weight = -1L;
            Long max_node = -1L;
            for (Long node :
                    unvisited) {
                if (nodeWeights.get(node) > max_weight) {
                    max_weight = nodeWeights.get(node);
                    max_node = node;
                }
            }
            long s = max_node;
            
            visited.put(s, true);
            unvisited.remove(s);
            pq.add(new WeightedNode(s, nodeWeights.get(s)));
            
            // push s into main stack
            List<Map<Long, Set<Long>>> tmpComp = new ArrayList<>();
            tmpComp.add(new HashMap<>()); //LHS
            tmpComp.add(new HashMap<>()); //RHS
            
            while (pq.size() != 0) {
                // Dequeue a vertex from queue
                s = pq.poll().getNode();
                System.out.print("[" + Long.toString(s) + ", " + nodeWeights.get(s) + "], ");
                
                // Get all adjacent vertices of the dequeued vertex s
                // If a adjacent has not been visited, then mark it
                // as visited and enqueue it
                int iterations = 0;
                // Here we only use neighbours which are connected with >1 weight edges
                Iterator<WeightedEdge> i = heavyEdgeAdj.get(s).iterator();
                
                while (i.hasNext()) { // iterate over everything connected to s
                    
                    long n = i.next().getDest();
                    if (!visited.get(n)) {
                        visited.put(n, true);
                        pq.add(new WeightedNode(n, nodeWeights.get(n)));
                        unvisited.remove(n);
                    }
                }
                long n = s;
                
                mainStack.push(n + 1);
                for (long vertex : mainStack) {
                    tmpComp.set(0, mergeAdjs(tmpComp.get(0), allChains.get((int) Math.abs(vertex) - 1).get(0), vertex < 0));
                    tmpComp.set(1, mergeAdjs(tmpComp.get(1), allChains.get((int) Math.abs(vertex) - 1).get(1), vertex < 0));
                }
                Graph2 tmpGraphLHS = new Graph2(tmpComp.get(0));
                Graph2 tmpGraphRHS = new Graph2(tmpComp.get(1));
                boolean isCyclicLHS = tmpGraphLHS.isCyclic();
                boolean isCyclicRHS = tmpGraphRHS.isCyclic();
                totalIterations += iterations;
                iterations = 0;
                while (isCyclicLHS || isCyclicRHS) {
                    // allow 100 iterations for each new element, then allow to check all iterations if size <= 20, otherwise put a time limit
                    if (iterations > 100) {
                        if (mainStack.size() > 20) {
                            if (System.nanoTime() - mod2startTime > 3e10) {
                                System.out.println("\n------------------ TIME limit exceeded. ----------------");
                                totalIterations += iterations;
                                System.out.println("Total number of iterations: " + totalIterations);
                                return null;
                            }
                        }
                    }
                    iterations += 1;
                    long popped = mainStack.pop();
                    while (true) {
                        if (mainStack.isEmpty()) {
                            totalIterations += iterations;
                            System.out.println("\nNot possible!");
                            System.out.println("Total number of iterations: " + totalIterations);
                            return null;
                        }
                        if (popped < 0) { // in order to handle potential popped == 0, store zero as 0.5 in the stack
                            sideStack.push(-1 * popped);
                            popped = mainStack.pop();
                        } else if (popped > 0) {
                            mainStack.push(-1 * popped);
                            while (!sideStack.isEmpty()) {
                                mainStack.push(sideStack.pop());
                            }
                            
                            break;
                        }
                    }
                    
                    // renew tmpComp
                    tmpComp = new ArrayList<>();
                    tmpComp.add(new HashMap<>()); //LHS
                    tmpComp.add(new HashMap<>()); //RHS
                    for (long vertex : mainStack) {
                        tmpComp.set(0, mergeAdjs(tmpComp.get(0), allChains.get((int) Math.abs(vertex) - 1).get(0), vertex < 0));
                        tmpComp.set(1, mergeAdjs(tmpComp.get(1), allChains.get((int) Math.abs(vertex) - 1).get(1), vertex < 0));
                    }
                    tmpGraphLHS = new Graph2(tmpComp.get(0));
                    tmpGraphRHS = new Graph2(tmpComp.get(1));
                    isCyclicLHS = tmpGraphLHS.isCyclic();
                    isCyclicRHS = tmpGraphRHS.isCyclic();
                }
                
            }
            
            finalFlakes.add(tmpComp);
            for (long vertex : mainStack) {
                allChains.get((int) Math.abs(vertex) - 1).set(0, new HashMap<>());
                allChains.get((int) Math.abs(vertex) - 1).set(1, new HashMap<>());
            }
        }
        
        System.out.println("\nTotal number of iterations: " + totalIterations);
        
        return finalFlakes;
    }
    
    // This function takes the adjacency list of a graph and finds the graph which consists only of
    // edges with weight more than 1 in the initial graph
    // will return the initial adj if no >1 edge exists in the graph
    private Map<Long, Set<WeightedEdge>> getHeavyEdgeAdjFromAdj(Map<Long, Set<WeightedEdge>> adj) {
        Map<Long, Set<WeightedEdge>> heavyEdgeAdj = new HashMap<>();
        boolean has_heavy_edge = false;
        for (long node :
                adj.keySet()) {
            heavyEdgeAdj.put(node, new HashSet<>());
            for (WeightedEdge edge :
                    adj.get(node)) {
                if (edge.getWeight() > 1) {
                    heavyEdgeAdj.get(node).add(edge);
                    has_heavy_edge = true;
                }
            }
        }
        if (has_heavy_edge)
            return heavyEdgeAdj;
        else
            return adj;
    }
    
    private Map<Long, Set<Long>> mergeAdjs(Map<Long, Set<Long>> adj1, Map<Long, Set<Long>> adj2, boolean reverse) {
        Map<Long, Set<Long>> adj1Clone = (Map) deepClone(adj1);
        if (reverse) {
            adj2 = reverseAdj(adj2); // adj2 will be emptied after this function is done
        }
        Map<Long, Set<Long>> merged = new HashMap<>(adj1Clone);
        for (long key : adj2.keySet()) {
            if (adj1Clone.containsKey(key)) {
                merged.get(key).addAll(adj2.get(key));
            } else {
                merged.put(key, adj2.get(key));
            }
        }
        return merged;
    }
    
    public static Object deepClone(Object object) {
        try {
            ByteArrayOutputStream baos = new ByteArrayOutputStream();
            ObjectOutputStream oos = new ObjectOutputStream(baos);
            oos.writeObject(object);
            ByteArrayInputStream bais = new ByteArrayInputStream(baos.toByteArray());
            ObjectInputStream ois = new ObjectInputStream(bais);
            return ois.readObject();
        } catch (Exception e) {
            e.printStackTrace();
            return null;
        }
    }
    
    private Map<Long, Set<Long>> reverseAdj(Map<Long, Set<Long>> adj) {
        HashMap<Long, Set<Long>> outputMap = new HashMap<>();
        for (long key : adj.keySet()) {
            for (long value : adj.get(key)) {
                try {
                    outputMap.get(value).add(key);
                } catch (Exception E) {
                    outputMap.put(value, new HashSet<>(Arrays.asList(key)));
                }
            }
        }
        Set keySet = adj.keySet();
        Set<Long> singles = setDeepCopy(keySet);
        singles.removeAll(outputMap.keySet());
        for (long single : singles) {
            outputMap.put(single, new HashSet<>(Arrays.asList()));
        }
        return outputMap;
    }
    
    private Set<Long> setDeepCopy(Set<Long> inpSet) {
        Set<Long> setClone = new HashSet<>();
        Iterator<Long> iterator = inpSet.iterator();
        
        while (iterator.hasNext()) {
            //Add the object clones
            setClone.add(new Long(iterator.next()));
        }
        return setClone;
    }
    
    
    private void mergeComps(long i, long j, Map<Long, Set<Long>> mergedLHS, Map<Long, Set<Long>> mergedRHS,
                            ArrayList<List<Map<Long, Set<Long>>>> allChains, ArrayList<Long> emptyComps, Map<Long, Long> mergeTrail) {
        ArrayList<Map<Long, Set<Long>>> newCompi = new ArrayList<>();
        newCompi.add((Map) deepClone(mergedLHS));
        newCompi.add((Map) deepClone(mergedRHS));
        allChains.set((int) i, newCompi);
        allChains.get((int) j).set(0, new HashMap<>());
        allChains.get((int) j).set(1, new HashMap<>());
        emptyComps.add(j);
        mergeTrail.put(j, i);
    }
    
}