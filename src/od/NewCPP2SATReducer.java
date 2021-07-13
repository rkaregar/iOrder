package od;

import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;

import java.util.*;
import java.util.stream.Collectors;

public class NewCPP2SATReducer {
    private int satVariableCounter;
    private List<Set<Long>> values;  // storing unique values in LHS and RHS
    public int maxCardinality;  // stores the maximum cardinality on each side for pruning purposes
    private final List<Map<SATVariable, Integer>> satVariable2Numeric;  // encode LHS and RHS
    private final Map<Integer, Integer> numericVar2side;  // this one will store the numeric variable's side,
    private final Map<Integer, SATVariable> numericVar2satVar;  // while this one keeps its (a, b) equiv. variable
    public List<SimpleGraph> simpleUndirGraphs;  // holds the undir graphs of PGs to compute connected components
    
    private final List<Graph> allBipGraphs;
    private final List<BipartiteGraph> allNewBipGraphs;
    private final List<List<Map<Long, Set<Long>>>> allChains;
    private final List<Map<TuplePair, Set<Integer>>> haveThisPairCoOccurred;
    public List<int[]> clauses;
    
    private List<Set<TuplePair>> nonremovables;
    
    public boolean satAnswer;
    public ArrayList<List<Map<Long, Set<Long>>>> finalOrder;
    
    public long reductionTime = -1, satTime = -1;
    
    public NewCPP2SATReducer(List<Graph> allBipGraphs, List<List<Map<Long, Set<Long>>>> allChains) {
        this.allBipGraphs = allBipGraphs;
        this.allChains = allChains;
        
        allNewBipGraphs = new ArrayList<>();
        for (Graph g : allBipGraphs) {
            allNewBipGraphs.add(new BipartiteGraph(g));
        }
        
        satVariable2Numeric = new ArrayList<>(Arrays.asList(new HashMap<>(), new HashMap<>()));
        numericVar2satVar = new HashMap<>();
        numericVar2side = new HashMap<>();
        haveThisPairCoOccurred = new ArrayList<>(Arrays.asList(new HashMap<>(), new HashMap<>()));
        
        nonremovables = new ArrayList<>(Arrays.asList(new HashSet<>(), new HashSet<>()));
        
        clauses = new ArrayList<>();
        satVariableCounter = 1;
        
        satAnswer = false;
    }
    
    
    // return false if the reduction/solving had exceeded time limit
    // the result (order/null) will be stored somewhere else
    // the new idea, based on pairs of tuples instead of only chains
    public boolean newReduceAndSolve(int initialCardinalityCutoff, int connectedComponentMaxSizeLimit) {
        long startTime = System.nanoTime();
        findUniqueValues();
        
        if (maxCardinality < initialCardinalityCutoff) {
            computeConnectedComponents();
            if ((Collections.max(simpleUndirGraphs.get(0).getConnectedComponents().stream().map(List::size).collect(Collectors.toList())) < connectedComponentMaxSizeLimit) &&
                    (Collections.max(simpleUndirGraphs.get(1).getConnectedComponents().stream().map(List::size).collect(Collectors.toList())) < connectedComponentMaxSizeLimit)) {
                createIntraECVariables();
                createInterPGVariables();
                
                handleStoringCoOccurrencesOfTuples();
                addConnectedPairOfTuplesClauses();
                addNotConnectedPairOfTuplesClauses();
                addTransitivityClauses();
                
                reductionTime = System.nanoTime() - startTime;
                startTime = System.nanoTime();
                
                boolean wasSuccessful = solveSAT();  // return if it was solved or exceeded time limit
                
                satTime = System.nanoTime() - startTime;
                
                return wasSuccessful;
            }
        }
        return false;
    }
    
    private void findUniqueValues() {
        values = new ArrayList<>();
        values.add(new HashSet<>());
        values.add(new HashSet<>());
        
        for (Graph bipGraph :
                allBipGraphs) {
            for (Node node :
                    bipGraph.nodes) {
                if (node.name.charAt(0) == 'l') {
                    values.get(0).add(node.tID);
                } else {
                    values.get(1).add(node.tID);
                }
            }
        }
        
        maxCardinality = Math.max(values.get(0).size(), values.get(1).size());
    }
    
    public void computeConnectedComponents() {
        simpleUndirGraphs = new ArrayList<>(Arrays.asList(new SimpleGraph(), new SimpleGraph()));
        // add the edges from the (potentially merged) PGs (chains)
        for (List<Map<Long, Set<Long>>> doubleChain : allChains) {
            for (int side = 0; side < 2; side++) {
                Map<Long, Set<Long>> currPG = doubleChain.get(side);
                for (Long source :
                        currPG.keySet()) {
                    List<Long> descendants = new ArrayList<>(currPG.get(source));
                    for (Long destination : descendants) {
                        simpleUndirGraphs.get(side).addEdge(source, destination);
                    }
                }
            }
        }
        simpleUndirGraphs.get(0).computeConnectedComponents();
        simpleUndirGraphs.get(1).computeConnectedComponents();
    }
    
    // this one includes all (singleton/non-singleton) values within each PG
    private void createIntraECVariables() {
        for (BipartiteGraph bg : allNewBipGraphs) {
            for (int i = 0; i < bg.getLeftNodes().size() - 1; i++) {
                for (int j = i + 1; j < bg.getLeftNodes().size(); j++) {
                    long first = bg.getLeftNodes().get(i).id;
                    long second = bg.getLeftNodes().get(j).id;
                    createTwoVariablesFromValues(0, first, second);
                }
            }
            for (int i = 0; i < bg.getRightNodes().size() - 1; i++) {
                for (int j = i + 1; j < bg.getRightNodes().size(); j++) {
                    long first = bg.getRightNodes().get(i).id;
                    long second = bg.getRightNodes().get(j).id;
                    createTwoVariablesFromValues(1, first, second);
                }
            }
        }
    }
    
    // this one includes only non-singleton elements across multiple PGs
    private void createInterPGVariables() {
        for (int side = 0; side < 2; side++) {
            for (List<Long> cc :
                    simpleUndirGraphs.get(side).getConnectedComponents()) {
                for (int i = 0; i < cc.size() - 1; i++) {
                    for (int j = i + 1; j < cc.size(); j++) {
                        Long first = cc.get(i);
                        Long second = cc.get(j);
                        createTwoVariablesFromValues(side, first, second);
                    }
                }
            }
        }
    }
    
    private void createTwoVariablesFromValues(int side, long first, long second) {
        SATVariable satVar = new SATVariable(first, second), satVarRev = new SATVariable(second, first);
        if ((!satVariable2Numeric.get(side).containsKey(satVar)) && (!satVariable2Numeric.get(side).containsKey(satVarRev))) {
            satVariable2Numeric.get(side).put(satVar, satVariableCounter);
            numericVar2side.put(satVariableCounter, side);
            numericVar2satVar.put(satVariableCounter, satVar);
            
            satVariable2Numeric.get(side).put(satVarRev, satVariableCounter + 1);
            numericVar2side.put(satVariableCounter + 1, side);
            numericVar2satVar.put(satVariableCounter + 1, satVarRev);
            
            clauses.add(new int[]{-satVariableCounter, -(satVariableCounter + 1)});
            
            satVariableCounter += 2;
        }
        
    }
    
    private void handleStoringCoOccurrencesOfTuples() {
        for (int i = 0; i < allNewBipGraphs.size(); i++) {
            BipartiteGraph bg = allNewBipGraphs.get(i);
            for (int j = 0; j < bg.getLeftNodes().size(); j++) {
                BipartiteNode firstEdgeLHS = bg.getLeftNodes().get(j);
                for (BipartiteNode firstEdgeRHS : bg.getAdj().get(firstEdgeLHS)) {
                    for (int k = j + 1; k < bg.getLeftNodes().size(); k++) {
                        BipartiteNode secondEdgeLHS = bg.getLeftNodes().get(k);
                        for (BipartiteNode secondEdgeRHS : bg.getAdj().get(secondEdgeLHS)) {
                            if (firstEdgeRHS != secondEdgeRHS) {
                                long l1 = firstEdgeLHS.id, r1 = firstEdgeRHS.id;
                                long l2 = secondEdgeLHS.id, r2 = secondEdgeRHS.id;
                                
                                storeTupleCoOccurrence(l1, l2, 0, i);
                                storeTupleCoOccurrence(r1, r2, 1, i);
                            }
                        }
                    }
                }
            }
        }
    }
    
    private void storeTupleCoOccurrence(long t1, long t2, int side, int pgNumber) {
        TuplePair p1 = new TuplePair(t1, t2), p2 = new TuplePair(t2, t1);
        Map<TuplePair, Set<Integer>> currSideData = haveThisPairCoOccurred.get(side);
        if (!currSideData.containsKey(p1)) {
            currSideData.put(p1, new HashSet<>());
            currSideData.put(p2, new HashSet<>());
        }
        currSideData.get(p1).add(pgNumber);
        currSideData.get(p2).add(pgNumber);
    }
    
    public void addConnectedPairOfTuplesClauses() {
        for (BipartiteGraph bg : allNewBipGraphs) {
            for (List<BipartiteNode> connectedComponent : bg.getConnectedComponents()) {
                for (int i = 0; i < connectedComponent.size(); i++) {
                    if (connectedComponent.get(i).side == 'l') {
                        BipartiteNode firstEdgeLHS = connectedComponent.get(i);
                        // iterate over RHS nodes connected to this
                        for (BipartiteNode firstEdgeRHS : bg.getAdj().get(firstEdgeLHS)) {
                            for (int j = i + 1; j < connectedComponent.size(); j++) {
                                if (connectedComponent.get(j).side == 'l') {
                                    BipartiteNode secondEdgeLHS = connectedComponent.get(j);
                                    for (BipartiteNode secondEdgeRHS : bg.getAdj().get(secondEdgeLHS)) {
                                        if (!firstEdgeRHS.equals(secondEdgeRHS)) {
                                            long l1 = firstEdgeLHS.id, r1 = firstEdgeRHS.id;
                                            long l2 = secondEdgeLHS.id, r2 = secondEdgeRHS.id;
                                        
                                            int ac = satVariable2Numeric.get(0).get(new SATVariable(l1, l2));
                                            int ca = satVariable2Numeric.get(0).get(new SATVariable(l2, l1));
                                            int bd = satVariable2Numeric.get(1).get(new SATVariable(r1, r2));
                                            int db = satVariable2Numeric.get(1).get(new SATVariable(r2, r1));
                                        
                                            clauses.add(new int[]{ac, db});
                                            clauses.add(new int[]{ca, bd});
                                            
                                            nonremovables.get(0).add(new TuplePair(l1, l2));
                                            nonremovables.get(0).add(new TuplePair(l2, l1));
                                            nonremovables.get(1).add(new TuplePair(r1, r2));
                                            nonremovables.get(1).add(new TuplePair(r2, r1));
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    
    // for each two connected component, first check if they have a pair that exist in at least one other PG 
    public void addNotConnectedPairOfTuplesClauses() {
        for (BipartiteGraph bg : allNewBipGraphs) {
            for (int i = 0; i < bg.getConnectedComponents().size(); i++) {
                List<BipartiteNode> firstCC = bg.getConnectedComponents().get(i);
                for (int j = i + 1; j < bg.getConnectedComponents().size(); j++) {
                    List<BipartiteNode> secondCC = bg.getConnectedComponents().get(j);
                    
                    // this indicates whether these CCs have at least two elements in common in another PG
                    boolean shouldConsiderThisCCPair = false;
                    
                    for (int k = 0; k < firstCC.size(); k++) {
                        if (firstCC.get(k).side == 'l') {
                            BipartiteNode firstEdgeLHS= firstCC.get(k);
                            for (BipartiteNode firstEdgeRHS : bg.getAdj().get(firstEdgeLHS)) {
                                for (int l = 0; l < secondCC.size(); l++) {
                                    if (secondCC.get(l).side == 'l') {
                                        BipartiteNode secondEdgeLHS = secondCC.get(l);
                                        for (BipartiteNode secondEdgeRHS : bg.getAdj().get(secondEdgeLHS)) {
                                            long l1 = firstEdgeLHS.id, r1 = firstEdgeRHS.id;
                                            long l2 = secondEdgeLHS.id, r2 = secondEdgeRHS.id;
                                            if (haveThisPairCoOccurred.get(0).get(new TuplePair(l1, l2)).size() > 1 ||
                                                    haveThisPairCoOccurred.get(0).get(new TuplePair(l2, l1)).size() > 1 ||
                                                    haveThisPairCoOccurred.get(1).get(new TuplePair(r1, r2)).size() > 1 ||
                                                    haveThisPairCoOccurred.get(1).get(new TuplePair(r1, r2)).size() > 1) {
                                                shouldConsiderThisCCPair = true;
                                                break;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
    
                    for (int k = 0; k < firstCC.size(); k++) {
                        if (firstCC.get(k).side == 'l') {
                            BipartiteNode firstEdgeLHS= firstCC.get(k);
                            for (BipartiteNode firstEdgeRHS : bg.getAdj().get(firstEdgeLHS)) {
                                for (int l = 0; l < secondCC.size(); l++) {
                                    if (secondCC.get(l).side == 'l') {
                                        BipartiteNode secondEdgeLHS = secondCC.get(l);
                                        for (BipartiteNode secondEdgeRHS : bg.getAdj().get(secondEdgeLHS)) {
                                            long l1 = firstEdgeLHS.id, r1 = firstEdgeRHS.id;
                                            long l2 = secondEdgeLHS.id, r2 = secondEdgeRHS.id;
    
                                            int ac = satVariable2Numeric.get(0).get(new SATVariable(l1, l2));
                                            int ca = satVariable2Numeric.get(0).get(new SATVariable(l2, l1));
                                            int bd = satVariable2Numeric.get(1).get(new SATVariable(r1, r2));
                                            int db = satVariable2Numeric.get(1).get(new SATVariable(r2, r1));
    
                                            if (shouldConsiderThisCCPair) {
                                                clauses.add(new int[]{ac, db});
                                                clauses.add(new int[]{ca, bd});
    
    
                                                nonremovables.get(0).add(new TuplePair(l1, l2));
                                                nonremovables.get(0).add(new TuplePair(l2, l1));
                                                nonremovables.get(1).add(new TuplePair(r1, r2));
                                                nonremovables.get(1).add(new TuplePair(r2, r1));
                                            } else {
                                                clauses.add(new int[]{-ac, bd});
                                                clauses.add(new int[]{-ca, db});
                                                clauses.add(new int[]{-bd, ac});
                                                clauses.add(new int[]{-db, ca});
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    
    public void addNewRestrictivePairSwapClauses() {
        for (Graph bipGraph :
                allBipGraphs) {
            List<Node> lhsNodes = new ArrayList<>();  // only checking LHS nodes will cover all the necessary clauses
            for (Node node :
                    bipGraph.nodes) {
                if (node.name.charAt(0) == 'l')
                    lhsNodes.add(node);
            }
            for (int i = 0; i < lhsNodes.size() - 1; i++) {
                Node firstNodeLhs = lhsNodes.get(i);
                for (Edge edge :
                        firstNodeLhs.connections) {
                    Node firstNodeRhs = edge.end;
                    for (int j = i + 1; j < lhsNodes.size(); j++) {
                        Node secondNodeLhs = lhsNodes.get(j);
                        for (Edge edge2 :
                                secondNodeLhs.connections) {
                            Node secondNodeRhs = edge2.end;
                            if (firstNodeRhs != secondNodeRhs) {  // add the swap clause
                                long l1 = firstNodeLhs.tID, r1 = firstNodeRhs.tID;
                                long l2 = secondNodeLhs.tID, r2 = secondNodeRhs.tID;
                                
                                int ac = satVariable2Numeric.get(0).get(new SATVariable(l1, l2));
                                int ca = satVariable2Numeric.get(0).get(new SATVariable(l2, l1));
                                int bd = satVariable2Numeric.get(1).get(new SATVariable(r1, r2));
                                int db = satVariable2Numeric.get(1).get(new SATVariable(r2, r1));
                                
                                clauses.add(new int[]{ac, db});
                                clauses.add(new int[]{ca, bd});
                            }
                        }
                    }
                }
            }
        }
    }
    
    public void addChainClauses() {
        for (List<Map<Long, Set<Long>>> doubleChain : allChains) {
            for (int side = 0; side < 2; side++) {
                Map<Long, Set<Long>> currPG = doubleChain.get(side);
                int representative = -1, reprRev = -1;
                int pairVar, pairVarRev;
                for (Long source :
                        currPG.keySet()) {
                    List<Long> descendants = new ArrayList<>(currPG.get(source));
                    for (Long destination : descendants) {
                        pairVar = satVariable2Numeric.get(side).get(new SATVariable(source, destination));
                        pairVarRev = satVariable2Numeric.get(side).get(new SATVariable(destination, source));
                        clauses.add(new int[]{pairVar, pairVarRev});  // to ensure that at least one of them is true
                        if (representative == -1) {
                            representative = pairVar;
                            reprRev = pairVarRev;
                        } else {
                            // to ensure that all edges are in one direction
                            clauses.add(new int[]{-representative, pairVar});
                            clauses.add(new int[]{-reprRev, pairVarRev});
                        }
                    }
                }
            }
        }
    }
    
    public void addTransitivityClauses() {
        for (int side = 0; side < 2; side++) {
            for (List<Long> cc :
                    simpleUndirGraphs.get(side).getConnectedComponents()) {
                for (int i = 0; i < cc.size(); i++) {
                    for (int j = 0; j < cc.size(); j++) {
                        for (int k = 0; k < cc.size(); k++) {
                            if ((i != j) && (i != k) && (j != k)) {
                                // these three are tIDs, or unique values in other words
                                Long v_i = cc.get(i);
                                Long v_j = cc.get(j);
                                Long v_k = cc.get(k);
                                
                                // add the clause for (ij && jk -> ik) === (!ij || !jk || ik)
                                int a = satVariable2Numeric.get(side).get(new SATVariable(v_i, v_j));
                                int b = satVariable2Numeric.get(side).get(new SATVariable(v_j, v_k));
                                int c = satVariable2Numeric.get(side).get(new SATVariable(v_i, v_k));
                                clauses.add(new int[]{-a, -b, c});
                            }
                        }
                    }
                }
            }
        }
    }
    
    public ArrayList<List<Map<Long, Set<Long>>>> getFinalOrders(int[] assignments) {
        // this is the only single chain for both sides, then we'll just append it to another list and return it
        List<Map<Long, Set<Long>>> doubleChain = new ArrayList<>(Arrays.asList(new HashMap<>(), new HashMap<>()));
        
        for (int side = 0; side < 2; side++) {
            for (Long val :
                    values.get(side)) {
                doubleChain.get(side).put(val, new HashSet<>());
            }
        }
        int side;
        SATVariable satVariable;
        
        for (int varAssignment :
                assignments) {
            if (varAssignment > 0) {
                side = numericVar2side.get(varAssignment);
                satVariable = numericVar2satVar.get(varAssignment);
                
                // if satVar = (a, b), we'll add the corresponding edge to the proper side graph
                
                long first = satVariable.getFirst();
                long second = satVariable.getSecond();
                if (nonremovables.get(side).contains(new TuplePair(first, second)) ||
                nonremovables.get(side).contains(new TuplePair(second, first))) {
                    doubleChain.get(side).get(first).add(second);
                }
            }
        }
        
        return new ArrayList<>(Collections.singletonList(doubleChain));
    }
    
    // return false if it exceeded time limit
    public boolean solveSAT() {
        ISolver solver = SolverFactory.newDefault();
        for (int[] clause :
                clauses) {
            try {
                solver.addClause(new VecInt(clause));
            } catch (ContradictionException e) {
                System.out.println(e.getMessage());
            }
        }
        
        try {
            satAnswer = solver.isSatisfiable();
            if (satAnswer)
                finalOrder = getFinalOrders(solver.model());
            else
                finalOrder = null;
            return true;
        } catch (TimeoutException e) {
            System.out.println("Time limit Exceeded");
            System.out.println(e.getMessage());
            return false;
        }
    }
}


class SATVariable {
    private final long first, second;
    
    public SATVariable(long first, long second) {
        this.first = first;
        this.second = second;
    }
    
    public long getFirst() {
        return first;
    }
    
    public long getSecond() {
        return second;
    }
    
    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof SATVariable)) return false;
        SATVariable that = (SATVariable) o;
        return first == that.first &&
                second == that.second;
    }
    
    @Override
    public int hashCode() {
        return Objects.hash(first, second);
    }
    
    @Override
    public String toString() {
        return "(" + first + ", " + second + ")";
    }
}


