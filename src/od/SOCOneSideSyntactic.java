// This is the class for validating E/I OCs.
// This class corresponds to Section 3 in the paper.

package od;

import it.unimi.dsi.fastutil.longs.LongBigArrayBigList;
import it.unimi.dsi.fastutil.objects.ObjectBigArrayBigList;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.*;

public class SOCOneSideSyntactic {
    private List<Map<Long, Long>> TAU_reverseMap;
    private int B_index;
    private int A_index;
    private boolean fdHolds;
    public List<List<Map<Long, Set<Long>>>> allChainsNoFD;
    public List<Map<Long, Set<Long>>> allChains;
    private ObjectBigArrayBigList<ObjectBigArrayBigList<LongBigArrayBigList>> TAU_XA;
    private ObjectBigArrayBigList<ObjectBigArrayBigList<LongBigArrayBigList>> TAU_XB;
    
    public boolean isOrderConditional = true;
    
    public SOCOneSideSyntactic(List<Map<Long, Long>> TAU_reverseMap, int B_index, int A_index, boolean fdHolds,
                               ObjectBigArrayBigList<ObjectBigArrayBigList<LongBigArrayBigList>> TAU_XA,
                               ObjectBigArrayBigList<ObjectBigArrayBigList<LongBigArrayBigList>> TAU_XB) {
        this.TAU_reverseMap = TAU_reverseMap;
        this.TAU_XA = TAU_XA;
        this.TAU_XB = TAU_XB;
        this.A_index = A_index;
        this.B_index = B_index;
        this.fdHolds = fdHolds;
        allChains = new ArrayList<>();
        allChainsNoFD = new ArrayList<>();
    }
    
    public List<Map<Long, Set<Long>>> execute() {
        // there are |X| entries in TAU_XA
        // ith entry in TAU_XA contains entries for ith equivalence class of X, but partitioned with values of A
        if (fdHolds) {
            return executeWithFD();
        } else {
            return executeNoFD();
        }
    }
    
    // This is used for the OD case.
    private List<Map<Long, Set<Long>>> executeNoFD() {
        boolean valid = deriveChainsNoFD();
        if (!valid) {
            return null;
        }
        if (allChainsNoFD.size() == 1) {  // it's also unconditional
            isOrderConditional = false;
            return new ArrayList<>(Collections.singletonList(allChainsNoFD.get(0).get(1)));
        }
        //merge everything in the chains (only RHS)
        Map<Long, Set<Long>> mergedChains = new HashMap<>();
        for (List<Map<Long, Set<Long>>> chains : allChainsNoFD) {
            Map<Long, Set<Long>> currChain = chains.get(1);
            allChains.add(currChain);
            mergeChains(mergedChains, currChain);
        }

        if ((new Graph2(mergedChains)).isCyclic()) {  // this is counted as conditional
            return allChains;
        }
        return new ArrayList<>(Collections.singletonList(mergedChains));
    }
    
    private void mergeChains(Map<Long, Set<Long>> adj1, Map<Long, Set<Long>> adj2) {
        for (long key : adj2.keySet()) {
            if (!adj1.containsKey(key)) {
                adj1.put(key, new HashSet<>());
            }
            adj1.get(key).addAll(adj2.get(key));
        }
    }
    
    // This is used for the OC case.
    private List<Map<Long, Set<Long>>> executeWithFD() {
        for (ObjectBigArrayBigList<LongBigArrayBigList> sorted_TAU_LHS : TAU_XA) {// iterate over each eq. class in X
            ArrayList<Long> listRHS = getListRHSwithFD(sorted_TAU_LHS);
            if (listRHS == null) { // at least one of the chains is individually invalid, this is not even conditional
                return null;
            }
            addChain(deriveChainWithFD(listRHS));
        }
        Map<Long, Set<Long>> adjList = mergeChains(allChains);
        boolean isValid = validateCandidate(adjList);
        if (isValid) {  // it's unconditional
            isOrderConditional = false;
            return new ArrayList<>(Collections.singletonList(adjList));
        } else {  // it's conditional
            return allChains;
        }
    }
    
    private Map<Long, Set<Long>> getSingleChain() {
        Map<Long, Set<Long>> chain = new HashMap<>();
        // TAU_XA , TAU_reverseMap, B_index
        for (ObjectBigArrayBigList<LongBigArrayBigList> eqC_X : TAU_XA) {
            // one chain should come out of this for loop after we're done with the current X equivalence class
            for (LongBigArrayBigList eqC_XA : eqC_X) {
                Set<Long> BtIDs = new HashSet<>();
                for (long AtID : eqC_XA) {
                    BtIDs.add(TAU_reverseMap.get(B_index - 1).get(AtID));
                }
            }
        }
        return chain;
    }
    
    // Extract the corresponding RHS values for an OD candidate.
    private ArrayList<Long> getListRHSwithFD(ObjectBigArrayBigList<LongBigArrayBigList> sorted_TAU_LHS) {
        ArrayList<Long> listRHS = new ArrayList<>();
        for (LongBigArrayBigList XA_eqC : sorted_TAU_LHS) {
            long tIDRHS = TAU_reverseMap.get(B_index - 1).get(XA_eqC.get(0)); // this only works if an FD holds,
            // if an FD doesn't hold, then we need to iterate over all tIDs in XA_eqC, not just index 0 of it.
            
            if (listRHS.contains(tIDRHS)) {
                if (listRHS.get(listRHS.size() - 1) != tIDRHS) {
                    return null;
                }
            } else {
                listRHS.add(tIDRHS);
            }
        }
        return listRHS;
    }
    
    
    private Map<Long, Set<Long>> deriveChainWithFD(List<Long> listRHS) {
        Map<Long, Set<Long>> chain = new HashMap<>();
        for (int i = 0; i < (listRHS.size() - 1); i++) {
            chain.put(listRHS.get(i), new HashSet<>(Collections.singletonList(listRHS.get(i + 1))));
        }
        chain.put(listRHS.get(listRHS.size() - 1), new HashSet<>());
        return chain;
    }
    
    //derives chains and returns true if all individual chains were acyclic, and false otherwise
    private boolean deriveChainsNoFD() {
        allChainsNoFD = new ArrayList<>();
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
            LinkedHashSet<Long> sortedLHSeqCs = new LinkedHashSet<>();
            for (LongBigArrayBigList eqC_lhs : sorted_TAU_LHS) { // now within the eq. class on X, iterating over eq. classes on LHS
                // add
                Node curr_lhs_node = new Node();
                
                tID = eqC_lhs.get(0);
                sortedLHSeqCs.add((long) TAU_reverseMap.get(A_index - 1).get(tID));
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
//                            eqC_lhs_clone.removeAll(eqC_rhs);
                        } catch (Exception e) {
                            eqC_rhs_idx = -1;
                            //just remove the single tID which we couldn't find on the rhs eq classes
//                            eqC_lhs_clone.remove(0);
                        }
                    }
                    j++;
                }
                loopC++;
            }
            
            Graph bipGraph = new Graph();
            bipGraph.nodes = new ArrayList<>(nodesMap.values());
            
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
            
            ArrayList<Map<Long, Set<Long>>> chains = bipGraph.getChainAdjsSpecSOC(new ArrayList<>(sortedLHSeqCs));
            if (chains == null) {
                return false;
            }
            allChainsNoFD.add(chains);
        }
        return true;
    }
    
    
    private boolean validateCandidate(Map<Long, Set<Long>> adjList) {
        Graph2 graph = new Graph2(adjList);
        return (!graph.isCyclic());
    }
    
    private void addChain(Map<Long, Set<Long>> newChain) {
        allChains.add(newChain);
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
    
    
    private Map<Long, Set<Long>> mergeChains(List<Map<Long, Set<Long>>> allChains) {
        Map<Long, Set<Long>> merged = new HashMap<>();
        for (Map<Long, Set<Long>> chain : allChains) {
            for (Long key : chain.keySet()) {
                if (!merged.containsKey(key)) {
                    merged.put(key, new HashSet<>());
                }
                merged.get(key).addAll(chain.get(key));
            }
        }
        return merged;
    }
    
    
}