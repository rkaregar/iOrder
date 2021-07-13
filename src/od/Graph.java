package od;

import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.lang.reflect.Array;
import java.util.*;

public class Graph {
    List<Node> nodes;
    int V;
    private List<Integer> childDeg2Cnt;
    public List<List<Integer>> adj;
    public static Boolean statAllZeros = true;
    public static int nonZeroCnt = 0;
    private List<Map<Long, Integer>> tIDToIdx;

    // create list of hypernodes (each node on the diameter gets one hypernode that it's connected to)
    private List<Map<Long, List<Long>>> hyperNodes = new ArrayList<>();
    public void initialize() {
        hyperNodes.add(new HashMap<>());
        hyperNodes.add(new HashMap<>());
        childDeg2Cnt = new ArrayList<>(V);
        V = nodes.size();
        adj = new ArrayList<>(V);

        int idx = 0;
        tIDToIdx = new ArrayList<>();
        tIDToIdx.add(new HashMap<>());
        tIDToIdx.add(new HashMap<>());
        for (Node node : nodes){
            int nodeSide = 0;
            if(node.name.charAt(0) == 'r'){
                nodeSide = 1;
            }
            tIDToIdx.get(nodeSide).put(node.tID, idx);
            childDeg2Cnt.add(0);
            adj.add(new LinkedList<>());
            if (node.status == 1)
                for (Edge edge: node.connections){
                    if (edge.end.status == 1) // end node status check
                        addEdge(idx, nodes.indexOf(edge.end));
                }
            else if(node.status == 0){
                Node parentNode = nodes.get(nodes.indexOf(node.connections.get(0).end)); // ideally get the tID of the parent node and put that instead
                int parentNodeSide = 0;
                if(parentNode.name.charAt(0) == 'r'){
                    parentNodeSide = 1;
                }
                if(!hyperNodes.get(parentNodeSide).containsKey(parentNode.tID)){
                    hyperNodes.get(parentNodeSide).put(parentNode.tID, new ArrayList<>());
                }
                hyperNodes.get(parentNodeSide).get(parentNode.tID).add(nodes.get(idx).tID);
            }
            else{
                System.out.println("Error in node.status values");
            }
            idx++;
        } // check that adj is created correctly
    }
    // This function is a variation of DFSUtil() in
    // https://www.geeksforgeeks.org/archives/18212
    Boolean isCyclicUtil(int v, Boolean[] visited, int parent)
    {
        // Mark the current node as visited
        visited[v] = true;
        Integer i;
        // Recur for all the vertices adjacent to this vertex (children)
        Iterator<Integer> it = adj.get(v).iterator();
        while (it.hasNext())
        {
            i = it.next();

            if (!visited[i])
            {
                if (isCyclicUtil(i, visited, v))
                    return true;
            }

            else if (i != parent)
                return true;
        }
        return false;
    }
    
    Boolean isCyclic()
    {
        Boolean visited[] = new Boolean[V];
        for (int i = 0; i < V; i++) {
            if (adj.get(i).size() > 2){
                return true;
            }
            visited[i] = false;
        }

        for (int u = 0; u < V; u++)
            if (!visited[u])
                if (isCyclicUtil(u, visited, -1))
                    return true;

        boolean allZeros = true;
        int nZC = 0;
        for (int i = 0; i < V ; i++){
            if(adj.get(i).size() > 0) {
                allZeros = false;
                nZC++;
            }
        }
        statAllZeros = allZeros;
        nonZeroCnt = nZC;
        return false;
    }

    public void writeAdjListToFile(String lhsName, String rhsName, String contextName, int L, boolean cycleFree, int eqIdx) throws IOException {
        String A_name = lhsName;
        String B_name = rhsName;
        String context_name = contextName;
        String fileAddrChainStats = MainClass.datasetName + " Adj Stats/Level " + L + "/" + context_name + "---" + A_name + "--" + B_name + ".csv";
        FileWriter fw = null;

        fw = new FileWriter(fileAddrChainStats, true);
        PrintWriter out = new PrintWriter(fw);
        String delim = ",";
        out.println("X" + delim + "A" + delim + "B" + delim + "X eq. cls ID" + delim + "Cycle Free?" + delim +
                "non-zero nodes" + delim + "src tID" + delim + "src node name" + delim + "dst tID list");
        for (int node_id = 0; node_id < adj.size() ; node_id++) {
            out.print(context_name);
            out.print(delim);
            out.print(A_name);
            out.print(delim);
            out.print(B_name);
            out.print(delim);
            out.print(eqIdx); // equivalence class ID for contextName
            out.print(delim);
            out.print(cycleFree);
            out.print(delim);
            out.print(Graph.nonZeroCnt);
            out.print(delim);
            out.print(nodes.get(node_id).tID);
            out.print(delim);
            out.print(nodes.get(node_id).name);
            out.print(delim);
            String arrayStr = Arrays.toString(nodes.get(node_id).getConnectedtIDs().toArray());
            String toPrint = arrayStr.replaceAll(",", ";");
            out.println(toPrint);
        }
        out.flush();
        out.close();
        fw.close();
    }

    private void addEdge(int source, int dest) {
        adj.get(source).add(dest);
    }

    public void removeNode(Node node){
        Node endNode;
        for (Edge edge: node.connections){
            endNode = edge.end;
            adj.get(nodes.indexOf(endNode)).remove(new Integer(nodes.indexOf(node)));
            adj.get(nodes.indexOf(node)).remove(new Integer(nodes.indexOf(endNode)));
        }
        nodes.remove(node);
    }


    // this function takes chain(s) from both sides of ONE equivalence class
    // and it returns an array containing two hashmaps (one for each side)
    // each map is an adjacency list produced to represent the sequence of things in a chain

    public ArrayList<ArrayList<Map<Long, Set<Long>>>> convertToAdjs(ArrayList<List<List<List<Long>>>> allChains)
    {
        ArrayList<ArrayList<Map<Long, Set<Long>>>> sidesAdjs = new ArrayList<>();
        sidesAdjs.add(new ArrayList<>()); //add entry (map) for LHS
        sidesAdjs.add(new ArrayList<>()); //add entry (map) for RHS
        int side = 0;
        for (List<List<List<Long>>> chains: allChains){ // each "chains" is a side (RHS/LHS)
            ArrayList<Map<Long, Set<Long>>> currSide = sidesAdjs.get(side);
            for(List<List<Long>> chain: chains){ //every chain is what you got
                currSide.add(new HashMap<>()); //add entry (map) for this particular chain

                for(int i = 0; i < chain.size(); i++){
                    List<Long> currNodes = chain.get(i);
                    List<Long> nextNodes;
                    try{
                        nextNodes = chain.get(i+1);
                    }catch(Exception E){
                        nextNodes = new ArrayList<>();
                    }
                    for(Long currtID: currNodes){
                        currSide.get(currSide.size()-1).put(currtID, new HashSet<>());
                        for (Long nexttID: nextNodes){
                            currSide.get(currSide.size()-1).get(currtID).add(nexttID);
                        }
                    }
                }
            }
            side = 1; // moving on to handling the RHS chains
        }
        ArrayList<ArrayList<Map<Long, Set<Long>>>> finalSidesAdjs = new ArrayList<>();
        for(int i = 0; i < sidesAdjs.get(0).size(); i++){
            finalSidesAdjs.add(new ArrayList<>());
            finalSidesAdjs.get(i).add(sidesAdjs.get(0).get(i));
            finalSidesAdjs.get(i).add(sidesAdjs.get(1).get(i));
        }
        return finalSidesAdjs;
    }

    public ArrayList<ArrayList<Map<Long, Set<Long>>>> getChainAdjs(){
        List<List<List<Long>>> chainsA = new ArrayList<>();
        List<List<List<Long>>> chainsB = new ArrayList<>();

        ArrayList<List<List<List<Long>>>> sidesChains = new ArrayList<>();
        sidesChains.add(chainsA);
        sidesChains.add(chainsB);
        // finding singleton nodes in the adj list:
        ArrayList<Integer> singles = new ArrayList<>();
        for (int i = 0 ; i < V; i++){
            if (adj.get(i).size() == 1){
                singles.add(i);
            }
        }

        ArrayList<ArrayList<List<Long>>> currSidesChain;
        int chainIdx = 0; // keeps index of the last chain in the chains, so we can add to it
        int currNodeIdx;

        while(singles.size() > 0){
            long[] prevNodetID = new long[] {-1, -1};
            long[] currNodetID = new long[] {-1, -1};
            int side = 0;
            currNodeIdx = singles.get(0);
            currSidesChain = new ArrayList();
            currSidesChain.add(new ArrayList<>());
            currSidesChain.add(new ArrayList<>());

            singles.remove(0);

            // check what side this node belongs to
            Node currNode = nodes.get(currNodeIdx);
            if(currNode.name.charAt(0) == 'r'){
                side = 1;
            }
            currNodetID[side] = currNode.tID;
            currSidesChain.get(side).add(Arrays.asList(currNode.tID));
            if(hyperNodes.get(side).containsKey(currNode.tID)){
                currSidesChain.get(side ^ 1).add(hyperNodes.get(side).get(currNode.tID));
            }
            int nextNodeIdx = adj.get(currNodeIdx).get(0);
            while(nextNodeIdx != -1){ // set nextNode to -1 when you reach the next singleton node
                side = side ^ 1;
                // add node to the corresponding chain
                currSidesChain.get(side).add(Arrays.asList(nodes.get(nextNodeIdx).tID));
                // need to also add the node's hypernode if it has any:
                if(hyperNodes.get(side).containsKey(nodes.get(nextNodeIdx).tID)){ // if this node has an hypernode, it has to be added to the other side (hence the XOR). To avoid having to deal with sets,
                    currSidesChain.get(side ^ 1).add(hyperNodes.get(side).get(nodes.get(nextNodeIdx).tID));
                }
                //
                if(adj.get(nextNodeIdx).size() == 1){
                    singles.remove(new Integer(nextNodeIdx));
                    nextNodeIdx = -1;
                }
                else{
                    List<Integer> conns = adj.get(nextNodeIdx);// make sure that you're not assigning the previous node as the next node and just going back and forth forever :D
                    conns.remove(new Integer(currNodeIdx));
                    currNodeIdx = nextNodeIdx;
                    nextNodeIdx = conns.get(0);
                }
            }

            sidesChains.get(0).add(new ArrayList<> (currSidesChain.get(0)));
            sidesChains.get(1).add(new ArrayList<> (currSidesChain.get(1)));
        }

        ArrayList<ArrayList<Map<Long, Set<Long>>>> sidesChainsAdjs = convertToAdjs(sidesChains);

        return sidesChainsAdjs; // contains two lists. One for LHS (at index 0) and one fore RHS (at index 1)
    }

    public ArrayList<Map<Long, Set<Long>>>  getChainAdjsSpecSOC(ArrayList<Long> sortedLHSeqCs){

        ArrayList<Integer> unvisitedNodeIndexes = new ArrayList<>();
        for (int i = 0; i < V; i++){
            unvisitedNodeIndexes.add(new Integer(i));
        }

        Map<Long, Integer> LHSeqCtoChainIndex = new HashMap<>();
        List<List<List<Long>>> chainsA = new ArrayList<>();
        List<List<List<Long>>> chainsB = new ArrayList<>();

        ArrayList<List<List<List<Long>>>> sidesChains = new ArrayList<>();
        sidesChains.add(chainsA);
        sidesChains.add(chainsB);
        // finding singleton nodes in the adj list:
        ArrayList<Integer> singles = new ArrayList<>();
        for (int i = 0 ; i < V; i++){
            if (adj.get(i).size() == 1){
                singles.add(i);
            }
        }

        ArrayList<ArrayList<List<Long>>> currSidesChain;

        int chainIdx = 0; // keeps index of the last chain in the chains, so we can add to it
        int currNodeIdx;

        while(singles.size() > 0){
            long[] prevNodetID = new long[] {-1, -1};
            long[] currNodetID = new long[] {-1, -1};
            int side = 0;
            currNodeIdx = singles.get(0);
            unvisitedNodeIndexes.remove(new Integer(currNodeIdx));
            currSidesChain = new ArrayList();
            currSidesChain.add(new ArrayList<>());
            currSidesChain.add(new ArrayList<>());

            singles.remove(0);

            // check what side this node belongs to
            Node currNode = nodes.get(currNodeIdx);

            if(currNode.name.charAt(0) == 'r'){
                side = 1;
            }
            currNodetID[side] = currNode.tID;
            currSidesChain.get(side).add(Arrays.asList(currNode.tID));
            if(hyperNodes.get(side).containsKey(currNode.tID)){ // if this node has an hypernode, it has to be added to the other side (hence the XOR). To avoid having to deal with sets,
                // I'm storing a hypernode as a single negative value of the tID of its parent, so it can be a flag for being a hypernode and I can retrieve it later on.
                currSidesChain.get(side ^ 1).add(hyperNodes.get(side).get(currNode.tID));
                for (Long tID: hyperNodes.get(side).get(currNode.tID)){
                    unvisitedNodeIndexes.remove(new Integer(tIDToIdx.get(side^1).get(tID)));
                }
            }
            
            int nextNodeIdx = adj.get(currNodeIdx).get(0);
            while(nextNodeIdx != -1){ // set nextNode to -1 when you reach the next singleton node
                unvisitedNodeIndexes.remove(new Integer(nextNodeIdx));
                side = side ^ 1;
                // add node to the corresponding chain
                currSidesChain.get(side).add(Arrays.asList(nodes.get(nextNodeIdx).tID)); //new long[] {nodes.get(nextNodeIdx).tID});
                // need to also add the node's hypernode if it has any:
                if(hyperNodes.get(side).containsKey(nodes.get(nextNodeIdx).tID)){ // if this node has a hypernode, it has to be added to the other side (hence the XOR). To avoid having to deal with sets,
                    // I'm storing a hypernode as a single negative value of the tID of its parent, so it can be a flag for being a hypernode and I can retrieve it later on.
                    currSidesChain.get(side ^ 1).add(hyperNodes.get(side).get(nodes.get(nextNodeIdx).tID));
                    for (Long tID: hyperNodes.get(side).get(nodes.get(nextNodeIdx).tID)){
                        unvisitedNodeIndexes.remove(new Integer(tIDToIdx.get(side^1).get(tID)));
                    }
                }
                //
                if(adj.get(nextNodeIdx).size() == 1){
                    singles.remove(new Integer(nextNodeIdx));
                    nextNodeIdx = -1;
                    //this node also needs to be removed from singles
                }
                else{
                    List<Integer> conns = adj.get(nextNodeIdx); // make sure that you're not assigning the previous node as the next node and just going back and forth forever :D
                    conns.remove(new Integer(currNodeIdx));
                    currNodeIdx = nextNodeIdx;
                    nextNodeIdx = conns.get(0);
                }
            } // adding of one chain for each side has ended

            if(getRankOftIDMin(currSidesChain.get(0).get(0), sortedLHSeqCs) > getRankOftIDMin(currSidesChain.get(0).get(1), sortedLHSeqCs)){
                Collections.reverse(currSidesChain.get(0));
                Collections.reverse(currSidesChain.get(1));
            }
            int minRankIdx = sortedLHSeqCs.size();
            for(List longList: currSidesChain.get(0)){
                int tmpMinRank = getRankOftIDMin(longList, sortedLHSeqCs);
                if(minRankIdx > tmpMinRank){
                    minRankIdx = tmpMinRank;
                }
            }
            LHSeqCtoChainIndex.put(sortedLHSeqCs.get(minRankIdx), sidesChains.get(0).size());
            sidesChains.get(0).add(new ArrayList<> (currSidesChain.get(0)));
            sidesChains.get(1).add(new ArrayList<> (currSidesChain.get(1)));
        }
        // add hypernodes that have not been visited yet:

        while(!unvisitedNodeIndexes.isEmpty()){
            Integer index = unvisitedNodeIndexes.get(0);
            Node parentNode = nodes.get(index);

            unvisitedNodeIndexes.remove(0);

            int parentNodeSide = 0;
            if(parentNode.name.charAt(0) == 'r'){
                parentNodeSide = 1;
            }
            if(hyperNodes.get(parentNodeSide).containsKey(parentNode.tID)){
                currSidesChain = new ArrayList<>();
                currSidesChain.add(new ArrayList<>());
                currSidesChain.add(new ArrayList<>());
                currSidesChain.get(parentNodeSide).add(Arrays.asList(parentNode.tID));//new long[] {parentNode.tID});
                currSidesChain.get(parentNodeSide ^ 1).add(hyperNodes.get(parentNodeSide).get(parentNode.tID));
                for(Long tID: hyperNodes.get(parentNodeSide).get(parentNode.tID)){
                    unvisitedNodeIndexes.remove(new Integer(tIDToIdx.get(parentNodeSide^1).get(tID)));
                }

                int indexOftIDMin = getRankOftIDMin(currSidesChain.get(0).get(0), sortedLHSeqCs);
                LHSeqCtoChainIndex.put(sortedLHSeqCs.get(indexOftIDMin), sidesChains.get(0).size());
                sidesChains.get(0).add(new ArrayList<>(currSidesChain.get(0)));
                sidesChains.get(1).add(new ArrayList<>(currSidesChain.get(1)));
            }

        }

        ArrayList<Map<Long, Set<Long>>> sidesChainsAdjs = convertToAdjsSpecSOC(sidesChains, sortedLHSeqCs, LHSeqCtoChainIndex);
        nodes = null;
        hyperNodes = null;
        adj = null;
        return sidesChainsAdjs; // contains two lists. One for LHS (at index 0) and one fore RHS (at index 1)
    }

    private int getRankOftIDMax(List<Long> tIDList, ArrayList<Long> sortedLHSeqCs){
        int indexOftIDMax = -1;
        for (Long tID: tIDList){
            if(sortedLHSeqCs.indexOf(tID) > indexOftIDMax){
                indexOftIDMax = sortedLHSeqCs.indexOf(tID);
            }
        }
        return indexOftIDMax;
    }

    private int getRankOftIDMin(List<Long> tIDList, ArrayList<Long> sortedLHSeqCs){
        int indexOftIDMin = sortedLHSeqCs.size();
        for (Long tID: tIDList){
            if (sortedLHSeqCs.indexOf(tID) < indexOftIDMin){
                indexOftIDMin = sortedLHSeqCs.indexOf(tID);
            }
        }
        return indexOftIDMin;
    }


    public ArrayList<Map<Long, Set<Long>>> convertToAdjsSpecSOC(ArrayList<List<List<List<Long>>>> sidesChains,
                                                                ArrayList<Long> sortedLHSeqCs, Map<Long, Integer> LHSeqCtoChainIndex)
    { //one map for LHS (index 0), one map for RHS (index 1)
        int nextIndex = 0;
        ArrayList<Map<Long, Set<Long>>> sidesAdjs = new ArrayList<>();
        sidesAdjs.add(new HashMap<>()); // add entry (map) for LHS
        sidesAdjs.add(new HashMap<>()); // add entry (map) for RHS
        int side = 0;
        ArrayList<Integer> indexSequence = new ArrayList<>();
        for (List<List<List<Long>>> chains: sidesChains){ // each "chains" is a side (RHS/LHS)
            ArrayList<Long> unvisited = new ArrayList<>(sortedLHSeqCs);
            int rhsChainCounter = 0;
            while((!unvisited.isEmpty() && side == 0) || (side == 1 && rhsChainCounter < indexSequence.size())){
                List<List<Long>> chain;
                if(side == 0){
                    chain = chains.get(LHSeqCtoChainIndex.get(unvisited.get(0)));
                    indexSequence.add(LHSeqCtoChainIndex.get(unvisited.get(0)));
                }else{
                    chain = chains.get(indexSequence.get(rhsChainCounter));
                    rhsChainCounter++;
                }
                List<Long> lastOfCurr = new ArrayList<>();// = new long[]{};
                for(int i = 0; i < chain.size(); i++){
                    List<Long> currNodes = chain.get(i);
                    lastOfCurr = currNodes;
                    List<Long> nextNodes;
                    try{
                        nextNodes = chain.get(i+1);
                    }catch(Exception E){
                        nextNodes = new ArrayList<>();//new long[]{};
                    }
                    if(side == 0 && nextNodes.size()>0) {
                        int maxPrev = getRankOftIDMax(currNodes, sortedLHSeqCs);
                        int minCurr = getRankOftIDMin(nextNodes, sortedLHSeqCs);
                        int maxCurr = getRankOftIDMax(nextNodes, sortedLHSeqCs);
                        if (minCurr <= maxPrev || maxCurr <= maxPrev) {
                            return null; // make sure to  interpret this result correctly outside this function
                        }
                    }


                    for(Long currtID: currNodes){
                        unvisited.remove(currtID);
                        sidesAdjs.get(side).put(currtID, new HashSet<>());
                        for (Long nexttID: nextNodes){
                            sidesAdjs.get(side).get(currtID).add(nexttID);
                        }
                    }
                }
                if(!unvisited.isEmpty() && side == 0) {
                    List<Long> firstOfNext = chains.get(LHSeqCtoChainIndex.get(unvisited.get(0))).get(0);
                    for (Long currtID : lastOfCurr) {
                        unvisited.remove(currtID);
                        sidesAdjs.get(side).put(currtID, new HashSet<>());
                        for (Long nexttID : firstOfNext) {
                            sidesAdjs.get(side).get(currtID).add(nexttID);
                        }
                    }
                }

                if(rhsChainCounter < indexSequence.size() && side == 1) {
                    List<Long> firstOfNext = chains.get(indexSequence.get(rhsChainCounter)).get(0);
                    for (Long currtID : lastOfCurr) {
                        sidesAdjs.get(side).put(currtID, new HashSet<>());
                        for (Long nexttID : firstOfNext) {
                            sidesAdjs.get(side).get(currtID).add(nexttID);
                        }
                    }
                }


            }


            side = 1; // moving on to handling the RHS chains
        }
        return sidesAdjs;
    }

    @Override
    public String toString() {
        return nodes.toString();
    }
}
