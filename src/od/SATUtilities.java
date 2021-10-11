// These are the auxiliary classes for the SAT reduction.

package od;

import java.util.*;

class TuplePair {
    public long a, b;
    
    public TuplePair(long a, long b) {
        this.a = a;
        this.b = b;
    }
    
    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof TuplePair)) return false;
        TuplePair tuplePair = (TuplePair) o;
        return a == tuplePair.a &&
                b == tuplePair.b;
    }
    
    @Override
    public int hashCode() {
        return Objects.hash(a, b);
    }
}

class BipartiteNode {
    public long id;
    public char side;  // either "l" or "r"
    
    public BipartiteNode(long id, char side) {
        this.id = id;
        this.side = side;
    }
    
    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof BipartiteNode)) return false;
        BipartiteNode that = (BipartiteNode) o;
        return id == that.id &&
                side == that.side;
    }
    
    @Override
    public int hashCode() {
        return Objects.hash(id, side);
    }
    
    @Override
    public String toString() {
        return id + "" + side;
    }
}
// this class is for improved storage of bipartite graph and computing connected components in it
class BipartiteGraph {
    private final List<BipartiteNode> leftNodes, rightNodes;
    private final Map<BipartiteNode, Set<BipartiteNode>> adj;
    private List<List<BipartiteNode>> connectedComponents;
    private Map<BipartiteNode, Integer> connectedComponentNumber;
    
    // the input graph is the one with the other design
    public BipartiteGraph(Graph initialGraph) {
        leftNodes = new ArrayList<>();
        rightNodes = new ArrayList<>();
        adj = new HashMap<>();
        
        for (Node node :
                initialGraph.nodes) {
            BipartiteNode bipNode;
            if (node.name.charAt(0) == 'l') {
                bipNode = new BipartiteNode(node.tID, 'l');
                leftNodes.add(bipNode);
            }
            else {
                bipNode = new BipartiteNode(node.tID, 'r');
                rightNodes.add(bipNode);
            }
            
            adj.put(bipNode, new HashSet<>());
            for (Edge neighbour : node.connections) {
                adj.get(bipNode).add(new BipartiteNode(neighbour.end.tID, neighbour.end.name.charAt(0)));
            }
        }
        computeConnectedComponents();
    }
    
    private void DFSUtil(BipartiteNode v, Set<BipartiteNode> visited, int currentCCNumber) {
        visited.add(v);
        connectedComponents.get(connectedComponents.size() - 1).add(v);
        connectedComponentNumber.put(v, currentCCNumber);
        for (BipartiteNode x :
                adj.get(v)) {
            if (!visited.contains(x))
                DFSUtil(x, visited, currentCCNumber);
        }
    }
    
    private void computeConnectedComponents() {
        connectedComponentNumber = new HashMap<>();
        int currentCCNumber = 0;
        connectedComponents = new ArrayList<>();
        Set<BipartiteNode> visited = new HashSet<>();
        for (BipartiteNode v :
                adj.keySet()) {
            if (!visited.contains(v)) {
                connectedComponents.add(new ArrayList<>());
                DFSUtil(v, visited, currentCCNumber);
                currentCCNumber += 1;
            }
        }
    }
    
    public List<List<BipartiteNode>> getConnectedComponents() {
        return connectedComponents;
    }
    
    public Map<BipartiteNode, Integer> getConnectedComponentNumber() {
        return connectedComponentNumber;
    }
    
    public Map<BipartiteNode, Set<BipartiteNode>> getAdj() {
        return adj;
    }
    
    public List<BipartiteNode> getLeftNodes() {
        return leftNodes;
    }
    
    public List<BipartiteNode> getRightNodes() {
        return rightNodes;
    }
    
    @Override
    public String toString() {
        return "SimpleGraph{" +
                "adj=" + adj +
                '}';
    }
}

// this class is for computing the connected components
class SimpleGraph {
    private Map<Long, Set<Long>> adj;
    private List<List<Long>> connectedComponents;
    
    public SimpleGraph() {
        adj = new HashMap<>();
    }
    
    public void addEdge(Long u, Long v) {
        if (!adj.containsKey(u))
            adj.put(u, new HashSet<>());
        adj.get(u).add(v);
        
        if (!adj.containsKey(v))
            adj.put(v, new HashSet<>());
        adj.get(v).add(u);
    }
    
    void DFSUtil(Long v, Set<Long> visited) {
        visited.add(v);
        connectedComponents.get(connectedComponents.size() - 1).add(v);
        for (Long x :
                adj.get(v)) {
            if (!visited.contains(x))
                DFSUtil(x, visited);
        }
    }
    
    void computeConnectedComponents() {
        connectedComponents = new ArrayList<>();
        Set<Long> visited = new HashSet<>();
        for (Long v :
                adj.keySet()) {
            if (!visited.contains(v)) {
                connectedComponents.add(new ArrayList<>());
                DFSUtil(v, visited);
            }
        }
    }
    
    public List<List<Long>> getConnectedComponents() {
        return connectedComponents;
    }
    
    public Map<Long, Set<Long>> getAdj() {
        return adj;
    }
    
    @Override
    public String toString() {
        return "SimpleGraph{" +
                "adj=" + adj +
                ", connectedComponents=" + connectedComponents +
                '}';
    }
}
