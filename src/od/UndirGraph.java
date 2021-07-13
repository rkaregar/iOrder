package od;

// A Java Program to detect cycle in an undirected graph
import java.io.*;
import java.util.*;

// This class represents a directed graph using adjacency list
// representation
class UndirGraph
{
    private int V;   // No. of vertices
    private Map<Long, Set<Long>> adj;
    // Constructor
    UndirGraph(Map<Long, Set<Long>> adj) {
        this.adj = adj;
    }

    // A recursive function that uses visited[] and parent to detect
    // cycle in subgraph reachable from vertex v.
    Boolean isCyclicUtil(long v, Map<Long, Boolean> visited, long parent)
    {
        // Mark the current node as visited
        visited.put(v,true);
        Long i;

        // Recur for all the vertices adjacent to this vertex
        Iterator<Long> it = adj.get(v).iterator();
        while (it.hasNext())
        {
            i = it.next();

            // If an adjacent is not visited, then recur for that
            // adjacent
            if (!visited.get(i))
            {
                if (isCyclicUtil(i, visited, v))
                    return true;
            }

            // If an adjacent is visited and not parent of current
            // vertex, then there is a cycle.
            else if (i != parent)
                return true;
        }
        return false;
    }

    // Returns true if the graph contains a cycle, else false.
    Boolean isCyclic() {
        // Mark all the vertices as not visited and not part of
        // recursion stack
        Map<Long, Boolean> visited = new HashMap<>();
        for (long key : adj.keySet()) {
            visited.put(key, false);
        }

        // Call the recursive helper function to detect cycle in
        // different DFS trees
        for (long key : adj.keySet()) {
            if (!visited.get(key)) {
                if (isCyclicUtil(key, visited, -1)) {
                    return true;
                }
            }
        }
        return false;
    }
}