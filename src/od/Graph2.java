// This is the auxiliary class for updated graph structure.

package od;

import java.util.*;

public class Graph2 {
    private Map<Long, Set<Long>> adj;

    public Graph2(Map<Long, Set<Long>> adj) {
        this.adj = adj;
    }

    public boolean isCyclic(){

        Map<Long, Integer> visited = new HashMap<>();

        for(Long key: adj.keySet()){
            visited.put(key, 0);
        }
        Iterator it = visited.entrySet().iterator();
        while(it.hasNext()) {
            Map.Entry pair = (Map.Entry)it.next();
            if(visited.get(pair.getKey()) == 2){
                continue;
            }

            Long startNode = (Long)pair.getKey();
            Stack<AbstractMap.SimpleEntry<Long, Integer>> stack = new Stack<>();
            stack.push(new AbstractMap.SimpleEntry<>(startNode, 0));
            while (!stack.isEmpty()) {
                AbstractMap.SimpleEntry<Long, Integer> currNode = stack.pop();
                if(currNode.getValue() == 1){
                    visited.put(currNode.getKey(), 2);
                    continue;
                }
                visited.put(currNode.getKey(), 1);
                stack.push(new AbstractMap.SimpleEntry<>(currNode.getKey(), 1));

                Set<Long> children = adj.get(currNode.getKey());
                for (Long child : children) {
                    if (visited.get(child) == 0) {
                        stack.add(new AbstractMap.SimpleEntry<>(child, 0));
                    } else if(visited.get(child) == 1){
                        return true;
                    }
                }

            }
        }
        return false;
    }
}






















