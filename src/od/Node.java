// This is the auxiliary class for nodes, used when constructing 
// graphs in the E/I and I/I cases.

package od;
import java.util.ArrayList;
import java.util.List;
import org.apache.lucene.util.OpenBitSet;
public class Node {
    public String name;
    public long tID; // a tID representing the value of the equivalence class that the node came from
    public OpenBitSet attr;
    public List<Edge> connections;
    public int status;
    public Node(){
        connections = new ArrayList<>();
        status = 1; // 1: Node stays in graph after singleton removal, 0: Node should get removed in the singleton removal process
    }

    public ArrayList<Long> getConnectedtIDs(){
        ArrayList<Long> conntIDs = new ArrayList<>();
        for (int i = 0; i < connections.size() ; i++){
            conntIDs.add(connections.get(i).end.tID);
        }
        return conntIDs;
    }

    @Override
    public String toString() {
        StringBuilder res = new StringBuilder(name + ", " + tID + ": [");
        for (Edge e :
                connections) {
            res.append("(").append(e.start.tID).append(", ").append(e.end.tID).append(")");
        }
        return  res + "]";
    }
}
