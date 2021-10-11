// This is the auxiliary class for edge.

package od;

public class Edge {
    public Node start;
    public Node end;
    public double weight;

    public Edge reverseEdge(){
        Edge e = new Edge();
        e.end = this.start;
        e.start = this.end;
        e.weight = this.weight;
        return e;
    }

    @Override
    public String toString() {
        return "(" + start + ", " + end + ")";
    }
}
