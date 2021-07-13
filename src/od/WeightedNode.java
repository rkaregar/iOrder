package od;

public class WeightedNode implements Comparable{
    private Long node;
    private Long weight;

    public WeightedNode(Long node, Long weight) {
        this.weight = weight;
        this.node = node;
    }

    public Long getWeight() {
        return weight;
    }

    public void setWeight(Long weight) {
        this.weight = weight;
    }

    public Long getNode() {
        return node;
    }

    public void setNode(Long node) {
        this.node = node;
    }


    @Override
    public int compareTo(Object o) {
        return (int)(((WeightedNode)o).getWeight() - this.getWeight());
    }

    @Override
    public String toString() {
        return "(" + node + ", " + weight + ")";
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        WeightedNode wn = (WeightedNode) obj;
        return wn.getNode().equals(this.getNode());
    }

    @Override
    public int hashCode() {
        return node.hashCode();
    }
}
