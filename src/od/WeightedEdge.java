// This is the auxiliary class for weighetd edges.

package od;

import java.io.Serializable;
import java.util.Set;

public class WeightedEdge {
    private Long dest;
    private Integer weight;
    private Set<Long> commonLHS;
    private Set<Long> commonRHS;

    public WeightedEdge(Long dest, Integer weight) {
        this.dest = dest;
        this.weight = weight;
    }

    public Set<Long> getCommonLHS() {
        return commonLHS;
    }

    public void setCommonLHS(Set<Long> commonLHS) {
        this.commonLHS = commonLHS;
    }

    public Set<Long> getCommonRHS() {
        return commonRHS;
    }

    public void setCommonRHS(Set<Long> commonRHS) {
        this.commonRHS = commonRHS;
    }

    public Long getDest() {
        return dest;
    }

    public void setDest(Long dest) {
        this.dest = dest;
    }

    public Integer getWeight() {
        return weight;
    }

    public void setWeight(Integer weight) {
        this.weight = weight;
    }

    @Override
    public String toString() {
        return "(" + this.getDest() + ", " + this.getWeight() + ")";
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        WeightedEdge we = (WeightedEdge) obj;
        return we.getDest().equals(this.getDest());
    }

    @Override
    public int hashCode() {
        return this.getDest().hashCode();
    }
}
