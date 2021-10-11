// This is a helper class for candidate verification.

package od;

import it.unimi.dsi.fastutil.objects.ObjectArrayList;
import org.apache.lucene.util.OpenBitSet;

import java.io.Serializable;

public class CombinationHelper implements Serializable {
 // keeps info about current cell in lattice
    private static final long serialVersionUID = 1L;

    private OpenBitSet rhsCandidates;
    private boolean valid;

    private StrippedPartition partition;

    public CombinationHelper() {
        valid = true;
    }

    public OpenBitSet getRhsCandidates() {
        return rhsCandidates;
    }

    public void setRhsCandidates(OpenBitSet rhsCandidates) {
        this.rhsCandidates = rhsCandidates;
    }

    public StrippedPartition getPartition() {
        return partition;
    }

    public void setPartition(StrippedPartition partition) {
        this.partition = partition;
    }

    public boolean isValid() {
        return valid;
    }

    public void setInvalid() {
        this.valid = false;
        partition = null;
    }

    //OD
    private ObjectArrayList<OpenBitSet> swapCandidates;

    //OD
    public ObjectArrayList<OpenBitSet> getSwapCandidates() {
        return swapCandidates;
    }

    //OD
    public void setSwapCandidates(ObjectArrayList<OpenBitSet> swapCandidates) {
        this.swapCandidates = swapCandidates;
    }

}

