package od.metanome.types;

import java.util.Comparator;

import od.metanome.sorting.partitions.RowIndexedValue;

public abstract class Datatype {
    public static enum type {
        LONG, DOUBLE, DATE, STRING
    }

    Comparator<?> indexedComparator;
    type specificType;

    @SuppressWarnings("unchecked")
    public Comparator<RowIndexedValue> getIndexedComparator() {
        return (Comparator<RowIndexedValue>) this.indexedComparator;
    }

    public void setIndexedComparator(final Comparator<RowIndexedValue> indexedComparator) {
        this.indexedComparator = indexedComparator;
    }

    public type getSpecificType() {
        return this.specificType;
    }

    public void setSpecificType(final type specificType) {
        this.specificType = specificType;
    }


}

