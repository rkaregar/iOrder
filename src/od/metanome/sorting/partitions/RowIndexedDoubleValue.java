package od.metanome.sorting.partitions;

public class RowIndexedDoubleValue extends RowIndexedValue {
    public final Double value;

    public RowIndexedDoubleValue(final long index, final Double value) {
        this.index = index;
        this.value = value;
    }
}
