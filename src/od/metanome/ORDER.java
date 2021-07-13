package od.metanome;

import od.MainClass;
import od.metanome.types.DatatypeString;
import de.metanome.algorithm_integration.configuration.ConfigurationSettingFileInput;
import de.metanome.algorithm_integration.input.*;
import de.metanome.algorithm_integration.result_receiver.ColumnNameMismatchException;
import it.unimi.dsi.fastutil.bytes.ByteArrays;
import it.unimi.dsi.fastutil.objects.Object2ObjectOpenCustomHashMap;

import java.io.*;
import java.text.ParseException;
import java.util.*;
import java.util.Map.Entry;

import org.apache.commons.lang3.time.DateUtils;

import de.metanome.algorithm_integration.AlgorithmConfigurationException;
import de.metanome.algorithm_integration.AlgorithmExecutionException;
import de.metanome.algorithm_integration.ColumnIdentifier;
import de.metanome.algorithm_integration.ColumnPermutation;
import de.metanome.algorithm_integration.algorithm_types.OrderDependencyAlgorithm;
import de.metanome.algorithm_integration.algorithm_types.RelationalInputParameterAlgorithm;
import de.metanome.algorithm_integration.configuration.ConfigurationRequirement;
import de.metanome.algorithm_integration.configuration.ConfigurationRequirementRelationalInput;
import de.metanome.algorithm_integration.result_receiver.CouldNotReceiveResultException;
import de.metanome.algorithm_integration.result_receiver.OrderDependencyResultReceiver;
import de.metanome.algorithm_integration.results.OrderDependency;
import od.metanome.measurements.Statistics;
import od.metanome.sorting.partitions.RowIndexedDateValue;
import od.metanome.sorting.partitions.RowIndexedDoubleValue;
import od.metanome.sorting.partitions.RowIndexedLongValue;
import od.metanome.sorting.partitions.RowIndexedStringValue;
import od.metanome.sorting.partitions.RowIndexedValue;
import od.metanome.sorting.partitions.SortedPartition;
import od.metanome.sorting.partitions.SortedPartitionCreator;
import od.metanome.types.ByteArrayPermutations;
import od.metanome.types.Datatype;
import od.metanome.types.TypeInferrer;
import od.metanome.extra.CollectionUtils;

public class ORDER implements OrderDependencyAlgorithm, RelationalInputParameterAlgorithm {

    protected OrderDependencyResultReceiver resultReceiver;
    protected String tableName;
    protected List<String> columnNames;
    protected int[] columnIndices;
    protected Statistics statistics;
    protected int partitionCacheSize = 0;

    List<List<RowIndexedValue>> dataByColumns;
    List<Datatype> types;

    public int numRows;
    public int level;

    Map<byte[], SortedPartition> permutationToPartition;
    Map<byte[], List<byte[]>> prefixBlocks;

    // should write out all dependencies when dependencyBatchLimit is reached
    
    public enum ConfigIdentifier {
        RELATIONAL_INPUT
    }

    @Override
    public ArrayList<ConfigurationRequirement<?>> getConfigurationRequirements() {
        final ArrayList<ConfigurationRequirement> config = new ArrayList<ConfigurationRequirement>(3);
        config.add(new ConfigurationRequirementRelationalInput(ORDER.ConfigIdentifier.RELATIONAL_INPUT.name()));
        return null;
    }

    @Override
    public void execute() throws AlgorithmExecutionException {
        try {
            this.initialize();
        } catch (final InputGenerationException i) {
            throw new AlgorithmConfigurationException("Could not initialize ORDER: " + i.getMessage(), i);
        } catch (FileNotFoundException e) {
            throw new AlgorithmConfigurationException("Could not initialize ORDER: " + e.getMessage(), e);
        }
    }

    @Override
    public String getAuthors() {
        return null;
    }

    @Override
    public String getDescription() {
        return null;
    }

    protected String prettyPrintPrefixBlocks() {
        final StringBuilder sb = new StringBuilder();

        for (final Entry<byte[], List<byte[]>> samePrefix : this.prefixBlocks.entrySet()) {
            sb.append("\n");
            sb.append(ByteArrayPermutations.permutationToIntegerString(samePrefix.getKey()));
            sb.append(" := ");
            for (final byte[] samePrefixList : samePrefix.getValue()) {
                sb.append(ByteArrayPermutations.permutationToIntegerString(samePrefixList));
            }
        }
        return sb.toString();
    }

    private void setInput() throws FileNotFoundException, InputIterationException {

        char QUOTE_CHAR = '\'';
        char SEPARATOR = ',';
        char ESCAPE = '\\';
        boolean STRICT_QUOTES = false;
        boolean IGNORE_LEADING_WHITESPACES = true;
        boolean HAS_HEADER = true;
        int SKIP_LINES = 0;
        boolean skipDifferingLines = false;

        ConfigurationSettingFileInput setting = new ConfigurationSettingFileInput("unique_name")
                .setSeparatorChar(String.valueOf(SEPARATOR))
                .setHeader(HAS_HEADER)
                .setIgnoreLeadingWhiteSpace(IGNORE_LEADING_WHITESPACES)
                .setStrictQuotes(STRICT_QUOTES)
                .setEscapeChar(String.valueOf(ESCAPE))
                .setQuoteChar(String.valueOf(QUOTE_CHAR))
                .setSkipLines(SKIP_LINES)
                .setNullValue("null")
                .setSkipDifferingLines(skipDifferingLines);

        File inputFile = new File(MainClass.DatasetFileName);

        FileIterator fileIterator = new FileIterator(inputFile.getName(), new FileReader(inputFile), setting);

    }

    protected void initialize() throws AlgorithmExecutionException, FileNotFoundException {

        this.statistics = new Statistics("ORDER");
        
        this.tableName = "tbl";
        this.loadData();

        this.initializePartitions();

    }

    protected void inferTypes() throws InputGenerationException {
    }

    protected void loadData() throws InputIterationException, InputGenerationException {
        
        String csvFile = MainClass.DatasetFileName;
        BufferedReader br = null;
        String line = "";

        try {
            br = new BufferedReader(new FileReader(csvFile));

            //firs line is header
            line = br.readLine();
            String[] attributes = line.split(MainClass.cvsSplitBy);

            columnNames = new ArrayList<String>();

            long columnCount = 0;
            for(String attributeName : attributes){
                if(columnCount < MainClass.MaxColumnNumber) {
                    columnNames.add(attributeName);
                    columnCount ++;
                }
            }

            // get column indices
            this.columnIndices = new int[this.columnNames.size()];
            for (int i = 0; i < this.columnNames.size(); i++) {
                this.columnIndices[i] = i;
            }

            this.dataByColumns = new ArrayList<List<RowIndexedValue>>();

            for (int i = 0; i < this.columnIndices.length; i++) {
                this.dataByColumns.add(new ArrayList<RowIndexedValue>());
            }

            this.types = new ArrayList<Datatype>();
            for(int i = 0; i<columnNames.size(); i ++){
                this.types.add(new DatatypeString(null));
            }

            long tupleId = 0;

            while ( ((line = br.readLine()) != null) && (tupleId < MainClass.MaxRowNumber)) {

                String[] tuples = line.split(MainClass.cvsSplitBy);

                List<String> currentRow = new ArrayList<String>();

                long columnCountForThisRow = 0;
                for(String tupleValue : tuples){
                    if(columnCountForThisRow < MainClass.MaxColumnNumber) {
                        currentRow.add(tupleValue);
                        columnCountForThisRow++;
                    }
                }

                for (final int column : this.columnIndices) {
                    this.storeData(tupleId, currentRow, column);
                }
                tupleId++;
                this.numRows++;
            }

            if(MainClass.FirstTimeRun) {
                System.out.println("# ROW    : " + numRows);
                System.out.println("# COLUMN : " + columnNames.size());
                System.out.println("");
            }

        } catch (FileNotFoundException e) {
            System.out.println("Error");
            e.printStackTrace();
        } catch (IOException e) {
            System.out.println("Error");
            e.printStackTrace();
        } catch (final Exception e) {
            throw new InputGenerationException("Error while loading data.", e);
        }
        finally {
            if (br != null) {
                try {
                    br.close();
                } catch (IOException e) {
                    System.out.println("Error");
                    e.printStackTrace();
                }
            }
        }

        if (this.dataByColumns == null || this.dataByColumns.isEmpty()) {
            throw new InputGenerationException("Did not find any data in " + this.tableName + ".");
        }

    }

    private void storeData(final long tupleId, final List<String> currentRow, final int column)
            throws ParseException {

        final String stringValue = currentRow.get(column);
        switch (this.types.get(column).getSpecificType()) {
            case DOUBLE:
                final Double doubleValue = (stringValue == null) ? null : Double.parseDouble(stringValue);
                this.dataByColumns.get(column).add(new RowIndexedDoubleValue(tupleId, doubleValue));
                break;
            case DATE:
                final Date dateValue =
                        (stringValue == null) ? null : DateUtils.parseDate(stringValue,
                                TypeInferrer.dateFormats);
                this.dataByColumns.get(column).add(new RowIndexedDateValue(tupleId, dateValue));
                break;
            case LONG:
                final Long longValue = (stringValue == null) ? null : Long.parseLong(stringValue);
                this.dataByColumns.get(column).add(new RowIndexedLongValue(tupleId, longValue));
                break;
            case STRING:
                this.dataByColumns.get(column).add(new RowIndexedStringValue(tupleId, stringValue));
                break;
            default:
                this.dataByColumns.get(column).add(new RowIndexedStringValue(tupleId, stringValue));
                break;
        }
    }

    protected void initializePartitions() throws AlgorithmExecutionException {
        this.permutationToPartition = new Object2ObjectOpenCustomHashMap<>(ByteArrays.HASH_STRATEGY);

        // create partitions for level 1
        for (final int columnIndex : this.columnIndices) {
            final byte[] singleColumnPermutation = {(byte) columnIndex};

            final SortedPartition partition =
                    SortedPartitionCreator.createPartition(this.dataByColumns.get(columnIndex),
                            this.types.get(columnIndex));

            this.permutationToPartition.put(singleColumnPermutation, partition);
        }

    }

    public String permutationToColumnNames(final byte[] permutation) {
        if (permutation.length == 0) {
            return "[]";
        }
        final int[] colIndices = new int[permutation.length];
        final StringBuilder sb = new StringBuilder();
        sb.append("[");
        for (int i = 0; i < colIndices.length; i++) {
            sb.append(this.columnNames.get(permutation[i]));
            sb.append(",");
        }
        sb.deleteCharAt(sb.length() - 1);
        sb.append("]");
        return sb.toString();
    }

    public int numberOfOrder = 0;

    public void signalFoundOrderDependency(final byte[] lhs, final byte[] rhs,
                                           final OrderDependency.ComparisonOperator comparisonOperator,
                                           final OrderDependency.OrderType orderType) {
        final OrderDependency orderDependency =
                new OrderDependency(new ColumnPermutation(new ColumnIdentifier(this.tableName,
                        this.permutationToColumnNames(lhs))), new ColumnPermutation(new ColumnIdentifier(
                        this.tableName, this.permutationToColumnNames(rhs))), orderType, comparisonOperator);
        numberOfOrder ++;

        if(MainClass.FirstTimeRun) {
            MakeFDs(orderDependency);
            MakeOrderComps(orderDependency);
        }
    }

    @Override
    public void setResultReceiver(final OrderDependencyResultReceiver resultReceiver) {
        this.resultReceiver = resultReceiver;
    }

    @Override
    public void setRelationalInputConfigurationValue(final String identifier,
                                                     final RelationalInputGenerator... values) throws AlgorithmConfigurationException {
        if (identifier.equals(ORDER.ConfigIdentifier.RELATIONAL_INPUT.name())) {
        } else {
            throw new AlgorithmConfigurationException("Unknown configuration identifier: " + identifier
                    + "->" + CollectionUtils.concat(values, ","));
        }
    }

    public List<String> FDList = new ArrayList<String>();

    private void MakeFDs(OrderDependency orderDependency){

        ColumnIdentifier lhsColumnIdentifier = orderDependency.getLhs().getColumnIdentifiers().get(0);
        String lhsOriginal = lhsColumnIdentifier.getColumnIdentifier();
        lhsOriginal = lhsOriginal.replaceAll("\\[", "");
        lhsOriginal = lhsOriginal.replaceAll("\\]", "");
        String[] lhsSS = lhsOriginal.split(",");

        List<String> lhsList = new ArrayList<String>(Arrays.asList(lhsSS));

        Collections.sort(lhsList);

        String lhsString = "";
        for(String sCol : lhsList){
            lhsString += sCol + ",";
        }

        ColumnIdentifier rhsColumnIdentifier = orderDependency.getRhs().getColumnIdentifiers().get(0);
        String rhsOriginal = rhsColumnIdentifier.getColumnIdentifier();
        rhsOriginal = rhsOriginal.replaceAll("\\[", "");
        rhsOriginal = rhsOriginal.replaceAll("\\]", "");
        String[] rhsSS = rhsOriginal.split(",");

        for(String oneRhsMember : rhsSS){
            String newFD = lhsString + " > " + oneRhsMember;
            if(!FDList.contains(newFD))
                FDList.add(newFD);
        }
    }

    public List<String> OrderCompList = new ArrayList<String>();

    private void MakeOrderComps(OrderDependency orderDependency){

        ColumnIdentifier lhsColumnIdentifier = orderDependency.getLhs().getColumnIdentifiers().get(0);
        String lhsOriginal = lhsColumnIdentifier.getColumnIdentifier();
        lhsOriginal = lhsOriginal.replaceAll("\\[", "");
        lhsOriginal = lhsOriginal.replaceAll("\\]", "");
        String[] lhsSS = lhsOriginal.split(",");

        ColumnIdentifier rhsColumnIdentifier = orderDependency.getRhs().getColumnIdentifiers().get(0);
        String rhsOriginal = rhsColumnIdentifier.getColumnIdentifier();
        rhsOriginal = rhsOriginal.replaceAll("\\[", "");
        rhsOriginal = rhsOriginal.replaceAll("\\]", "");
        String[] rhsSS = rhsOriginal.split(",");


        for(int i = 0; i < lhsSS.length; i ++){
            for(int j=0; j<rhsSS.length; j ++){

                Set<String> simSet = new HashSet<String>();
                for(int ii = 0; ii<i; ii ++){
                    simSet.add(lhsSS[ii]);
                }
                for(int jj = 0; jj<j; jj ++){
                    simSet.add(rhsSS[jj]);
                }

                List<String> simList = new ArrayList<String>(simSet);
                Collections.sort(simList);

                String simString = "{";
                for(String sCol : simList){
                    simString += sCol + ",";
                }
                simString = simString + "} : ";

                List<String> doubleList = new ArrayList<String>();
                doubleList.add(lhsSS[i]);
                doubleList.add(rhsSS[j]);
                Collections.sort(doubleList);

                String doubleString = doubleList.get(0) + "~" + doubleList.get(1);

                String orderCompSim = simString + " > " + doubleString;

                if(!OrderCompList.contains(orderCompSim))
                    OrderCompList.add(orderCompSim);
            }
        }

    }

}
