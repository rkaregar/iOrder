// This is a helper class for validating FD candidates.

package od;

import de.metanome.algorithm_integration.AlgorithmExecutionException;
import de.metanome.algorithm_integration.ColumnCombination;
import de.metanome.algorithm_integration.ColumnIdentifier;
import de.metanome.algorithm_integration.result_receiver.ColumnNameMismatchException;
import de.metanome.algorithm_integration.results.FunctionalDependency;
import it.unimi.dsi.fastutil.longs.LongBigArrayBigList;
import it.unimi.dsi.fastutil.objects.Object2ObjectOpenHashMap;
import it.unimi.dsi.fastutil.objects.ObjectArrayList;
import it.unimi.dsi.fastutil.objects.ObjectBigArrayBigList;
import org.apache.lucene.util.OpenBitSet;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

public class TaneAlgorithm {

    private Object2ObjectOpenHashMap<OpenBitSet, CombinationHelper> level0 = null;
    private Object2ObjectOpenHashMap<OpenBitSet, CombinationHelper> level1 = null;
    private Object2ObjectOpenHashMap<OpenBitSet, ObjectArrayList<OpenBitSet>> prefix_blocks = null;

    private String tableName;
    private int numberAttributes;
    private long numberTuples;
    private List<String> columnNames;
    private ObjectArrayList<ColumnIdentifier> columnIdentifiers;

    private LongBigArrayBigList tTable;

    private List<String> columnNamesList;
    private List<List<String>> rowList;

    private void fillData() {

        String csvFile = MainClass.DatasetFileName;
        BufferedReader br = null;
        String line = "";

        try {
            br = new BufferedReader(new FileReader(csvFile));

            line = br.readLine();
            String[] attributes = line.split(MainClass.cvsSplitBy);

            columnNamesList = new ArrayList<String>();

            long columnCount = 0;
            for(String attributeName : attributes){
                if(columnCount < MainClass.MaxColumnNumber) {
                    columnNamesList.add(attributeName);
                    columnCount ++;
                }
            }

            rowList = new ArrayList<List<String>>();

            long rowCount = 0;

            while ( ((line = br.readLine()) != null) && (rowCount < MainClass.MaxRowNumber)) {

                String[] tuples = line.split(MainClass.cvsSplitBy);

                List<String> row = new ArrayList<String>();

                long columnCountForThisRow = 0;
                for(String tupleValue : tuples){
                    if(columnCountForThisRow < MainClass.MaxColumnNumber) {
                        row.add(tupleValue);
                        columnCountForThisRow++;
                    }
                }
                rowList.add(row);

                rowCount ++;
            }

        } catch (FileNotFoundException e) {
            System.out.println("Error");
            e.printStackTrace();
        } catch (IOException e) {
            System.out.println("Error");
            e.printStackTrace();
        } finally {
            if (br != null) {
                try {
                    br.close();
                } catch (IOException e) {
                    System.out.println("Error");
                    e.printStackTrace();
                }
            }
        }
    }

    public void execute() throws AlgorithmExecutionException {

        long start1 = System.currentTimeMillis();

        level0 = new Object2ObjectOpenHashMap<OpenBitSet, CombinationHelper>();
        level1 = new Object2ObjectOpenHashMap<OpenBitSet, CombinationHelper>();
        prefix_blocks = new Object2ObjectOpenHashMap<OpenBitSet, ObjectArrayList<OpenBitSet>>();

        // Get information about table from database or csv file (as partitions)
        ObjectArrayList<Object2ObjectOpenHashMap<Object, LongBigArrayBigList>> partitions = loadData();
        setColumnIdentifiers(); // set columns headers
        numberAttributes = this.columnNames.size();

        // Initialize table used for stripped partition product
        tTable = new LongBigArrayBigList(numberTuples);
        for (long i = 0; i < numberTuples; i++) {
            tTable.add(-1);
        }

        // Initialize Level 0
        CombinationHelper chLevel0 = new CombinationHelper();
        OpenBitSet rhsCandidatesLevel0 = new OpenBitSet();

        rhsCandidatesLevel0.set(1, numberAttributes + 1);
        chLevel0.setRhsCandidates(rhsCandidatesLevel0);
        StrippedPartition spLevel0 = new StrippedPartition(numberTuples);
        chLevel0.setPartition(spLevel0);
        spLevel0 = null;
        level0.put(new OpenBitSet(), chLevel0);
        chLevel0 = null;

        // Initialize Level 1
        for (int i = 1; i <= numberAttributes; i++) {
            OpenBitSet combinationLevel1 = new OpenBitSet();
            combinationLevel1.set(i);

            CombinationHelper chLevel1 = new CombinationHelper();
            OpenBitSet rhsCandidatesLevel1 = new OpenBitSet();
            rhsCandidatesLevel1.set(1, numberAttributes + 1);
            chLevel1.setRhsCandidates(rhsCandidatesLevel0);

            StrippedPartition spLevel1 = new StrippedPartition(partitions.get(i - 1));
            chLevel1.setPartition(spLevel1);

            level1.put(combinationLevel1, chLevel1);
        }

        if(MainClass.FirstTimeRun) {
            System.out.println("# ROW    : " + numberTuples);
            System.out.println("# COLUMN : " + numberAttributes);
            System.out.println("");
        }

        partitions = null;

        long end1 = System.currentTimeMillis();

        int l = 1;
        while (!level1.isEmpty() && l <= numberAttributes) {

            System.out.println("L : " + l + " size : " + level1.size());

            // compute dependencies for a level
            computeDependencies();

            // prune the search space
            prune();

            // compute the combinations for the next level
            generateNextLevel();
            l++;
        }

        if(MainClass.FirstTimeRun) {
            System.out.println("# FD : " + numberOfFD);
            System.out.println("");
        }

        return;
    }

    private void generateNextLevel() {
        level0 = level1;
        level1 = null;
        System.gc();

        Object2ObjectOpenHashMap<OpenBitSet, CombinationHelper> new_level = new Object2ObjectOpenHashMap<OpenBitSet, CombinationHelper>();

        buildPrefixBlocks();

        for (ObjectArrayList<OpenBitSet> prefix_block_list : prefix_blocks.values()) {

            // continue only, if the prefix_block contains at least 2 elements
            if (prefix_block_list.size() < 2) { //refer to slides
                continue;
            }

            ObjectArrayList<OpenBitSet[]> combinations = getListCombinations(prefix_block_list);
            for (OpenBitSet[] c : combinations) {
                OpenBitSet X = (OpenBitSet) c[0].clone();
                X.or(c[1]);

                if (checkSubsets(X)) {
                    StrippedPartition st = null;
                    CombinationHelper ch = new CombinationHelper();
                    if (level0.get(c[0]).isValid() && level0.get(c[1]).isValid()) {
                        st = multiply(level0.get(c[0]).getPartition(), level0.get(c[1]).getPartition());
                    } else {
                        ch.setInvalid();
                    }
                    OpenBitSet rhsCandidates = new OpenBitSet();

                    ch.setPartition(st);
                    ch.setRhsCandidates(rhsCandidates);

                    new_level.put(X, ch);
                }
            }
        }

        level1 = new_level;
    }

    /**
     * Calculate the product of two stripped partitions and return the result as a new stripped partition.
     *
     * @param pt1: First StrippedPartition
     * @param pt2: Second StrippedPartition
     * @return A new StrippedPartition as the product of the two given StrippedPartitions.
     */
    public StrippedPartition multiply(StrippedPartition pt1, StrippedPartition pt2) {
        ObjectBigArrayBigList<LongBigArrayBigList> result = new ObjectBigArrayBigList<LongBigArrayBigList>();
        ObjectBigArrayBigList<LongBigArrayBigList> pt1List = pt1.getStrippedPartition();
        ObjectBigArrayBigList<LongBigArrayBigList> pt2List = pt2.getStrippedPartition();
        ObjectBigArrayBigList<LongBigArrayBigList> partition = new ObjectBigArrayBigList<LongBigArrayBigList>();
        long noOfElements = 0;
        // iterate over first stripped partition and fill tTable.
        for (long i = 0; i < pt1List.size64(); i++) {
            for (long tId : pt1List.get(i)) {
                tTable.set(tId, i);
            }
            partition.add(new LongBigArrayBigList());
        }
        // iterate over second stripped partition.
        for (long i = 0; i < pt2List.size64(); i++) {
            for (long t_id : pt2List.get(i)) {
                // tuple is also in an equivalence class of pt1
                if (tTable.get(t_id) != -1) {
                    partition.get(tTable.get(t_id)).add(t_id);
                }
            }
            for (long tId : pt2List.get(i)) {
                // if condition not in the paper;
                if (tTable.get(tId) != -1) {
                    if (partition.get(tTable.get(tId)).size64() > 1) {
                        LongBigArrayBigList eqClass = partition.get(tTable.get(tId));
                        result.add(eqClass);
                        noOfElements += eqClass.size64();
                    }
                    partition.set(tTable.get(tId), new LongBigArrayBigList());
                }
            }
        }
        // cleanup tTable to reuse it in the next multiplication.
        for (long i = 0; i < pt1List.size64(); i++) {
            for (long tId : pt1List.get(i)) {
                tTable.set(tId, -1);
            }
        }
        return new StrippedPartition(result, noOfElements);
    }

    /**
     * Checks whether all subsets of X (with length of X - 1) are part of the last level.
     * Only if this check return true X is added to the new level.
     *
     * @param X
     * @return
     */
    private boolean checkSubsets(OpenBitSet X) {
        boolean xIsValid = true;

        // clone of X for usage in the following loop
        OpenBitSet Xclone = (OpenBitSet) X.clone();

        for (int l = X.nextSetBit(0); l >= 0; l = X.nextSetBit(l + 1)) {
            Xclone.clear(l);
            if (!level0.containsKey(Xclone)) {
                xIsValid = false;
                break;
            }
            Xclone.set(l);
        }

        return xIsValid;
    }

    /**
     * Get all combinations, which can be built out of the elements of a prefix block
     *
     * @param list: List of OpenBitSets, which are in the same prefix block.
     * @return All combinations of the OpenBitSets.
     */
    private ObjectArrayList<OpenBitSet[]> getListCombinations(ObjectArrayList<OpenBitSet> list) {
        ObjectArrayList<OpenBitSet[]> combinations = new ObjectArrayList<OpenBitSet[]>();
        for (int a = 0; a < list.size(); a++) {
            for (int b = a + 1; b < list.size(); b++) {
                OpenBitSet[] combi = new OpenBitSet[2];
                combi[0] = list.get(a);
                combi[1] = list.get(b);
                combinations.add(combi);
            }
        }
        return combinations;
    }

    /**
     * Build the prefix blocks for a level. It is a HashMap containing the
     * prefix as a key and the corresponding attributes as  the value.
     */
    private void buildPrefixBlocks() {
        this.prefix_blocks.clear();
        for (OpenBitSet level_iter : level0.keySet()) {
            OpenBitSet prefix = getPrefix(level_iter);

            if (prefix_blocks.containsKey(prefix)) {
                prefix_blocks.get(prefix).add(level_iter);
            } else {
                ObjectArrayList<OpenBitSet> list = new ObjectArrayList<OpenBitSet>();
                list.add(level_iter);
                prefix_blocks.put(prefix, list);
            }
        }
    }

    /**
     * Get prefix of OpenBitSet by copying it and removing the last Bit.
     *
     * @param bitset
     * @return A new OpenBitSet, where the last set Bit is cleared.
     */
    private OpenBitSet getPrefix(OpenBitSet bitset) {
        OpenBitSet prefix = (OpenBitSet) bitset.clone();
        prefix.clear(getLastSetBitIndex(prefix));
        return prefix;
    }

    private long getLastSetBitIndex(OpenBitSet bitset) {
        int lastSetBit = 0;
        for (int A = bitset.nextSetBit(0); A >= 0; A = bitset.nextSetBit(A + 1)) {
            lastSetBit = A;
        }
        return lastSetBit;
    }

    /**
     * Prune the current level (level1) by removing all elements with no rhs candidates.
     * All keys are marked as invalid.
     * In case a key is found, minimal dependencies are added to the result receiver.
     *
     * @throws AlgorithmExecutionException if the result receiver cannot handle the functional dependency.
     */
    private void prune() throws AlgorithmExecutionException {
        ObjectArrayList<OpenBitSet> elementsToRemove = new ObjectArrayList<OpenBitSet>();
        for (OpenBitSet x : level1.keySet()) {
            if (level1.get(x).getRhsCandidates().isEmpty()) {
                elementsToRemove.add(x);
                continue;
            }
            // Check if x is a key. Thats the case, if the error is 0.
            // See definition of the error on page 104 of the TANE-99 paper.
            if (level1.get(x).isValid() && level1.get(x).getPartition().getError() == 0) {

                // C+(X)\X
                OpenBitSet rhsXwithoutX = (OpenBitSet) level1.get(x).getRhsCandidates().clone();
                rhsXwithoutX.andNot(x);
                for (int a = rhsXwithoutX.nextSetBit(0); a >= 0; a = rhsXwithoutX.nextSetBit(a + 1)) {
                    OpenBitSet intersect = new OpenBitSet();
                    intersect.set(1, numberAttributes + 1);

                    OpenBitSet xUnionAWithoutB = (OpenBitSet) x.clone();
                    xUnionAWithoutB.set(a);
                    for (int b = x.nextSetBit(0); b >= 0; b = x.nextSetBit(b + 1)) {
                        xUnionAWithoutB.clear(b);
                        CombinationHelper ch = level1.get(xUnionAWithoutB);
                        if (ch != null) {
                            intersect.and(ch.getRhsCandidates());
                        } else {
                            intersect = new OpenBitSet();
                            break;
                        }
                        xUnionAWithoutB.set(b);
                    }

                    if (intersect.get(a)) {
                        OpenBitSet lhs = (OpenBitSet) x.clone();
                        processFunctionalDependency(lhs, a);
                        level1.get(x).getRhsCandidates().clear(a);
                        level1.get(x).setInvalid();
                    }
                }
            }
        }
        for (OpenBitSet x : elementsToRemove) {
            level1.remove(x);
        }
    }

    /**
     * Computes the dependencies for the current level (level1).
     *
     * @throws AlgorithmExecutionException
     */
    private void computeDependencies() throws AlgorithmExecutionException {
        initializeCplusForLevel();

        // iterate through the combinations of the level
        for (OpenBitSet X : level1.keySet()) {
            if (level1.get(X).isValid()) {
                // Build the intersection between X and C_plus(X)
                OpenBitSet C_plus = level1.get(X).getRhsCandidates();
                OpenBitSet intersection = (OpenBitSet) X.clone();
                intersection.intersect(C_plus);

                // clone of X for usage in the following loop
                OpenBitSet Xclone = (OpenBitSet) X.clone();

                // iterate through all elements (A) of the intersection
                for (int A = intersection.nextSetBit(0); A >= 0; A = intersection.nextSetBit(A + 1)) {
                    Xclone.clear(A);

                    // check if X\A -> A is valid
                    StrippedPartition spXwithoutA = level0.get(Xclone).getPartition();
                    StrippedPartition spX = level1.get(X).getPartition();

                    if (spX.getError() == spXwithoutA.getError()) {
                        // found Dependency
                        OpenBitSet XwithoutA = (OpenBitSet) Xclone.clone();
                        processFunctionalDependency(XwithoutA, A);

                        // remove A from C_plus(X)
                        level1.get(X).getRhsCandidates().clear(A);

                        // remove all B in R\X from C_plus(X)
                        OpenBitSet RwithoutX = new OpenBitSet();
                        // set to R
                        RwithoutX.set(1, numberAttributes + 1);
                        // remove X
                        RwithoutX.andNot(X);

                        for (int i = RwithoutX.nextSetBit(0); i >= 0; i = RwithoutX.nextSetBit(i + 1)) {
                            level1.get(X).getRhsCandidates().clear(i);
                        }

                    }
                    Xclone.set(A);
                }
            }
        }
    }

    /**
     * Adds the FD lhs -> a to the resultReceiver and also prints the dependency.
     *
     * @param lhs: left-hand-side of the functional dependency
     * @param a:   dependent attribute. Possible values: 1 <= a <= maxAttributeNumber.
     */
    private void processFunctionalDependency(OpenBitSet lhs, int a) {
        try {
            addDependencyToResultReceiver(lhs, a);
        } catch (ColumnNameMismatchException e) {
            System.out.println("Error");
            e.printStackTrace();
        }
    }

    /**
     * Add the functional dependency to the ResultReceiver.
     *
     * @param X: A OpenBitSet representing the Columns of the determinant.
     * @param a: The number of the dependent column (starting from 1).
     */

    private int numberOfFD = 0;

    private void addDependencyToResultReceiver(OpenBitSet X, int a) throws ColumnNameMismatchException {

        ColumnIdentifier[] columns = new ColumnIdentifier[(int) X.cardinality()];
        int j = 0;
        for (int i = X.nextSetBit(0); i >= 0; i = X.nextSetBit(i + 1)) {
            columns[j++] = this.columnIdentifiers.get(i - 1);
        }
        ColumnCombination colCombination = new ColumnCombination(columns);
        FunctionalDependency fdResult = new FunctionalDependency(colCombination, columnIdentifiers.get((int) a - 1));

        numberOfFD ++;
    }

    /**
     * Initialize Cplus (resp. rhsCandidates) for each combination of the level.
     */
    private void initializeCplusForLevel() {
        for (OpenBitSet X : level1.keySet()) {

            ObjectArrayList<OpenBitSet> CxwithoutA_list = new ObjectArrayList<OpenBitSet>();

            // clone of X for usage in the following loop
            OpenBitSet Xclone = (OpenBitSet) X.clone();
            for (int A = X.nextSetBit(0); A >= 0; A = X.nextSetBit(A + 1)) {
                Xclone.clear(A);
                OpenBitSet CxwithoutA = level0.get(Xclone).getRhsCandidates();
                CxwithoutA_list.add(CxwithoutA);
                Xclone.set(A);
            }

            OpenBitSet CforX = new OpenBitSet();

            if (!CxwithoutA_list.isEmpty()) {
                CforX.set(1, numberAttributes + 1);
                for (OpenBitSet CxwithoutA : CxwithoutA_list) {
                    CforX.and(CxwithoutA);
                }
            }

            CombinationHelper ch = level1.get(X);
            ch.setRhsCandidates(CforX);
        }
    }

    private void setColumnIdentifiers() {
        this.columnIdentifiers = new ObjectArrayList<ColumnIdentifier>(this.columnNames.size());
        for (String column_name : this.columnNames) {
            columnIdentifiers.add(new ColumnIdentifier(this.tableName, column_name));
        }
    }

    private ObjectArrayList<Object2ObjectOpenHashMap<Object, LongBigArrayBigList>> loadData() {

        fillData();

        this.numberAttributes = columnNamesList.size();//input.numberOfColumns();
        this.tableName = "Table1";//input.relationName();

        this.columnNames = columnNamesList;// input.columnNames();

        ObjectArrayList<Object2ObjectOpenHashMap<Object, LongBigArrayBigList>> partitions =
                new ObjectArrayList<Object2ObjectOpenHashMap<Object, LongBigArrayBigList>>(this.numberAttributes);
        for (int i = 0; i < this.numberAttributes; i++) {
            Object2ObjectOpenHashMap<Object, LongBigArrayBigList> partition = new Object2ObjectOpenHashMap<Object, LongBigArrayBigList>();
            partitions.add(partition);
        }
        long tupleId = 0;

        //while (input.hasNext()) {
        for(int rowId=0; rowId<rowList.size(); rowId ++) {
            //List<String> row = input.next();
            List<String> row = rowList.get(rowId);

            for (int i = 0; i < this.numberAttributes; i++) {
                Object2ObjectOpenHashMap<Object, LongBigArrayBigList> partition = partitions.get(i);
                String entry = row.get(i);
                if (partition.containsKey(entry)) {
                    partition.get(entry).add(tupleId);
                } else {
                    LongBigArrayBigList newEqClass = new LongBigArrayBigList();
                    newEqClass.add(tupleId);
                    partition.put(entry, newEqClass);
                }
                ;
            }
            tupleId++;
        }


        this.numberTuples = tupleId;
        return partitions;

    }
}
