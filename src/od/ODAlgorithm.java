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


import java.io.*;
import java.util.*;


public class ODAlgorithm {
    
    private Object2ObjectOpenHashMap<OpenBitSet, CombinationHelper> level_minus1 = null;
    private Object2ObjectOpenHashMap<OpenBitSet, CombinationHelper> level0 = null;
    private Object2ObjectOpenHashMap<OpenBitSet, CombinationHelper> level1 = null;
    private Object2ObjectOpenHashMap<OpenBitSet, ObjectArrayList<OpenBitSet>> prefix_blocks = null;
    public static int flakeCount;
    private String tableName;
    public int numberAttributes;
    public long numberTuples;
    private List<String> columnNames;
    private ObjectArrayList<ColumnIdentifier> columnIdentifiers;
    
    private LongBigArrayBigList tTable;
    
    private List<String> columnNamesList;
    private List<List<String>> rowList;
    
    private boolean firstTimeWritingGeneralInfo = true; // do not append to the file if it's the first time
    private boolean firstTimeWritingValidationInfo = true; // do not append to the file if it's the first time
    
    //OD
    //for each attribute, in order, we have a list of its partition, sorted based on their values in ASC order
    ArrayList<ObjectBigArrayBigList<LongBigArrayBigList>> TAU_SortedList; //sorted partitions Tau
    List<Map<Long, Long>> TAU_reverseMap = new ArrayList<>(); // each map is <Long, Long>
    ArrayList<ObjectBigArrayBigList<Integer>> attributeValuesList;
    
    List<FDODScore> FDODScoreList;
    List<SpecialScore> SpecialScoreList;
    List<GeneralScore> GeneralScoreList;
    
    Map<OpenBitSet, Long> XScoreMap = new HashMap<OpenBitSet, Long>();
    int answerCountFD = 1;
    int answerCountOD = 1;
    
    private int numberOfFD = 0, prevFD = 0;
    private int numberOfOD = 0, prevOD = 0;
    private int numberOfEIOC_cond = 0, prevEIOC_cond = 0;
    private int numberOfEIOC_uncond = 0, prevEIOC_uncond = 0;
    private int numberOfEIOD_cond = 0, prevEIOD_cond = 0;
    private int numberOfEIOD_uncond = 0, prevEIOD_uncond = 0;
    private int numberOfIIOC_cond = 0, prevIIOCcond = 0;
    private int numberOfIIOC_uncond = 0, prevIIOCuncond = 0;
    
    private ArrayList<HashMap<Long, String>> id2Val;
    
    public void execute() throws AlgorithmExecutionException {
        
        
        FDODScoreList = new ArrayList<>();
        SpecialScoreList = new ArrayList<>();
        GeneralScoreList = new ArrayList<>();
        
        long start1 = System.currentTimeMillis();
        
        level0 = new Object2ObjectOpenHashMap<OpenBitSet, CombinationHelper>(); //prev
        level1 = new Object2ObjectOpenHashMap<OpenBitSet, CombinationHelper>(); //curr
        prefix_blocks = new Object2ObjectOpenHashMap<OpenBitSet, ObjectArrayList<OpenBitSet>>();
        
        // Get information about table from database or csv file
        ObjectArrayList<Object2ObjectOpenHashMap<Object, LongBigArrayBigList>> partitions = loadData();
        setColumnIdentifiers();
        numberAttributes = this.columnNames.size();
        
        // Initialize table used for stripped partition product
        tTable = new LongBigArrayBigList(numberTuples);
        for (long i = 0; i < numberTuples; i++) {
            tTable.add(-1);
        }
        
        //Begin Initialize Level 0
        CombinationHelper chLevel0 = new CombinationHelper();
        
        OpenBitSet rhsCandidatesLevel0 = new OpenBitSet();
        rhsCandidatesLevel0.set(1, numberAttributes + 1);
        chLevel0.setRhsCandidates(rhsCandidatesLevel0);
        
        ObjectArrayList<OpenBitSet> swapCandidatesLevel0 = new ObjectArrayList<OpenBitSet>();//the C_s is empty for L0
        chLevel0.setSwapCandidates(swapCandidatesLevel0);
        
        StrippedPartition spLevel0 = new StrippedPartition(numberTuples);
        chLevel0.setPartition(spLevel0);
        
        spLevel0 = null;
        level0.put(new OpenBitSet(), chLevel0);
        chLevel0 = null;
        //End Initialize Level 0
        
        //OD
        TAU_SortedList = new ArrayList<ObjectBigArrayBigList<LongBigArrayBigList>>();
        attributeValuesList = new ArrayList<ObjectBigArrayBigList<Integer>>();
        
        //Begin Initialize Level 1
        for (int i = 1; i <= numberAttributes; i++) {
            OpenBitSet combinationLevel1 = new OpenBitSet();
            combinationLevel1.set(i);
            
            CombinationHelper chLevel1 = new CombinationHelper();
            OpenBitSet rhsCandidatesLevel1 = new OpenBitSet();
            rhsCandidatesLevel1.set(1, numberAttributes + 1);
            chLevel1.setRhsCandidates(rhsCandidatesLevel0);
            
            ObjectArrayList<OpenBitSet> swapCandidatesLevel1 = new ObjectArrayList<OpenBitSet>();//the C_s is empty for L1
            chLevel1.setSwapCandidates(swapCandidatesLevel1);
            
            MainClass.reverseRank = false;
            if (MainClass.Rand.nextInt(100) < MainClass.ReverseRankingPercentage) {
                MainClass.reverseRank = true;
            }
            
            //we also initialize TAU_SortedList with all equivalent classes, even for size 1
            StrippedPartition spLevel1 =
                    new StrippedPartition(partitions.get(i - 1), TAU_SortedList, attributeValuesList, numberTuples);
            chLevel1.setPartition(spLevel1);
            
            
            level1.put(combinationLevel1, chLevel1);
        }
        //End Initialize Level 1
        
        // At this point you can create a mapping between tupleIDs and the equivalence class that they belong to (first tID in the equivalence class can stand as its representative)
        // we need as many entries as there are attributes in the data:
        
        
        //SOC ADD REMOVE
        for (ObjectBigArrayBigList attrTau : TAU_SortedList) {
            Map<Long, Long> attrMap = new HashMap();
            for (Object sortedEqCs : attrTau) { // each of these is an array of Long values
                long thisEqCID = ((LongBigArrayBigList) sortedEqCs).get(0);
                for (Long tID : (LongBigArrayBigList) sortedEqCs) {
                    attrMap.put(tID, thisEqCID);
                }
            }
            TAU_reverseMap.add(attrMap);
        }

        if (MainClass.DoubleAttributes) {
            DoubleAttributes();
            System.out.println("DoubleAttributes is DONE!");
            return;
        }
        
        if (MainClass.FirstTimeRun) {
            System.out.println("# ROW    : " + numberTuples);
            System.out.println("# COLUMN : " + numberAttributes);
            System.out.println("");
        }
        
        partitions = null;
        
        long end1 = System.currentTimeMillis();
        
        int L = 1;
        
        while (!level1.isEmpty() && L <= numberAttributes) { //main loop of the algorithm
            long startTime = System.nanoTime();
            
            //compute dependencies for a level
            System.out.println("LEVEL : " + L + " size : " + level1.size() + " # FD : " + numberOfFD + " # OD : " + numberOfOD);
            
            try {
                computeODs(L);
            } catch (IOException e) {
                e.printStackTrace();
            }
            
            // prune the search space
            if (MainClass.Prune)
                prune(L);
            
            // compute the combinations for the next level
            generateNextLevel();
            L++;
            
            MainClass.latticeWiseData.add(((System.nanoTime() - startTime) / 1_000_000) + " " +
                    (numberOfFD - prevFD) + " " +
                    (numberOfOD - prevOD) + " " +
                    // E/I OCs
                    (numberOfEIOC_cond - prevEIOC_cond) + " " +
                    (numberOfEIOC_uncond - prevEIOC_uncond) + " " +
                    // E/I ODs
                    (numberOfEIOD_cond - prevEIOD_cond) + " " +
                    (numberOfEIOD_uncond - prevEIOD_uncond) + " " +
                    // I/I OCs
                    (numberOfIIOC_cond - prevIIOCcond) + " " +
                    (numberOfIIOC_uncond - prevIIOCuncond));
            // update the prev data to use in the next level
            prevFD = numberOfFD;
            prevOD = numberOfOD;
            prevEIOC_cond = numberOfEIOC_cond;
            prevEIOC_uncond = numberOfEIOC_uncond;
            prevEIOD_cond = numberOfEIOD_cond;
            prevEIOD_uncond = numberOfEIOD_uncond;
            prevIIOCcond = numberOfIIOC_cond;
            prevIIOCuncond = numberOfIIOC_uncond;
        }
        
        if (MainClass.FirstTimeRun) {
            System.out.println("# FD : " + numberOfFD);
            System.out.println("# OD : " + numberOfOD);
            System.out.println("");
        }
        
        // store num of OCs somewhere, also clear the file if it already exists
        MainClass.writeMainStatToFile(numberOfFD + " FD\n" + numberOfOD + " EEOC\n" +
                numberOfEIOC_cond + " EIOCcond\n" + numberOfEIOC_uncond + " EIOCuncond\n" +
                numberOfEIOD_cond + " EIODcond\n" + numberOfEIOD_uncond + " EIODuncond\n" +
                numberOfIIOC_cond + " IIOCcond\n" + numberOfIIOC_uncond + " IIOCuncond", true);
        //sore FDODScoreList
        
        if (FDODScoreList.size() < MainClass.topk)
            MainClass.topk = FDODScoreList.size();
        
        Collections.sort(FDODScoreList, FDODScore.FDODScoreComparator());
        
        if (MainClass.FirstTimeRun) {
            String messageToPrint;
            System.out.println("-------------------------------------------------------------------------------------");
            SpecialScoreList.sort(Collections.reverseOrder());
            for (SpecialScore specScore :
                    SpecialScoreList) {
                messageToPrint = "Score = ";
                messageToPrint += String.format("%.6f", specScore.score) + ", ";
                messageToPrint += String.format("%.6f", specScore.simpleScore) + ", ";
                messageToPrint += specScore.doesFdHold ? "E/I OD " : "E/I OC ";
                messageToPrint += specScore.isConditional ? "cond " : "unco ";
                messageToPrint += specScore.direction;
                
                printOpenBitSetNames(messageToPrint, specScore.X_minus_AB, specScore.oneAB);
                MainClass.finalOCResults.add(messageToPrint + " " + MainClass.odList.get(MainClass.odList.size() - 1) + " " + specScore.order);
            }
            
            GeneralScoreList.sort(Collections.reverseOrder());
            for (GeneralScore genScore :
                    GeneralScoreList) {
                messageToPrint = "Score = ";
                messageToPrint += String.format("(%.6f, %.6f), ", genScore.leftScore, genScore.rightScore);
                messageToPrint += String.format("(%.6f, %.6f), ", genScore.leftSimpleScore, genScore.rightSimpleScore);
                messageToPrint += genScore.isConditional ? "I/I OC cond" : "I/I OC unco";
                
                printOpenBitSetNames(messageToPrint, genScore.X_minus_AB, genScore.oneAB);
                MainClass.finalOCResults.add(messageToPrint + " " + MainClass.odList.get(MainClass.odList.size() - 1) + " " + genScore.order);
            }
            System.out.println("-------------------------------------------------------------------------------------");
            System.out.println("FD = " + numberOfFD + "\nEEOC = " + numberOfOD +
                    "\nEIOCcond = " + numberOfEIOC_cond + "\nEIOCuncond = " + numberOfEIOC_uncond +
                    "\nEIODcond = " + numberOfEIOD_cond + "\nEIODuncond = " + numberOfEIOD_uncond +
                    "\nIIOCcond = " + numberOfIIOC_cond + "\nIIOCuncond = " + numberOfIIOC_uncond);
        }
    }
    
    private ArrayList<ObjectBigArrayBigList<Integer>> DoubleAttributes() {
        
        ArrayList<ObjectBigArrayBigList<Integer>> newAttributeValuesList = new ArrayList<ObjectBigArrayBigList<Integer>>();
        
        for (ObjectBigArrayBigList<Integer> attValues : attributeValuesList) {
            
            Set<Integer> uniqueValueSet = new HashSet<Integer>();
            
            for (int rankedPosition : attValues) {
                uniqueValueSet.add(rankedPosition);
            }
            
            int numberOfUniqeValues = uniqueValueSet.size();
            
            ObjectBigArrayBigList<Integer> newBigList = new ObjectBigArrayBigList<Integer>();
            
            for (int rankedPosition : attValues) {
                int newRankedPosition = numberOfUniqeValues - rankedPosition;
                newBigList.add(newRankedPosition);
            }
            
            newAttributeValuesList.add(newBigList);
        }
        
        try {
            BufferedWriter bw =
                    new BufferedWriter(new FileWriter(MainClass.DatasetFileName + ".new"));
            
            ObjectBigArrayBigList<Integer> newBigList1 = newAttributeValuesList.get(0);
            
            for (int i = 0; i < newBigList1.size64(); i++) {
                
                for (int j = 0; j < newAttributeValuesList.size(); j++) {
                    
                    int val = newAttributeValuesList.get(j).get(i);
                    
                    if (j == newAttributeValuesList.size() - 1)
                        bw.write(val + "");
                    else
                        bw.write(val + ",");
                }
                bw.write("\n");
            }
            bw.close();
            
        } catch (Exception ex) {
        
        }
        return newAttributeValuesList;
    }
    
    private void generateNextLevel() {
        
        //OD
        level_minus1 = level0;
        
        level0 = level1;
        level1 = null;
        System.gc();
        
        Object2ObjectOpenHashMap<OpenBitSet, CombinationHelper> new_level = new Object2ObjectOpenHashMap<OpenBitSet, CombinationHelper>();
        
        buildPrefixBlocks();
        
        for (ObjectArrayList<OpenBitSet> prefix_block_list : prefix_blocks.values()) {
            
            // continue only, if the prefix_block contains at least 2 elements
            if (prefix_block_list.size() < 2) {
                continue;
            }
            //Let's see what's in the prefix block:
            
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
    private void prune(int L) throws AlgorithmExecutionException {
        
        
        if (L >= 2) {
            
            ObjectArrayList<OpenBitSet> elementsToRemove = new ObjectArrayList<OpenBitSet>();
            for (OpenBitSet x : level1.keySet()) {
                
                if (level1.get(x).getRhsCandidates().isEmpty() && (level1.get(x).getSwapCandidates().size() == 0)) {
                    elementsToRemove.add(x);
                    //this continue is useful when we add KEY checking after this if statement
                    continue;
                }
                
            }
            
            for (OpenBitSet x : elementsToRemove) {
                level1.remove(x);
            }
        }
    }
    
    
    /**
     * Computes the dependencies and ODs for the current level (level1).
     *
     * @throws AlgorithmExecutionException
     */
    private void computeODs(int L) throws AlgorithmExecutionException, IOException {
        String datasetName = MainClass.DatasetFileName;
        
        // candidate attributes for FDs
        initializeCplus_c_ForLevel(); //Line 2 in Algorithm 3
        
        //candidate attributes for ODs
        initializeCplus_s_ForLevel(L);
        
        // iterate through the combinations of the level
        //this ArrayList is for the purpose of stats collection over datasets to see how common the worst case is for our problem 1
        // This arraylist keeps track of whose stats we've printed so far since we've stepped into the current context
        Map<OpenBitSet, ArrayList> seenColIndexes = new HashMap<>();
        int SOCctrAll = 0;
        int genSocCtr = 0;
        int SOCctrPerPair = 0;
        
        for (OpenBitSet X : level1.keySet()) {
            
            //*************************** FUNCTIONAL DEPENDENCIES (CANONICAL FORM 1)
            
            // Build the intersection between X and C_plus(X)
            OpenBitSet C_plus = level1.get(X).getRhsCandidates();
            OpenBitSet intersection = (OpenBitSet) X.clone();
            intersection.intersect(C_plus);
            
            // clone of X for usage in the following loop
            OpenBitSet Xclone = (OpenBitSet) X.clone();
            
            // iterate through all elements (A) of the intersection -- High level block for processing FDs
            for (int A = intersection.nextSetBit(0); A >= 0; A = intersection.nextSetBit(A + 1)) {
                Xclone.clear(A);
                
                OpenBitSet lhsBitSet = Xclone;
                OpenBitSet rhsBitSet = new OpenBitSet();
                rhsBitSet.set(A);
                
                // check if X\A -> A is valid
                StrippedPartition spXwithoutA = level0.get(Xclone).getPartition();
                StrippedPartition spX = level1.get(X).getPartition();
                
                
                if (!MainClass.BidirectionalPruneTrue) {
                    StrippedPartition spXwithoutA_Temp = level0.get(Xclone).getPartition();
                    StrippedPartition spX_Temp = level1.get(X).getPartition();
                    if (spX_Temp.getError() == spXwithoutA_Temp.getError()) {
                        //do nothing
                    }
                }
                
                int isFD;
                int isOC;
                double FDCandidateError = (spXwithoutA.getError() - spX.getError()) / numberTuples;
                if (spX.getError() == spXwithoutA.getError()) { // subtract to get error for X\A --> A
                    
                    //we found one FD here
                    isFD = 1;
                    
                    OpenBitSet XwithoutA = (OpenBitSet) Xclone.clone();
                    
                    processFunctionalDependency(XwithoutA, A, spXwithoutA, L);
                    
                    // remove A from C_plus(X)
                    if (MainClass.Prune)
                        level1.get(X).getRhsCandidates().clear(A);
                    
                    // remove all B in R\X from C_plus(X)
                    if (MainClass.Prune) {
                        OpenBitSet RwithoutX = new OpenBitSet();
                        
                        // set to R
                        RwithoutX.set(1, numberAttributes + 1);
                        // remove X
                        RwithoutX.andNot(X);
                        
                        for (int i = RwithoutX.nextSetBit(0); i >= 0; i = RwithoutX.nextSetBit(i + 1)) {
                            level1.get(X).getRhsCandidates().clear(i);
                        }
                    }
                } else {
                    isFD = 0;
                }
                // you can write an else clause here to mark the lhs and rhs as not having an FD (for the writing into general stats csv file)
                Xclone.set(A);
                
            }
            
            
            //*************************** ORDER DEPENDENCIES (CANONICAL FORM 2)
            long startTime = System.nanoTime(); // time at the beginning of OD validation procedure
            
            ArrayList<OpenBitSet> removeFromC_s_List = new ArrayList<OpenBitSet>();
            
            //SwapCandidates is C_s_plus
            // high level block for processing OCs:
            for (OpenBitSet oneAB : level1.get(X).getSwapCandidates()) {  //begin
                ArrayList<List<Map<Long, Set<Long>>>> allChains = new ArrayList<>(); // this will keep the chains from each equivalence class of context. (if the chain was valid)
                Map<Long, Set<WeightedEdge>> flakyMap = new HashMap<>();
                
                OpenBitSet[] A_B_Separate = getSeparateOpenBitSet_AB(oneAB);
                int[] A_B_Index = getIndexOfOpenBitSet_AB(oneAB);
                //lhs and rhs are here:
                OpenBitSet A = A_B_Separate[0];
                OpenBitSet B = A_B_Separate[1];
                
                int A_index = A_B_Index[0]; //starts from 1
                int B_index = A_B_Index[1]; //starts from 1
                
                OpenBitSet X_minus_A = (OpenBitSet) X.clone();
                X_minus_A.remove(A);
                OpenBitSet C_c_X_minus_A = level0.get(X_minus_A).getRhsCandidates();
                OpenBitSet C_c_X_minus_A_Clone = C_c_X_minus_A.clone();
                C_c_X_minus_A_Clone.union(B);
                
                OpenBitSet X_minus_B = (OpenBitSet) X.clone();
                X_minus_B.remove(B);
                OpenBitSet C_c_X_minus_B = level0.get(X_minus_B).getRhsCandidates();
                OpenBitSet C_c_X_minus_B_Clone = C_c_X_minus_B.clone();
                C_c_X_minus_B_Clone.union(A);
                
                // this is exactly the if statement in line 18
                // Checking if A belongs to C+_c(X\B) and B belongs to C+_c(X\A). (because the clone is union with A (or B))
                if (!(C_c_X_minus_B.equals(C_c_X_minus_B_Clone)) || !(C_c_X_minus_A.equals(C_c_X_minus_A_Clone))) {
                    removeFromC_s_List.add(oneAB);
                    
                    
                } else {
                    
                    //line 20, if( X\{A,B} : A ~ B)
                    
                    //step 1: find X\{A,B}
                    OpenBitSet X_minus_AB = (OpenBitSet) X.clone();
                    
                    X_minus_AB.remove(A);
                    X_minus_AB.remove(B);
                    if (!seenColIndexes.containsKey(X_minus_AB)) {
                        seenColIndexes.put(X_minus_AB, new ArrayList<Integer>());
                    }
                    ObjectBigArrayBigList<LongBigArrayBigList> strippedPartition_X_minus_AB =
                            level_minus1.get(X_minus_AB).getPartition().getStrippedPartition();
                    
                    //create hash table based on strippedPartition_X_minus_AB
                    Object2ObjectOpenHashMap<Long, Integer> strippedPartition_X_minus_AB_Hash =
                            new Object2ObjectOpenHashMap<Long, Integer>();
                    int counter = 0;
                    for (LongBigArrayBigList strippedPartitionElement : strippedPartition_X_minus_AB) {
                        for (long element_index : strippedPartitionElement) {
                            strippedPartition_X_minus_AB_Hash.put(element_index, counter);
                        }
                        counter++;
                    }
                    
                    ObjectBigArrayBigList<LongBigArrayBigList> sorted_TAU_A = TAU_SortedList.get(A_index - 1);//A_index starts from 1
                    
                    ObjectBigArrayBigList<ObjectBigArrayBigList<LongBigArrayBigList>> PI_X_TAU_A_1 =
                            new ObjectBigArrayBigList<ObjectBigArrayBigList<LongBigArrayBigList>>();
                    
                    //PI_X_TAU_A is Table 6 in my Excel file
                    //the number of items in this list is equal to the number of items in strippedPartition_X_minus_AB
                    for (LongBigArrayBigList strippedPartitionElement : strippedPartition_X_minus_AB) {
                        PI_X_TAU_A_1.add(new ObjectBigArrayBigList<LongBigArrayBigList>());
                    }
                    
                    ArrayList<Integer> a_counter_list = new ArrayList<Integer>();
                    // a_counter_list has same size as sorted_TAU_A
                    // There exists one such list fo each order compatibility candidacy
                    
                    for (LongBigArrayBigList tau_A_element : sorted_TAU_A) {
                        int a_counter = 0;
                        //every tau_A_element is one equivalence class within sorted partitions on A
                        Set<Integer> seenIndexSet = new HashSet<Integer>();
                        for (long l_a : tau_A_element) {
                            //insert in PI_X_TAU_A
                            if (strippedPartition_X_minus_AB_Hash.containsKey(l_a)) {
                                
                                int index_in_PI_X_TAU_A = strippedPartition_X_minus_AB_Hash.get(l_a);
                                //what is this trying to handle?
                                if (seenIndexSet.contains(index_in_PI_X_TAU_A)) {
                                    //In this case, this will be added to the last list
                                } else {
                                    //In this case, a new list is created
                                    a_counter++;
                                    seenIndexSet.add(index_in_PI_X_TAU_A);
                                    PI_X_TAU_A_1.get(index_in_PI_X_TAU_A).add(new LongBigArrayBigList());
                                }
                                
                                long currentSize = PI_X_TAU_A_1.get(index_in_PI_X_TAU_A).size64();
                                PI_X_TAU_A_1.get(index_in_PI_X_TAU_A).get(currentSize - 1).add(l_a);
                            }
                        }
                        a_counter_list.add(a_counter);
                    }
                    
                    ObjectBigArrayBigList<LongBigArrayBigList> sorted_TAU_B = TAU_SortedList.get(B_index - 1);//A_index starts from 1
                    
                    ObjectBigArrayBigList<ObjectBigArrayBigList<LongBigArrayBigList>> PI_X_TAU_B_1 =
                            new ObjectBigArrayBigList<ObjectBigArrayBigList<LongBigArrayBigList>>();
                    
                    //the number of items in this list is equal to the number of items in strippedPartition_X_minus_AB
                    for (LongBigArrayBigList strippedPartitionElement : strippedPartition_X_minus_AB) {
                        PI_X_TAU_B_1.add(new ObjectBigArrayBigList<LongBigArrayBigList>());
                    }
                    
                    ArrayList<Integer> b_counter_list = new ArrayList<Integer>();
                    // b_counter_list has same size as sorted_TAU_B
                    // There exists one such list fo each order compatibility candidacy
                    
                    for (LongBigArrayBigList tau_B_element : sorted_TAU_B) {
                        //every tau_B_element is one equivalence class within sorted partitions on B
                        int b_counter = 0; //keeps count of how many equivalence classes in X has tau_B_elem's
                        // representative B value appeared in. Resets with each new unique B value.
                        // Gets incremented when a new list is created a few lines below here
                        Set<Integer> seenIndexSet = new HashSet<Integer>();
                        for (long l_b : tau_B_element) { // iterating over each tid in this equivalence class of B
                            //insert in PI_X_TAU_B
                            if (strippedPartition_X_minus_AB_Hash.containsKey(l_b)) {
                                
                                int index_in_PI_X_TAU_B = strippedPartition_X_minus_AB_Hash.get(l_b);
                                if (seenIndexSet.contains(index_in_PI_X_TAU_B)) {
                                    //In this case, this will be added to the last list
                                } else {
                                    b_counter++;
                                    //In this case, a new list is created
                                    seenIndexSet.add(index_in_PI_X_TAU_B);
                                    PI_X_TAU_B_1.get(index_in_PI_X_TAU_B).add(new LongBigArrayBigList());
                                }
                                
                                long currentSize = PI_X_TAU_B_1.get(index_in_PI_X_TAU_B).size64();
                                PI_X_TAU_B_1.get(index_in_PI_X_TAU_B).get(currentSize - 1).add(l_b);
                            }
                        }
                        b_counter_list.add(b_counter);
                    }
                    
                    if (!MainClass.BidirectionalPruneTrue) {
                        
                        ObjectBigArrayBigList<ObjectBigArrayBigList<LongBigArrayBigList>> PI_X_TAU_A_2 =
                                new ObjectBigArrayBigList<ObjectBigArrayBigList<LongBigArrayBigList>>();
                        
                        for (LongBigArrayBigList strippedPartitionElement : strippedPartition_X_minus_AB) {
                            PI_X_TAU_A_2.add(new ObjectBigArrayBigList<LongBigArrayBigList>());
                        }
                        
                        for (LongBigArrayBigList tau_A_element : sorted_TAU_A) {
                            
                            Set<Integer> seenIndexSet = new HashSet<Integer>();
                            for (long l_a : tau_A_element) {
                                //insert in PI_X_TAU_A_TEMP
                                if (strippedPartition_X_minus_AB_Hash.containsKey(l_a)) {
                                    
                                    int index_in_PI_X_TAU_A_TEMP = strippedPartition_X_minus_AB_Hash.get(l_a);
                                    if (seenIndexSet.contains(index_in_PI_X_TAU_A_TEMP)) {
                                        //In this case, this will be added to the last list
                                    } else {
                                        //In this case, a new list is created
                                        seenIndexSet.add(index_in_PI_X_TAU_A_TEMP);
                                        PI_X_TAU_A_2.get(index_in_PI_X_TAU_A_TEMP).add(new LongBigArrayBigList());
                                    }
                                    
                                    long currentSize = PI_X_TAU_A_2.get(index_in_PI_X_TAU_A_TEMP).size64();
                                    PI_X_TAU_A_2.get(index_in_PI_X_TAU_A_TEMP).get(currentSize - 1).add(l_a);
                                }
                            }
                        }
                    }
                    
                    long endTime = System.nanoTime(); // time at the end of OC validation
                    long duration = (endTime - startTime);
                    writeValidationTimeToCSV(datasetName, L, null, null, null, duration, "Preprocess", -1, -1, false, "");
                    
                    startTime = System.nanoTime(); // time at the beginning of OD validation procedure
                    //check to see whether a swap or reverse swap happened (both ASC vs. DSC and ASC vs. ASC are checked)
                    
                    ObjectBigArrayBigList<Integer> bValues = attributeValuesList.get(B_index - 1);
                    
                    boolean swapHappen = false;
                    for (int j = 0; j < PI_X_TAU_A_1.size64() && (!swapHappen); j++) {
                        
                        ObjectBigArrayBigList oneListInX = PI_X_TAU_A_1.get(j);
                        
                        for (int i = 0; i < oneListInX.size64() - 1 && (!swapHappen); i++) {
                            LongBigArrayBigList List1 = (LongBigArrayBigList) oneListInX.get(i); //current equivalence class in A
                            LongBigArrayBigList List2 = (LongBigArrayBigList) oneListInX.get(i + 1); //next equivalence class in A
                            
                            //check to make sure a swap does not happen between List1 and List2 with respect to A and B
                            int maxB_inList1 = -1;
                            for (long index1 : List1) {
                                int value = bValues.get(index1);
                                if (value > maxB_inList1) {
                                    maxB_inList1 = value;
                                }
                            }
                            
                            int minB_inList2 = Integer.MAX_VALUE;
                            for (long index2 : List2) {
                                int value = bValues.get(index2);
                                if (value < minB_inList2) {
                                    minB_inList2 = value;
                                }
                            }
                            
                            //NO Swap: maxB_inList1 < minB_inList2
                            //Swap: maxB_inList1 > minB_inList2
                            if (maxB_inList1 > minB_inList2) {
                                swapHappen = true;
                            }
                        }
                    }
                    
                    endTime = System.nanoTime(); // time at the end of OC validation
                    duration = (endTime - startTime);
                    writeValidationTimeToCSV(datasetName, L, X_minus_AB, A, B, duration, "EEOC", -1, strippedPartition_X_minus_AB.size64(), !swapHappen, "");
                    
                    boolean swapReverseHappen = false;
                    if (MainClass.BidirectionalTrue) {
                        for (int j = 0; j < PI_X_TAU_A_1.size64() && (!swapReverseHappen); j++) {
                            
                            ObjectBigArrayBigList oneListInX = PI_X_TAU_A_1.get(j);
                            
                            for (int i = 0; i < oneListInX.size64() - 1 && (!swapReverseHappen); i++) {
                                LongBigArrayBigList List1 = (LongBigArrayBigList) oneListInX.get(i);
                                LongBigArrayBigList List2 = (LongBigArrayBigList) oneListInX.get(i + 1);
                                
                                //check to make sure a reverse swap does not happen between List1 and List2 with respect to A and B
                                
                                int minB_inList1 = Integer.MAX_VALUE;
                                for (long index1 : List1) {
                                    int value = bValues.get(index1);
                                    if (value < minB_inList1) {
                                        minB_inList1 = value;
                                    }
                                }
                                
                                int maxB_inList2 = -1;
                                for (long index2 : List2) {
                                    int value = bValues.get(index2);
                                    if (value > maxB_inList2) {
                                        maxB_inList2 = value;
                                    }
                                }
                                
                                //NO Reverse Swap: maxB_inList2 < minB_inList1
                                //Reverse Swap: maxB_inList2 > minB_inList1
                                if (maxB_inList2 > minB_inList1) {
                                    swapReverseHappen = true;
                                }
                            }
                        }
                    }
                    
                    
                    if (!MainClass.BidirectionalPruneTrue) {
                        
                        boolean swapHappen_temp = false;
                        for (int j = 0; j < PI_X_TAU_A_1.size64() && (!swapHappen_temp); j++) {
                            
                            ObjectBigArrayBigList oneListInX = PI_X_TAU_A_1.get(j);
                            
                            for (int i = 0; i < oneListInX.size64() - 1 && (!swapHappen_temp); i++) {
                                LongBigArrayBigList List1 = (LongBigArrayBigList) oneListInX.get(i);
                                LongBigArrayBigList List2 = (LongBigArrayBigList) oneListInX.get(i + 1);
                                
                                //check to make sure a swap does not happen between List1 and List2 with respect to A and B
                                int maxB_inList1 = -1;
                                for (long index1 : List1) {
                                    int value = bValues.get(index1);
                                    if (value > maxB_inList1) {
                                        maxB_inList1 = value;
                                    }
                                }
                                
                                int minB_inList2 = Integer.MAX_VALUE;
                                for (long index2 : List2) {
                                    int value = bValues.get(index2);
                                    if (value < minB_inList2) {
                                        minB_inList2 = value;
                                    }
                                }
                                
                                //NO Swap: maxB_inList1 < minB_inList2
                                //Swap: maxB_inList1 > minB_inList2
                                if (maxB_inList1 > minB_inList2) {
                                    swapHappen_temp = true;
                                }
                            }
                        }
                        
                        boolean swapReverseHappen_temp = false;
                        if (MainClass.BidirectionalTrue) {
                            for (int j = 0; j < PI_X_TAU_A_1.size64() && (!swapReverseHappen_temp); j++) {
                                
                                ObjectBigArrayBigList oneListInX = PI_X_TAU_A_1.get(j);
                                
                                for (int i = 0; i < oneListInX.size64() - 1 && (!swapReverseHappen_temp); i++) {
                                    LongBigArrayBigList List1 = (LongBigArrayBigList) oneListInX.get(i);
                                    LongBigArrayBigList List2 = (LongBigArrayBigList) oneListInX.get(i + 1);
                                    
                                    //check to make sure a reverse swap does not happen between List1 and List2 with respect to A and B
                                    
                                    int minB_inList1 = Integer.MAX_VALUE;
                                    for (long index1 : List1) {
                                        int value = bValues.get(index1);
                                        if (value < minB_inList1) {
                                            minB_inList1 = value;
                                        }
                                    }
                                    
                                    int maxB_inList2 = -1;
                                    for (long index2 : List2) {
                                        int value = bValues.get(index2);
                                        if (value > maxB_inList2) {
                                            maxB_inList2 = value;
                                        }
                                    }
                                    
                                    //NO Reverse Swap: maxB_inList2 < minB_inList1
                                    //Reverse Swap: maxB_inList2 > minB_inList1
                                    if (maxB_inList2 > minB_inList1) {
                                        swapReverseHappen_temp = true;
                                    }
                                }
                            }
                        }
                    }
                    // ----------------------- Done validating OCC ----------------------
                    
                    
                    boolean ODPass = false;
                    boolean BidODPass = false;
                    if (MainClass.BidirectionalTrue) { //breakpoint to check if allChains array has accurately kept all the chains
                        if (!swapHappen) {
                            ODPass = true;
                        }
                        if (!swapReverseHappen) {
                            BidODPass = true;
                        }
                    } else {
                        if (!swapHappen) {
                            ODPass = true;
                        }
                    }
                    int isOC;
                    // find and save names here
                    
                    if (ODPass || BidODPass) {
                        // an OC is found
                        isOC = 1;
                        long score = 0;
                        if (!XScoreMap.containsKey(X_minus_AB)) {
                            score = calculateInterestingnessScore(strippedPartition_X_minus_AB, X_minus_AB);
                            XScoreMap.put(X_minus_AB, score);
                        } else {
                            score = XScoreMap.get(X_minus_AB);
                        }
                        
                        FDODScore fdodScore = new FDODScore(score, X_minus_AB, oneAB);
                        //
                        FDODScoreList.add(fdodScore);
                        //calculate interestingness score
                        
                        numberOfOD++;
                        System.out.println("****** OD SIM is Found #" + numberOfOD);
                        System.out.println("#SCORE# " + score);
                        
                        if (ODPass)
                            printOpenBitSetNames("REG-OD:", X_minus_AB, oneAB);
                        if (BidODPass)
                            printOpenBitSetNames("BID-OD:", X_minus_AB, oneAB);
                        
                        System.out.println(score);
                        System.out.println("");
                        
                        removeFromC_s_List.add(oneAB);
                    }
                    else {
                        isOC = 0;
                        
                        
                        // only when an OC doesn't hold should you check for SOCs. Otherwise an OC is more important
                        
                        Xclone = X.clone();
                        Xclone.clear(A_index);
                        boolean xDeterminesA = existsFD(Xclone, A_index);
                        
                        Xclone.set(A_index);
                        Xclone.clear(B_index);
                        boolean xDeterminesB = existsFD(Xclone, B_index);
                        
                        boolean socHolds = false;
                        SOCOneSideSyntactic specSocMiner;
                        List<Map<Long, Set<Long>>> specOrders;  // because we want to handle conditional too
                        
                        boolean isOD;
                        String ocOrOd;
                        
                        boolean didFindUnconditionalEI = false;
                        
                        if (MainClass.isColumnActive.get(A_index - 1)) {
                            if (xDeterminesA) {
                                isOD = true;
                                ocOrOd = "OD";
                            } else {
                                isOD = false;
                                ocOrOd = "OC";
                            }
                            printOpenBitSetNames("Inspecting E/I " + ocOrOd + " (R->L): ", X_minus_AB, oneAB);
                            
                            startTime = System.nanoTime();
                            specSocMiner = new SOCOneSideSyntactic(TAU_reverseMap, A_index, B_index, isOD, PI_X_TAU_B_1, PI_X_TAU_A_1);
                            specOrders = specSocMiner.execute();
                            duration = System.nanoTime() - startTime;
                            
                            String orderStr = "";
                            if (specOrders != null) {
                                orderStr = orderToString(specOrders, A_index);
                            }
    
                            writeValidationTimeToCSV(datasetName, L, X_minus_AB, A, B, duration, "EI" + ocOrOd,
                                    -1, strippedPartition_X_minus_AB.size64(), specOrders != null, orderStr);
                            
                            if (specOrders != null) {
                                printOpenBitSetNames(SOCctrAll + " - E/I " + ocOrOd + " (R->L)", X_minus_AB, oneAB);
                                socHolds = true;
                                SOCctrAll++;
                                if (specSocMiner.isOrderConditional) {
                                    if (isOD)
                                        numberOfEIOD_cond++;
                                    else
                                        numberOfEIOC_cond++;
                                } else {
                                    if (isOD)
                                        numberOfEIOD_uncond++;
                                    else
                                        numberOfEIOC_uncond++;
                                    
                                    didFindUnconditionalEI = true;
                                }
                                
                                double[] specialScores = calculateSpecialInterestingness(specOrders, specSocMiner.isOrderConditional);
                                SpecialScoreList.add(new SpecialScore(specialScores[0], specialScores[1], "(R->L)", isOD, specSocMiner.isOrderConditional, X_minus_AB, oneAB, orderStr));
                            }
                        }
                        
                        if (MainClass.isColumnActive.get(B_index - 1)) {
                            if (xDeterminesB) {
                                isOD = true;
                                ocOrOd = "OD";
                            } else {
                                isOD = false;
                                ocOrOd = "OC";
                            }
                            
                            printOpenBitSetNames("Inspecting E/I " + ocOrOd + " (L->R): ", X_minus_AB, oneAB);
                            
                            startTime = System.nanoTime();
                            specSocMiner = new SOCOneSideSyntactic(TAU_reverseMap, B_index, A_index, isOD, PI_X_TAU_A_1, PI_X_TAU_B_1);
                            specOrders = specSocMiner.execute();
                            duration = System.nanoTime() - startTime;
                            
                            String orderStr = "";
                            if (specOrders != null) {
                                orderStr = orderToString(specOrders, B_index);
                            }
                            
                            writeValidationTimeToCSV(datasetName, L, X_minus_AB, B, A, duration, "EI" + ocOrOd,
                                    -1, strippedPartition_X_minus_AB.size64(), specOrders != null, orderStr);
                            
                            if (specOrders != null) {
                                printOpenBitSetNames(SOCctrAll + " - E/I " + ocOrOd + " (L->R)", X_minus_AB, oneAB);
                                socHolds = true;
                                SOCctrAll++;
                                if (specSocMiner.isOrderConditional) {
                                    if (isOD)
                                        numberOfEIOD_cond++;
                                    else
                                        numberOfEIOC_cond++;
                                } else {
                                    if (isOD)
                                        numberOfEIOD_uncond++;
                                    else
                                        numberOfEIOC_uncond++;
                                    
                                    didFindUnconditionalEI = true;
                                }
                                
                                double[] specialScores = calculateSpecialInterestingness(specOrders, specSocMiner.isOrderConditional);
                                SpecialScoreList.add(new SpecialScore(specialScores[0], specialScores[1], "(L->R)", isOD, specSocMiner.isOrderConditional, X_minus_AB, oneAB, orderStr));
                            }
                        }
                        
                        if (MainClass.isColumnActive.get(A_index - 1) && MainClass.isColumnActive.get(B_index - 1) &&
                                !didFindUnconditionalEI) {
                            // run gen soc
                            printOpenBitSetNames("Inspecting I/I OC : ", X_minus_AB, oneAB);
                            writeGeneralCaseDetailToCSV(datasetName, L, X_minus_AB, A, B, strippedPartition_X_minus_AB.size64());
                            startTime = System.nanoTime();
                            
                            SOCGeneralCase genSocMiner = new SOCGeneralCase(TAU_reverseMap, A_index, B_index,
                                    PI_X_TAU_A_1, PI_X_TAU_B_1, flakyMap);
                            ODAlgorithm.flakeCount = 0;
                            ArrayList<List<Map<Long, Set<Long>>>> genOrder = genSocMiner.execute();
                            
                            duration = (System.nanoTime() - startTime);
                            
                            String orderStr = "";
                            System.out.println(genOrder);
                            if (genOrder != null) {
                                StringBuilder o1 = new StringBuilder("LHS: ");
                                StringBuilder o2 = new StringBuilder("RHS: ");
                                List<Map<Long, Set<Long>>> tmp;
                                for (List<Map<Long, Set<Long>>> pgOrders: genOrder) {
                                    tmp = new ArrayList<>();
                                    tmp.add(pgOrders.get(0));
                                    o1.append(orderToString(tmp, A_index));
                                    
                                    tmp = new ArrayList<>();
                                    tmp.add(pgOrders.get(1));
                                    o2.append(orderToString(tmp, B_index));
                                }
                                orderStr = o1 + "" + o2;
                            }
                            
                            writeValidationTimeToCSV(datasetName, L, X_minus_AB, A, B, duration, "IIOC" + (genSocMiner.isTheOrderConditional ? "cond" : "uncond"),
                                    ODAlgorithm.flakeCount, strippedPartition_X_minus_AB.size64(), genOrder != null, orderStr);
                            if (genOrder != null) {
                                // accept the new order only if eioc didn't hold before or if the iioc is  unconditional
                                if (!socHolds || !genSocMiner.isTheOrderConditional) {
                                    double[][] scores = calculateGeneralInterestingness(genOrder, genSocMiner.isTheOrderConditional);
                                    if (scores[0][0] > 0d || scores[0][1] > 0d) {
                                        
                                        if (xDeterminesA || xDeterminesB) {
                                            MainClass.numOfFoundIIODs++;
                                        }
                                        
                                        SOCctrAll++;
                                        socHolds = true;
                                        printOpenBitSetNames(genSocCtr + " - I/I OC", X_minus_AB, oneAB);
                                        genSocCtr++;
                                        if (genSocMiner.isTheOrderConditional)
                                            numberOfIIOC_cond++;
                                        else
                                            numberOfIIOC_uncond++;
        
                                        GeneralScoreList.add(new GeneralScore(scores[0][0], scores[0][1], scores[1][0],
                                                scores[1][1], genSocMiner.isTheOrderConditional, X_minus_AB, oneAB, orderStr));
                                    }
                                }
                            }
                        }
                        // prune
                        if (socHolds) {
                            removeFromC_s_List.add(oneAB);
                        }
                    }
                }
            }
            
            //remove ABs
            if (MainClass.Prune) {
                for (OpenBitSet removedAB : removeFromC_s_List) {
                    level1.get(X).getSwapCandidates().remove(removedAB);
                }
            }
        }
    }
    
    private long calculateInterestingnessScore(
            ObjectBigArrayBigList<LongBigArrayBigList> strippedPartition,
            OpenBitSet X) {
        long score = 0;
        
        if (X.isEmpty()) {
            score = MainClass.MaxRowNumber * MainClass.MaxRowNumber;
        } else {
            
            int totalNumberOfRowsCountedAlready = 0; //this is used to add stirppted partition rows later
            for (LongBigArrayBigList strippedPartitionElement : strippedPartition) {
                score += (strippedPartitionElement.size64() * strippedPartitionElement.size64());
                totalNumberOfRowsCountedAlready += strippedPartitionElement.size64();
            }
            //add the stripped partitions, since each of them is 1, raising them to the power of two will not change their value
            score += (numberTuples - totalNumberOfRowsCountedAlready);
            ;
        }
        
        return score;
    }
    
    // defined multiple measures (original, simplified), will compute both of them for storage and comparison
    public double[] calculateSpecialInterestingness(List<Map<Long, Set<Long>>> specOrders, boolean isConditional) {
        long numUnique;
        long max_pairs;
        
        Set<Long> allUniques = new HashSet<>();
        long countOfLocalPairs = 0;
        long countOfLocalLongestPath = 0;
        for (Map<Long, Set<Long>> singleOrder :
                specOrders) {
            allUniques.addAll(singleOrder.keySet());
            countOfLocalPairs += auxGetNumberOfPairOrders(singleOrder);
            countOfLocalLongestPath += auxLongestPathDAG(singleOrder);
        }
        
        numUnique = allUniques.size();
        max_pairs = numUnique * (numUnique - 1) / 2;
        
        double[] result = {0., 0.};
        
        if (numUnique > 1) {
            result[0] = (double) countOfLocalPairs / max_pairs;
            result[1] = (double) countOfLocalLongestPath / (numUnique - 1);
        }
        
        int numOfChains = specOrders.size();
        if (isConditional && (numOfChains > 0)) {
            result[0] /= numOfChains;
            result[1] /= numOfChains;
        }
        
        return result;
    }
    
    // gets list of pairs of all chains in the final order
    // first dimension original/simple measure, second dimension left/right chains
    // depending of conditional or not, aggregate individual chains
    public double[][] calculateGeneralInterestingness(ArrayList<List<Map<Long, Set<Long>>>> allChains, boolean isConditional) {
        long[] totalUniques = {0, 0};
        long[] existingPairs = {0, 0};
        long[] longestPaths = {0, 0};
        
        List<Set<Long>> allUniques = new ArrayList<>(Arrays.asList(new HashSet<>(), new HashSet<>()));
        double[] avgOfPathScores = {0., 0.};
        
        long localUniques, localPairs;
        for (List<Map<Long, Set<Long>>> doubleChain :
                allChains) {
            for (int i = 0; i < 2; i++) {
                Map<Long, Set<Long>> singleOrder = doubleChain.get(i);
                localPairs = auxGetNumberOfPairOrders(singleOrder);
                
                allUniques.get(i).addAll(singleOrder.keySet());
                existingPairs[i] += localPairs;
                
                long longestLocalPath = auxLongestPathDAG(singleOrder);
                if (isConditional)
                    longestPaths[i] += longestLocalPath;
                else if (longestLocalPath > longestPaths[i])
                    longestPaths[i] = longestLocalPath;
            }
        }
        
        totalUniques[0] = allUniques.get(0).size();
        totalUniques[1] = allUniques.get(1).size();
        long[] maxPairs = {totalUniques[0] * (totalUniques[0] - 1) / 2, totalUniques[1] * (totalUniques[1] - 1) / 2};
        
        double[][] result = {{0., 0.}, {0., 0.}};
        
        if (totalUniques[0] > 0) {
            result[0][0] = (double) existingPairs[0] / maxPairs[0];
            result[1][0] = (double) longestPaths[0] / (totalUniques[0] - 1);
        }
        if (totalUniques[1] > 0) {
            result[0][1] = (double) existingPairs[1] / maxPairs[1];
            result[1][1] = (double) longestPaths[1] / (totalUniques[1] - 1);
        }
        
        // if it's conditional, divide the score over # of chains to normalize
        int numOfChains = allChains.size();
        if (isConditional && (numOfChains > 0)) {
            result[0][0] /= numOfChains;
            result[0][1] /= numOfChains;
            result[1][0] /= numOfChains;
            result[1][1] /= numOfChains;
        }
        
        return result;
    }
    
    private long auxGetNumberOfPairOrders(Map<Long, Set<Long>> singleOrder) {
        long numOfPairs = 0;
        
        long startTime = System.nanoTime();
        for (Long source :
                singleOrder.keySet()) {
            List<Long> descendants = new ArrayList<>(singleOrder.get(source));
            Set<Long> visited = new HashSet<>(singleOrder.get(source));
            for (int j = 0; j < descendants.size(); j++) {
                Long destination = descendants.get(j);
                for (long node :
                        singleOrder.get(destination)) {
                    if (!visited.contains(node)) {
                        descendants.add(node);
                        visited.add(node);
                    }
                }
            }
            numOfPairs += descendants.size();
        }
        MainClass.pairBasedScoreTotalTime += (System.nanoTime() - startTime);
        
        return numOfPairs;
    }
    
    private long auxLongestPathDAG(Map<Long, Set<Long>> singleOrder) {
        long startTime = System.nanoTime();
        
        Map<Long, Long> longestPath = new HashMap<>();
        for (Long source :
                singleOrder.keySet()) {
            if (!longestPath.containsKey(source)) {
                dfsUtil(source, singleOrder, longestPath);
            }
        }
        MainClass.pathBasedScoreTotalTime += (System.nanoTime() - startTime);
        
        return longestPath.size() > 0 ? Collections.max(longestPath.values()) : 0;
    }
    
    private void dfsUtil(long node, Map<Long, Set<Long>> singleOrder, Map<Long, Long> longestPath) {
        longestPath.put(node, 0L);
        Set<Long> adj = singleOrder.get(node);
        for (Long v :
                adj) {
            if (!longestPath.containsKey(v)) {
                dfsUtil(v, singleOrder, longestPath);
            }
            if (longestPath.get(v) + 1 > longestPath.get(node)) {
                longestPath.put(node, longestPath.get(v) + 1);
            }
        }
    }
    
    private OpenBitSet[] getSeparateOpenBitSet_AB(OpenBitSet oneAB) {
        
        OpenBitSet A = new OpenBitSet();
        OpenBitSet B = new OpenBitSet();
        
        boolean foundA = false;
        
        for (int i = 0; i < numberAttributes + 1; i++) {
            if (oneAB.get(i)) {
                if (!foundA) {
                    foundA = true;
                    A.set(i);
                } else {
                    B.set(i);
                }
            }
        }
        
        OpenBitSet[] results = new OpenBitSet[2];
        results[0] = A;
        results[1] = B;
        
        return results;
    }
    
    private int[] getIndexOfOpenBitSet_AB(OpenBitSet oneAB) {
        
        int A_index = -1;
        int B_index = -1;
        
        boolean foundA = false;
        
        for (int i = 0; i < numberAttributes + 1; i++) {
            if (oneAB.get(i)) {
                if (!foundA) {
                    foundA = true;
                    A_index = i;
                } else {
                    B_index = i;
                }
            }
        }
        
        int[] results = new int[2];
        results[0] = A_index;
        results[1] = B_index;
        
        return results;
    }
    
    private boolean existsFD(OpenBitSet lhs, int a) {
        ColumnIdentifier[] columns = new ColumnIdentifier[(int) lhs.cardinality()];
        int j = 0;
        for (int i = lhs.nextSetBit(0); i >= 0; i = lhs.nextSetBit(i + 1)) {
            columns[j++] = this.columnIdentifiers.get(i - 1);
        }
        ColumnCombination colCombination = new ColumnCombination(columns);
        FunctionalDependency fd = new FunctionalDependency(colCombination, columnIdentifiers.get((int) a - 1));
        // check fdodlist to see if fd exists in there:
        for (FDODScore fdOdScore : FDODScoreList) {
            if (fdOdScore.functionalDependency == null)
                continue;
            if (fdOdScore.functionalDependency.equals(fd)) {
                return true;
            }
        }
        return false;
    }
    
    /**
     * Adds the FD lhs -> a to the resultReceiver and also prints the dependency.
     *
     * @param lhs: left-hand-side of the functional dependency
     * @param a:   dependent attribute. Possible values: 1 <= a <= maxAttributeNumber.
     */
    private void processFunctionalDependency(OpenBitSet lhs, int a, StrippedPartition spXwithoutA, int L) {
        try {
            addDependencyToResultReceiver(lhs, a, spXwithoutA, L);
        } catch (ColumnNameMismatchException e) {
            e.printStackTrace();
        }
    }
    
    private void addDependencyToResultReceiver(OpenBitSet X, int a, StrippedPartition spXwithoutA, int L) throws ColumnNameMismatchException {
        //+M add FD to hash map:
        OpenBitSet aOBS = new OpenBitSet();
        aOBS.set(a);
        
        //-M
        ColumnIdentifier[] columns = new ColumnIdentifier[(int) X.cardinality()];
        int j = 0;
        for (int i = X.nextSetBit(0); i >= 0; i = X.nextSetBit(i + 1)) {
            columns[j++] = this.columnIdentifiers.get(i - 1);
        }
        ColumnCombination colCombination = new ColumnCombination(columns);
        FunctionalDependency fdResult = new FunctionalDependency(colCombination, columnIdentifiers.get((int) a - 1));
        
        long score = 0;
        if (!XScoreMap.containsKey(X)) {
            score = calculateInterestingnessScore(spXwithoutA.getStrippedPartition(), X);
            XScoreMap.put(X, score);
        } else {
            score = XScoreMap.get(X);
        }
        
        FDODScore fdodScore = new FDODScore(score, fdResult);
        FDODScoreList.add(fdodScore);
        
        numberOfFD++;
        System.out.println("##### FD Found " + numberOfFD);
        System.out.println("FD#  " + (answerCountFD++) + "  #SCORE#  " + score + "  #L#  " + L);
        System.out.println(score + "#" + numberOfFD + "#L#" + L + "#FD:#" + fdResult);
        System.out.println("FD:" + fdResult);
        
        System.out.println(score);
        System.out.println("");
    }
    
    //OD
    private void initializeCplus_s_ForLevel(int L) {
        
        //ACS  vs   DSC
        
        if (L == 2) { //Line 3 in Algorithm 3
            
            for (OpenBitSet X : level1.keySet()) {
                OpenBitSet Xclone = (OpenBitSet) X.clone();
                
                ObjectArrayList<OpenBitSet> SofX = new ObjectArrayList<OpenBitSet>();
                SofX.add(Xclone);//at level 2, each element X has one C_s
                
                CombinationHelper ch = level1.get(X);
                ch.setSwapCandidates(SofX);
            }
            
        } else {
            if (L > 2) { //Line 5 in Algorithm 3
                
                //loop through all members of current level, this loop is missing in the pseudo-code
                for (OpenBitSet X : level1.keySet()) {
                    
                    ObjectArrayList<OpenBitSet> allPotentialSwapCandidates = new ObjectArrayList<OpenBitSet>();
                    
                    //clone of X for usage in the following loop
                    //loop over all X\C (line 6 Algorithm 3)
                    OpenBitSet Xclone1 = (OpenBitSet) X.clone();
                    for (int C = X.nextSetBit(0); C >= 0; C = X.nextSetBit(C + 1)) {
                        Xclone1.clear(C);
                        //now Xclone is X/C
                        ObjectArrayList<OpenBitSet> C_s_withoutC_List = level0.get(Xclone1).getSwapCandidates();
                        for (OpenBitSet oneAB : C_s_withoutC_List) {
                            if (!allPotentialSwapCandidates.contains(oneAB)) {
                                allPotentialSwapCandidates.add(oneAB);
                            }
                        }
                        Xclone1.set(C);
                    }
                    
                    ObjectArrayList<OpenBitSet> allActualSwapCandidates = new ObjectArrayList<OpenBitSet>();
                    
                    //loop over all potential {A,B}
                    for (OpenBitSet oneAB : allPotentialSwapCandidates) {
                        //step 1: form X\{A, B}
                        OpenBitSet X_minus_AB = (OpenBitSet) X.clone();
                        X_minus_AB.remove(oneAB);//This is X\{A,B}
                        
                        //now we have to examine all members of X\{A,B}
                        OpenBitSet Xclone2 = (OpenBitSet) X.clone();
                        
                        boolean doesAllofThemContains_AB = true;
                        
                        //loop over X_minus_AB, but check c_s_plus on X_minus_D
                        for (int D = X_minus_AB.nextSetBit(0); D >= 0; D = X_minus_AB.nextSetBit(D + 1)) {
                            Xclone2.clear(D);
                            //now Xclone2 does not contain D
                            ObjectArrayList<OpenBitSet> C_s_withoutD_List = level0.get(Xclone2).getSwapCandidates();
                            if (!C_s_withoutD_List.contains(oneAB))
                                doesAllofThemContains_AB = false;
                            
                            Xclone2.set(D);
                        }
                        
                        if (doesAllofThemContains_AB) {
                            
                            
                            OpenBitSet X__clone_minusAB = (OpenBitSet) X.clone();
                            X__clone_minusAB.remove(oneAB);//This is X\{A,B}
                            ObjectBigArrayBigList<LongBigArrayBigList> strippedPartition_X_minus_AB =
                                    level_minus1.get(X__clone_minusAB).getPartition().getStrippedPartition();
                            
                            long score = 0;
                            if (!XScoreMap.containsKey(X__clone_minusAB)) {
                                score = calculateInterestingnessScore(strippedPartition_X_minus_AB, X__clone_minusAB);
                                XScoreMap.put(X__clone_minusAB, score);
                            } else {
                                score = XScoreMap.get(X__clone_minusAB);
                            }
                            
                            if (MainClass.InterestingnessPrune) {
                                //check to see whether we should add oneAB or not
                                if (score > MainClass.InterestingnessThreshold) {
                                    allActualSwapCandidates.add(oneAB);
                                }
                                
                            } else {
                                allActualSwapCandidates.add(oneAB);
                            }
                            
                        }
                        
                    }
                    
                    CombinationHelper ch = level1.get(X);
                    
                    ch.setSwapCandidates(allActualSwapCandidates); // in the end set the swap candidates
                    
                }
            }
        }
    }
    
    /**
     * Initialize Cplus_c (resp. rhsCandidates) for each combination of the level.
     */
    private void initializeCplus_c_ForLevel() {
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
            
            
            OpenBitSet CforX_prune = new OpenBitSet();
            
            boolean isRemovedFromCPlus = false;
            
            for (int i = 1; i < numberAttributes + 1; i++) {
                if (CforX.get(i)) {
                    
                    if (X.get(i)) {
                        //we have to check the score of X\i
                        OpenBitSet X__clone = (OpenBitSet) X.clone();
                        X__clone.clear(i);
                        //now X__clone is X\A
                        
                        if (X__clone.isEmpty()) {
                            CforX_prune.set(i);
                        } else {
                            //add to the map to improve performance: XScoreMap.containsKey(CforX_clone)
                            
                            StrippedPartition spXwithoutA = level0.get(X__clone).getPartition();
                            
                            long score = 0;
                            if (!XScoreMap.containsKey(X__clone)) {
                                score = calculateInterestingnessScore(spXwithoutA.getStrippedPartition(), X__clone);
                                XScoreMap.put(X__clone, score);
                            } else {
                                score = XScoreMap.get(X__clone);
                            }
                            if (score > MainClass.InterestingnessThreshold) {
                                CforX_prune.set(i);
                            } else {
                                isRemovedFromCPlus = true;
                            }
                        }
                    } else {
                        //if it is not in X, it should stay in C_c+
                        CforX_prune.set(i);
                    }
                    
                }
                
            }
            
            if (MainClass.InterestingnessPrune) {
                
                
                if (isRemovedFromCPlus) {
                    for (int i = 1; i < numberAttributes + 1; i++) {
                        if (CforX_prune.get(i)) {
                            if (X.get(i)) {
                                //do nothing
                            } else {
                                CforX_prune.clear(i);
                            }
                        }
                    }
                }
                ch.setRhsCandidates(CforX_prune);
            } else {
                ch.setRhsCandidates(CforX);
            }
            
            
        }
    }
    
    private void setColumnIdentifiers() {
        this.columnIdentifiers = new ObjectArrayList<ColumnIdentifier>(this.columnNames.size());
        for (String column_name : this.columnNames) {
            columnIdentifiers.add(new ColumnIdentifier(this.tableName, column_name));
        }
    }
    
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
            for (String attributeName : attributes) {
                if (columnCount < MainClass.MaxColumnNumber) {
                    columnNamesList.add(attributeName);
                    columnCount++;
                }
            }
            
            rowList = new ArrayList<List<String>>();
            
            long rowCount = 0;
            
            while (((line = br.readLine()) != null) && (rowCount < MainClass.MaxRowNumber)) {
                
                String[] tuples = line.split(MainClass.cvsSplitBy);
                
                List<String> row = new ArrayList<String>();
                
                long columnCountForThisRow = 0;
                for (String tupleValue : tuples) {
                    if (columnCountForThisRow < MainClass.MaxColumnNumber) {
                        row.add(tupleValue);
                        columnCountForThisRow++;
                    }
                }
                rowList.add(row);
                
                rowCount++;
            }
            
        } catch (FileNotFoundException e) {
            e.printStackTrace();
        } catch (IOException e) {
            e.printStackTrace();
        } finally {
            if (br != null) {
                try {
                    br.close();
                } catch (IOException e) {
                    e.printStackTrace();
                }
            }
        }
    }
    
    private ObjectArrayList<Object2ObjectOpenHashMap<Object, LongBigArrayBigList>> loadData() {
        
        fillData();
        
        this.numberAttributes = columnNamesList.size();//input.numberOfColumns();
        this.tableName = "";//input.relationName();
        
        this.columnNames = columnNamesList;// input.columnNames();
        
        ObjectArrayList<Object2ObjectOpenHashMap<Object, LongBigArrayBigList>> partitions =
                new ObjectArrayList<Object2ObjectOpenHashMap<Object, LongBigArrayBigList>>(this.numberAttributes);
        for (int i = 0; i < this.numberAttributes; i++) {
            Object2ObjectOpenHashMap<Object, LongBigArrayBigList> partition = new Object2ObjectOpenHashMap<Object, LongBigArrayBigList>();
            partitions.add(partition);
        }
        long tupleId = 0;
        
        id2Val = new ArrayList<>();
        for (int i = 0; i < this.numberAttributes; i++) {
            id2Val.add(new HashMap<>());
        }
        
        //while (input.hasNext()) {
        for (int rowId = 0; rowId < rowList.size(); rowId++) {
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
                    
                    id2Val.get(i).put(tupleId, entry);
                }
            }
            tupleId++;
        }
        
        this.numberTuples = tupleId;
        return partitions;
        
    }
    
    private void printOpenBitSet(String message, OpenBitSet bitSet) {
        System.out.print(message + "  ");
        for (int i = 1; i < numberAttributes + 1; i++) {
            if (bitSet.get(i))
                System.out.print(1 + " ");
            else
                System.out.print(0 + " ");
        }
        System.out.println("");
    }
    
    private void printOpenBitSetNames(String message, OpenBitSet bitSet, OpenBitSet bitSet2) {
        System.out.print("" + message + "  ");
        
        String odVal = "";
        System.out.print("[");
        odVal += "[";
        for (int i = 1; i < numberAttributes + 1; i++) {
            if (bitSet.get(i)) {
                System.out.print(this.columnNames.get(i - 1) + " ");
                odVal += this.columnNames.get(i - 1) + " ";
            }
        }
        System.out.print("] Orders [");
        odVal += "] Orders [";
        
        for (int i = 1; i < numberAttributes + 1; i++) {
            if (bitSet2.get(i)) {
                System.out.print(this.columnNames.get(i - 1) + " ");
                odVal += this.columnNames.get(i - 1) + " ";
            }
        }
        System.out.println("]");
        odVal += "]";
        
        MainClass.odList.add(odVal);
    }
    
    private void printOpenBitSetNamesOCC(String message, OpenBitSet contextBitset, OpenBitSet bitSet, OpenBitSet bitSet2) {
        System.out.print("" + message + "  ");
        for (int i = 1; i < numberAttributes + 1; i++) {
            if (contextBitset.get(i)) {
                System.out.print(this.columnNames.get(i - 1) + " ");
            }
        }
        System.out.print(" -- [");
        for (int i = 1; i < numberAttributes + 1; i++) {
            if (bitSet.get(i)) {
                System.out.print(this.columnNames.get(i - 1) + " ");
            }
        }
        System.out.print("] Orders [");
        
        for (int i = 1; i < numberAttributes + 1; i++) {
            if (bitSet2.get(i)) {
                System.out.print(this.columnNames.get(i - 1) + " ");
            }
        }
        System.out.println("]");

    }
    
    public String getColumnSetName(OpenBitSet bitSet) {
        String columnSetName = "";
        for (int i = 1; i < numberAttributes + 1; i++) {
            if (bitSet.get(i)) {
                columnSetName = columnSetName + this.columnNames.get(i - 1) + "";
            }
        }
        return columnSetName;
    }

// added the function for getting the string output of the function above with some modifications (e.g. removing "orders"):
    // can make it writing into csv instead:
    // need to input three OpenBitSets : A, B, and C (for C:A~B, where C can be a set of attributes)
    
    // This function receives the following as input: OpenBitSets for A, B, and C for C:A~B, number of eq. classes (cardinality) for A, and for B
    // And writes the following information into the csv file specified in input:
    private void toCsvOpenBitSetInfo(String fileAddr, OpenBitSet bitSetC, OpenBitSet bitSetLHS, OpenBitSet bitSetRHS, int cCnt, String LhsCnt, String RhsCnt, int isOC) throws IOException {
        String cName = "";
        String lhsName = "";
        String rhsName = "";
        
        cName = getColumnSetName(bitSetC);
        lhsName = getColumnSetName(bitSetLHS);
        rhsName = getColumnSetName(bitSetRHS);
        
        FileWriter fw = new FileWriter(fileAddr, true);
        PrintWriter out = new PrintWriter(fw);
        // creating the csv line:
        String delim = ";";
        out.print(cName + delim + lhsName + delim + rhsName + delim);
        
        out.print(cCnt);
        out.print(delim);
        
        out.print(LhsCnt);
        out.print(delim);
        out.print(RhsCnt);
        out.print(delim);
        out.println(isOC);
        // writing to csv file:
        out.flush();
        out.close();
        fw.close();
    }
    
    private void writeValidationTimeToCSV(String datasetName, int level, OpenBitSet X_min_AB, OpenBitSet A, OpenBitSet B,
                                          long duration, String depType, long polGroups, long numEqCs, boolean holds, String order) {
        
        String toWrite = new String();
        if (A != null) {
            toWrite += level + ",";
            toWrite += getColumnSetName(X_min_AB) + ",";
            toWrite += getColumnSetName(A) + ",";
            toWrite += getColumnSetName(B) + ",";
            toWrite += duration / 1_000_000 + ",";
            toWrite += depType + ",";
            toWrite += polGroups + ",";
            toWrite += numEqCs + ",";
            toWrite += holds + ",";
            toWrite += order;
            toWrite += '\n';
        } else {
            toWrite += level + ",,,," + (duration / 1_000_000) + "," + depType + ",,,,\n";
        }
        
        try {
            String filename = "stats/" + datasetName + "-ValidationTimeStats-" + numberTuples + "-" + numberAttributes + ".csv";
            FileWriter fw;
            
            if (firstTimeWritingValidationInfo) {
                fw = new FileWriter(filename, false); // will first clear the file
                firstTimeWritingValidationInfo = false;
            } else {
                fw = new FileWriter(filename, true); //the true will append the new data
            }
            
            fw.write(toWrite);//appends the string to the file
            fw.close();
        } catch (IOException ioe) {
            System.err.println("IOException: " + ioe.getMessage());
        }
    }
    
    private void writeGeneralCaseDetailToCSV(String datasetName, int level, OpenBitSet X_min_AB, OpenBitSet A, OpenBitSet B, long numEqCs) {
        
        String toWrite = "";
        toWrite += level + ",";
        toWrite += MainClass.ODAlgorithm.getColumnSetName(X_min_AB) + ",";
        toWrite += MainClass.ODAlgorithm.getColumnSetName(A) + ",";
        toWrite += MainClass.ODAlgorithm.getColumnSetName(B) + ",";
        toWrite += numEqCs + ",";
        
        try {
            String filename = "stats/" + datasetName + "-GeneralCaseStats-" + MainClass.ODAlgorithm.numberTuples + "-" + MainClass.ODAlgorithm.numberAttributes + ".csv";
            FileWriter fw;
            if (firstTimeWritingGeneralInfo) {
                fw = new FileWriter(filename, false); // will first clear the file
                firstTimeWritingGeneralInfo = false;
            } else {
                fw = new FileWriter(filename, true); //the true will append the new data
            }
            fw.write(toWrite);//appends the string to the file
            fw.close();
        } catch (IOException ioe) {
            System.err.println("IOException: " + ioe.getMessage());
        }
    }
    
    public void writeNewReductionGeneralCaseRunTimeToCSV(String datasetName, boolean isConditional, long chainDuration,
                                                         boolean didPassChains, boolean wasSatSuccessful, long reductionDuration,
                                                         long satDuration, long maxUniqVals, boolean holds) {
        
        String toWrite = "";
        toWrite += isConditional + ",";  // index 5
        toWrite += chainDuration / 1_000_000 + ",";  // index 6
        toWrite += didPassChains + ",";
        toWrite += wasSatSuccessful + ",";  // index 8
        toWrite += reductionDuration / 1_000_000 + ",";
        toWrite += satDuration / 1_000_000 + ",";
        toWrite += maxUniqVals + ",";  // index 11
        toWrite += holds;
        toWrite += '\n';
        
        try {
            String filename = "stats/" + datasetName + "-GeneralCaseStats-" + MainClass.ODAlgorithm.numberTuples + "-" + MainClass.ODAlgorithm.numberAttributes + ".csv";
            FileWriter fw = new FileWriter(filename, true); //the true will append the new data
            fw.write(toWrite);//appends the string to the file
            fw.close();
        } catch (IOException ioe) {
            System.err.println("IOException: " + ioe.getMessage());
        }
    }
    
    public String orderToString(List<Map<Long, Set<Long>>> order, int colIndex) {
        StringBuilder res = new StringBuilder();
        Map<Long, String> curId2Val = id2Val.get(colIndex - 1);
        for (Map<Long, Set<Long>> lst: order) {
            res.append("{");
            for (Long k: lst.keySet()) {
                for (Long v: lst.get(k)) {
                    res.append(curId2Val.get(k) + "<" + curId2Val.get(v) + "; ");
                }
            }
            res.append("}; ");
        }
        return res.toString();
    }
}

class FDODScore {
    public long score;
    public OpenBitSet X_minus_AB;
    public OpenBitSet oneAB;
    public FunctionalDependency functionalDependency;
    
    public FDODScore(long score, OpenBitSet X_minus_AB, OpenBitSet oneAB) { // OC
        this.score = score;
        this.X_minus_AB = X_minus_AB;
        this.oneAB = oneAB;
        this.functionalDependency = null;
    }
    
    public FDODScore(long score, FunctionalDependency functionalDependency) { // FD
        this.score = score;
        this.X_minus_AB = null;
        this.oneAB = null;
        this.functionalDependency = functionalDependency;
    }
    
    // add something for generalCaseSOC
    // add something for SOC with syntactic order on one side
    
    public static Comparator<FDODScore> FDODScoreComparator() {
        
        Comparator comp = new Comparator<FDODScore>() {
            public int compare(FDODScore s1, FDODScore s2) {
                if (s1.score < s2.score)
                    return 1;
                if (s1.score > s2.score)
                    return -1;
                return 0;
            }
        };
        return comp;
    }
}

class SpecialScore implements Comparable<SpecialScore> {
    public double score;
    public double simpleScore;
    public String direction;
    public boolean doesFdHold; // storing whether is OC or OD
    public boolean isConditional;
    public OpenBitSet X_minus_AB;
    public OpenBitSet oneAB;
    public String order;
    
    public SpecialScore(double score, double simpleScore, String direction, boolean doesFdHold, boolean isConditional, OpenBitSet x_minus_AB, OpenBitSet oneAB, String order) {
        this.score = score;
        this.simpleScore = simpleScore;
        this.direction = direction;
        this.doesFdHold = doesFdHold;
        this.isConditional = isConditional;
        this.order = order;
        
        X_minus_AB = x_minus_AB;
        this.oneAB = oneAB;
    }
    
    @Override
    public int compareTo(SpecialScore o) {
        return Double.compare(this.score, o.score);
    }
}

class GeneralScore implements Comparable<GeneralScore> {
    public double leftScore;
    public double rightScore;
    public double leftSimpleScore;
    public double rightSimpleScore;
    public boolean isConditional;
    
    public OpenBitSet X_minus_AB;
    public OpenBitSet oneAB;
    
    public String order;
    
    public GeneralScore(double leftScore, double rightScore, double leftSimpleScore, double rightSimpleScore,
                        boolean isConditional, OpenBitSet x_minus_AB, OpenBitSet oneAB, String order) {
        this.leftScore = leftScore;
        this.rightScore = rightScore;
        this.leftSimpleScore = leftSimpleScore;
        this.rightSimpleScore = rightSimpleScore;
        this.isConditional = isConditional;
        this.order = order;
        
        X_minus_AB = x_minus_AB;
        this.oneAB = oneAB;
    }
    
    @Override
    public int compareTo(GeneralScore o) {
        return Double.compare(Math.min(this.leftScore, this.rightScore), Math.min(o.leftScore, o.rightScore));
    }
}
