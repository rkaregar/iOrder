// This is the main class responsible for reading the config file and the initial setup.

package od;

import od.metanome.ORDERLhsRhs;
import org.apache.lucene.util.OpenBitSet;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileReader;
import java.io.FileWriter;
import java.util.*;

public class MainClass {
    public static ODAlgorithm ODAlgorithm;
    public static String datasetName = "NCVoter Shuff";
    public static String ConfigFileName = "config.txt";
    
    
    public static String DatasetFileName = "";
    public static String AlgorithmName = "";
    
    public static int MaxRowNumber = 1000000;
    public static int MaxColumnNumber = 1000;
    public static int RunTimeNumber = 1;
    
    public static String cvsSplitBy = ",";
    
    public static boolean Prune = true;
    
    public static boolean FirstTimeRun = true;
    
    public static boolean InterestingnessPrune = false; // default = false
    
    public static long InterestingnessThreshold = 10000000;
    
    public static int topk = 100; // return how many results
    
    public static boolean BidirectionalTrue = false; // false for now (for bidirectional ODs)
    
    public static boolean RankDoubleTrue = true; // keep true
    
    public static boolean ReverseRankingTrue = false; // keep false (for bidirectional ODs)
    
    public static boolean BidirectionalPruneTrue = false; // no need for now (for bidirectional ODs)
    
    public static boolean DoubleAttributes = false; //
    
    public static boolean FindUnionBool = false; // no need for now (for bidirectional ODs)
    
    public static Random Rand;
    
    public static boolean reverseRank = false; // (for bidirectional ODs)
    
    public static int ReverseRankingPercentage = 90; //(not needed) larger than 100 will always reverse it, negative will be regular ranking
    
    public static boolean OnlyCheckConditionalIIOC = false;  // will never consider unconditional cases
    
    public static List<Boolean> isColumnActive = new ArrayList<>();
    
    public static List<String> odList = new ArrayList<String>(); // results
    public static List<String> finalOCResults = new ArrayList<>(); // final results, used to print in the log file
    public static List<String> latticeWiseData = new ArrayList<>();  // stores runtime + # of OCs at each level
    public static long pairBasedScoreTotalTime = 0;
    public static long pathBasedScoreTotalTime = 0;
    
    public static int numOfFoundIIODs = 0;
    
    public static void main(String[] args) {
        
        printTime();
        
        Rand = new Random(19999);
        
        try {
            BufferedReader br = new BufferedReader(new FileReader(ConfigFileName));
            
            DatasetFileName = br.readLine().trim();
            AlgorithmName = br.readLine().trim();
            
            MaxRowNumber = Integer.parseInt(br.readLine().trim());
            MaxColumnNumber = Integer.parseInt(br.readLine().trim());
            RunTimeNumber = Integer.parseInt(br.readLine().trim());
            
            String lineSeparator = br.readLine().trim();
            cvsSplitBy = lineSeparator;
            
            String pruneS = br.readLine().trim();
            if (pruneS.equals("PruneFalse"))
                Prune = false;
            
            String InterestingnessPruneS = br.readLine().trim();
            if (InterestingnessPruneS.equals("InterestingnessPruneTrue"))
                InterestingnessPrune = true;
            
            InterestingnessThreshold = Long.parseLong(br.readLine().trim());
            
            topk = Integer.parseInt(br.readLine().trim()); // now it's 100 in the input file
            
            String BidirectionalTrueS = br.readLine().trim();
            if (BidirectionalTrueS.equals("BidirectionalTrue"))
                BidirectionalTrue = true;
            
            String RankDoubleTrueS = br.readLine().trim();
            if (!RankDoubleTrueS.equals("RankDoubleTrue"))
                RankDoubleTrue = false;
            
            String ReverseRankingTrueS = br.readLine().trim();
            if (ReverseRankingTrueS.equals("ReverseRankingTrue"))
                ReverseRankingTrue = true;
            
            String BidirectionalPruneTrueS = br.readLine().trim();
            if (BidirectionalPruneTrueS.equals("BidirectionalPruneTrue"))
                BidirectionalPruneTrue = true;
            
            ReverseRankingPercentage = Integer.parseInt(br.readLine().trim());
            
            String OnlyCheckConditionalIIOCS = br.readLine().trim();
            if (OnlyCheckConditionalIIOCS.equals("OnlyConditionalIIOCTrue"))
                OnlyCheckConditionalIIOC = true;
            
            String listOfColActivation = br.readLine();
            if (listOfColActivation != null) {
                String[] activeColumns = listOfColActivation.trim().split(" ");
                for (String activeColumn : activeColumns) {
                    isColumnActive.add(Integer.parseInt(activeColumn) == 1);
                }
            } else {
                for (int i = 0; i < MaxColumnNumber; i++) {
                    isColumnActive.add(true);
                }
            }
            
        } catch (Exception ex) {
            ex.printStackTrace();
            return;
        }
        
        TaneAlgorithm taneAlgorithm = new TaneAlgorithm();

        ODAlgorithm = new ODAlgorithm();
        
        
        ORDERLhsRhs ORDERAlgorithm = new ORDERLhsRhs();
        
        System.out.println("Algorithm: " + AlgorithmName);
        System.out.println("InterestingnessPrune: " + InterestingnessPrune);
        System.out.println("InterestingnessThreshold: " + InterestingnessThreshold);
        System.out.println("BidirectionalTrue: " + BidirectionalTrue);
        System.out.println("BidirectionalPruneTrue: " + BidirectionalPruneTrue);
        
        // Executing the proper discovery algorithm based on the provided config file.
        long startTime, runTime = 0;
        try {
            startTime = System.currentTimeMillis();
            
            for (int i = 0; i < RunTimeNumber; i++) {
                
                if (AlgorithmName.equals("TANE"))
                    taneAlgorithm.execute();
                
                if (AlgorithmName.equals("FastOD"))
                    ODAlgorithm.execute();
                
                if (AlgorithmName.equals("ORDER"))
                    ORDERAlgorithm.execute();
                
                FirstTimeRun = false;
            }
            
            long endTime = System.currentTimeMillis();
            runTime = (endTime - startTime) / RunTimeNumber;
            
            System.out.println("Run Time (ms): " + runTime);
        } catch (Exception ex) {
            System.out.println("Error");
            ex.printStackTrace();
        }
        
        printTime();
        
        writeMainStatToFile(runTime + " runtime(ms)", false);
        writeMainStatToFile((pairBasedScoreTotalTime / 1_000_000) + " PairScoreTime(ms)", false);
        writeMainStatToFile((pathBasedScoreTotalTime / 1_000_000) + " PathScoreTime(ms)", false);
    
        for (String latticeDetail :
                latticeWiseData) {
            writeMainStatToFile(latticeDetail, false);
        }
        for (String ocDetail :
                finalOCResults) {
            writeMainStatToFile(ocDetail, false);
        }
        
        if (numOfFoundIIODs > 0)
            writeMainStatToFile("Found" + numOfFoundIIODs + "  IIODs", false);
        
        try {
            BufferedWriter bw =
                    new BufferedWriter(new FileWriter("result.txt"));
            
            for (String str : odList)
                bw.write(str + "\n");
            
            bw.close();
        } catch (Exception ex) {
            System.out.println(ex.getMessage());
        }
        
    }
    
    // Writing final aggregated statistics in the `stats/` directory
    public static void writeMainStatToFile(String textToWrite, boolean clearFileIfExists) {
        try {
            String filename = "stats/" + DatasetFileName + "-MainStats-" + ODAlgorithm.numberTuples + "-" + ODAlgorithm.numberAttributes + ".txt";
            FileWriter fw;
            if (clearFileIfExists) {
                fw = new FileWriter(filename, false);
            } else {
                fw = new FileWriter(filename, true);
            }
            fw.write(textToWrite + "\n");
            fw.close();
        } catch (Exception ex) {
            System.out.println(ex.getMessage());
        }
    }
    
    // Printing the runtime output in the standard output stream.
    public static void printTime() {
        Calendar now = Calendar.getInstance();
        int year = now.get(Calendar.YEAR);
        int month = now.get(Calendar.MONTH) + 1; // Note: zero based!
        int day = now.get(Calendar.DAY_OF_MONTH);
        int hour = now.get(Calendar.HOUR_OF_DAY);
        int minute = now.get(Calendar.MINUTE);
        int second = now.get(Calendar.SECOND);
        int millis = now.get(Calendar.MILLISECOND);
        
        System.out.printf("%d-%02d-%02d %02d:%02d:%02d", year, month, day, hour, minute, second);
        System.out.println("\n");
    }
    
    public static void printOpenBitSet(OpenBitSet bitSet, int maxLength) {
        for (int i = 0; i < maxLength; i++) {
            if (bitSet.get(i))
                System.out.print(1 + " ");
            else
                System.out.print(0 + " ");
        }
        System.out.println("");
    }
    
}

