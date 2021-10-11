// This is the helper class for discovering FDs used the stripped partitions.

package od;

import it.unimi.dsi.fastutil.longs.LongBigArrayBigList;
import it.unimi.dsi.fastutil.objects.Object2ObjectOpenHashMap;
import it.unimi.dsi.fastutil.objects.ObjectBigArrayBigList;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;

public class StrippedPartition {
    private double error;
    private long elementCount;
    //isAllDouble is a proxy for numeric/non numeric column data type.
    // Only valid for partitions on single attributes (up to 2nd level of lattice)
    private boolean isAllDouble = true;
    private ObjectBigArrayBigList<LongBigArrayBigList> strippedPartition = null;

    /**
     * Create a StrippedPartition with only one equivalence class with the definied number of elements. <br/>
     * Tuple ids start with 0 to numberOfElements-1
     *
     * @param numberTuples
     */
    public StrippedPartition(long numberTuples) {
        this.strippedPartition = new ObjectBigArrayBigList<LongBigArrayBigList>();
        this.elementCount = numberTuples;
        // StrippedPartition only contains partition with more than one elements.
        if (numberTuples > 1) {
            LongBigArrayBigList newEqClass = new LongBigArrayBigList();
            for (int i = 0; i < numberTuples; i++) {
                newEqClass.add(i);
            }
            this.strippedPartition.add(newEqClass);
        }
        this.calculateError();
    }

    /**
     * Create a StrippedPartition from a HashMap mapping the values to the tuple ids.
     *
     * @param partition
     */
    public StrippedPartition(Object2ObjectOpenHashMap<Object, LongBigArrayBigList> partition) {
        this.strippedPartition = new ObjectBigArrayBigList<LongBigArrayBigList>();
        this.elementCount = 0;

        //create stripped partitions -> only use equivalence classes with size > 1.
        for (LongBigArrayBigList eqClass : partition.values()) {
            if (eqClass.size64() > 1) {
                strippedPartition.add(eqClass);
                elementCount += eqClass.size64();
            }
        }
        this.calculateError();
    }

    //

    /**
     * Create a StrippedPartition from a HashMap mapping the values to the tuple ids.
     *
     * @param partition
     * @param TAU_SortedList
     */
    public StrippedPartition(
            Object2ObjectOpenHashMap<Object, LongBigArrayBigList> partition,
            ArrayList<ObjectBigArrayBigList<LongBigArrayBigList>> TAU_SortedList,
            ArrayList<ObjectBigArrayBigList<Integer>> attributeValuesList,
            long numberTuples) {

        this.strippedPartition = new ObjectBigArrayBigList<LongBigArrayBigList>();
        this.elementCount = 0;

        ObjectBigArrayBigList<LongBigArrayBigList> TAU_singleList = new ObjectBigArrayBigList<LongBigArrayBigList>();
        ObjectBigArrayBigList<Integer> attributeSingleList = new ObjectBigArrayBigList<Integer>();



        //OD
        ArrayList<Object> partitionKeyList = new ArrayList<Object>(partition.keySet());

        Collections.sort(partitionKeyList, new Comparator<Object>() {
            @Override
            public int compare(Object o1, Object o2)
            {

                if(!MainClass.ReverseRankingTrue) {

                    boolean isDouble = true;
                    try {
                        double d1 = Double.parseDouble(o1.toString().trim());
                        double d2 = Double.parseDouble(o2.toString().trim());
                    } catch (Exception ex) {
                        isDouble = false;
                        isAllDouble = false;
                    }

                    if (isDouble && MainClass.RankDoubleTrue) {

                        double d1 = Double.parseDouble(o1.toString().trim());
                        double d2 = Double.parseDouble(o2.toString().trim());

                        if (d1 == d2)
                            return 0;
                        if (d1 > d2)
                            return 1;
                        else
                            return -1;

                    } else {
                        String s1 = o1.toString();
                        String s2 = o2.toString();
                        return s1.compareTo(s2);
                    }

                }else{

                    //ReverseRankingTrue is TRUE

                    boolean isDouble = true;
                    try {
                        double d1 = Double.parseDouble(o1.toString().trim());
                        double d2 = Double.parseDouble(o2.toString().trim());
                    } catch (Exception ex) {
                        isDouble = false;
                        isAllDouble = false;
                    }

                    if (isDouble && MainClass.RankDoubleTrue) {

                        double d1 = Double.parseDouble(o1.toString().trim());
                        double d2 = Double.parseDouble(o2.toString().trim());

                        if (d1 == d2)
                            return 0;
                        if (d1 > d2)
                            return 1;
                        else
                            return -1;

                    } else {
                        String s1 = o1.toString();
                        String s2 = o2.toString();

                        if(MainClass.reverseRank) {
                            return -s1.compareTo(s2); //reverse
                        }else{
                            return s1.compareTo(s2); //regular
                        }
                    }

                }
            }
        });

        //create stripped partitions -> only use equivalence classes with size > 1.

        for(int i = 0; i<numberTuples; i ++){
            attributeSingleList.add(-1);
        }

        //OD
        for(int i = 0; i<partitionKeyList.size(); i ++) {
            LongBigArrayBigList eqClass = partition.get(partitionKeyList.get(i));

            if (eqClass.size64() > 1) {
                strippedPartition.add(eqClass);
                elementCount += eqClass.size64();
            }

            //for TAU, we need all eqClasses, including size 1
            TAU_singleList.add(eqClass);

            //add elements to attributeSingleList
            for(long elementId : eqClass){
                attributeSingleList.set(elementId, i);
            }
        }

        TAU_SortedList.add(TAU_singleList);
        attributeValuesList.add(attributeSingleList);

        this.calculateError();
    }



    public StrippedPartition(ObjectBigArrayBigList<LongBigArrayBigList> sp, long elementCount) {
        this.strippedPartition = sp;
        this.elementCount = elementCount;
        this.calculateError();

    }

    public double getError() {
        return error;
    }

    public ObjectBigArrayBigList<LongBigArrayBigList> getStrippedPartition() {
        return this.strippedPartition;
    }

    public boolean getIsAllDouble(){ //if true then attr type is numeric (all column values were numeric)
        return isAllDouble;
    }
    private void calculateError() {
        // calculating the error. Dividing by the number of entries
        // in the whole population is not necessary.
        this.error = this.elementCount - this.strippedPartition.size64();
    }

    public void empty() {
        this.strippedPartition = new ObjectBigArrayBigList<LongBigArrayBigList>();
        this.elementCount = 0;
        this.error = 0.0;
    }
}
