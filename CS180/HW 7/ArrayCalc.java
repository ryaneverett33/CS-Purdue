/**
 * CS 180 Homework 07 ArrayCalc
 * This program loops through the contents of a given Array, returns the highest, lowest, and average
 * @author Ryan Everett, everettr@purdue.edu
 */
public class ArrayCalc {
    public String arrayCalc(int[] array) {
        int high = 0;
        int low = 0;
        int average = 0;
        int count = 0;
        int sum = 0;
        boolean lazyBool = false;
        if (array == null ) {
            return "";
        }
        //JAVA HAS A FOREACH LOOP. PRAISE JESUS
        //IT DOESN'T SUCK THAT MUCH AFTER ALL
        for (int i : array) {
            count++;
            if (count == 1) {
                high = i;
                low = i;
                sum = sum + i;
                continue;
            }
            if (high < i) {
                high = i;
            }
            if (low > i) {
                low = i;
            }
            sum = sum + i;
        }
        average = sum / count;
        return "high: " + high + ", low: " + low + ", average: " + average;
        //“high: <highest value in array>, low: <lowest value in array>, average: <mean of values in array>”
    }
}
