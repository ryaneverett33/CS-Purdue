/**
 * Created by Ryan on 9/20/2015.
 */
public class ArrayCalcClient {
    static public void main(String args[]) {
        ArrayCalc a = new ArrayCalc();
        System.out.println(a.arrayCalc(new int[]{1, 2, 3})); //prints "high: 3, low: 1, average: 2"
        System.out.println(a.arrayCalc(new int[]{0})); //prints "high: 0, low: 0, average: 0"
        System.out.println(a.arrayCalc(null)); //prints ""
    }
}
