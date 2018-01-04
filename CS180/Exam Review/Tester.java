/**
 * Created by Ryan on 11/10/2015.
 */
public class Tester {
    public static void main(String args[]) {
        MoarMath m = new MoarMath(10,10);
        m.doubleX();
        m.doubleX();
        m.halfX();
        m.doubleX();
        System.out.println(m.getX());
        mathdos md = new mathdos(10,10);
        md.doubleX();
        md.multiplyX(50);
        System.out.println(md.getX());
    }
}
