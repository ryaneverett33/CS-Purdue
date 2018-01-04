/**
 * Created by Ryan on 12/2/2015.
 */
public class EvalTest {
    public static void main(String args[]) {
        System.out.println(Evaluator.evaluate("5 1 2 + 4 * + 3 -"));    //print 14
        System.out.println(Evaluator.evaluate("20 30 +"));  //print 50
        System.out.println(Evaluator.evaluate("3 5 * 5 – 3 5 + * 2 /"));    //print 40

    }
}
