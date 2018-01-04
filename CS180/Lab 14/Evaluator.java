/**
 * Created by Ryan on 12/2/2015.
 */
import java.util.*;
public class Evaluator {
    public static double evaluate(String arg) {
        Stack<Double> data = new Stack<>();
        String[] arguments = arg.split(" ");
        for (int i = 0; i < arguments.length; i++) {
            double current = Double.MIN_VALUE;
            boolean parsed = false;
            try {
                current = Double.parseDouble(arguments[i]);
                parsed = true;
            }
            catch (Exception e) {
                parsed = false; //Just double check
            }
            if (parsed) {
                data.push(current);
            }
            else {
                if (arguments[i].equals("+")) {
                    //Add last two
                    Double first = data.pop();
                    Double second = data.pop();
                    data.push(first + second);
                }
                else if (arguments[i].equals("–") || arguments[i].equals("-")) {
                    //Subtract last two
                    Double first = data.pop();
                    Double second = data.pop();
                    data.push(second - first);
                }
                else if (arguments[i].equals("*")) {
                    //Multiply last two
                    Double first = data.pop();
                    Double second = data.pop();
                    data.push(first * second);
                }
                else if (arguments[i].equals("/")) {
                    //Divide last two
                    Double first = data.pop();
                    Double second = data.pop();
                    data.push(second / first);
                }
            }
        }
        return data.pop();
    }
}
