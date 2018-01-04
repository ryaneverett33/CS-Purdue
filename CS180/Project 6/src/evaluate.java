/**
 * Created by Ryan on 12/5/2015.
 */
public class evaluate {
    public static double equal(String display) {
        final int ADDOP = 1;    //currentOp
        final int SUBOP = 2;
        final int MULOP = 3;
        final int DIVOP = 4;

        String displayCopy = "";
        boolean hasCopy = false;

        if (display.length() == 0) {
            //view.invalid();
            return 0.0;
        }
        //If display contains a '/' or a '*'
        boolean mulDiv = display.contains("/") || display.contains("*");
        boolean addSub = display.contains("+") || display.contains("-");
        //Expression is already equal to itself, no evaluation required
        if (!mulDiv && !addSub) return Double.parseDouble(display);
        String[] lines = evaluate.split(display);
        if (lines[lines.length - 1].length() == 0) {
            //view.invalid();
            return 0.0;
        }
        if (!mulDiv && addSub) {
            //The most basic expression evaluation
            boolean found = false;
            boolean finished = false;
            double first = -200;
            double second = -200;
            int currentOp = -1;
            double result = -1000;
            do {
                char[] digits = display.toCharArray();
                found = false;
                finished = false;
                currentOp = -1;
                first = -200;
                second = -200;
                for (int i = 0; i < digits.length; i++) {
                    if (digits[i] == '+' || digits[i] == '-' || (i == (digits.length - 1) && currentOp != -1)) {
                        found = true;
                        if (currentOp == -1) {
                            //set currentOp
                            if (digits[i] == '+') currentOp = ADDOP;
                            else currentOp = SUBOP;
                            first = Double.parseDouble(lines[0]);
                        }
                        else {
                            //Do the operation
                            second = Double.parseDouble(lines[1]);
                            if (currentOp == ADDOP) result = first + second;
                            else result = first - second;
                            finished = true;
                        }
                    }
                    if (finished) {
                        //pass finished, set display and lines
                        int begin = lines[0].length() + 1 + lines[1].length();
                        display = Double.toString(result) + display.substring(begin, display.length());
                        lines = evaluate.split(display);
                        break;
                    }
                }
            }
            while (found);
            return result;
        }
        else if (!addSub && mulDiv) {
            //Lesser easy expression evaluation
            return 0.0;
        }
        else {
            //Things become hard
            return 0.0;
        }
    }
    public static String[] split(String display) {
        //Returns the split version of the display string
        int count = 0;
        char[] characters = display.toCharArray();
        //'/', '*', '+', '-'
        for (char c : characters) {
            if (c == '/' || c == '*' || c == '+' || c == '-') {
                count++;
            }
        }
        String[] splitted =  display.split("[/*+-]");
        //Regular expression to split based on the operators
        if (splitted.length == count) {
            String[] tmp = new String[count + 1];
            for (int i = 0; i < count; i++) {
                tmp[i] = splitted[i];
            }
            tmp[count] = "";
            return tmp;
        }
        else {
            return splitted;
        }
    }
}
